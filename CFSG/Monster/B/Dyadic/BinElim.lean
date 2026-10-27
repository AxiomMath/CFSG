module

public import Certificates.Data.CFSGNative.MonsterB.BinaryElim
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Monster.B.Binary

open CFSG.Sporadic.SmallF2 Native

structure TableInv (d : ℕ) (T : Array ℕ) (S : Submodule (ZMod 2) (Fin d → ZMod 2)) : Prop where
  size : T.size = d
  entry : ∀ p < d, T[p]! = 0 ∨ Nat.log2 T[p]! = p
  mem : ∀ p < d, toVecD d T[p]! ∈ S

@[expose] noncomputable def entrySpan (d : ℕ) (T : Array ℕ) : Submodule (ZMod 2) (Fin d → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun p : Fin d => toVecD d T[(p : ℕ)]!)

theorem getD_eq_get! (T : Array ℕ) (p : ℕ) : T[p]?.getD 0 = T[p]! := by
  by_cases h : p < T.size
  · rw [getElem?_pos T p h, Option.getD_some, getElem!_pos T p h]
  · rw [getElem?_neg T p h, Option.getD_none, getElem!_neg T p h]
    rfl

theorem size_set! (T : Array ℕ) (p v : ℕ) : (T.set! p v).size = T.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem get!_set! (T : Array ℕ) (p q v : ℕ) (hp : p < T.size) :
    (T.set! p v)[q]! = if p = q then v else T[q]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hq : q < T.size
  · rw [getElem!_pos (T.setIfInBounds p v) q (by rw [Array.size_setIfInBounds]; exact hq),
      Array.getElem_setIfInBounds, getElem!_pos T q hq]
  · rw [getElem!_neg (T.setIfInBounds p v) q (by rw [Array.size_setIfInBounds]; exact hq),
      getElem!_neg T q hq, ite_eq_right (by omega)]

theorem toVecD_xor_add (d v t : ℕ) : toVecD d v = toVecD d (v ^^^ t) + toVecD d t := by
  rw [toVecD_xor]
  funext j
  simp only [Pi.add_apply]
  generalize toVecD d v j = a
  generalize toVecD d t j = b
  revert a b
  decide

theorem entrySpan_mono {d : ℕ} {T T' : Array ℕ} (h : ∀ p < d, T[p]! ≠ 0 → T'[p]! = T[p]!) :
    entrySpan d T ≤ entrySpan d T' := by
  rw [entrySpan, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  show toVecD d T[(p : ℕ)]! ∈ entrySpan d T'
  by_cases hp : T[(p : ℕ)]! = 0
  · rw [hp, toVecD_zero]
    exact Submodule.zero_mem _
  · rw [← h p p.2 hp]
    exact Submodule.subset_span ⟨p, rfl⟩

theorem insertVec_spec {d : ℕ} {S : Submodule (ZMod 2) (Fin d → ZMod 2)} :
    ∀ (fuel : ℕ) (T T' : Array ℕ) (v : ℕ), TableInv d T S → v < 2 ^ d → toVecD d v ∈ S →
      insertVec T fuel v = some T' →
      TableInv d T' S ∧ (∀ p < d, T[p]! ≠ 0 → T'[p]! = T[p]!) ∧ toVecD d v ∈ entrySpan d T'
  | 0, T, T', v, _, _, _, h => by simp [insertVec] at h
  | fuel + 1, T, T', v, hT, hv, hS, h => by
    rw [insertVec] at h
    by_cases hv0 : v = 0
    · rw [ite_eq_left hv0, Option.some.injEq] at h
      subst h
      refine ⟨hT, fun _ _ _ => rfl, ?_⟩
      rw [hv0, toVecD_zero]
      exact Submodule.zero_mem _
    · rw [ite_eq_right hv0] at h
      simp only at h
      have hp : Nat.log2 v < d := (Nat.log2_lt hv0).2 hv
      have hps : Nat.log2 v < T.size := hT.size ▸ hp
      rw [getD_eq_get!] at h
      by_cases ht : T[Nat.log2 v]! = 0
      · rw [ite_eq_left ht, Option.some.injEq] at h
        subst h
        refine ⟨⟨by rw [size_set!, hT.size], fun q hq => ?_, fun q hq => ?_⟩,
          fun q hq hq0 => ?_, ?_⟩
        · rw [get!_set! _ _ _ _ hps]
          split
          · next he => subst he; right; rfl
          · exact hT.entry q hq
        · rw [get!_set! _ _ _ _ hps]
          split
          · exact hS
          · exact hT.mem q hq
        · rw [get!_set! _ _ _ _ hps, ite_eq_right]
          rintro rfl
          exact hq0 ht
        · have : toVecD d v =
              toVecD d (T.set! (Nat.log2 v) v)[((⟨Nat.log2 v, hp⟩ : Fin d) : ℕ)]! := by
            rw [get!_set! _ _ _ _ hps, ite_eq_left rfl]
          rw [this]
          exact Submodule.subset_span ⟨⟨Nat.log2 v, hp⟩, rfl⟩
      · rw [ite_eq_right ht] at h
        have htlt : T[Nat.log2 v]! < 2 ^ d := by
          rcases hT.entry _ hp with h0 | h0
          · exact absurd h0 ht
          · have := @Nat.lt_log2_self (T[Nat.log2 v]!)
            rw [h0] at this
            exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hp)
        obtain ⟨h1, h2, h3⟩ := insertVec_spec fuel T T' (v ^^^ T[Nat.log2 v]!) hT
          (Nat.xor_lt_two_pow hv htlt)
          (by rw [toVecD_xor]; exact Submodule.add_mem _ hS (hT.mem _ hp)) h
        refine ⟨h1, h2, ?_⟩
        rw [toVecD_xor_add d v (T[Nat.log2 v]!)]
        refine Submodule.add_mem _ h3 ?_
        rw [← h2 _ hp ht]
        exact Submodule.subset_span ⟨⟨Nat.log2 v, hp⟩, rfl⟩

theorem elimList_spec {d : ℕ} {S : Submodule (ZMod 2) (Fin d → ZMod 2)} :
    ∀ (vs : List ℕ) (T T' : Array ℕ), TableInv d T S → (∀ v ∈ vs, v < 2 ^ d ∧ toVecD d v ∈ S) →
      elimList d T vs = some T' →
      TableInv d T' S ∧ (∀ p < d, T[p]! ≠ 0 → T'[p]! = T[p]!) ∧
        ∀ v ∈ vs, toVecD d v ∈ entrySpan d T'
  | [], T, T', hT, _, h => by
    rw [elimList, Option.some.injEq] at h
    subst h
    exact ⟨hT, fun _ _ _ => rfl, fun v hv => by simp at hv⟩
  | v :: vs, T, T', hT, hvs, h => by
    rw [elimList] at h
    split at h
    · exact absurd h (by simp)
    · next T1 h1 =>
      obtain ⟨hT1, hm1, hv1⟩ := insertVec_spec (d + 1) T T1 v hT (hvs v (by simp)).1
        (hvs v (by simp)).2 h1
      obtain ⟨hT', hm', hvs'⟩ := elimList_spec vs T1 T' hT1
        (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) h
      refine ⟨hT', fun p hp hp0 => ?_, fun w hw => ?_⟩
      · rw [hm' p hp (by rw [hm1 p hp hp0]; exact hp0), hm1 p hp hp0]
      · rcases List.mem_cons.1 hw with rfl | hw
        · exact entrySpan_mono hm' hv1
        · exact hvs' w hw

@[expose] noncomputable def listSpan (d : ℕ) (vs : List ℕ) : Submodule (ZMod 2) (Fin d → ZMod 2) :=
  Submodule.span (ZMod 2) {w | ∃ v ∈ vs, toVecD d v = w}

theorem elimTable_spec {d : ℕ} {vs : List ℕ} {T : Array ℕ} (hvs : ∀ v ∈ vs, v < 2 ^ d)
    (h : elimTable d vs = some T) :
    TableInv d T (listSpan d vs) ∧ ∀ v ∈ vs, toVecD d v ∈ entrySpan d T := by
  have h0 : TableInv d (Array.replicate d 0) (listSpan d vs) := by
    refine ⟨by simp, fun p _ => Or.inl ?_, fun p _ => ?_⟩
    · rw [getElem!_pos _ p (by simpa using ‹p < d›)]
      simp
    · rw [getElem!_pos _ p (by simpa using ‹p < d›), Array.getElem_replicate, toVecD_zero]
      exact Submodule.zero_mem _
  obtain ⟨hT, -, hin⟩ := elimList_spec vs _ T h0
    (fun v hv => ⟨hvs v hv, Submodule.subset_span ⟨v, hv, rfl⟩⟩) h
  exact ⟨hT, hin⟩

theorem entrySpan_elimTable {d : ℕ} {vs : List ℕ} {T : Array ℕ} (hvs : ∀ v ∈ vs, v < 2 ^ d)
    (h : elimTable d vs = some T) : entrySpan d T = listSpan d vs := by
  obtain ⟨hT, hin⟩ := elimTable_spec hvs h
  apply le_antisymm
  · rw [entrySpan, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hT.mem p p.2
  · rw [listSpan, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact hin v hv

theorem bit_high {x p : ℕ} (hx : Nat.log2 x = p) {j : ℕ} (hj : p < j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (hx ▸ Nat.lt_log2_self)
    (Nat.pow_le_pow_right (by norm_num) hj))

theorem bit_top {x p : ℕ} (h0 : x ≠ 0) (hx : Nat.log2 x = p) : x.testBit p = true :=
  hx ▸ Nat.testBit_log2 h0

theorem dot_entry {d : ℕ} {x : ℕ} {p : Fin d} (h0 : x ≠ 0) (hx : Nat.log2 x = p)
    (δ : Fin d → ZMod 2) (hlow : ∀ j : Fin d, j < p → δ j = 0) : δ ⬝ᵥ toVecD d x = δ p := by
  rw [dotProduct, Finset.sum_eq_single p]
  · rw [toVecD_apply, ite_eq_left (bit_top h0 hx), mul_one]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hlow j h, zero_mul]
    · rw [toVecD_apply, ite_eq_right (by rw [bit_high hx h]; simp), mul_zero]
  · simp

theorem orth_unique {d : ℕ} {T : Array ℕ} (hT : ∀ p < d, T[p]! = 0 ∨ Nat.log2 T[p]! = p)
    {y y' : Fin d → ZMod 2} (hy : ∀ p : Fin d, T[(p : ℕ)]! ≠ 0 → y ⬝ᵥ toVecD d T[(p : ℕ)]! = 0)
    (hy' : ∀ p : Fin d, T[(p : ℕ)]! ≠ 0 → y' ⬝ᵥ toVecD d T[(p : ℕ)]! = 0)
    (hfree : ∀ p : Fin d, T[(p : ℕ)]! = 0 → y p = y' p) : y = y' := by
  have key : ∀ n, ∀ p : Fin d, (p : ℕ) = n → (y - y') p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp
      by_cases h0 : T[(p : ℕ)]! = 0
      · rw [Pi.sub_apply, hfree p h0, sub_self]
      · have hx := (hT p p.2).resolve_left h0
        have := dot_entry h0 hx (y - y') (fun j hj => ih j (hp ▸ hj) j rfl)
        rw [← this, sub_dotProduct, hy p h0, hy' p h0, sub_self]
  funext p
  exact sub_eq_zero.1 (key p p rfl)

theorem entry_linIndep {d : ℕ} {T : Array ℕ} (hT : ∀ p < d, T[p]! = 0 ∨ Nat.log2 T[p]! = p) :
    LinearIndependent (ZMod 2)
      (fun p : {p : Fin d // T[(p : ℕ)]! ≠ 0} => toVecD d T[((p : Fin d) : ℕ)]!) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg
  set v := fun p : {p : Fin d // T[(p : ℕ)]! ≠ 0} => toVecD d T[((p : Fin d) : ℕ)]! with hv
  have hcoord : ∀ (c : {p : Fin d // T[(p : ℕ)]! ≠ 0} → ZMod 2)
      (i : {p : Fin d // T[(p : ℕ)]! ≠ 0}), (∑ r, c r • v r) (i : Fin d) =
        c i + ∑ r : {p : Fin d // T[(p : ℕ)]! ≠ 0},
          if (i : Fin d) < (r : Fin d) then c r * v r (i : Fin d) else 0 := by
    intro c i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hci : c i = ∑ r : {p : Fin d // T[(p : ℕ)]! ≠ 0}, if r = i then c r else 0 := by
      rw [Finset.sum_ite_eq']
      simp
    rw [hci, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hri : r = i
    · subst hri
      rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _), add_zero, hv]
      simp only
      rw [toVecD_apply, ite_eq_left (bit_top r.2 ((hT _ (r : Fin d).2).resolve_left r.2)),
        mul_one]
    · rw [ite_eq_right hri, zero_add]
      have hne : (r : Fin d) ≠ (i : Fin d) := fun e => hri (Subtype.ext e)
      rcases lt_or_gt_of_ne hne with h | h
      · rw [ite_eq_right (not_lt.2 h.le), hv]
        simp only
        rw [toVecD_apply, ite_eq_right (by
          rw [bit_high ((hT _ (r : Fin d).2).resolve_left r.2) h]; simp), mul_zero]
      · rw [ite_eq_left h]
  have key : ∀ n, ∀ i : {p : Fin d // T[(p : ℕ)]! ≠ 0}, d - (i : Fin d) = n → f i = g i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hc := congrFun hfg (i : Fin d)
      rw [hcoord f i, hcoord g i] at hc
      have htail : (∑ r : {p : Fin d // T[(p : ℕ)]! ≠ 0},
          if (i : Fin d) < (r : Fin d) then f r * v r (i : Fin d) else 0) =
          ∑ r : {p : Fin d // T[(p : ℕ)]! ≠ 0},
            if (i : Fin d) < (r : Fin d) then g r * v r (i : Fin d) else 0 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        split
        · next h =>
          have h1 := (r : Fin d).2
          have h2 := (i : Fin d).2
          rw [Fin.lt_def] at h
          rw [ih (d - (r : Fin d)) (by omega) r rfl]
        · rfl
      rw [htail] at hc
      exact add_right_cancel hc
  intro i
  exact key _ i rfl

theorem entrySpan_eq {d : ℕ} (T : Array ℕ) :
    entrySpan d T = Submodule.span (ZMod 2)
      (Set.range fun p : {p : Fin d // T[(p : ℕ)]! ≠ 0} => toVecD d T[((p : Fin d) : ℕ)]!) := by
  apply le_antisymm
  · rw [entrySpan, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    show toVecD d T[(p : ℕ)]! ∈ _
    by_cases hp : T[(p : ℕ)]! = 0
    · rw [hp, toVecD_zero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨p, rfl⟩
    exact ⟨p, rfl⟩

theorem finrank_entrySpan {d : ℕ} {T : Array ℕ} (hT : ∀ p < d, T[p]! = 0 ∨ Nat.log2 T[p]! = p) :
    Module.finrank (ZMod 2) (entrySpan d T) =
      (Finset.univ.filter fun p : Fin d => T[(p : ℕ)]! ≠ 0).card := by
  rw [entrySpan_eq, finrank_span_eq_card (entry_linIndep hT), Fintype.card_subtype]

end CFSG.Monster.B.Binary
