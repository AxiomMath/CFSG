
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def EnumOK (n : ℕ) (Gt : List (List ℕ)) (L : List (List ℕ)) (par : List (ℕ × ℕ)) :
    Prop :=
  L.Nodup ∧ L.head? = some (List.range n) ∧ par.length = L.length ∧
    (∀ i < L.length, 0 < i → (par.getD i (0, 0)).1 < i ∧ (par.getD i (0, 0)).2 < Gt.length ∧
      L.getD i [] = compTab (L.getD (par.getD i (0, 0)).1 []) (Gt.getD (par.getD i (0, 0)).2 [])) ∧
    (∀ t ∈ L, ∀ s ∈ Gt, compTab t s ∈ L)

instance (n : ℕ) (Gt : List (List ℕ)) (L : List (List ℕ)) (par : List (ℕ × ℕ)) :
    Decidable (EnumOK n Gt L par) := by
  unfold EnumOK; infer_instance

section Clos

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem right_inv_of_right (P : Γ → Prop) (g : Γ) (h : ∀ x, P x → P (x * g)) {x : Γ}
    (hx : P x) : P (x * g⁻¹) := by
  have hpow : ∀ k : ℕ, P (x * g ^ k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ, ← mul_assoc]; exact h _ ih
  have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
  rw [hinv]
  exact hpow _

theorem enum_closure {n : ℕ} (T : Γ → List ℕ) (hT1 : T 1 = List.range n)
    (hTm : ∀ x y, T (x * y) = compTab (T x) (T y)) (hTi : Function.Injective T)
    (gens : List Γ) {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK n (gens.map T) L par) :
    (∀ x : Γ, x ∈ Subgroup.closure {g | g ∈ gens} ↔ T x ∈ L) ∧
      Nat.card (Subgroup.closure {g | g ∈ gens}) = L.length ∧
      ∀ t ∈ L, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, T x = t := by
  obtain ⟨hnd, hhead, hpar, hstep, hclosed⟩ := h
  have hgl : (gens.map T).length = gens.length := List.length_map _
  have hreach : ∀ i, ∀ hi : i < L.length, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, T x = L[i] := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [hT1]
        cases L with
        | nil => simp at hi
        | cons a l => simpa using hhead.symm
      · obtain ⟨hp, hs, heq⟩ := hstep i hi hpos
        have hp' : (par.getD i (0, 0)).1 < L.length := by omega
        obtain ⟨x, hx, hxT⟩ := ih _ hp hp'
        have hs' : (par.getD i (0, 0)).2 < gens.length := by omega
        refine ⟨x * gens[(par.getD i (0, 0)).2], Subgroup.mul_mem _ hx
          (Subgroup.subset_closure (List.getElem_mem hs')), ?_⟩
        rw [hTm, hxT]
        have e1 : L.getD i [] = L[i] := by rw [List.getD_eq_getElem _ _ hi]
        have e2 : L.getD (par.getD i (0, 0)).1 [] = L[(par.getD i (0, 0)).1] := by
          rw [List.getD_eq_getElem _ _ hp']
        have e3 : (gens.map T).getD (par.getD i (0, 0)).2 [] = T gens[(par.getD i (0, 0)).2] := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          simp
        rw [e1, e2, e3] at heq
        exact heq.symm
  have hin : ∀ x ∈ Subgroup.closure {g | g ∈ gens}, T x ∈ L := by
    intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one =>
      rw [hT1]
      cases L with
      | nil => simp at hhead
      | cons a l => simp at hhead; simp [hhead]
    | mul_right x hx y hy ih =>
      rw [hTm]
      exact hclosed _ ih _ (List.mem_map.mpr ⟨y, hy, rfl⟩)
    | mul_inv_cancel x hx y hy ih =>
      exact right_inv_of_right (fun z => T z ∈ L) y (fun z hz => by
        rw [hTm]; exact hclosed _ hz _ (List.mem_map.mpr ⟨y, hy, rfl⟩)) ih
  refine ⟨fun x => ⟨hin x, fun hxL => ?_⟩, ?_, fun t ht => ?_⟩
  · obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem hxL
    obtain ⟨y, hy, hyT⟩ := hreach i hi
    have : y = x := hTi (hyT.trans hiL)
    rwa [← this]
  · have hbij : Function.Bijective (fun x : Subgroup.closure {g | g ∈ gens} =>
        (⟨T x, hin x x.2⟩ : {t // t ∈ L})) := by
      constructor
      · intro x y hxy
        exact Subtype.ext (hTi (congrArg Subtype.val hxy))
      · rintro ⟨t, ht⟩
        obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem ht
        obtain ⟨y, hy, hyT⟩ := hreach i hi
        exact ⟨⟨y, hy⟩, Subtype.ext (hyT.trans hiL)⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
    have hnd' : L.attach.Nodup := List.nodup_attach.mpr hnd
    let e := hnd'.getEquivOfForallMemList L.attach (fun x => List.mem_attach _ x)
    rw [← Nat.card_congr e]
    simp
  · obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem ht
    obtain ⟨y, hy, hyT⟩ := hreach i hi
    exact ⟨y, hy, hyT.trans hiL⟩

end Clos

end CFSG.Quasithin.A312M24
