module

public import CFSG.Timmesfeld.ARS.LinearHyper
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Linear

theorem le_stabSet_iff_of_mem_dualPoint {Δ : Set (Subgroup G)} {X Y : Subgroup G}
    (hX : X ∈ dualPoint R Δ Y) {P : Set (Subgroup G)} (hP : IsPoint Δ P) :
    X ≤ stabSet P ↔ Y ≤ stabSet P := by
  constructor
  · intro h
    have : P ∈ axis Δ X := ⟨hP, h⟩
    rw [hX.2] at this
    exact this.2
  · intro h
    have : P ∈ axis Δ Y := ⟨hP, h⟩
    rw [← hX.2] at this
    exact this.2

theorem card_gen_conjSet (S : Set (Subgroup G)) (g : G) :
    Nat.card ↥(gen (conjSet S g)) = Nat.card ↥(gen S) := by
  rw [← conjSub_gen, conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem IsPoint.card_gen {Δ P : Set (Subgroup G)} (hP : IsPoint Δ P) :
    Nat.card ↥(gen P) = Nat.card ↥(gen Δ) := by
  obtain ⟨g, rfl⟩ := hP
  exact card_gen_conjSet Δ g

theorem one_lt_card_of_mem [Finite G] (hR : IsRootClass R) {E : Subgroup G} (hE : E ∈ R) :
    1 < Nat.card E :=
  (Subgroup.one_lt_card_iff_ne_bot E).2 (hR.ne_bot E hE)

section Counting

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ)
include hR hiso hnd hΩ hΔ

theorem relIndex_stabSet_eq {P P' : Set (Subgroup G)} (hP : IsPoint Δ P) (hP' : IsPoint Δ P')
    (hne : P ≠ P') {E : Subgroup G} (hE : E ∈ R) :
    (stabSet P').relIndex (gen P) = Nat.card E := by
  have h1 := Subgroup.relIndex_mul_card (H := stabSet P') (K := gen P)
  rw [inf_comm, card_gen_eq_card_mul_card_inf hR hiso hnd hΩ hΔ hP hP' hne hE] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem card_gen_le_pow_mul {ι : Type*} {P : Set (Subgroup G)} (hP : IsPoint Δ P)
    {E : Subgroup G} (hE : E ∈ R) (f : ι → Set (Subgroup G)) (s : Finset ι)
    (hf : ∀ i ∈ s, IsPoint Δ (f i)) (hne : ∀ i ∈ s, f i ≠ P) :
    Nat.card ↥(gen P) ≤ Nat.card E ^ s.card * Nat.card ↥(gen P ⊓ ⨅ i ∈ s, stabSet (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi))
    set K := gen P ⊓ ⨅ i ∈ s, stabSet (f i) with hK
    have hKle : K ≤ gen P := inf_le_left
    have hrel := relIndex_stabSet_eq hR hiso hnd hΩ hΔ hP (hf a (Finset.mem_insert_self a s))
      (Ne.symm (hne a (Finset.mem_insert_self a s))) hE
    have hrelK : (stabSet (f a)).relIndex K ≤ Nat.card E := by
      rw [← hrel]
      exact Subgroup.relIndex_le_of_le_right hKle
        (by rw [hrel]; exact (one_lt_card_of_mem hR hE).ne_bot)
    have h1 := Subgroup.relIndex_mul_card (H := stabSet (f a)) (K := K)
    have heq : gen P ⊓ ⨅ i ∈ insert a s, stabSet (f i) = stabSet (f a) ⊓ K := by
      rw [Finset.iInf_insert, hK, ← inf_assoc, inf_comm (gen P) (stabSet (f a)), inf_assoc]
    rw [heq, Finset.card_insert_of_notMem has, pow_succ]
    calc Nat.card ↥(gen P) ≤ Nat.card E ^ s.card * Nat.card K := ih'
      _ = Nat.card E ^ s.card * ((stabSet (f a)).relIndex K * Nat.card ↥(stabSet (f a) ⊓ K)) := by
          rw [h1]
      _ ≤ Nat.card E ^ s.card * (Nat.card E * Nat.card ↥(stabSet (f a) ⊓ K)) := by
          gcongr
      _ = Nat.card E ^ s.card * Nat.card E * Nat.card ↥(stabSet (f a) ⊓ K) := by ring

theorem card_iSup_eq_pow {ι : Type*} {P : Set (Subgroup G)} (hP : IsPoint Δ P) {E : Subgroup G}
    (hE : E ∈ R) (Y : ι → Subgroup G) (f : ι → Set (Subgroup G)) (s : Finset ι)
    (hY : ∀ i ∈ s, Y i ∈ P) (hf : ∀ i ∈ s, IsPoint Δ (f i))
    (hYf : ∀ i ∈ s, ∀ j ∈ s, (Y i ≤ stabSet (f j) ↔ i ≠ j)) :
    Nat.card ↥(⨆ i ∈ s, Y i) = Nat.card E ^ s.card ∧
      (⨆ i ∈ s, Y i) ⊓ ⨅ j ∈ s, stabSet (f j) = ⊥ := by
  classical
  have hPw := hP.isWeakTI hR hΔ
  have hab := commuting_gen_of_isWeakTI_of hR hiso hnd hPw
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    obtain ⟨hcard, hinf⟩ := ih (fun i hi => hY i (hs i hi)) (fun i hi => hf i (hs i hi))
      fun i hi j hj => hYf i (hs i hi) j (hs j hj)
    set V := ⨆ i ∈ s, Y i with hV
    have hYaR : Y a ∈ R := hPw.1 (hY a ha)
    have hVle : V ≤ gen P := iSup₂_le fun i hi => le_gen (hY i (hs i hi))
    have hVa : V ≤ stabSet (f a) := iSup₂_le fun i hi =>
      (hYf i (hs i hi) a ha).2 fun e => has (e ▸ hi)
    have hYa : ∀ y ∈ Y a, y ∈ stabSet (f a) → y = 1 := by
      intro y hy hya
      by_contra hy1
      exact (hYf a ha a ha).1 (le_stabSet_of_mem_stabSet hR hiso hnd hΩ hΔ (hf a ha) hYaR hy
        hy1 hya) rfl
    have hYV : Y a ⊓ V = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 fun y hy => hYa y hy.1 (hVa hy.2)
    have hcomm : Commuting (Y a) V := hab.mono (le_gen (hY a ha)) hVle
    have hsup : (⨆ i ∈ insert a s, Y i) = Y a ⊔ V := by
      rw [Finset.iSup_insert]
    refine ⟨?_, ?_⟩
    · rw [hsup, Finset.card_insert_of_notMem has, pow_succ, ← hcard, hR.card_eq hE hYaR,
        mul_comm]
      exact le_antisymm (card_sup_le_of_commuting hcomm) (card_mul_card_le_card_sup hYV)
    · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      rw [hsup] at hx
      have hnorm : Y a ≤ Subgroup.normalizer ((V : Subgroup G) : Set G) := by
        intro y hy
        rw [Subgroup.mem_normalizer_iff]
        intro v
        constructor
        · intro hv
          rw [(hcomm y hy v hv).eq, mul_inv_cancel_right]
          exact hv
        · intro hv
          have h1 := (hcomm y hy _ hv).eq
          have e : v = y * v * y⁻¹ := by
            calc v = y⁻¹ * ((y * v * y⁻¹) * y) := by group
              _ = y⁻¹ * (y * (y * v * y⁻¹)) := by rw [h1]
              _ = y * v * y⁻¹ := by group
          rw [e]
          exact hv
      have hxmem : x ∈ ((Y a : Set G) * (V : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]
        exact hx.1
      obtain ⟨y, hy, v, hv, rfl⟩ := hxmem
      have hxa : y * v ∈ stabSet (f a) := by
        have := hx.2
        rw [Finset.iInf_insert] at this
        exact this.1
      have hy1 : y = 1 := hYa y hy (by
        have := (stabSet (f a)).mul_mem hxa ((stabSet (f a)).inv_mem (hVa hv))
        rwa [mul_inv_cancel_right] at this)
      subst hy1
      simp only [one_mul] at hx ⊢
      have hvs : v ∈ ⨅ j ∈ s, stabSet (f j) := by
        have := hx.2
        rw [Finset.iInf_insert] at this
        exact this.2
      have : v ∈ V ⊓ ⨅ j ∈ s, stabSet (f j) := ⟨hv, hvs⟩
      rw [hinf] at this
      exact this

end Counting

structure IsFrame (R Δ : Set (Subgroup G)) {n : ℕ} (P : Fin n → Set (Subgroup G))
    (Q : Fin n → Subgroup G) : Prop where
  isPoint : ∀ i, IsPoint Δ (P i)
  mem : ∀ j, Q j ∈ R
  le_stabSet_iff : ∀ i j, Q j ≤ stabSet (P i) ↔ i ≠ j

namespace IsFrame

variable {Δ : Set (Subgroup G)} {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}

theorem ne (hfr : IsFrame R Δ P Q) {i k : Fin n} (h : i ≠ k) : P i ≠ P k := by
  intro e
  have h1 : Q i ≤ stabSet (P k) := (hfr.le_stabSet_iff k i).2 (Ne.symm h)
  rw [← e] at h1
  exact (hfr.le_stabSet_iff i i).1 h1 rfl

theorem dualPoint_ne {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) {j k : Fin n} (h : j ≠ k) :
    dualPoint R Δ (Q j) ≠ dualPoint R Δ (Q k) := by
  intro e
  have h1 : Q j ∈ dualPoint R Δ (Q k) := e ▸ mem_dualPoint_self (hfr.mem j)
  have h2 : Q j ≤ stabSet (P k) := (hfr.le_stabSet_iff k j).2 (Ne.symm h)
  rw [le_stabSet_iff_of_mem_dualPoint h1 (hfr.isPoint k)] at h2
  exact (hfr.le_stabSet_iff k k).1 h2 rfl

end IsFrame

section Frames

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ)
include hR hiso hnd hΩ hΔ

theorem IsFrame.exists_mem {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) {i j : Fin n} (hij : i ≠ j) :
    ∃ X ∈ P i, X ∈ dualPoint R Δ (Q j) :=
  (inter_dualPoint_nonempty_iff hR hiso hnd hΩ hΔ (hfr.isPoint i) (hfr.mem j)).2
    ((hfr.le_stabSet_iff i j).2 hij)

theorem exists_isFrame_one :
    ∃ (P : Fin 1 → Set (Subgroup G)) (Q : Fin 1 → Subgroup G), IsFrame R Δ P Q := by
  obtain ⟨A, hA, -⟩ := hΔ.2.1
  obtain ⟨B, hB, hAB⟩ := hiso A (hΔ.1 hA)
  refine ⟨fun _ => Δ, fun _ => B, ⟨fun _ => isPoint_self Δ, fun _ => hB, fun i j => ?_⟩⟩
  rw [Subsingleton.elim i j]
  simp only [ne_eq, not_true_eq_false, iff_false]
  exact not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ (isPoint_self Δ) hB hA hAB.symm

theorem IsFrame.exists_succ {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) (hn : 0 < n) {E : Subgroup G} (hE : E ∈ R)
    (hcard : Nat.card E ^ n ≤ Nat.card ↥(gen (dualPoint R Δ (Q ⟨0, hn⟩)))) :
    ∃ (P' : Fin (n + 1) → Set (Subgroup G)) (Q' : Fin (n + 1) → Subgroup G),
      IsFrame R Δ P' Q' := by
  classical
  set i₀ : Fin n := ⟨0, hn⟩
  have hC₀ : Q i₀ ∈ R := hfr.mem i₀
  set Δ' := dualPoint R Δ (Q i₀)
  have hΔ' : IsTI R Δ' := isTI_dualPoint hR hiso hnd hΩ hΔ hC₀
  set D : Fin n → Set (Subgroup G) := fun j => dualPoint R Δ (Q j) with hD
  have hDpt : ∀ j, IsPoint Δ' (D j) := fun j =>
    (isPoint_dualPoint_iff hR hC₀).2 ⟨Q j, hfr.mem j, rfl⟩
  set s := (Finset.univ : Finset (Fin n)).erase i₀ with hs
  have hscard : s.card = n - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hq := one_lt_card_of_mem hR hE
  have hbound := card_gen_le_pow_mul hR hiso hnd hΩ hΔ' (hDpt i₀) hE D s (fun j _ => hDpt j)
    fun j hj => hfr.dualPoint_ne (Finset.ne_of_mem_erase hj)
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ gen (D i₀) ⊓ ⨅ j ∈ s, stabSet (D j), y ≠ 1 := by
    by_contra! h
    have hbot : gen (D i₀) ⊓ ⨅ j ∈ s, stabSet (D j) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [hbot, Subgroup.card_bot, mul_one, hscard] at hbound
    exact absurd (hcard.trans hbound) (not_le.2 (Nat.pow_lt_pow_right hq (by omega)))
  obtain ⟨Y, hYD, -, hyY⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ
    ((hDpt i₀).isWeakTI hR hΔ') subset_rfl hy.1 hy1
  have hYR : Y ∈ R := hYD.1
  have hYst : ∀ j, j ≠ i₀ → Y ≤ stabSet (D j) := by
    intro j hj
    have hj' : j ∈ s := Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩
    have hyj : y ∈ stabSet (D j) := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy.2 j) hj'
    exact le_stabSet_of_mem_stabSet hR hiso hnd hΩ hΔ' (hDpt j) hYR hyY hy1 hyj
  obtain ⟨Pn, hPn, hYPn⟩ := exists_isPoint_mem hR hΔ hYR
  have hPnw := hPn.isWeakTI hR hΔ
  have hQPn : ∀ j, Q j ≤ stabSet Pn := by
    intro j
    by_cases hj : j = i₀
    · rw [hj]
      exact (le_stabSet_iff_of_mem_dualPoint hYD hPn).1
        (Sec5.le_stabSet_of_commuting hR hPnw hYR hYPn (hR.commuting_self hYR))
    · exact (le_stabSet_dualPoint_iff hR hiso hnd hΩ hΔ hC₀ hPn hYPn (hfr.mem j)).1 (hYst j hj)
  have hP0 := hfr.isPoint i₀
  have hP0w := hP0.isWeakTI hR hΔ
  have hPnne : Pn ≠ P i₀ := by
    intro h
    have := hQPn i₀
    rw [h] at this
    exact (hfr.le_stabSet_iff i₀ i₀).1 this rfl
  have hex : ∀ j, ∃ X, j ≠ i₀ → X ∈ P i₀ ∧ X ∈ dualPoint R Δ (Q j) := by
    intro j
    by_cases hj : j = i₀
    · exact ⟨⊥, fun h => absurd hj h⟩
    · obtain ⟨X, hX1, hX2⟩ := hfr.exists_mem hR hiso hnd hΩ hΔ (Ne.symm hj)
      exact ⟨X, fun _ => ⟨hX1, hX2⟩⟩
  choose X hX using hex
  have hXs : ∀ j ∈ s, X j ∈ P i₀ ∧ X j ∈ dualPoint R Δ (Q j) := fun j hj =>
    hX j (Finset.ne_of_mem_erase hj)
  have hXst : ∀ j ∈ s, ∀ k ∈ s, (X j ≤ stabSet (P k) ↔ j ≠ k) := by
    intro j hj k _
    rw [le_stabSet_iff_of_mem_dualPoint (hXs j hj).2 (hfr.isPoint k), hfr.le_stabSet_iff k j]
    exact ne_comm
  obtain ⟨hVcard, hVinf⟩ := card_iSup_eq_pow hR hiso hnd hΩ hΔ hP0 hE X P s
    (fun j hj => (hXs j hj).1) (fun j _ => hfr.isPoint j) hXst
  set V := ⨆ j ∈ s, X j with hV
  set S := gen (P i₀) ⊓ ⨅ i ∈ s, stabSet (P i) with hS
  have hSbound := card_gen_le_pow_mul hR hiso hnd hΩ hΔ hP0 hE P s (fun i _ => hfr.isPoint i)
    fun i hi => hfr.ne (Finset.ne_of_mem_erase hi)
  obtain ⟨x, hxS, hxn⟩ : ∃ x ∈ S, x ∉ stabSet Pn := by
    by_contra! h
    have hVst : V ≤ stabSet Pn := iSup₂_le fun j hj =>
      (le_stabSet_iff_of_mem_dualPoint (hXs j hj).2 hPn).2 (hQPn j)
    have hSV : S ⊓ V = ⊥ := by
      rw [eq_bot_iff, ← hVinf, inf_comm]
      exact inf_le_inf_left V inf_le_right
    have hle : S ⊔ V ≤ gen (P i₀) :=
      sup_le inf_le_left (iSup₂_le fun j hj => le_gen (hXs j hj).1)
    have hcard' : Nat.card ↥(gen (P i₀)) ≤ Nat.card ↥(S ⊔ V) := by
      calc Nat.card ↥(gen (P i₀)) ≤ Nat.card E ^ s.card * Nat.card S := hSbound
        _ = Nat.card S * Nat.card V := by rw [hVcard, mul_comm]
        _ ≤ Nat.card ↥(S ⊔ V) := card_mul_card_le_card_sup hSV
    have heq : S ⊔ V = gen (P i₀) := Subgroup.eq_of_le_of_card_ge hle hcard'
    exact not_gen_le_stabSet hR hiso hnd hΩ hΔ hP0 hPn (Ne.symm hPnne)
      (heq ▸ sup_le (fun z hz => h z hz) hVst)
  have hx1 : x ≠ 1 := fun h => hxn (h ▸ one_mem _)
  obtain ⟨Z, hZP, -, hxZ⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hP0w subset_rfl hxS.1 hx1
  have hZR := hP0w.1 hZP
  have hZst : ∀ i, Z ≤ stabSet (P i) := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      exact Sec5.le_stabSet_of_commuting hR hP0w hZR hZP (hR.commuting_self hZR)
    · have hi' : i ∈ s := Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩
      exact le_stabSet_of_mem_stabSet hR hiso hnd hΩ hΔ (hfr.isPoint i) hZR hxZ hx1
        (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxS.2 i) hi')
  have hZn : ¬ Z ≤ stabSet Pn := fun h => hxn (h hxZ)
  refine ⟨Fin.snoc P Pn, Fin.snoc Q Z, ⟨fun i => ?_, fun j => ?_, fun i j => ?_⟩⟩
  · induction i using Fin.lastCases with
    | last => simpa using hPn
    | cast i => simpa using hfr.isPoint i
  · induction j using Fin.lastCases with
    | last => simpa using hZR
    | cast j => simpa using hfr.mem j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using hZn
      | cast j => simpa [Fin.castSucc_ne_last, Ne.symm (Fin.castSucc_ne_last j)] using hQPn j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [Fin.castSucc_ne_last] using hZst i
      | cast j => simpa using hfr.le_stabSet_iff i j

theorem exists_isFrame {E : Subgroup G} (hE : E ∈ R) {C : Subgroup G} (hC : C ∈ R) :
    ∀ n, 0 < n → Nat.card E ^ (n - 1) ≤ Nat.card ↥(gen (dualPoint R Δ C)) →
      ∃ (P : Fin n → Set (Subgroup G)) (Q : Fin n → Subgroup G), IsFrame R Δ P Q := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ n ih =>
    intro _ hcard
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact exists_isFrame_one hR hiso hnd hΩ hΔ
    obtain ⟨P, Q, hfr⟩ := ih hn (le_trans (Nat.pow_le_pow_right
      (one_lt_card_of_mem hR hE).le (by omega)) hcard)
    refine hfr.exists_succ hR hiso hnd hΩ hΔ hn hE ?_
    obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hC (hfr.mem ⟨0, hn⟩)
    rw [← hg, dualPoint_conjSub hR, card_gen_conjSet]
    simpa using hcard

end Frames

end Linear

end CFSG.Timmesfeld.ARS
