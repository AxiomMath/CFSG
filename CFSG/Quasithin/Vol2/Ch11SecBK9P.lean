module

public import CFSG.Quasithin.Vol2.Ch11SecBK9N

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LieType.Universal.Spin (quadPlus)

variable {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 4)

include hK in
theorem card_stabQ_of_tr_eq_zero {e : Fin 2 ⊕ Fin 2 → K} (h : tr (quadPlus 2 K e) = 0) :
    Nat.card ↥(stabQ (qOf e)) = 7200 := by
  have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (polarBilin_nondegenerate (isSpForm_qOf e)) (m := 1) finrank_four (ε := 1)
    (Or.inl ⟨rfl, (isPlusType_qOf_iff hK e).mpr h⟩)
  rw [card_stabQ (isSpForm_qOf e)]
  generalize Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (qOf e)) = N at hc ⊢
  rw [hK] at hc
  norm_num [Finset.Icc_self] at hc
  exact_mod_cast hc

include hK in
theorem card_stabQ_of_tr_eq_one {e : Fin 2 ⊕ Fin 2 → K} (h : tr (quadPlus 2 K e) = 1) :
    Nat.card ↥(stabQ (qOf e)) = 8160 := by
  have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (polarBilin_nondegenerate (isSpForm_qOf e)) (m := 1) finrank_four (ε := -1)
    (Or.inr ⟨rfl, fun hp => one_ne_zero (h.symm.trans ((isPlusType_qOf_iff hK e).mp hp))⟩)
  rw [card_stabQ (isSpForm_qOf e)]
  generalize Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (qOf e)) = N at hc ⊢
  rw [hK] at hc
  norm_num [Finset.Icc_self] at hc
  exact_mod_cast hc

include hK in
theorem tr_eq_of_card_stabQ_eq {e e' : Fin 2 ⊕ Fin 2 → K}
    (h : Nat.card ↥(stabQ (qOf e)) = Nat.card ↥(stabQ (qOf e'))) :
    tr (quadPlus 2 K e) = tr (quadPlus 2 K e') := by
  rcases tr_eq_zero_or_one hK (quadPlus 2 K e) with h1 | h1 <;>
    rcases tr_eq_zero_or_one hK (quadPlus 2 K e') with h2 | h2
  · rw [h1, h2]
  · rw [card_stabQ_of_tr_eq_zero hK h1, card_stabQ_of_tr_eq_one hK h2] at h
    omega
  · rw [card_stabQ_of_tr_eq_one hK h1, card_stabQ_of_tr_eq_zero hK h2] at h
    omega
  · rw [h1, h2]

include hK in
theorem exists_orderOf_eq_three (e : Fin 2 ⊕ Fin 2 → K) :
    ∃ γ ∈ stabQ (qOf e), orderOf γ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card ↥(stabQ (qOf e)) := by
    rcases tr_eq_zero_or_one hK (quadPlus 2 K e) with h | h
    · rw [card_stabQ_of_tr_eq_zero hK h]
      norm_num
    · rw [card_stabQ_of_tr_eq_one hK h]
      norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

namespace CovData

variable {W : Type*} [CommGroup W] (C : CovData K W)
  {Ψ : (Fin 2 ⊕ Fin 2 → K) ≃ (Fin 2 ⊕ Fin 2 → K)}
  (hΨ : ∀ γ a, Ψ (mat 2 K γ *ᵥ a + C.kappa hK γ) = mat 2 K γ *ᵥ Ψ a + bm hK γ)

include hΨ in
theorem map_compl_eq_iff (γ : ↥(StatedSp 2 K)) (a : Fin 2 ⊕ Fin 2 → K) :
    (C.compl a).map (C.pi' γ).toMonoidHom = C.compl a ↔ γ ∈ stabQ (qOf (Ψ a)) := by
  rw [C.map_compl hK, (C.compl_injective hK).eq_iff, mem_stabQ_iff_kapQ hK, kapQ, sub_eq_zero,
    ← hΨ, Ψ.injective.eq_iff]

include hΨ in
theorem exists_map_compl_iff (a a' : Fin 2 ⊕ Fin 2 → K) :
    (∃ γ, (C.compl a).map (C.pi' γ).toMonoidHom = C.compl a') ↔
      tr (quadPlus 2 K (Ψ a')) = tr (quadPlus 2 K (Ψ a)) := by
  rw [← exists_orbit_iff hK]
  refine exists_congr fun γ => ?_
  rw [C.map_compl hK, (C.compl_injective hK).eq_iff, ← hΨ, Ψ.injective.eq_iff]

end CovData

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
