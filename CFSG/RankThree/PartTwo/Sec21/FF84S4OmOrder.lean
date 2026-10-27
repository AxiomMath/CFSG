module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmIso
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

theorem commutator_mem_of_index_le_two {Γ : Type*} [Group Γ] [Finite Γ] (K : Subgroup Γ)
    (hK : K.index ≤ 2) (x y : Γ) : x * y * x⁻¹ * y⁻¹ ∈ K := by
  have hcard := Subgroup.card_mul_index K
  have hpos : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have hidx : K.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcard
    exact hpos hcard.symm
  rcases (by omega : K.index = 1 ∨ K.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  · haveI := Subgroup.normal_of_index_eq_two h2
    have hq : Nat.card (Γ ⧸ K) = 2 := h2
    have hsq : ∀ g : Γ ⧸ K, g * g = 1 := by
      intro g
      have hd := orderOf_dvd_natCard g
      rw [hq] at hd
      have h2' : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
      rwa [pow_two] at h2'
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have ha := hsq (x : Γ ⧸ K)
    have hb := hsq (y : Γ ⧸ K)
    have hab := hsq ((x : Γ ⧸ K) * (y : Γ ⧸ K))
    rw [inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
    simpa only [mul_assoc] using hab

theorem card_orthogonalGroup_qMinusForm :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup qMinusForm) = 51840 := by
  have hV : Module.finrank (ZMod 2) (Fin 6 → ZMod 2) = 2 * 3 := by rw [finrank_fin_six]
  have h := CFSG.LargeExtraspecial.S12DW.card_orthogonalGroup_mul_ncard_eq
    qMinusForm_nondegenerate hV
  have hsing : {v : F6 | qMinusForm v = 0}.ncard = 28 := by
    have e : {v : F6 | qMinusForm v = 0} =
        ↑(Finset.univ.filter fun v : F6 => qMinus v = 0) := by
      ext v
      simp [coe_qMinusForm]
    rw [e, Set.ncard_coe_finset]
    decide
  rw [hsing] at h
  have hprod : (2 : ℕ) ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by
    decide
  rw [hprod] at h
  omega

instance instFiniteF6Equiv : Finite (F6 ≃ₗ[ZMod 2] F6) :=
  Finite.of_injective (fun e : F6 ≃ₗ[ZMod 2] F6 => (e : F6 → F6))
    (fun _ _ h => LinearEquiv.ext fun x => congrFun h x)

theorem Om_ge_of_card (H : Subgroup (F6 ≃ₗ[ZMod 2] F6))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm) (hc : 25920 ≤ Nat.card H) :
    CFSG.Open.timmesfeldOmega qMinus ≤ H := by
  rw [timmesfeldOmega_qMinus, Subgroup.commutator_le]
  intro x hx y hy
  have hK : (H.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup qMinusForm)).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (H.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup qMinusForm))
    have hc' : Nat.card (H.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup qMinusForm)) =
        Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
    rw [hc', card_orthogonalGroup_qMinusForm] at h1
    by_contra hlt
    push Not at hlt
    have h3 : 25920 * 3 ≤ Nat.card H * (H.subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup qMinusForm)).index :=
      Nat.mul_le_mul hc hlt
    omega
  have key := commutator_mem_of_index_le_two
    (H.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup qMinusForm)) hK ⟨x, hx⟩ ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf] at key
  simpa [commutatorElement_def] using key

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
