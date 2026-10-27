module

public import CFSG.Sporadic.J2.CentEAModel

public section

namespace CFSG.Sporadic.J2

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.GH74.Generic.S45.EvSpor
  CFSG.GH74.Generic.S45 CFSG.GH74.GLS.C3.Layer1.Bk.J2C

private theorem two_pow_seven_dvd_card_inf_centralizer_sq
    {y : Equiv.Perm (Fin 315)} (hy : y ∈ j2P)
    (hy4 : orderOf y = 4) :
    2 ^ 7 ∣ Nat.card ↥(j2P ⊓ centralizer ({y ^ 2} : Set (Equiv.Perm (Fin 315)))) := by
  have hy2 : orderOf (y ^ 2) = 2 := by
    rw [orderOf_pow' y two_ne_zero, hy4]
    rfl
  rcases j2_cover (y ^ 2) (j2P.pow_mem hy 2) hy2 with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · rw [hgt, inf_comm, card_cent_conj hg, inf_comm,
      (j2_rows_spec.1 j2Row2A j2Row2A_mem).2.2.2.2, j2Row2A_centOrder]
    norm_num
  · exfalso
    have hz2 : (g⁻¹ * y * g) ^ 2 = tp 315 j2Row2B.rep := by
      have e : (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := by
        rw [pow_two, pow_two]
        group
      rw [e, hgt]
      group
    have hz : g⁻¹ * y * g ∈
        j2P ⊓ centralizer ({tp 315 j2Row2B.rep} : Set (Equiv.Perm (Fin 315))) := by
      refine Subgroup.mem_inf.2 ⟨j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hy) hg, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hz2]
      exact (Commute.self_pow _ 2).eq
    refine orderOf_ne_four_of_mem_cent_tB hz ?_
    have := orderOf_conj' g⁻¹ y
    rw [inv_inv] at this
    rw [this, hy4]

theorem two_pow_seven_dvd_card_centralizer_of_sq_isConj
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.NativeSporadic.IsSporadic X .J2) {t x : X} (hx : orderOf x = 4)
    (ht : IsConj t (x ^ 2)) : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({t} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 ht
  have hconj := card_cent_symm (MulAut.conj c) (x ^ 2)
  rw [MulAut.conj_symm_apply] at hconj
  have htc : t = c⁻¹ * x ^ 2 * c := by
    rw [← hc]
    group
  obtain ⟨e⟩ := hX
  let φ : X ≃* ↥j2P := e.trans j2PermEquiv
  have hcard := card_cent_symm φ (φ (x ^ 2))
  rw [MulEquiv.symm_apply_apply] at hcard
  rw [htc, hconj, hcard, card_cent_subtype j2P (φ (x ^ 2)), map_pow, Subgroup.coe_pow]
  refine two_pow_seven_dvd_card_inf_centralizer_sq (φ x).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact hx

private theorem exists_mulEquiv_apply_eq_tAj
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.NativeSporadic.IsSporadic X .J2) {t : X} (ht : orderOf t = 2)
    (h128 : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({t} : Set X))) :
    ∃ Φ : X ≃* ↥j2P, Φ t = tAj := by
  obtain ⟨e⟩ := hX
  let φ₀ : X ≃* ↥j2P := e.trans j2PermEquiv
  have hs2 : orderOf ((φ₀ t : ↥j2P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  rcases j2_cover (φ₀ t).1 (φ₀ t).2 hs2 with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · let g' : ↥j2P := ⟨g, hg⟩
    have hsg : φ₀ t = g' * (tAj : ↥j2P) * g'⁻¹ := Subtype.ext hgt
    refine ⟨φ₀.trans (MulAut.conj g'⁻¹), ?_⟩
    show g'⁻¹ * φ₀ t * g'⁻¹⁻¹ = tAj
    rw [hsg]
    group
  · exfalso
    have hcardC := card_cent_symm φ₀ (φ₀ t)
    rw [MulEquiv.symm_apply_apply] at hcardC
    rw [hcardC, card_cent_subtype j2P (φ₀ t), hgt, inf_comm, card_cent_conj hg, inf_comm,
      (j2_rows_spec.1 j2Row2B j2Row2B_mem).2.2.2.2, j2Row2B_centOrder] at h128
    omega

theorem j2_cent_ea_facts
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.NativeSporadic.IsSporadic X .J2) {t : X} {E : Subgroup X}
    (ht : orderOf t = 2) (h128 : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({t} : Set X)))
    (hE : CFSG.GH74.GLS.C3.Layer1.Bk.J2C.J2CentFacts X t E) : J2CentEAFacts X t E := by
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_apply_eq_tAj hX ht h128
  have hΦ' : Φ.symm tAj = t := by
    rw [MulEquiv.symm_apply_eq]
    exact hΦ.symm
  have h1 := J2CentFacts.of_mulEquiv Φ j2CentFacts_model
  have h2 := J2CentEAFacts.of_mulEquiv Φ j2CentEAFacts_model
  rw [hΦ'] at h1 h2
  rwa [eq_of_j2CentFacts hE h1]

end CFSG.Sporadic.J2
