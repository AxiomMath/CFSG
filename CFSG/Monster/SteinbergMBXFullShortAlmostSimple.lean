module

public import CFSG.Monster.Existence.Monolith
public import CFSG.Monster.B.TwoA.Base.GeomRes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B

namespace FullShortAlmostSimple

theorem isSimpleGroup_Shat :
    IsSimpleGroup Shat := by
  have := short_centralizer_generated_quotient_simple.2.2.1
  exact (MonoidHom.ofInjective iotaD_injective).symm.isSimpleGroup

theorem Shat_nonabelian :
    ∃ a ∈ Shat, ∃ b ∈ Shat, a * b ≠ b * a := by
  obtain ⟨-, hnt, -, -⟩ := short_centralizer_generated_quotient_simple
  obtain ⟨c, hc⟩ := exists_ne (1 : Cbar)
  have hcz : c ∉ Subgroup.center Cbar := by
    rw [center_Cbar, Subgroup.mem_bot]
    exact hc
  rw [Subgroup.mem_center_iff] at hcz
  push Not at hcz
  obtain ⟨d, hd⟩ := hcz
  exact ⟨iotaD c, ⟨c, rfl⟩, iotaD d, ⟨d, rfl⟩, fun h =>
    hd (iotaD_injective (by rw [map_mul, map_mul]; exact h.symm))⟩

theorem isElementaryAbelian_Vhat : IsElementaryAbelian 2 Vhat := by
  have := isKleinFour_Vhat
  exact { toIsMulCommutative := IsKleinFour.isMulCommutative
          exponent_dvd_p := dvd_of_eq IsKleinFour.exponent_two }

theorem tauhat_conj_iotaD (c : Cbar) :
    tauhat * iotaD c * tauhat⁻¹ = iotaD (taubar * c * taubar⁻¹) := by
  rw [tauhat, map_mul, map_mul, map_inv]

theorem taubar_conj_mem_Vbar {c : Cbar} (hc : c ∈ Vbar) : taubar * c * taubar⁻¹ ∈ Vbar := by
  rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Vbar.one_mem
  · rw [taubar_conj_xbar]
    exact ybar_mem_Vbar
  · rw [taubar_conj_ybar]
    exact zbar_mem_Vbar
  · rw [taubar_conj_zbar]
    exact xbar_mem_Vbar

theorem taubar_conj_ne {c : Cbar} (hc : c ∈ Vbar) (hc1 : c ≠ 1) : taubar * c * taubar⁻¹ ≠ c := by
  rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
  · exact absurd rfl hc1
  · rw [taubar_conj_xbar]
    exact xbar_ne_ybar.symm
  · rw [taubar_conj_ybar]
    exact ybar_ne_zbar.symm
  · rw [taubar_conj_zbar]
    exact zbar_ne_xbar.symm

theorem exists_sylow_le_Shat :
    ∃ P : Sylow 2 Dfull, (P : Subgroup Dfull) ≤ Shat ∧ Nat.card (Subgroup.center P) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Jhat) := inferInstance
  obtain ⟨T, hT, hZ⟩ := full_short_centralizer_odd_index.2.2.2.2.2.2.1 P
  refine ⟨T, ?_, ?_⟩
  · rw [hT]
    exact (Subgroup.map_subtype_le _).trans Jhat_le_Shat
  · have h1 := congrArg (fun H : Subgroup Dfull => Nat.card H) hZ
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers,
      orderOf_xhat] at h1

end FullShortAlmostSimple

open FullShortAlmostSimple

theorem full_short_centralizer_almost_simple :
    Function.Injective iotaD ∧
    (∀ N : Subgroup Dfull, N.Normal → N ≠ ⊥ → Shat ≤ N) ∧
    (∃ A : Subgroup Dfull, ∃ _ : A.Normal, A ≠ ⊥ ∧
      (∀ N : Subgroup Dfull, N.Normal → N ≠ ⊥ → A ≤ N) ∧
      (∀ M : Subgroup Dfull, M.Normal → M ≠ ⊥ →
        (∀ N : Subgroup Dfull, N.Normal → N ≠ ⊥ → N ≤ M → N = M) → M = A) ∧
      IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧ Shat ≤ A ∧
      Subgroup.centralizer (A : Set Dfull) = ⊥ ∧ Odd A.index ∧
      Function.Injective (MulAut.conjNormal (H := A)) ∧
      ∀ a : A, MulAut.conjNormal (a : Dfull) = MulAut.conj a) ∧
    (∀ (H : Type u) [Group H] (f : Dfull →* H), (∃ s ∈ Shat, f s ≠ 1) →
      Function.Injective f) := by
  have := isSimpleGroup_Shat
  have := isElementaryAbelian_Vhat
  have hx1 : xhat ≠ 1 := by
    intro h
    have := orderOf_xhat
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hτV : ∀ v ∈ Vhat, tauhat * v * tauhat⁻¹ ∈ Vhat := by
    rintro _ ⟨c, hc, rfl⟩
    rw [tauhat_conj_iotaD]
    exact ⟨_, taubar_conj_mem_Vbar hc, rfl⟩
  have hτfix : ∀ v ∈ Vhat, v ≠ 1 → tauhat * v * tauhat⁻¹ ≠ v := by
    rintro _ ⟨c, hc, rfl⟩ hv
    rw [tauhat_conj_iotaD]
    have hc1 : c ≠ 1 := fun h => hv (by rw [h, map_one])
    exact iotaD_injective.ne (taubar_conj_ne hc hc1)
  have hC : Subgroup.centralizer {xhat} ≤ Shat := by
    rw [centralizer_xhat]
    exact Jhat_le_Shat
  obtain ⟨h1, h2, h3⟩ := CFSG.Monster.Existence.cycled_four_group_simple_subgroup_monolith
    Shat_nonabelian isKleinFour_Vhat.card_four xhat_mem_Vhat hx1 ⟨taubar, rfl⟩ hτV hτfix hC
  obtain ⟨A, hAn, hA1, hAmin, hAsimple, hAnab, hSA, hAcent, hAodd, hinj, hinner⟩ :=
    h3 exists_sylow_le_Shat
  refine ⟨iotaD_injective, h1, ⟨A, hAn, hA1, hAmin, fun M hM hM1 hMmin => ?_, hAsimple, hAnab,
    hSA, hAcent, hAodd, hinj, hinner⟩, fun H _ f hf => h2 H f hf⟩
  exact (hMmin A hAn hA1 (hAmin M hM hM1)).symm

end CFSG.Monster.B.TwoA
