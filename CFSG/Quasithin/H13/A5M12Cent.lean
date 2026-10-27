
module

public import CFSG.Quasithin.H13.A5M12CentBase

public import CFSG.Quasithin.Background.HMathieuFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A5.M12

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.Blueprint

theorem four_le_rkIdx_rhoC11
    {t : MulAut W11} (ht : t ∈ (rhoC11 AutPerm le_rfl).range) (ht2 : orderOf t = 2) :
    4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  exact code24_four_le_rkIdx ⟨le_rfl, Subgroup.le_normalizer⟩ codeCoords_realizes ht ht2

theorem rhoC12_m24Pair_injective :
    Function.Injective (rhoC12 m24Pair le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ u : W11, projYW (codeCoords.rhoHom σ u) = projYW u := by
    intro u
    rw [projYW_rhoHom σ.2 u]
    exact congrArg (fun φ : MulAut W10 => φ (projYW u)) hσ
  have hδ : ∀ u : W11, codeCoords.rhoHom σ u * u⁻¹ = 1 ∨ codeCoords.rhoHom σ u * u⁻¹ = dYW :=
    fun u => (projYW_eq_one_iff _).1 (by rw [map_mul, map_inv, hfix, mul_inv_cancel])
  obtain ⟨t, ht⟩ : ∃ t : MulAut W11, t = rhoC11 AutPerm le_rfl ⟨σ, σ.2.1⟩ := ⟨_, rfl⟩
  have htapp : ∀ u, t u = codeCoords.rhoHom σ u := fun u => by rw [ht]; rfl
  have htt : t * t = 1 := by
    ext u
    rw [MulAut.mul_apply, MulAut.one_apply, htapp, htapp]
    rcases hδ u with h | h
    · rw [mul_inv_eq_one.mp h, mul_inv_eq_one.mp h]
    · have h1 : codeCoords.rhoHom σ u = dYW * u := by rw [← h, inv_mul_cancel_right]
      rw [h1, map_mul, rhoHom_dYW σ.2, h1, ← mul_assoc, dYW_sq, one_mul]
  have ht1 : t = 1 := by
    by_contra hne
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) hne
    have h4 := four_le_rkIdx_rhoC11 (t := t) (by rw [ht]; exact ⟨_, rfl⟩) hord
    have hle := rkIdx_le_of_proj W10_sq projYW projYW_surjective projYW_eq_one_iff
      (φ := t) (φ' := 1) (fun u => by rw [htapp, hfix, MulAut.one_apply])
    have htop : fixV (Subgroup.zpowers (1 : MulAut W10)) = ⊤ :=
      eq_top_iff.mpr fun v _ => (H.Mathieu.mem_fixV_zpowers_iff).2 rfl
    have h0 : rkIdx (fixV (Subgroup.zpowers (1 : MulAut W10))) = 0 := by
      rw [htop, rkIdx, Subgroup.index_top, padicValNat_one_right]
    omega
  have h1 : rhoC11 AutPerm le_rfl ⟨σ, σ.2.1⟩ = 1 := by rw [← ht, ht1]
  have h2 := rhoC11_injective AutPerm le_rfl (h1.trans (map_one _).symm)
  have h3 := congrArg Subtype.val h2
  exact Subtype.ext h3

theorem normalizer_rhoC12 :
    Subgroup.normalizer ((rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range :
      Set (MulAut W10)) = (rhoC12 m24Pair le_rfl).range := by
  have := finite_mulAut W10
  have := m24Fix_normal
  have hmap : ((m24Fix dodecadE).subgroupOf m24Pair).map (rhoC12 m24Pair le_rfl) =
      (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range := by
    apply le_antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, hσ⟩, rfl⟩
    · rintro _ ⟨σ, rfl⟩
      exact ⟨⟨σ, m24Fix_le_m24Pair σ.2⟩, σ.2, rfl⟩
  rw [← hmap]
  exact normalizer_map_eq (rhoC12 m24Pair le_rfl) rhoC12_m24Pair_injective _
    (by rw [hmap]; exact centralizer_rhoC12) card_mulAut_m12_le

end CFSG.Quasithin.H13.A5.M12
