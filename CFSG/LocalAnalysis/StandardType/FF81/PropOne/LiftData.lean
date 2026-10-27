module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLiftX
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBSylow

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

theorem lift_data {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hB₁ : ∀ m ∈ nB b z, ∀ y ∈ bOne z, m * y * m⁻¹ ∈ bOne z) :
    CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Data b (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) := by
  have hs : GGFF.SettingCore b L z := h.settingCore
  have hBB : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BB b (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) = GGFF.Bt b z :=
    (GGFF.SettingCore.Bt_eq_closure b z).symm
  have hBO : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BO (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) = GGFF.tor (GGFF.zs z) :=
    (GGFF.SettingCore.tor_eq_closure z).symm
  obtain ⟨τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ, -, hM, hirr⟩ := exists_mono_irreducible h
  refine CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Data0.toData ?_ hM hirr ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      rw [hBB] at hx hy
      exact congrArg Subtype.val ((hs.isElemAbelian_Bt).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · intro x hx
      rw [hBB] at hx
      exact (hs.isElemAbelian_Bt).2 x hx
    · rw [hBB, hs.card_Bt]
    · rw [hBO, hs.card_torG]
    · intro n hn y hy
      rw [hBB] at hn
      rw [hBO] at hy ⊢
      exact hB₁ n hn y hy
    · intro x hx hpx
      rw [hBB] at hx ⊢
      exact mem_Bt_of_isPGroup_cen h x hx hpx
  · rw [hBB]
    obtain ⟨m, hm, hmnor⟩ := IsConcreteLE.not_le_iff_exists.mp h.facts.not_nor
    refine ⟨m, hm, fun hconj => hmnor ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : (Subgroup.zpowers b).map (MulAut.conj m) ≤ Subgroup.zpowers b := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hconj
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj m).injective).ge

end CFSG.StandardType.FF81.PropOne

end
