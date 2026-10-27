module

public import CFSG.Quasithin.Vol2.Ch6InputsF7
public import CFSG.Quasithin.Background.F7TwoZ
public import CFSG.Quasithin.Background.F7TwoCfg
public import CFSG.Quasithin.Background.F7TwoFix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem isSQTKCat_conjSub {G : Type} [Group G] [Finite G] {X : Subgroup G} (g : G)
    (h : CFSG.SectionRank.IsSQTKCat ↥X) : CFSG.SectionRank.IsSQTKCat ↥(conjSub g X) := by
  let e : ↥(conjSub g X) ≃* ↥X := ((MulAut.conj g).subgroupMap X).symm
  exact CFSG.SectionRank.IsSQTKCat.of_mulEquiv h e

theorem f713Two_of_claimCE1 (hC : F7Two.ClaimCE1) : F713Two := by
  intro G _ _ G₀ G₁ G₂ T V hyp hV hSQ γ hγ ha₃ ha₂ hb hc _ A hA₁ hA₂
  obtain ⟨⟨g, hstab⟩, hAel, hnot, S, H, W, hS, hAS, hH, hAH, hSW, hex, hvert⟩ :=
    CosetGeom.exists_E1_config hyp hV hγ ha₃ ha₂ hb hc hA₁ hA₂
  have hSQγ : CFSG.SectionRank.IsSQTKCat ↥(CosetGeom.stab γ) := by
    rw [hstab]
    exact isSQTKCat_conjSub g hSQ
  have hgen := hC G (CosetGeom.stab γ) S A H hSQγ hS hAS hAel hnot hH hAH
  have hSH : IsSylowTwoOf (S ⊓ H) H := hH.2.2.1
  have hHγ : H ≤ CosetGeom.stab γ := hH.1
  obtain ⟨h, hh, g', hg', hAh, hAg'⟩ := F7Two.exists_nonTwoConj_not_normalizing (A := A)
    (H := H) (P := S ⊓ H) (X := twoResidual H) (W := W) (le_inf hAS hAH) inf_le_right
    (inf_le_left.trans hSW) (inf_le_right.trans (le_normalizer_twoResidual H))
    (by rw [sup_comm]; exact (sup_twoResidual_eq hSH).ge) hgen hex
  obtain ⟨α₀, hα₀, hVα₀⟩ := hvert g' hg'
  obtain ⟨R, hRA, hRH, hRidx⟩ := F7.exists_index_two_of_isE hAel hAH hH
  have hRN : R ≤ Subgroup.normalizer (conjSub g' W : Set G) := by
    have e : conjSub g'⁻¹ (pCoreOf 2 H) = pCoreOf 2 H :=
      F7.conjSub_eq_of_mem_normalizer (inv_mem (le_normalizer_pCoreOf 2 H (hg')))
    have hK : pCoreOf 2 H ≤ Subgroup.normalizer (conjSub g' W : Set G) := by
      rw [conjSub_normalizer, le_conjSub_iff, e]
      exact ((F7.isSylowTwoOf_pCoreOf_le hSH).trans inf_le_left).trans hSW
    exact hRH.trans hK
  have hidx : (A ⊓ Subgroup.normalizer (conjSub g' W : Set G)).relIndex A = 2 :=
    F7Two.relIndex_inf_eq_two hRN hRA hRidx hAg'
  have hhγ : h ∈ CosetGeom.stab γ := hHγ hh.1
  have hAγ : A ≤ CosetGeom.stab γ := hAS.trans hS.1
  have hXγ : conjSubgroup A h ≤ CosetGeom.stab γ := by
    have := conjSub_mono h⁻¹ hAγ
    rwa [F7.conjSub_eq_of_mem (inv_mem hhγ)] at this
  have hXp : IsPGroup 2 ↥(conjSubgroup A h) :=
    (F7Two.isPGroup_conjSubgroup_iff h).mpr (F7.isPGroup_of_isElemAbelian hAel)
  obtain ⟨α, hα, hVα, hXα⟩ := CosetGeom.exists_nbr_fixed_of_le_normalizer hyp hα₀ hXp hXγ
    (by rw [hVα₀]; exact hAh)
  exact ⟨α, hα, by rw [hVα, hVα₀]; exact hidx, h, hhγ, hXα, hh.2⟩

end CFSG.Quasithin.H13
