module

public import CFSG.LocalAnalysis.StandardType.GGHalfInnerLocalR
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerLine
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerUniq
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerPackage
public import CFSG.LocalAnalysis.StandardType.GGHalfNbrCentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

theorem nbr_eq_of_alphaInner {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hα : GGHalfAlphaInner φ₁ φ₂)
    (hRig : GGLabelRigidInput) (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (hKG : GGHalfNbrCentInput) {y' : G} {K' : Subgroup G} (hnbr : GGNbr p B x D J y' K') :
    K' = K := by
  obtain rfl : p = 3 := h.nbr.2.1
  have hm3 : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hm1 : 1 ≤ m := by omega
  have hK1 : GGHalfNormSL014 φ₁ φ₂ :=
    h.normSL014_of_alphaInner_of_three_le hm3 hα
  have hinj : Function.Injective (φ₁.comp (slLower2Hom m)) :=
    h.coords.inj₁.comp (slLower2Hom_injective m)
  have hcardJ : Nat.card J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
    rw [← h.coords.rangeJ]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h3J : 3 ∣ Nat.card J := by
    rw [hcardJ]
    exact three_dvd_card_sl m hm1
  rcases nbr_line h hnbr with hy | ⟨e, he, hzy⟩
  · exact nbr_eq_of_zpowers_eq h hLB hnbr hy
  · obtain ⟨R, hRperf, hR3, hRcentY, hRcentJ, hxR⟩ := exists_localR h hK1 e he
    let g : G := vElt φ₁ * wElt φ₂ ^ e
    obtain ⟨hJK', hJcomp, hQK, hBN, lab, hLabel, hlab⟩ :=
      nbr_package h hRig hTP hLB hnbr
    have hJperf : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJcomp.2.2
    have hPC : LargeEvenPComponent 3 (Subgroup.centralizer ({y'} : Set G)) K' :=
      hnbr.1.2.2.2.2.1
    have hx3 : x ^ 3 = 1 := h.basic.2.1 x h.basic.2.2.1
    have hK'cent : K' ≤ Subgroup.centralizer ({y'} : Set G) :=
      hnbr.1.2.2.2.1
    have hK'r : ∀ r ∈ R, K'.map (MulAut.conj r).toMonoidHom = K' := by
      intro r hr
      have hrJcent : r ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact (hRcentJ r hr j hj).symm
      have hJmap : J.map (MulAut.conj r).toMonoidHom = J :=
        map_conj_eq_of_mem_normalizer
          ((Subgroup.centralizer_le_normalizer (J : Set G)) hrJcent)
      have hP : J ≤ J ⊓ J.map (MulAut.conj r).toMonoidHom := by
        rw [hJmap]
        exact le_inf le_rfl le_rfl
      have hrzg : r ∈ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hzg : Subgroup.zpowers g ≤ Subgroup.centralizer ({r} : Set G) :=
          Subgroup.zpowers_le.mpr
            (Subgroup.mem_centralizer_singleton_iff.mpr (hRcentY r hr).symm)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hzg hz)
      have hrzg' : r ∈ Subgroup.centralizer (Subgroup.zpowers y' : Set G) := by
        rw [hzy]
        exact hrzg
      have hrnorm : r ∈ Subgroup.normalizer (Subgroup.zpowers y' : Set G) :=
        Subgroup.centralizer_le_normalizer _ hrzg'
      exact pComponent_conj_eq_of_perfect_common hPC hJK' hrnorm hP hJperf h3J
    have hRN : R ≤ Subgroup.normalizer (K' : Set G) := by
      intro r hr
      exact mem_normalizer_iff_map_conj.mpr (hK'r r hr)
    have hRCJ : R ≤ Subgroup.centralizer (J : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (hRcentJ r hr j hj).symm
    have hJeq : Nonempty (↥J ≃* SpecialLinearGroup (Fin ((m + 2) - 1)) F2) := by
      refine ⟨?e⟩
      exact ((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr h.coords.rangeJ)).symm
    have hn5 : 5 ≤ m + 2 := h.nbr.2.2.1
    have hRCK : R ≤ Subgroup.centralizer (K' : Set G) :=
      hKG G K' J R x (m + 2) lab hn5 hQK hLabel hlab
        (by
          have hgC : g ∈ Subgroup.centralizer (K' : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro k hk
            have hg_z : g ∈ Subgroup.zpowers y' := by
              rw [hzy]
              exact Subgroup.mem_zpowers g
            have hyk : y' * k = k * y' :=
              (Subgroup.mem_centralizer_singleton_iff.mp (hK'cent hk)).symm
            have hzle : Subgroup.zpowers y' ≤ Subgroup.centralizer ({k} : Set G) :=
              Subgroup.zpowers_le.mpr
                (Subgroup.mem_centralizer_singleton_iff.mpr hyk)
            exact (Subgroup.mem_centralizer_singleton_iff.mp (hzle hg_z)).symm
          have hZN : Subgroup.zpowers g ≤ Subgroup.normalizer (K' : Set G) :=
            (Subgroup.zpowers_le.mpr hgC).trans
              (Subgroup.centralizer_le_normalizer (K' : Set G))
          exact (sup_le hRN hZN) hxR)
        hx3 hJeq hJcomp hRN hRCJ hRperf
    have hgC : g ∈ Subgroup.centralizer (K' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hg_z : g ∈ Subgroup.zpowers y' := by
        rw [hzy]
        exact Subgroup.mem_zpowers g
      have hyk : y' * k = k * y' :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hK'cent hk)).symm
      have hzle : Subgroup.zpowers y' ≤ Subgroup.centralizer ({k} : Set G) :=
        Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr hyk)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hzle hg_z)).symm
    have hZcent : Subgroup.zpowers g ≤ Subgroup.centralizer (K' : Set G) :=
      Subgroup.zpowers_le.mpr hgC
    have hxC : x ∈ Subgroup.centralizer (K' : Set G) := (sup_le hRCK hZcent) hxR
    have hcomm : ⁅K', Subgroup.zpowers x⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hxC))
    exfalso
    exact hnbr.2.2.2 (hcomm ▸ bot_le)

end GGHalfCtx

end CFSG.StandardType

end
