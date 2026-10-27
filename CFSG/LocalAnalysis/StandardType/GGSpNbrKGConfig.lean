module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin

section JFacts

variable {G : Type} [Group G] [Finite G]

theorem ggSpNbr_J_facts (hlift : GGSpLiftInput) (hMp : GGInnerDiagMpInput)
    (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) {y' : G} {K' : Subgroup G}
    (hK' : GGNbr p B x D J y' K') :
    x ∈ Bs ∧ x ^ p = 1 ∧ x ∉ Subgroup.centralizer (K' : Set G) ∧ J ≤ K' ∧
      J ≤ Subgroup.centralizer ({x} : Set G) ∧
      CFSG.Assembly.IsSubnormal J (K' ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      Subgroup.center J = ⊥ ∧
      ∃ ψ : StatedSp m (GaloisField 2 f) →* G, Function.Injective ψ ∧ ψ.range = J := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  have hJK : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2
    (hJp G p B x L D J hcfg.1 hcfg.2.2) hK'
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hcfg.2.2.1 hK'.2.1
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := hJY.1.trans inf_le_right
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hcfg.2.2 hK')
  have hsub : CFSG.Assembly.IsSubnormal J (K' ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hle : K' ⊓ Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.centralizer ({y'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
      inf_le_inf_right _ hKc.1
    have h := CFSG.Assembly.IsSubnormal.inf_of_le hJY.2.1 hle
    rwa [inf_eq_left.mpr (le_inf hJK hJx)] at h
  obtain ⟨φ₀, hφ₀inj, hφ₀range⟩ := hlift G L (m + 1) f hN.2.1 hInn.1.1 hN.1
  obtain ⟨φ, hφinj, -, hφlevi⟩ :=
    ggSpLeviInputAtL_of_inputs hMp hlift G p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN
      φ₀ hφ₀inj hφ₀range
  let ψ : StatedSp m (GaloisField 2 f) →* G := φ.comp (spLeviBlock m (GaloisField 2 f))
  have hψinj : Function.Injective ψ := hφinj.comp spLeviBlock_injective
  have hψrange : ψ.range = J := hφlevi
  refine ⟨hcfg.x_facts.1, hxp, ggNbr_x_not_mem_centralizer hK', hJK, hJx, hsub, ?_, ?_⟩
  · have hcent := center_range_statedSp_eq_bot ψ hψinj
    rwa [hψrange] at hcent
  · exact ⟨ψ, hψinj, hψrange⟩

end JFacts

end CFSG.StandardType
