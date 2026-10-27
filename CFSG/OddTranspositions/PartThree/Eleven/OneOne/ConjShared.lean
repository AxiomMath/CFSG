module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.SixNineUnconditional
public import CFSG.OddTranspositions.PartFour.LineTransport
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

noncomputable def conjEquiv (hC : HypothesisC D) (g : G) :
    Halpha D hC.alpha ≃* Halpha D (hC.conj g).alpha :=
  let hH : Halpha D (cimg g hC.alpha) =
      (Halpha D hC.alpha).map (↑(MulAut.conj g)) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      CFSG.OddTranspositions.PartFour.Halpha_cimg hC.setup.normal g hC.alpha
  ((MulEquiv.subgroupMap (MulAut.conj g) (Halpha D hC.alpha)).trans
    (MulEquiv.subgroupCongr hH.symm)).trans
    (MulEquiv.subgroupCongr (congrArg (Halpha D) (hC.conj_alpha g)).symm)

lemma conjEquiv_coe (hC : HypothesisC D) (g : G) (x : Halpha D hC.alpha) :
    ((conjEquiv hC g x : Halpha D (hC.conj g).alpha) : G) = g * (x : G) * g⁻¹ := by
  dsimp only [conjEquiv]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [MulEquiv.subgroupCongr_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]
  rfl

lemma conjRadical_map (hC : HypothesisC D) (g : G) :
    (CFSG.solvableRadical (Halpha D hC.alpha)).map (↑(conjEquiv hC g)) =
      CFSG.solvableRadical (Halpha D (hC.conj g).alpha) := by
  simpa only [MulEquiv.toMonoidHom_eq_coe] using
    CFSG.LieType.SteinbergBR.solvableRadical_map_equiv (conjEquiv hC g)

lemma conjEquiv_DstarH (hC : HypothesisC D) (g : G)
    (x : Halpha D hC.alpha) :
    x ∈ DstarH hC ↔ conjEquiv hC g x ∈ DstarH (hC.conj g) := by
  rw [mem_DstarH_iff, mem_DstarH_iff, conjEquiv_coe, hC.conj_alpha,
    CFSG.OddTranspositions.PartFour.DalphaStar_cimg hC.setup.normal g hC.alpha, mem_cimg]
  have h : g⁻¹ * (g * (x : G) * g⁻¹) * g = (x : G) := by group
  rw [h]

lemma imageClass_conj (hC : HypothesisC D) (g : G) :
    (QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
      (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
      (conjRadical_map hC g)) '' imageClass hC = imageClass (hC.conj g) := by
  ext y
  rw [imageClass, imageClass]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rw [QuotientGroup.congr_mk']
    exact ⟨conjEquiv hC g x, (conjEquiv_DstarH hC g x).mp hx, rfl⟩
  · rintro ⟨y', hy', rfl⟩
    let x := (conjEquiv hC g).symm y'
    have hx : x ∈ DstarH hC := by
      rw [conjEquiv_DstarH hC g x]
      simpa [x] using hy'
    refine ⟨QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [QuotientGroup.congr_mk']
    simp [x]

theorem d_not_mem_DalphaStar (hC : HypothesisC D) :
    hC.d ∉ DalphaStar D hC.alpha := by
  rintro ⟨β, hβ, hdβ⟩
  have heq : β = hC.alpha :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha (mem_Dalpha_iff.mp hβ).1
      (mem_blockClass_self hC.alpha) ⟨hC.d, hdβ, hC.d_mem_alpha⟩
  exact (mem_Dalpha_iff.mp hβ).2.2.1 heq

theorem d_mem_centralizer (hC : HypothesisC D) :
    hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
  change hC.d ∈ Subgroup.centralizer (Subgroup.closure (DalphaStar D hC.alpha) : Set G)
  rw [Subgroup.centralizer_closure]
  exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hC.DalphaStar_subset_commute hy).2)

end CFSG.OddTranspositions.PartThree
