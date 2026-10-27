module

public import CFSG.GroupTheory.FixedCentralQuotientFamily
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ComponentNormal
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public noncomputable section

namespace CFSG.StandardType.QTwoCentralizer

open CFSG.GroupTheory.FixedCentralQuotientFamily

variable {G : Type*} [Group G] (L D : Subgroup G)
  (hDL : D ≤ Subgroup.normalizer (L : Set G))

@[expose] def action (d : D) : MulAut L :=
  L.normalizerMonoidHom ⟨d, hDL d.property⟩

theorem centerInvariant (d : D) :
    (Subgroup.center L).map (action L D hDL d).toMonoidHom = Subgroup.center L :=
  (Subgroup.characteristic_iff_map_eq.mp inferInstance) (action L D hDL d)

@[expose] def quotientCentralizer : Subgroup (L ⧸ Subgroup.center L) :=
  quotientFixed (Subgroup.center L) (action L D hDL) (centerInvariant L D hDL)

@[expose] def centralizerPreimage : Subgroup L :=
  fixedPreimage (Subgroup.center L) (action L D hDL) (centerInvariant L D hDL)

theorem commonFixed_eq :
    commonFixed (action L D hDL) = (Subgroup.centralizer (D : Set G)).subgroupOf L := by
  ext l
  change ((l : L) ∈ (⨅ d : D, CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
    (action L D hDL d))) ↔ (l : G) ∈ Subgroup.centralizer (D : Set G)
  rw [Subgroup.mem_iInf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h d hd
    have hx : d * (l : G) * d⁻¹ = l := congrArg Subtype.val (h ⟨d, hd⟩)
    calc d * (l : G) = d * (l : G) * d⁻¹ * d := by group
      _ = (l : G) * d := by rw [hx]
  · intro h d
    apply Subtype.ext
    change (d : G) * (l : G) * (d : G)⁻¹ = l
    rw [h d d.property]
    group

theorem centralizer_le_preimage :
    (Subgroup.centralizer (D : Set G)).subgroupOf L ≤ centralizerPreimage L D hDL := by
  rw [← commonFixed_eq L D hDL]
  exact commonFixed_le (Subgroup.center L) (action L D hDL) (centerInvariant L D hDL)

@[expose] def projection : centralizerPreimage L D hDL →* quotientCentralizer L D hDL :=
  CFSG.GroupTheory.FixedCentralQuotientFamily.projection
    (Subgroup.center L) (action L D hDL) (centerInvariant L D hDL)

@[expose] def componentImage (J : Subgroup G) :
    Subgroup (quotientCentralizer L D hDL) :=
  ((J.subgroupOf L).subgroupOf (centralizerPreimage L D hDL)).map (projection L D hDL)

theorem isComponentOf_componentImage {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    CFSG.Assembly.IsComponentOf
      (componentImage L D hDL J) ⊤ := by
  let H : Subgroup L := centralizerPreimage L D hDL
  let C : Subgroup L := (Subgroup.centralizer (D : Set G)).subgroupOf L
  let P : Subgroup L := J.subgroupOf L
  have hJC : P ≤ C := fun _ hj => hJ.1 hj |>.2
  have hCH : C ≤ H := centralizer_le_preimage L D hDL
  have hPL : CFSG.Assembly.IsSubnormal P C := by
    have hchain := hJ.2.1.comap L.subtype
    have hLtop : L.comap L.subtype = ⊤ := by
      ext l
      exact iff_of_true l.property (Subgroup.mem_top _)
    change CFSG.Assembly.IsSubnormal (J.comap L.subtype)
      ((Subgroup.centralizer (D : Set G)).comap L.subtype)
    simpa only [Subgroup.comap_inf, hLtop, top_inf_eq] using hchain
  have hJq : CFSG.Assembly.IsQuasisimple P :=
    (CFSG.Assembly.IsQuasisimple.congr
      (Subgroup.subgroupOfEquivOfLe (hJ.1.trans inf_le_left))).mpr hJ.2.2
  let hCn : (C.subgroupOf H).Normal := by
    have hkerC : (CFSG.GroupTheory.FixedCentralQuotientFamily.displacement
        (Subgroup.center L) (action L D hDL) (centerInvariant L D hDL) le_rfl).ker =
        C.subgroupOf H := by
      rw [CFSG.GroupTheory.FixedCentralQuotientFamily.displacement_kernel,
        commonFixed_eq L D hDL]
      rfl
    rw [← hkerC]
    exact MonoidHom.normal_ker _
  have hcompH : CFSG.Assembly.IsComponentOf P H := by
    refine ⟨hJC.trans hCH, ?_, hJq⟩
    exact hPL.trans (.step hCH hCn (.refl H))
  let π := projection L D hDL
  have hPH : P ≤ H := hJC.trans hCH
  let f : P →* (P.subgroupOf H).map π :=
    π.subgroupMap (P.subgroupOf H) |>.comp
      (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom
  have hf : Function.Surjective f :=
    (π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hPH).symm.surjective
  have hfker : f.ker ≤ Subgroup.center P := by
    intro a ha
    have haz : (a : L) ∈ Subgroup.center L := by
      apply (QuotientGroup.eq_one_iff _).mp
      have hfa : f a = 1 := (MonoidHom.mem_ker (f := f)).mp ha
      have ha1 := congrArg
        (fun t : ((P.subgroupOf H).map π) =>
          (((t : quotientCentralizer L D hDL) : L ⧸ Subgroup.center L))) hfa
      exact ha1
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp haz b
  have hmapq : CFSG.Assembly.IsQuasisimple ((P.subgroupOf H).map π) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_surjective
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hJq)
        f hf hfker)
  have hmapComp : CFSG.Assembly.IsComponentOf ((P.subgroupOf H).map π) ⊤ := by
    refine ⟨le_top, ?_, hmapq⟩
    have hsn : CFSG.Assembly.IsSubnormal (P.subgroupOf H) ⊤ :=
      CFSG.Assembly.IsSubnormal.of_mathlib hcompH.2.1.subgroupOf
    have hmap := hsn.map π
    rwa [Subgroup.map_top_of_surjective π (CFSG.GroupTheory.FixedCentralQuotientFamily.projection_surjective
      (Subgroup.center L) (action L D hDL) (centerInvariant L D hDL))] at hmap
  exact hmapComp

end CFSG.StandardType.QTwoCentralizer

end
