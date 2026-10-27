module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.RankThree.Chevalley.SteinbergBID4Kernel
public import CFSG.LieType.Chevalley.WeylRootTransport

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Lang.D4Three

private lemma d3a_d4Support_eq_d4Nodes : d4Support = d4Nodes Tag.E6 := by
  ext i
  fin_cases i <;> simp [d4Support, CFSG.RankThree.PartOne.KE.d4Nodes] <;> decide

noncomputable abbrev d4KernelGroup
    (L : Type) [Field L] (v : WeylGroup Tag.E6) : Subgroup (ModGL Tag.E6 L) :=
  rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))

@[expose] def NTPThetaChar
    {L : Type} [Field L] (v : WeylGroup Tag.E6)
    (Θ : ↥(d4KernelGroup L v) ≃* ↥(adjointGroup Tag.D4 L)) : Prop :=
  ∀ (y : ↥(d4KernelGroup L v)) (k : Fin Tag.D4.rank) (c : L),
    ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ → (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c) ∧
    ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ → (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c)

theorem ntpD4_theta
    {L : Type} [Field L] [CharP L 2] (v : WeylGroup Tag.E6) :
    ∃ Θ : ↥(d4KernelGroup L v) ≃* ↥(adjointGroup Tag.D4 L), NTPThetaChar v Θ := by
  let nv : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L v
  let Φ : MulAut (ModGL Tag.E6 L) := MulAut.conj nv
  let H : Subgroup (ModGL Tag.E6 L) := subsystemGroup Tag.E6 L d4Support
  let H' : Subgroup (ModGL Tag.E6 L) := d4KernelGroup L v
  have hH : H.map Φ.toMonoidHom = H' := by
    have e1 : H = rootSpan Tag.E6 L (parabolicRoots Tag.E6 d4Support) :=
      subsystemGroup_eq_rootSpan d4Support
    have e2 : H' = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 d4Support) := by
      change rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) = _
      rw [d3a_d4Support_eq_d4Nodes]
    rw [e1, e2]
    exact (canonical_weyl_root_transport Tag.E6 L).1 v _ (by intro α hα; exact hα.1)
  let e : H ≃* H' :=
    (H.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans (MulEquiv.subgroupCongr hH)
  let d4ResCod : H →* ↥(adjointGroup Tag.D4 L) :=
    (d4Res L).codRestrict _ (fun g => d4Res_mem_adjointGroup g)
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hinj : Function.Injective d4ResCod := by
    intro x y hxy
    have h1 : d4Res L x = d4Res L y := congrArg Subtype.val hxy
    exact d4Res_injective_of_ringChar_eq_two h2 h1
  have hsurj : Function.Surjective d4ResCod := by
    intro x
    have hx : (x : ModGL Tag.D4 L) ∈ (d4Res L).range := by
      rw [range_d4Res]
      exact x.2
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, Subtype.ext hg⟩
  let d4ResEquiv : H ≃* ↥(adjointGroup Tag.D4 L) :=
    MulEquiv.ofBijective d4ResCod ⟨hinj, hsurj⟩
  let Θ : ↥(d4KernelGroup L v) ≃* ↥(adjointGroup Tag.D4 L) := e.symm.trans d4ResEquiv
  refine ⟨Θ, ?_⟩
  have hcoe : ∀ x : H, ((e x : H') : ModGL Tag.E6 L) = nv * (x : ModGL Tag.E6 L) * nv⁻¹ := by
    intro x
    have h1 : ((H.equivMapOfInjective Φ.toMonoidHom Φ.injective x :
        H.map Φ.toMonoidHom) : ModGL Tag.E6 L) = Φ ↑x := by
      exact Subgroup.coe_equivMapOfInjective_apply H Φ.toMonoidHom Φ.injective x
    have h2 : ((MulEquiv.subgroupCongr hH (H.equivMapOfInjective Φ.toMonoidHom Φ.injective x) :
        H') : ModGL Tag.E6 L) =
        ((H.equivMapOfInjective Φ.toMonoidHom Φ.injective x : H.map Φ.toMonoidHom) :
          ModGL Tag.E6 L) := by rfl
    calc ((e x : H') : ModGL Tag.E6 L) =
          ((MulEquiv.subgroupCongr hH (H.equivMapOfInjective Φ.toMonoidHom Φ.injective x) :
            H') : ModGL Tag.E6 L) := by rfl
      _ = ((H.equivMapOfInjective Φ.toMonoidHom Φ.injective x : H.map Φ.toMonoidHom) :
            ModGL Tag.E6 L) := h2
      _ = Φ ↑x := h1
      _ = nv * (x : ModGL Tag.E6 L) * nv⁻¹ := rfl
  intro y k c
  constructor
  · intro h
    have hx : ((e.symm y : H) : ModGL Tag.E6 L) = xUnit Tag.E6 L (d4Idx k) c := by
      have h1 : nv * ((e.symm y : H) : ModGL Tag.E6 L) * nv⁻¹ =
          nv * xUnit Tag.E6 L (d4Idx k) c * nv⁻¹ := by
        calc nv * ((e.symm y : H) : ModGL Tag.E6 L) * nv⁻¹ =
              ((e (e.symm y) : H') : ModGL Tag.E6 L) := by rw [hcoe]
          _ = (y : ModGL Tag.E6 L) := by rw [MulEquiv.apply_symm_apply]
          _ = nv * xUnit Tag.E6 L (d4Idx k) c * nv⁻¹ := h
      exact mul_left_cancel (mul_right_cancel h1)
    have hres : d4Res L (e.symm y) = xUnit Tag.D4 L k c := by
      have heq : e.symm y = ⟨xUnit Tag.E6 L (d4Idx k) c, by rw [← hx]; exact (e.symm y).2⟩ :=
        Subtype.ext hx
      rw [heq, d4Res_xUnit]
    have hTheta : (Θ y : ModGL Tag.D4 L) = (d4ResEquiv (e.symm y) : ModGL Tag.D4 L) := rfl
    rw [hTheta]
    change (d4Res L (e.symm y) : ModGL Tag.D4 L) = xUnit Tag.D4 L k c
    exact hres
  · intro h
    have hx : ((e.symm y : H) : ModGL Tag.E6 L) = yUnit Tag.E6 L (d4Idx k) c := by
      have h1 : nv * ((e.symm y : H) : ModGL Tag.E6 L) * nv⁻¹ =
          nv * yUnit Tag.E6 L (d4Idx k) c * nv⁻¹ := by
        calc nv * ((e.symm y : H) : ModGL Tag.E6 L) * nv⁻¹ =
              ((e (e.symm y) : H') : ModGL Tag.E6 L) := by rw [hcoe]
          _ = (y : ModGL Tag.E6 L) := by rw [MulEquiv.apply_symm_apply]
          _ = nv * yUnit Tag.E6 L (d4Idx k) c * nv⁻¹ := h
      exact mul_left_cancel (mul_right_cancel h1)
    have hres : d4Res L (e.symm y) = yUnit Tag.D4 L k c := by
      have heq : e.symm y = ⟨yUnit Tag.E6 L (d4Idx k) c, by rw [← hx]; exact (e.symm y).2⟩ :=
        Subtype.ext hx
      rw [heq, d4Res_yUnit]
    have hTheta : (Θ y : ModGL Tag.D4 L) = (d4ResEquiv (e.symm y) : ModGL Tag.D4 L) := rfl
    rw [hTheta]
    change (d4Res L (e.symm y) : ModGL Tag.D4 L) = yUnit Tag.D4 L k c
    exact hres

end CFSG.StandardType.NTPlane

end
