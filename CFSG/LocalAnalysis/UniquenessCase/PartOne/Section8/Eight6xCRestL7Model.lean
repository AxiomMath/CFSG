module

public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_modelEquiv {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]
    {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (w : WeylGroup TwistTag.D4.tag) {g0 : ModGL TwistTag.D4.tag L}
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) :
    ∃ e : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
        ↥(LangDatum.ofTwist TwistTag.D4 Fr (p ^ f) hFr w hg0C hg0).model,
      ∀ x, (e x : ModGL TwistTag.D4.tag L) = g0⁻¹ * triEmb K σ L x * g0 := by
  let M := (LangDatum.ofTwist TwistTag.D4 Fr (p ^ f) hFr w hg0C hg0).model
  let F := fixModel (twistHom TwistTag.D4 L Fr)
  have hrange : (triEmb K σ L).range = F := by
    rw [triEmb_range hp hf hK hσ Fr hFr]
    rfl
  let e₁ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥F :=
    (MulEquiv.ofBijective (MonoidHom.rangeRestrict (triEmb K σ L))
      ⟨fun x y h => triEmb_injective (congrArg Subtype.val h),
       MonoidHom.rangeRestrict_surjective (triEmb K σ L)⟩).trans
      (MulEquiv.subgroupCongr hrange)
  have hmap : M.map (MulAut.conj g0).toMonoidHom = F := by
    have h := map_conj_fixModel (τ := TwistTag.D4.tag) (L := L)
      (Φ := twistHom TwistTag.D4 L Fr)
      (n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w) (g0 := g0) hg0C hg0
    exact h
  have hmap_inv : F.map (MulAut.conj g0).symm.toMonoidHom = M := by
    have h := congrArg (Subgroup.map (MulAut.conj g0).symm.toMonoidHom) hmap
    have hcomp : (MulAut.conj g0).symm.toMonoidHom.comp (MulAut.conj g0).toMonoidHom =
        MonoidHom.id _ := by
      simpa only [MulEquiv.toMonoidHom_eq_coe] using
        MulEquiv.toMonoidHom_symm_comp_toMonoidHom (MulAut.conj g0)
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    exact h.symm
  let e₂ : ↥F ≃* ↥M :=
    ((MulAut.conj g0).symm.subgroupMap F).trans (MulEquiv.subgroupCongr hmap_inv)
  refine ⟨e₁.trans e₂, ?_⟩
  intro x
  have he₁ : (e₁ x : ModGL TwistTag.D4.tag L) = triEmb K σ L x := rfl
  change ((MulAut.conj g0).symm (e₁ x) : ModGL TwistTag.D4.tag L) =
    g0⁻¹ * triEmb K σ L x * g0
  rw [MulAut.conj_symm_apply, he₁]

private theorem coe_fieldActor_eq_conj_l7m {K : Type} [Field K] {σ : K ≃+* K}
    [Finite K]
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ((fieldActor (t := TwistTag.D4) σ σ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * s * diagramMap TwistTag.D4 K := by
  have hx := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
    (graphFixedRootGroup_le _ _ _ s.2)).2
  rw [twistHom_apply] at hx
  rw [coe_fieldActor]
  calc Units.map (entrywiseHom σ.toRingHom) (s : ModGL TwistTag.D4.tag K) =
      (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
        Units.map (entrywiseHom σ.toRingHom) (s : ModGL TwistTag.D4.tag K) *
          (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
    _ = (diagramMap TwistTag.D4 K)⁻¹ * s * diagramMap TwistTag.D4 K := by rw [hx]

theorem modelEquiv_fieldActor {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]
    [Finite K]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} {g0 : ModGL TwistTag.D4.tag L}
    (e : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥M)
    (he : ∀ x, (e x : ModGL TwistTag.D4.tag L) = g0⁻¹ * triEmb K σ L x * g0)
    (hP : diagramMap TwistTag.D4 L * g0 = g0 * diagramMap TwistTag.D4 L)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    (e (fieldActor (t := TwistTag.D4) σ σ x) : ModGL TwistTag.D4.tag L) =
      (diagramMap TwistTag.D4 L)⁻¹ * e x * diagramMap TwistTag.D4 L := by
  have htri : (triEmb K σ L (fieldActor (t := TwistTag.D4) σ σ x) :
      ModGL TwistTag.D4.tag L) =
      (diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L x * diagramMap TwistTag.D4 L := by
    rw [triEmb_apply, coe_fieldActor_eq_conj_l7m]
    rw [map_mul, map_mul, map_inv,
      baseChangeGL_diagramMap (algebraMap K L) TwistTag.D4, ← triEmb_apply]
  have hPinv : g0⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ =
      (diagramMap TwistTag.D4 L)⁻¹ * g0⁻¹ := by
    calc
      g0⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ =
          (diagramMap TwistTag.D4 L * g0)⁻¹ :=
        (mul_inv_rev (diagramMap TwistTag.D4 L) g0).symm
      _ = (g0 * diagramMap TwistTag.D4 L)⁻¹ := by rw [hP]
      _ = (diagramMap TwistTag.D4 L)⁻¹ * g0⁻¹ :=
        mul_inv_rev g0 (diagramMap TwistTag.D4 L)
  rw [he (fieldActor (t := TwistTag.D4) σ σ x), htri]
  calc
    g0⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L x *
        diagramMap TwistTag.D4 L) * g0 =
        (g0⁻¹ * (diagramMap TwistTag.D4 L)⁻¹) * triEmb K σ L x *
          (diagramMap TwistTag.D4 L * g0) := by group
    _ = ((diagramMap TwistTag.D4 L)⁻¹ * g0⁻¹) * triEmb K σ L x *
          (g0 * diagramMap TwistTag.D4 L) := by rw [hPinv, hP]
    _ = (diagramMap TwistTag.D4 L)⁻¹ * (g0⁻¹ * triEmb K σ L x * g0) *
          diagramMap TwistTag.D4 L := by group
    _ = (diagramMap TwistTag.D4 L)⁻¹ * e x * diagramMap TwistTag.D4 L := by rw [← he x]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
