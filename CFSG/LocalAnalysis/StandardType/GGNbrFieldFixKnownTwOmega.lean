module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FROmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA

namespace FieldFixTwOmega

private theorem center_eq_bot {R : Type} [Group R] [IsSimpleGroup R]
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_fixGeom {l n p : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))
    (hna : ∃ x y : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)), x * y ≠ y * x)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))}
    (hf : f ∈ LargeEvenPhiQ (l - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))
    (hord : orderOf f = p) :
    LargeEvenRecipeOmegaMinus (l - 1) (2 ^ (n / p)) fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenInnSet _) f I₀ θ₀ := by
  haveI := hS
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcl := statedClassicalModel_omegaMinus l n hK b c hirr ⟨Nat.prime_two, hn, hl⟩
  have hαp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hαin : f ∉ ComponentClassification.OuterAutomorphisms.inner
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) := by
    intro h
    have hnot := (RecipeFieldOmega.ggRawInnField_omegaMinus hl hirr hK hn hp.one_lt.ne' hS
      hna).2.2.2 f hf hord
    rw [← RecipeFieldOmega.coe_inner_eq_innSet] at hnot
    exact hnot h
  obtain ⟨f₀, k, hkF, hkfin, b', c', hirr', hf0, hkcard, ⟨e⟩⟩ :=
    FR.omegaMinus_fixed_equiv hcl hp hp2 f hαp hαin
  have hdiv : n / p = f₀ := by rw [hf0, Nat.mul_div_cancel_left _ hp.pos]
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus l k b' c'))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hl hirr'
  haveI : Group.IsPerfect (StatedOmega (StatedQuadMinus l k b' c')) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus hl hirr'
  haveI : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus l k b' c'))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  set e₀ := omegaMinusProjEquiv l b' c'
  haveI hS₀ : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b' c'))) :=
    e₀.isSimpleGroup
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b' c'))) :=
    Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
  have hna₀ : ∃ x y : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b' c')),
      x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b' c'))) :=
      isMulCommutative_iff.mpr hcon
    exact Group.IsPerfect.not_isMulCommutative
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b' c'))) ‹_›
  have hfix : ggFixSub f = FP.fixSub f := Subgroup.ext fun _ => Iff.rfl
  let e' : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b' c')) ≃* ↥(ggFixSub f) :=
    e₀.trans (e.symm.trans (MulEquiv.subgroupCongr hfix.symm))
  refine ⟨k, hkF, hkfin, by rw [hdiv]; exact hkcard, b', c', hirr', hS₀, hna₀, ?_⟩
  exact ggFixGeom_of_inn hna₀ (center_eq_bot hna) (fun _ h => h) (fun _ h => h) e'

end FieldFixTwOmega

open FieldFixTwOmega in
theorem ggFieldFixKnown_twOmega : GGFieldFixKnown GGFieldFixTwOmegaLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨-, -, hrow⟩, ht⟩ := hS
  have h4 : 4 ≤ lab.rank := by
    rcases hrow with (h | h | h) | ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨-, h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      first | exact h4 | (rw [ht] at h; cases h)
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hn
  subst ht
  refine largeEvenLabelAll_omegaMinus (lab := ⟨.twD, l, n⟩) rfl h4 fun K _ _ _ hK b c hirr => ?_
  intro hS' hna f hf hord
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h2, h3, ↓reduceIte]
  exact exists_fixGeom h4 hn hp hp2 hK hirr hS' hna hf hord

end CFSG.StandardType

end
