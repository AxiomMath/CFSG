module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.HardMathSupport.Lang.Coordinator
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_injective_fixed_of_subfieldSetup {K : Type} [Field K] [Finite K]
    {k : Subfield K} {d p : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
    {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}
    (S : SubfieldSetup k Q₀ Q' σ p) (hd : 0 < d)
    {β : MulAut (matrixProjectiveDerived Q)}
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hg1 : g'.val.left = 1) (hgσ : g'.val.right = σ)
    (hΘ : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q' g' (Θ x)) :
    ∃ ι : matrixProjectiveDerived Q₀ →* matrixProjectiveDerived Q,
      Function.Injective ι ∧ ∀ y, β (ι y) = ι y := by
  let ι : matrixProjectiveDerived Q₀ →* matrixProjectiveDerived Q :=
    Θ.symm.toMonoidHom.comp (incl k S.hext)
  have hι : Function.Injective ι :=
    Θ.symm.injective.comp (incl_injective k S.hext hd)
  refine ⟨ι, hι, fun y => ?_⟩
  apply Θ.injective
  change Θ (β (Θ.symm (incl k S.hext y))) =
    Θ (Θ.symm (incl k S.hext y))
  calc
    Θ (β (Θ.symm (incl k S.hext y))) =
        matrixProjectiveConjugationHom Q' g' (Θ (Θ.symm (incl k S.hext y))) := hΘ _
    _ = matrixProjectiveConjugationHom Q' g' (incl k S.hext y) := by
      rw [MulEquiv.apply_symm_apply]
    _ = fieldAutT Q' σ S.hQσ (incl k S.hext y) := by
      rw [CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.matrixProjectiveConjugationHom_eq_fieldAutT
        S g' hg1 hgσ]
    _ = incl k S.hext y :=
      (fieldAutT_apply_iff S (incl k S.hext y)).mpr
        (subfieldDerivedImage_le k S.hext ⟨y, rfl⟩)
    _ = Θ (Θ.symm (incl k S.hext y)) := by
      rw [MulEquiv.apply_symm_apply]

theorem fieldAutOdd_pomegaOdd_subfield {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X .POmegaOdd n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧
      LieModel Y .POmegaOdd n p (f / r) := by
  classical
  have hcl : StatedClassicalModel X .POmegaOdd n p f := hX.statedClassicalModel (by decide)
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn3, hℓ2⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd hcl' F hF e
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [hchar]; exact hp2)
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates X .POmegaOdd
    (Or.inl rfl) n p f hcl' F hF e
  set θX := coordinateOddWitnessEquiv F e with hθX
  set Q := coordinateQuadOdd n F with hQ
  set β := MulAut.congr θX θ with hβdef
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hβr : β ^ r = 1 := by rw [hβdef, ← map_pow, hθr, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hout ((congr_mem_inner_iff θX θ).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = r := orderOf_eq_prime hβr hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_odd F n hn3 (by omega)]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hr hr2 hD hβr)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      X .POmegaOdd (Or.inl rfl) n p f r hcl' hr hr2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ :=
    hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = r := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / r) := by
    rw [hUr]; exact hcard
  have hsetup := subfieldSetup_odd (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hr hr2 hord' hn3 h2F
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  obtain ⟨ι, hι_inj, hι_fix⟩ :=
    exists_injective_fixed_of_subfieldSetup hsetup (by omega) Θ g' hg'l
      (hg'r.trans rfl) hΘ'
  let ιX : matrixProjectiveDerived (coordinateQuadOdd n
      (semilinearFixedSubfield U.val.right)) →* X := θX.symm.toMonoidHom.comp ι
  have hιX_inj : Function.Injective ιX := θX.symm.injective.comp hι_inj
  have hιX_fix : ∀ y, θ (ιX y) = ιX y := by
    intro y
    apply θX.injective
    change θX (θ (θX.symm (ι y))) = θX (θX.symm (ι y))
    calc
      θX (θ (θX.symm (ι y))) = β (ι y) := by
        simp [hβdef, MulAut.congr_apply]
      _ = ι y := hι_fix y
      _ = θX (θX.symm (ι y)) := by
        rw [MulEquiv.apply_symm_apply]
  have hf0 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hr.pos
  have hmodel0 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n
      (semilinearFixedSubfield U.val.right)))) .POmegaOdd n p (f / r) :=
    ⟨⟨hp, hf0, hn3, hp2⟩, semilinearFixedSubfield U.val.right, inferInstance,
      Subtype.finite, hcard', ⟨MulEquiv.refl _⟩⟩
  have hm0 : LieModel (matrixProjectiveDerived (coordinateQuadOdd n
      (semilinearFixedSubfield U.val.right))) .POmegaOdd n p (f / r) :=
    LieModel.of_mulEquiv
      (coordinateOddWitnessEquiv (semilinearFixedSubfield U.val.right) (MulEquiv.refl _))
      (Or.inl ⟨by decide, hmodel0⟩)
  refine ⟨hpf, ιX.range, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hιX_fix y
  · exact LieModel.of_mulEquiv (MonoidHom.ofInjective hιX_inj) hm0

theorem fieldAutOdd_pomegaPlus_subfield {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hX : LieModel X .POmegaPlus n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧
      LieModel Y .POmegaPlus n p (f / r) := by
  classical
  have hcl : StatedClassicalModel X .POmegaPlus n p f := hX.statedClassicalModel (by decide)
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates X .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f hcl' F hF e
  set θX := coordinatePlusWitnessEquiv F e with hθX
  set Q := coordinateQuadPlus n F with hQ
  set β := MulAut.congr θX θ with hβdef
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hβr : β ^ r = 1 := by rw [hβdef, ← map_pow, hθr, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hout ((congr_mem_inner_iff θX θ).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = r := orderOf_eq_prime hβr hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hr3 : 3 < r := by omega
      have hA : Subgroup.zpowers β ≤ familyOrbitKernel Q :=
        hgates.2.2.2.2.2.2.1 r hr hr3 _ (IsPGroup.of_card (n := 1)
          (by rw [Nat.card_zpowers, hβord, pow_one]))
      have h1 := hgates.2.2.2.2.1 (hA (Subgroup.mem_zpowers β))
      rw [hgates.2.2.2.2.2.1] at h1
      exact h1
    · rw [matrixProjectiveImage_eq_top_plus F n h5]
      exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hr hr2 hD hβr)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      X .POmegaPlus (Or.inr (Or.inl rfl)) n p f r hcl' hr hr2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ :=
    hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = r := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / r) := by
    rw [hUr]; exact hcard
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hr hr2 hord' (n := n) (by omega)
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  obtain ⟨ι, hι_inj, hι_fix⟩ :=
    exists_injective_fixed_of_subfieldSetup hsetup (by omega) Θ g' hg'l hg'r hΘ'
  let ιX : matrixProjectiveDerived (coordinateQuadPlus n
      (semilinearFixedSubfield U.val.right)) →* X := θX.symm.toMonoidHom.comp ι
  have hιX_inj : Function.Injective ιX := θX.symm.injective.comp hι_inj
  have hιX_fix : ∀ y, θ (ιX y) = ιX y := by
    intro y
    apply θX.injective
    change θX (θ (θX.symm (ι y))) = θX (θX.symm (ι y))
    calc
      θX (θ (θX.symm (ι y))) = β (ι y) := by
        simp [hβdef, MulAut.congr_apply]
      _ = ι y := hι_fix y
      _ = θX (θX.symm (ι y)) := by
        rw [MulEquiv.apply_symm_apply]
  have hf0 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hr.pos
  have hmodel0 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n
      (semilinearFixedSubfield U.val.right)))) .POmegaPlus n p (f / r) :=
    ⟨⟨hp, hf0, hn4⟩, semilinearFixedSubfield U.val.right, inferInstance,
      Subtype.finite, hcard', ⟨MulEquiv.refl _⟩⟩
  have hm0 : LieModel (matrixProjectiveDerived (coordinateQuadPlus n
      (semilinearFixedSubfield U.val.right))) .POmegaPlus n p (f / r) :=
    LieModel.of_mulEquiv
      (coordinatePlusWitnessEquiv (semilinearFixedSubfield U.val.right) (MulEquiv.refl _))
      (Or.inl ⟨by decide, hmodel0⟩)
  refine ⟨hpf, ιX.range, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hιX_fix y
  · exact LieModel.of_mulEquiv (MonoidHom.ofInjective hιX_inj) hm0

theorem fieldAutOdd_pomegaMinus_subfield {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hX : LieModel X .POmegaMinus n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧
      LieModel Y .POmegaMinus n p (f / r) := by
  classical
  have hcl : StatedClassicalModel X .POmegaMinus n p f := hX.statedClassicalModel (by decide)
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates X .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f hcl' hn1 F hF b c hirr e
  set θX := coordinateMinusWitnessEquiv F hn1 b c e with hθX
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θX θ with hβdef
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hβr : β ^ r = 1 := by rw [hβdef, ← map_pow, hθr, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hout ((congr_mem_inner_iff θX θ).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = r := orderOf_eq_prime hβr hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hr hr2 hD hβr)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      X .POmegaMinus (Or.inr (Or.inr rfl)) n p f r hcl' hr hr2 hn1 F hF b c hirr e β
      hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ :=
    hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = r := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / r) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hr.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = r := by
    have hK' : Nat.card F = p ^ ((f / r) * r) := by
      rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hp hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hr hr2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  obtain ⟨ι, hι_inj, hι_fix⟩ :=
    exists_injective_fixed_of_subfieldSetup hsetup (by omega) Θ g' hg'l hg'r hΘ'
  let ιX : matrixProjectiveDerived (coordinateQuadMinus n
      (semilinearFixedSubfield U.val.right) hn1 b' c') →* X :=
    θX.symm.toMonoidHom.comp ι
  have hιX_inj : Function.Injective ιX := θX.symm.injective.comp hι_inj
  have hιX_fix : ∀ y, θ (ιX y) = ιX y := by
    intro y
    apply θX.injective
    change θX (θ (θX.symm (ι y))) = θX (θX.symm (ι y))
    calc
      θX (θ (θX.symm (ι y))) = β (ι y) := by
        simp [hβdef, MulAut.congr_apply]
      _ = ι y := hι_fix y
      _ = θX (θX.symm (ι y)) := by
        rw [MulEquiv.apply_symm_apply]
  have hf0 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hr.pos
  have hmodel0 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n
      (semilinearFixedSubfield U.val.right) b' c'))) .POmegaMinus n p (f / r) :=
    ⟨⟨hp, hf0, hn4⟩, semilinearFixedSubfield U.val.right, inferInstance,
      Subtype.finite, hcard', b', c', hirr', ⟨MulEquiv.refl _⟩⟩
  have hm0 : LieModel (matrixProjectiveDerived (coordinateQuadMinus n
      (semilinearFixedSubfield U.val.right) hn1 b' c')) .POmegaMinus n p (f / r) :=
    LieModel.of_mulEquiv
      (coordinateMinusWitnessEquiv (semilinearFixedSubfield U.val.right) hn1 b' c'
        (MulEquiv.refl _))
      (Or.inl ⟨by decide, hmodel0⟩)
  refine ⟨hpf, ιX.range, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hιX_fix y
  · exact LieModel.of_mulEquiv (MonoidHom.ofInjective hιX_inj) hm0

end CFSG.LocalAnalysis.UniquenessCase.UC22
