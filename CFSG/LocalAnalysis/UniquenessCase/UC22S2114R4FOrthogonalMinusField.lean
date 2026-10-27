module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FOrthogonalPlusField
import CFSG.RankThree.PartOne.AUTSL.OmegaModel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Rank
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTwoPart
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem hyperbolicHom_injective {K : Type} [Field K] {m : ℕ}
    {ρ ι : Type} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι) :
    Function.Injective (hyperbolicHom (K := K) e) := by
  intro A B h
  apply Units.ext
  ext i j
  have hh := congrArg (fun M : GL ι K =>
    (M : Matrix ι ι K) (e (.inl (.inl i))) (e (.inl (.inl j)))) h
  simpa [coe_hyperbolicHom, hyperbolicBlock] using hh

theorem glFieldAut_hyperbolicHom {K : Type} [Field K] {m : ℕ}
    {ρ ι : Type} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι) (σ : K ≃+* K) (A : GL (Fin m) K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut ι K σ (hyperbolicHom e A) =
      hyperbolicHom e
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin m) K σ A) := by
  apply Units.ext
  have hblock : (hyperbolicBlock ρ A).map σ =
      hyperbolicBlock ρ
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin m) K σ A) := by
    have hA := congrArg (fun B : GL (Fin m) K => (B : Matrix (Fin m) (Fin m) K))
      (map_inv (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin m) K σ).toMonoidHom A)
    change ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map σ =
      (((CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin m) K σ A)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) at hA
    simp only [hyperbolicBlock, fromBlocks_map, transpose_map, hA]
    simp
    rfl
  ext i j
  change σ ((hyperbolicHom e A : GL ι K).val i j) = _
  have h := congrFun₂ hblock (e.symm i) (e.symm j)
  simpa [coe_hyperbolicHom] using h

theorem isHyperbolicSplit_coordinateQuadMinus {K : Type} [Field K] {n : ℕ}
    (hn : 1 ≤ n) (b c : K) :
    IsHyperbolicSplit
      ((Equiv.sumAssoc (Fin (n - 1)) (Fin (n - 1)) (Fin 2)).trans (minusIndexEquiv n hn))
      (coordinateQuadMinus n K hn b c)
      (fun w : Fin 2 → K => w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2) := by
  change ∀ v, _
  intro v
  rw [coordinateQuadMinus_apply]
  change (∑ i, v (minusIndexEquiv n hn (.inl i)) *
      v (minusIndexEquiv n hn (.inr (.inl i)))) +
      v (minusIndexEquiv n hn (.inr (.inr 0))) ^ 2 +
      b * v (minusIndexEquiv n hn (.inr (.inr 0))) *
        v (minusIndexEquiv n hn (.inr (.inr 1))) +
      c * v (minusIndexEquiv n hn (.inr (.inr 1))) ^ 2 =
    (∑ i, v (minusIndexEquiv n hn (.inl i)) *
      v (minusIndexEquiv n hn (.inr (.inl i)))) +
      (v (minusIndexEquiv n hn (.inr (.inr 0))) ^ 2 +
        b * v (minusIndexEquiv n hn (.inr (.inr 0))) *
          v (minusIndexEquiv n hn (.inr (.inr 1))) +
        c * v (minusIndexEquiv n hn (.inr (.inr 1))) ^ 2)
  ring

@[expose] noncomputable def orthogonalMinusLeviHom {K : Type} [Field K] {n : ℕ}
    (hn : 4 ≤ n) (b c : K) :
    SpecialLinearGroup (Fin (n - 1)) K →* matrixDerived (coordinateQuadMinus n K (by omega) b c) :=
  (((hyperbolicHom
      ((Equiv.sumAssoc (Fin (n - 1)) (Fin (n - 1)) (Fin 2)).trans (minusIndexEquiv n (by omega)))).comp
        SpecialLinearGroup.toGL).codRestrict
    (matrixDerived (coordinateQuadMinus n K (by omega) b c)) (by
      intro A
      rw [CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega]
      exact range_le_statedOmega (by omega : 3 ≤ n - 1)
        (isHyperbolicSplit_coordinateQuadMinus (by omega) b c) ⟨A, rfl⟩))

theorem orthogonalMinusLeviHom_injective {K : Type} [Field K] {n : ℕ} (hn : 4 ≤ n)
    (b c : K) : Function.Injective (orthogonalMinusLeviHom (K := K) hn b c) := by
  intro A B h
  exact SpecialLinearGroup.toGL_injective
    (hyperbolicHom_injective _ (congrArg Subtype.val h))

theorem fieldPair_orthogonalMinusLeviHom {K : Type} [Field K] {n : ℕ} (hn : 4 ≤ n)
    (σ : K ≃+* K) (b c : semilinearFixedSubfield σ)
    (A : SpecialLinearGroup (Fin (n - 1)) K) :
    matrixDerivedConjugation (coordinateQuadMinus n K (by omega) (b : K) (c : K))
      (fieldPair _ σ (coordinateQuadMinus_fieldAut _ n (by omega) (fun _ => Iff.rfl) b c))
      (orthogonalMinusLeviHom hn (b : K) (c : K) A) =
    orthogonalMinusLeviHom hn (b : K) (c : K) (SpecialLinearGroup.map σ.toRingHom A) := by
  apply Subtype.ext
  rw [matrixDerivedConjugation_fieldPair_val]
  change CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut _ K σ
      (hyperbolicHom _ (SpecialLinearGroup.toGL A)) =
    hyperbolicHom _ (SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom A))
  rw [glFieldAut_hyperbolicHom]
  congr 1
  apply Units.ext
  ext i j
  rfl

theorem uc22s2114r4f_exists_fpf_orthogonalMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n f r : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (σ : K ≃+* K) (hσ : orderOf σ = r)
    (b c : semilinearFixedSubfield σ)
    (hirr : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) (b : K) (c : K)),
            Function.Injective ι ∧ ∀ a,
              fieldAutT _ σ (coordinateQuadMinus_fieldAut _ n (by omega) (fun _ => Iff.rfl) b c)
                (ι a) = ι (κ a) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = d + 4 + 1 := ⟨n - 5, by omega⟩
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, j, hj, hσj⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hK hr hr5 σ hσ
  let A := Q × Q
  let κ : A →* A := τ.prodMap τ
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hc
    have h := (Group.isCyclic_prod_iff.1 hc).2.2
    simp only [hQ] at h
    exact hq.ne_one (Nat.coprime_self q |>.1 h)
  have hκ : ∀ a : A, κ a = a → a = 1 := fun a ha =>
    Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let ψ : SpecialLinearGroup (Fin (d + 4)) K →*
      matrixDerived (coordinateQuadMinus (d + 4 + 1) K (by omega) (b : K) (c : K)) :=
    orthogonalMinusLeviHom (by omega : 4 ≤ (d + 4 + 1)) (b : K) (c : K)
  have hψ : Function.Injective ψ := orthogonalMinusLeviHom_injective
    (by omega : 4 ≤ (d + 4 + 1)) (b : K) (c : K)
  let J : A →* SpecialLinearGroup (Fin (d + 4)) K :=
    (slBlockPairHom d).comp (j.prodMap j)
  have hJ : Function.Injective J := (slBlockPairHom_injective d).comp (by
    intro a b hab
    exact Prod.ext (hj (congrArg Prod.fst hab)) (hj (congrArg Prod.snd hab)))
  have hQnz : ∃ v, coordinateQuadMinus (d + 4 + 1) K (by omega) (b : K) (c : K) v ≠ 0 :=
    CFSG.RankThree.PartOne.AUTSL.exists_ne_zero_of_polar_nondegenerate (by omega) _
      (regular_coordinateQuadMinus (d + 4 + 1) K (b : K) (c : K) (by omega) hirr).1
  have hproj : Function.Injective (matrixProjectiveProjection
      (coordinateQuadMinus (d + 4 + 1) K (by omega) (b : K) (c : K))) :=
    (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv _ hQnz).injective
  let ι : A →* matrixProjectiveDerived (coordinateQuadMinus (d + 4 + 1) K (by omega) (b : K) (c : K)) :=
    (matrixProjectiveProjection _).comp (ψ.comp J)
  have hι : Function.Injective ι := hproj.comp (hψ.comp hJ)
  have hψσ : ∀ g : SpecialLinearGroup (Fin (d + 4)) K,
      matrixDerivedConjugation _
          (fieldPair _ σ (coordinateQuadMinus_fieldAut _ (d + 4 + 1) (by omega) (fun _ => Iff.rfl) b c))
          (ψ g) = ψ (SpecialLinearGroup.map σ.toRingHom g) := by
    exact fieldPair_orthogonalMinusLeviHom (by omega : 4 ≤ (d + 4 + 1)) σ b c
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change fieldAutT _ σ _ (matrixProjectiveProjection _ (ψ (J a))) =
    matrixProjectiveProjection _ (ψ (J (κ a)))
  rw [fieldAutT_mk, hψσ]
  apply congrArg (fun x => matrixProjectiveProjection _ (ψ x))
  change SpecialLinearGroup.map σ.toRingHom (slBlockPairHom d (j a.1, j a.2)) =
    slBlockPairHom d (j (τ a.1), j (τ a.2))
  rw [map_slBlockPairHom, hσj, hσj]

theorem uc22s2114r4f_orthogonalMinus_field_descent {Y : Type} [Group Y] [Finite Y]
    {n f r : ℕ} (hn : 5 ≤ n) (hY : LieModel Y .POmegaMinus n 2 f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
        ∃ b c : semilinearFixedSubfield σ,
          (∀ s : semilinearFixedSubfield σ, s ^ 2 + b * s + c ≠ 0) ∧
          (∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0) ∧
          ∃ ε : Y ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) (b : K) (c : K)),
            ∀ x, ε (θ x) = fieldAutT _ σ
              (coordinateQuadMinus_fieldAut _ n (by omega) (fun _ => Iff.rfl) b c) (ε x) := by
  classical
  have hcl := hY.statedClassicalModel (by decide)
  have hcl' := hcl
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates Y .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hcl' hn1 K hK b c hirr e
  let θY := coordinateMinusWitnessEquiv K hn1 b c e
  let Q := coordinateQuadMinus n K hn1 b c
  let β := MulAut.congr θY θ
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hβr : β ^ r = 1 := by rw [← map_pow, hθr, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hout ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θY θ).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout
    (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = r := orderOf_eq_prime hβr hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus K n (by omega) b c hirr]
    exact mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
      hk hr hr2 hD hβr)
  obtain ⟨hrf, hrest⟩ := orthogonal_prime_semilinear_actual_fixed_form_descent
    Y .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f r hcl' hr (by omega) hr2
      hn1 K hK b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, -, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hσ : orderOf U.val.right = r := hUr ▸ hord
  have hk : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / r) := hUr ▸ hcard
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) K = r := by
    have hf0 := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < f) hrf) hr.pos
    apply finrank_subfield_eq _ Nat.prime_two hf0 hk
    rw [Nat.div_mul_cancel hrf]
    exact hK
  have hroot := rootFree_of_odd_degree (semilinearFixedSubfield U.val.right) hr hr2 hdeg b' c' hirr'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hr hr2 hσ (by omega : 4 ≤ n) hdeg b' c' hirr'
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, hK, U.val.right, hσ,
    b', c', hirr', hroot, θY.trans Θ, ?_⟩
  intro x
  have hx : Θ (β (θY x)) = matrixProjectiveConjugationHom _ g' (Θ (θY x)) := by
    rw [← hUκ]
    exact hΘ _
  rw [CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.matrixProjectiveConjugationHom_eq_fieldAutT
    hsetup g' hg'l hg'r] at hx
  have hβapply : β (θY x) = θY (θ x) := by
    change θY (θ (θY.symm (θY x))) = θY (θ x)
    rw [MulEquiv.symm_apply_apply]
  rw [hβapply] at hx
  exact hx

theorem uc22s2114r4f_exists_fixed_three_orthogonalMinus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn : 5 ≤ n) (σ : K ≃+* K) (b c : semilinearFixedSubfield σ) :
    ∃ X : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) (b : K) (c : K))),
      IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, fieldAutT _ σ
        (coordinateQuadMinus_fieldAut _ n (by omega) (fun _ => Iff.rfl) b c) x = x := by
  let k := semilinearFixedSubfield σ
  let e := coordinateMinusWitnessEquiv k (by omega : 1 ≤ n) b c (MulEquiv.refl
    (StatedProj (StatedOmega (StatedQuadMinus n k b c))))
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived
      (coordinateQuadMinus n k (by omega) b c))) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.omegaMinus_four_le_pRank_three hn b c
  obtain ⟨E, -, hEp, hEc⟩ :=
    PartTwo.Inputs1719.FourteenEight.exists_noncyclic_le_of_two_le_pRank Nat.prime_three
      (by omega : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived
        (coordinateQuadMinus n k (by omega) b c))))
  let j : E →* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) (b : K) (c : K)) :=
    (incl k (coordinateQuadMinus_isExtension k n (by omega) b c)).comp E.subtype
  have hj : Function.Injective j :=
    (incl_injective k (coordinateQuadMinus_isExtension k n (by omega) b c) (by omega)).comp
      E.subtype_injective
  let η := MonoidHom.ofInjective hj
  refine ⟨j.range, hEp.of_equiv η, fun hc => hEc (η.isCyclic.2 hc), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact fieldAutT_fixes_J k _ σ
    (coordinateQuadMinus_fieldAut k n (by omega) (fun _ => Iff.rfl) b c)
    (coordinateQuadMinus_isExtension k n (by omega) b c) (fun _ => Iff.rfl) ⟨(x : _), rfl⟩

theorem uc22s2114r4f_fieldSubgroups_of_pomegaMinus {Y : Type} [Group Y] [Finite Y]
    {n f r : ℕ} (hn : 5 ≤ n) (hY : LieModel Y .POmegaMinus n 2 f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, hK, σ, hσ, b, c, -, hirr, e, he⟩ :=
    uc22s2114r4f_orthogonalMinus_field_descent hn hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm (fieldAutT _ σ
      (coordinateQuadMinus_fieldAut _ n (by omega) (fun _ => Iff.rfl) b c) x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_orthogonalMinus hn σ b c
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_orthogonalMinus hn hY.admissible.2.1 hK hr hr5 σ hσ b c hirr
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

section Multiplier


theorem uc22s2114r4f_card_center_pomegaMinus {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 5 ≤ n) (hf : 2 ≤ f)
    (hX : LieModel (BarInf L) .POmegaMinus n 2 f) : Nat.card (center (Bar2 L)) ∣ 4 := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨-, ⟨ε⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pomegaMinus_hopfMultiplier
    (by omega : 4 ≤ n) hirr hK hK4
  have hMK : Nat.card (griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) =
      Nat.gcd 4 ((2 ^ f) ^ n + 1) := by
    rw [Nat.card_congr ε.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hM : Nat.card (griessHopfMultiplier (BarInf L)) = Nat.gcd 4 ((2 ^ f) ^ n + 1) := by
    rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv, hMK]
  have : Finite (griessHopfMultiplier (BarInf L)) := Nat.finite_of_card_ne_zero (by
    rw [hM]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 4)).ne')
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  rw [hM] at hd
  exact hd.trans (Nat.gcd_dvd_left 4 _)

theorem uc22s2114r4f_not_dvd_radical_pomegaMinus {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 5 ≤ n) (hf : 2 ≤ f)
    (hX : LieModel (BarInf L) .POmegaMinus n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL]
  intro hd
  rcases hq.dvd_mul.1 hd with h2 | hZ
  · obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
    rw [ha] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
  · have h4 := hZ.trans (uc22s2114r4f_card_center_pomegaMinus hL hn hf hX)
    have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (by simpa using h4 : q ∣ 2 ^ 2)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2)

theorem uc22s2114r4f_four_le_pRank_three_pomegaMinus {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 5 ≤ n) (hf : 2 ≤ f)
    (hX : LieModel (BarInf L) .POmegaMinus n 2 f) : 4 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := fun h => by
    have h4 := h.trans (uc22s2114r4f_card_center_pomegaMinus hL hn hf hX)
    norm_num at h4
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, b, c, -, ⟨e⟩⟩ :=
    (LieModel.of_mulEquiv eb hX).statedClassicalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.omegaMinus_four_le_pRank_three hn b c

theorem uc22s2114r4f_fieldDataBody_pomegaMinus {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n f : ℕ} (hn : 5 ≤ n) (hX : LieModel (BarInf L) .POmegaMinus n 2 f)
    {b : G} (hbL : b ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_pomegaMinus hn hX hr hr5
      (inducedBarInfAutHom L ⟨b, hbL⟩) (orderOf_eq_prime hθr hθ1) hin
  have hf : 2 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_pomegaMinus hL hn hf hX hr (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_pomegaMinus hL hn hf hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_pomegaMinus hL hn hf hX hq (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end Multiplier

end CFSG.LocalAnalysis.UniquenessCase.UC22
