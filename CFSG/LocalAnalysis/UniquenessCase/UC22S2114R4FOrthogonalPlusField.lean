module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLinearField
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.LieType.SpecialLinear.Block222.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Rank
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
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
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem glFieldAut_orthogonalLeviGL {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K)
    (A : GL (Fin n) K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin n ⊕ Fin n) K σ
      (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.leviGL A) =
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.leviGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin n) K σ A) := by
  apply Units.ext
  have hA : ((A : Matrix (Fin n) (Fin n) K)⁻¹).map σ =
      (((CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin n) K σ A) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)⁻¹ := by
    have h := congrArg
      (fun B : GL (Fin n) K => (B : Matrix (Fin n) (Fin n) K))
      (map_inv (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin n) K σ).toMonoidHom A)
    change ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      (((CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin n) K σ A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) at h
    simpa only [Matrix.coe_units_inv] using h
  change (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.blockDiagInv
      (A : Matrix (Fin n) (Fin n) K)).map σ =
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.blockDiagInv
      (((CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin n) K σ A) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.blockDiagInv,
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.blockDiagInv,
    fromBlocks_map, transpose_map, hA]
  simp
  rfl

@[expose] noncomputable def orthogonalPlusLeviHom {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) : SpecialLinearGroup (Fin n) K →* matrixDerived (coordinateQuadPlus n K) :=
  (statedMatrixDerivedEquiv (plusIndexEquiv n) (quadPlus n K)).toMonoidHom.comp
    (((CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.leviGL).comp
      SpecialLinearGroup.toGL).codRestrict (StatedOmega ⇑(quadPlus n K)) (by
        intro A
        rw [statedOmega_eq_comap rfl,
          CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.commutator_orthogonalGroup_quadPlus hn]
        exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.levi_toGL_mem_orthElementaryGroup hn A))

theorem orthogonalPlusLeviHom_val {K : Type} [Field K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n)
    (A : SpecialLinearGroup (Fin n) K) :
    (orthogonalPlusLeviHom hn A).val = reindexMatrixEquiv (plusIndexEquiv n)
      (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.leviGL (SpecialLinearGroup.toGL A)) := rfl

theorem orthogonalPlusLeviHom_injective {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) : Function.Injective (orthogonalPlusLeviHom (K := K) hn) := by
  intro A B h
  have hr := (reindexMatrixEquiv (plusIndexEquiv n)).injective
    (congrArg Subtype.val h)
  have hl := congrArg (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.matrixEquiv n K) hr
  exact SpecialLinearGroup.toGL_injective
    (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.levi_injective hl)

theorem fieldPair_orthogonalPlusLeviHom {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (σ : K ≃+* K) (A : SpecialLinearGroup (Fin n) K) :
    matrixDerivedConjugation (coordinateQuadPlus n K)
      (fieldPair (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ))
      (orthogonalPlusLeviHom hn A) =
    orthogonalPlusLeviHom hn (SpecialLinearGroup.map σ.toRingHom A) := by
  apply Subtype.ext
  rw [matrixDerivedConjugation_fieldPair_val, orthogonalPlusLeviHom_val,
    orthogonalPlusLeviHom_val]
  rw [CFSG.StandardType.RecipeFieldOmega.glFieldAut_reindex, glFieldAut_orthogonalLeviGL]
  congr 2
  apply Units.ext
  ext i j
  rfl

@[expose] noncomputable def slBlockPairHom {K : Type} [Field K] (c : ℕ) :
    (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) →*
      SpecialLinearGroup (Fin (c + 4)) K :=
  (CFSG.LieType.SpecialLinear.blockEmbed222 c K).comp
    ((MonoidHom.fst _ _).prod ((1 :
      (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) →*
        SpecialLinearGroup (Fin c) K).prod (MonoidHom.snd _ _)))

theorem slBlockPairHom_injective {K : Type} [Field K] (c : ℕ) :
    Function.Injective (slBlockPairHom (K := K) c) := by
  intro A B h
  have hb := CFSG.LieType.SpecialLinear.blockEmbed222_injective c K h
  apply Prod.ext
  · simpa [MonoidHom.fst, MonoidHom.snd, MonoidHom.prod] using congrArg Prod.fst hb
  · simpa [MonoidHom.fst, MonoidHom.snd, MonoidHom.prod] using congrArg (fun x => x.2.2) hb

theorem map_slBlockPairHom {K : Type} [Field K] (c : ℕ) (σ : K ≃+* K)
    (A : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :
    SpecialLinearGroup.map σ.toRingHom (slBlockPairHom c A) =
      slBlockPairHom c (SpecialLinearGroup.map σ.toRingHom A.1,
        SpecialLinearGroup.map σ.toRingHom A.2) := by
  apply Subtype.ext
  ext i j
  obtain ⟨i, rfl⟩ := (CFSG.LieType.SpecialLinear.e222 c).surjective i
  obtain ⟨j, rfl⟩ := (CFSG.LieType.SpecialLinear.e222 c).surjective j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [slBlockPairHom, MonoidHom.fst, MonoidHom.snd, MonoidHom.prod,
      SpecialLinearGroup.map_apply_coe, CFSG.LieType.SpecialLinear.coe_blockEmbed222,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, CFSG.LieType.SpecialLinear.triDiagMat,
      Matrix.one_apply]

theorem uc22s2114r4f_exists_fpf_orthogonalPlus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n f r : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (σ : K ≃+* K) (hσ : orderOf σ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* matrixProjectiveDerived (coordinateQuadPlus n K),
            Function.Injective ι ∧ ∀ a,
              fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) (ι a) =
                ι (κ a) := by
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, n = c + 4 := ⟨n - 4, by omega⟩
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
  let J : A →* SpecialLinearGroup (Fin (c + 4)) K :=
    (slBlockPairHom c).comp (j.prodMap j)
  have hJ : Function.Injective J := (slBlockPairHom_injective c).comp (by
    intro a b hab
    exact Prod.ext (hj (congrArg Prod.fst hab)) (hj (congrArg Prod.snd hab)))
  have hQnz : ∃ v, coordinateQuadPlus (c + 4) K v ≠ 0 :=
    CFSG.RankThree.PartOne.AUTSL.exists_ne_zero_of_polar_nondegenerate (by omega) _
      (regular_coordinateQuadPlus _ K (by omega)).1
  have hproj : Function.Injective (matrixProjectiveProjection (coordinateQuadPlus (c + 4) K)) :=
    (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv _ hQnz).injective
  let ι : A →* matrixProjectiveDerived (coordinateQuadPlus (c + 4) K) :=
    (matrixProjectiveProjection _).comp ((orthogonalPlusLeviHom (by omega)).comp J)
  have hι : Function.Injective ι := hproj.comp ((orthogonalPlusLeviHom_injective (by omega)).comp hJ)
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change fieldAutT _ σ (coordinateQuadPlus_fieldAut _ σ)
      (matrixProjectiveProjection _ (orthogonalPlusLeviHom (by omega) (J a))) =
    matrixProjectiveProjection _ (orthogonalPlusLeviHom (by omega) (J (κ a)))
  rw [fieldAutT_mk, fieldPair_orthogonalPlusLeviHom]
  apply congrArg (fun x => matrixProjectiveProjection _ (orthogonalPlusLeviHom (by omega) x))
  change SpecialLinearGroup.map σ.toRingHom (slBlockPairHom c (j a.1, j a.2)) =
    slBlockPairHom c (j (τ a.1), j (τ a.2))
  rw [map_slBlockPairHom, hσj, hσj]

theorem uc22s2114r4f_orthogonalPlus_field_descent {Y : Type} [Group Y] [Finite Y]
    {n f r : ℕ} (hn : 4 ≤ n) (hY : LieModel Y .POmegaPlus n 2 f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
        ∃ ε : Y ≃* matrixProjectiveDerived (coordinateQuadPlus n K),
          ∀ x, ε (θ x) =
            fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) (ε x) := by
  classical
  have hcl := hY.statedClassicalModel (by decide)
  have hcl' := hcl
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates Y .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hcl' K hK e
  let θY := coordinatePlusWitnessEquiv K e
  let Q := coordinateQuadPlus n K
  let β := MulAut.congr θY θ
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hβr : β ^ r = 1 := by rw [← map_pow, hθr, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hout ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θY θ).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout
    (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = r := orderOf_eq_prime hβr hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hA : zpowers β ≤ familyOrbitKernel Q :=
        hgates.2.2.2.2.2.2.1 r hr (by omega) _ (IsPGroup.of_card (n := 1)
          (by rw [Nat.card_zpowers, hβord, pow_one]))
      have h1 := hgates.2.2.2.2.1 (hA (mem_zpowers β))
      rw [hgates.2.2.2.2.2.1] at h1
      exact h1
    · rw [matrixProjectiveImage_eq_top_plus K n h5]
      exact mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
      hk hr hr2 hD hβr)
  obtain ⟨hrf, hrest⟩ := orthogonal_prime_semilinear_actual_fixed_form_descent
    Y .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f r hcl' hr (by omega) hr2 K hK e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hord, -, U, cc, Q₀, hUκ, hUr, -, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hσ : orderOf U.val.right = r := hUr ▸ hord
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hr hr2 hσ (n := n) (by omega)
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, hK, U.val.right, hσ,
    θY.trans Θ, ?_⟩
  intro x
  change Θ (θY (θ x)) = fieldAutT Q U.val.right (coordinateQuadPlus_fieldAut n U.val.right)
    (Θ (θY x))
  have hx : Θ (β (θY x)) = matrixProjectiveConjugationHom Q g' (Θ (θY x)) := by
    rw [← hUκ]
    exact hΘ _
  rw [CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.matrixProjectiveConjugationHom_eq_fieldAutT
    hsetup g' hg'l hg'r] at hx
  have hβapply : β (θY x) = θY (θ x) := by
    change θY (θ (θY.symm (θY x))) = θY (θ x)
    rw [MulEquiv.symm_apply_apply]
  rw [hβapply] at hx
  exact hx

theorem uc22s2114r4f_exists_fixed_three_orthogonalPlus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn : 4 ≤ n) (σ : K ≃+* K) :
    ∃ X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)),
      IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X,
        fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) x = x := by
  let k := semilinearFixedSubfield σ
  let e := coordinatePlusWitnessEquiv k (MulEquiv.refl
    (StatedProj (StatedOmega (StatedQuadPlus n k))))
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n k))) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.omegaPlus_four_le_pRank_three hn
  obtain ⟨E, -, hEp, hEc⟩ :=
    PartTwo.Inputs1719.FourteenEight.exists_noncyclic_le_of_two_le_pRank Nat.prime_three
      (by omega : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
        (matrixProjectiveDerived (coordinateQuadPlus n k))))
  let j : E →* matrixProjectiveDerived (coordinateQuadPlus n K) :=
    (incl k (coordinateQuadPlus_isExtension k n)).comp E.subtype
  have hj : Function.Injective j :=
    (incl_injective k (coordinateQuadPlus_isExtension k n) (by omega)).comp E.subtype_injective
  let η := MonoidHom.ofInjective hj
  refine ⟨j.range, hEp.of_equiv η, fun hc => hEc (η.isCyclic.2 hc), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact fieldAutT_fixes_J k (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ)
    (coordinateQuadPlus_isExtension k n) (fun _ => Iff.rfl) ⟨(x : _), rfl⟩

theorem uc22s2114r4f_fieldSubgroups_of_pomegaPlus {Y : Type} [Group Y] [Finite Y]
    {n f r : ℕ} (hn : 4 ≤ n) (hY : LieModel Y .POmegaPlus n 2 f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, hK, σ, hσ, e, he⟩ :=
    uc22s2114r4f_orthogonalPlus_field_descent hn hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm
      (fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_orthogonalPlus hn σ
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_orthogonalPlus hn hY.admissible.2.1 hK hr hr5 σ hσ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

theorem uc22s2114r4f_card_center_pomegaPlus {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hX : LieModel (BarInf L) .POmegaPlus n 2 f) : Nat.card (center (Bar2 L)) = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨-, ⟨ε⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
    (by omega : 3 ≤ n) hK hK4
  have hEven : Even (2 ^ f) := even_iff_two_dvd.2 (dvd_pow_self 2 (by omega : f ≠ 0))
  have hMK : Nat.card (griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadPlus n K)))) = 1 := by
    rw [Nat.card_congr ε.toEquiv]
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.genericOrders, hEven]
  have hM : Nat.card (griessHopfMultiplier (BarInf L)) = 1 := by
    rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv, hMK]
  have : Finite (griessHopfMultiplier (BarInf L)) := Nat.finite_of_card_ne_zero (by simp [hM])
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  rw [hM] at hd
  exact Nat.dvd_one.1 hd

theorem uc22s2114r4f_not_dvd_radical_pomegaPlus {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hX : LieModel (BarInf L) .POmegaPlus n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL, uc22s2114r4f_card_center_pomegaPlus hL hn hf hX,
    mul_one]
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
  rw [ha]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem uc22s2114r4f_four_le_pRank_three_pomegaPlus {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hX : LieModel (BarInf L) .POmegaPlus n 2 f) : 4 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [uc22s2114r4f_card_center_pomegaPlus hL hn hf hX]
    norm_num
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    (LieModel.of_mulEquiv eb hX).statedClassicalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.omegaPlus_four_le_pRank_three hn

theorem uc22s2114r4f_fieldDataBody_pomegaPlus {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n f : ℕ} (hn : 4 ≤ n) (hX : LieModel (BarInf L) .POmegaPlus n 2 f)
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
    uc22s2114r4f_fieldSubgroups_of_pomegaPlus hn hX hr hr5
      (inducedBarInfAutHom L ⟨b, hbL⟩) (orderOf_eq_prime hθr hθ1) hin
  have hf : 2 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_pomegaPlus hL hn hf hX hr (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_pomegaPlus hL hn hf hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_pomegaPlus hL hn hf hX hq (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
