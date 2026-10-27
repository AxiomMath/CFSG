module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaMinusNatTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixAut
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix MatrixGroups

open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

private lemma hermFourSpace_map_mem {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E]
    [Algebra K E] (D : EvenNormPlane K E) (τ : E ≃+* E) {X : Matrix (Fin 2) (Fin 2) E}
    (hX : X ∈ hermFourSpace D.σ) : X.map τ ∈ hermFourSpace D.σ := by
  rw [mem_hermFourSpace] at hX ⊢
  intro i j
  rw [Matrix.map_apply, Matrix.map_apply, EvenNormPlane.sigma_comm_ringEquiv, hX i j]

private noncomputable def hermFourMap {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E]
    [Algebra K E] (D : EvenNormPlane K E) (τ : E ≃+* E) :
    ↥(hermFourSpace D.σ) → ↥(hermFourSpace D.σ) :=
  fun X => ⟨(X : Matrix (Fin 2) (Fin 2) E).map τ, hermFourSpace_map_mem D τ X.2⟩

private lemma coe_hermFourMap {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E]
    [Algebra K E] (D : EvenNormPlane K E) (τ : E ≃+* E) (X : ↥(hermFourSpace D.σ)) :
    ((hermFourMap D τ X : ↥(hermFourSpace D.σ)) : Matrix (Fin 2) (Fin 2) E) =
      (X : Matrix (Fin 2) (Fin 2) E).map τ := rfl

private lemma hermFourRho_map {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E]
    [Algebra K E] (D : EvenNormPlane K E) (τ : E ≃+* E) (g : SL(2, E))
    (X : ↥(hermFourSpace D.σ)) :
    hermFourMap D τ (hermFourRho D g X) =
      hermFourRho D (Matrix.SpecialLinearGroup.map τ.toRingHom g) (hermFourMap D τ X) := by
  apply Subtype.ext
  rw [coe_hermFourMap, coe_hermFourRho, coe_hermFourRho, coe_hermFourMap,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map]
  have hσ : (⇑D.σ ∘ ⇑τ) = (⇑τ ∘ ⇑D.σ) :=
    funext fun z => EvenNormPlane.sigma_comm_ringEquiv D τ z
  have hg : (τ.toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) E)).map ⇑D.σ =
      (g : Matrix (Fin 2) (Fin 2) E).map (⇑τ ∘ ⇑D.σ) := by
    rw [show τ.toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) E).map ⇑τ from rfl, Matrix.map_map, hσ]
  rw [hg, show τ.toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) E) =
    (g : Matrix (Fin 2) (Fin 2) E).map ⇑τ from rfl]

private theorem exists_natAct_intertwine_omegaFourMinus {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
    ∃ A : Multiplicative (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≃*
        Multiplicative (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      ∀ (γ : ↥(StatedOmega (StatedQuadMinus 2 K b c)))
        (x : Multiplicative (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)),
        A (natAct (StatedOmega (StatedQuadMinus 2 K b c)) γ x) =
          natAct (StatedOmega (StatedQuadMinus 2 K b c)) (α γ) (A x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hm1 : 1 ≤ 2 * (m : ℕ) := by
    have := m.pos
    omega
  have hKcard : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  let Q : QuadraticForm K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 2 K b c
  have hQ : ⇑Q = StatedQuadMinus 2 K b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c
  have hQnd : LinearMap.Nondegenerate (QuadraticMap.polarBilin Q) :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hdim : Module.finrank K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = 4 := by
    simpa using CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (m := 2) (by norm_num)
  have hts : ∀ U : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      Module.finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0 :=
    fun U hU => CFSG.RankThree.GF2n.Stroth80.exists_quadMinus_ne_zero_of_finrank
      (by norm_num) hirr U hU
  obtain ⟨E, hEfield, hEalg, D, ψ, ρ, hψQ, hψρ, hρinj, hρmem, hcomm, hsimple, hperf, hna,
    hcard, hidx, hnorm, hodd⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction Q hQnd hdim hts
  letI : Field E := hEfield
  letI : Algebra K E := hEalg
  haveI : Finite E := D.finite_E
  haveI : CharP E 2 := charP_two_of_algebra (K := K)
  let Ψ : ↥(StatedOmega (StatedQuadMinus 2 K b c)) ≃* SL(2, E) :=
    ((CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived hQ).trans
      (MulEquiv.subgroupCongr hcomm)).trans (MonoidHom.ofInjective hρinj).symm
  let Φ : SL(2, E) ≃* ↥(StatedOmega (StatedQuadMinus 2 K b c)) := Ψ.symm
  let α' : MulAut SL(2, E) := MulAut.congr Φ.symm α
  have hα' : ∀ g : SL(2, E), Φ (α' g) = α (Φ g) := fun g => by
    simp [α', MulAut.congr_apply, Φ]
  have hEcard : Nat.card E = 2 ^ (2 * (m : ℕ)) := by
    rw [D.card_E, hKcard, ← pow_mul, mul_comm]
  obtain ⟨⟨s, σ⟩, hs, -⟩ :=
    (even_SL2_full_automorphism_semilinear_model
      (F := E) (n := 2 * (m : ℕ)) hm1 hEcard).2.2.2.2 α'
  have hP1 : ∀ x : ↥(StatedOmega (StatedQuadMinus 2 K b c)),
      (((x : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) =
      LinearMap.toMatrix' ((ρ (Ψ x)).toLinearMap) := by
    intro x
    have hy : (((MulEquiv.subgroupCongr hcomm)
          (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived hQ x) :
          ↥ρ.range) : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
            (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K (x : GL _ K) := by
      rw [MulEquiv.subgroupCongr_apply]
      rw [CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived]
      rfl
    have hΨx : ρ (Ψ x) = ((MulEquiv.subgroupCongr hcomm)
        (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived hQ x) :
        ↥ρ.range) := by
      dsimp only [Ψ]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
      rw [← MonoidHom.ofInjective_apply hρinj, MulEquiv.apply_symm_apply]
    rw [hΨx, hy,
      show (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K (x : GL _ K)).toLinearMap =
        Matrix.toLin' (((x : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
            (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) from by
        apply LinearMap.ext
        intro v
        rw [LinearEquiv.coe_toLinearMap, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
          Matrix.toLin'_apply]]
    exact (LinearMap.toMatrix'_toLin' _).symm
  let mapσ : ↥(hermFourSpace D.σ) ≃+ ↥(hermFourSpace D.σ) :=
    { toFun := hermFourMap D σ
      invFun := hermFourMap D σ.symm
      left_inv := fun X => by
        apply Subtype.ext
        rw [coe_hermFourMap, coe_hermFourMap]
        ext i j
        simp
      right_inv := fun X => by
        apply Subtype.ext
        rw [coe_hermFourMap, coe_hermFourMap]
        ext i j
        simp
      map_add' := fun X Y => by
        apply Subtype.ext
        rw [coe_hermFourMap]
        ext i j
        simp [hermFourMap, Matrix.map_add] }
  let Aadd : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≃+
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    (ψ.toAddEquiv.trans (mapσ.trans (hermFourRho D s).toAddEquiv)).trans
      ψ.toAddEquiv.symm
  have hAadd : ∀ v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      Aadd v = ψ.symm (hermFourRho D s (mapσ (ψ v))) := fun v => rfl
  have hψsymm : ∀ (g : SL(2, E)) (Y : ↥(hermFourSpace D.σ)),
      ψ.symm (hermFourRho D g Y) = ρ g (ψ.symm Y) := by
    intro g Y
    conv_lhs => rw [← LinearEquiv.apply_symm_apply ψ Y]
    rw [← hψρ g (ψ.symm Y), LinearEquiv.symm_apply_apply]
  have hΨα : ∀ γ : ↥(StatedOmega (StatedQuadMinus 2 K b c)), Ψ (α γ) = α' (Ψ γ) := by
    intro γ
    have h := hα' (Ψ γ)
    dsimp only [Φ] at h
    rw [MulEquiv.symm_apply_apply] at h
    have h2 := congrArg Ψ h
    rw [show Ψ (Φ (α' (Ψ γ))) = α' (Ψ γ) from Ψ.apply_symm_apply _] at h2
    exact h2.symm
  refine ⟨Aadd.toMultiplicative, fun γ x => ?_⟩
  set v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K := Multiplicative.toAdd x with hv
  apply Multiplicative.toAdd.injective
  show Aadd (((γ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ v) =
    (((α γ : ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
      GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ Aadd v
  have hγ : ((γ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ v = ρ (Ψ γ) v := by
    rw [hP1 γ]
    exact LinearMap.toMatrix'_mulVec (ρ (Ψ γ)).toLinearMap v
  have hαγ : (((α γ : ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
      GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ (Aadd v) = ρ (Ψ (α γ)) (Aadd v) := by
    rw [hP1 (α γ)]
    exact LinearMap.toMatrix'_mulVec (ρ (Ψ (α γ))).toLinearMap (Aadd v)
  rw [hγ, hαγ, hAadd, hAadd]
  have hstep : hermFourRho D s (hermFourMap D σ (hermFourRho D (Ψ γ) (ψ v))) =
      hermFourRho D (s * Matrix.SpecialLinearGroup.map σ.toRingHom (Ψ γ))
        (hermFourMap D σ (ψ v)) := by
    rw [hermFourRho_map D σ (Ψ γ) (ψ v), map_mul]
    rfl
  dsimp only [mapσ]
  change ψ.symm (hermFourRho D s (hermFourMap D σ (ψ (ρ (Ψ γ) v)))) =
    ρ (Ψ (α γ)) (ψ.symm (hermFourRho D s (hermFourMap D σ (ψ v))))
  rw [hψρ (Ψ γ) v, hstep]
  rw [← hψsymm (Ψ (α γ)) (hermFourRho D s (hermFourMap D σ (ψ v)))]
  have hmul : hermFourRho D (Ψ (α γ) * s) (hermFourMap D σ (ψ v)) =
      hermFourRho D (Ψ (α γ)) (hermFourRho D s (hermFourMap D σ (ψ v))) := by
    rw [map_mul]
    rfl
  rw [← hmul, hΨα γ, hs (Ψ γ)]
  have hgroup : (s * Matrix.SpecialLinearGroup.map σ.toRingHom (Ψ γ) * s⁻¹) * s =
      s * Matrix.SpecialLinearGroup.map σ.toRingHom (Ψ γ) := by group
  rw [hgroup]

theorem k146NatIsoOm4m_holds : K146NatIsoOm4m := by
  intro W _ _ _ L n I J _ _ _ hI hJ
  obtain ⟨-, K₁, hf₁, hfin₁, b₁, c₁, hK₁, hirr₁, hreal₁⟩ := hI
  obtain ⟨-, K₂, hf₂, hfin₂, b₂, c₂, hK₂, hirr₂, hreal₂⟩ := hJ
  obtain ⟨π₁, hπ₁⟩ := hreal₁
  obtain ⟨π₂, hπ₂⟩ := hreal₂
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  have hchar₁ : CharP K₁ 2 :=
    charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card]; exact hK₁)
  have hchar₂ : CharP K₂ 2 :=
    charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card]; exact hK₂)
  have hinj₁ : Function.Injective π₁ := hπ₁.injective_of_faithful_on (FFModel.nat_faithful _)
  have hinj₂ : Function.Injective π₂ := hπ₂.injective_of_faithful_on (FFModel.nat_faithful _)
  let e₁ := MulEquiv.ofBijective π₁ ⟨hinj₁, hπ₁.1⟩
  let e₂ := MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂.1⟩
  let φ := e₁.trans e₂.symm
  obtain ⟨χ, B, hB⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_statedOmegaMinus_natTransport
      (hK₁.trans hK₂.symm) 2 hirr₁ hirr₂
  obtain ⟨A₁, hA₁⟩ :=
    exists_natAct_intertwine_omegaFourMinus hirr₁ (φ.trans χ.symm)
  have hIso : CFSG.Quasithin.H.Pair.IsoMod L I J :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isoMod_of_realizesVia_nat_intertwine
      hπ₁ hπ₂ φ.toMonoidHom φ.surjective
      (MonoidHom.ext fun γ => e₂.apply_symm_apply (e₁ γ)) (A₁.trans B) (by
        intro γ x
        rw [MulEquiv.trans_apply, hA₁, hB]
        exact congrArg (fun g => natAct _ g (B (A₁ x))) (χ.apply_symm_apply (φ γ)))
  have hstableI : StableUnder L I := fun x hx u hu => hπ₁.2.2.2.1 ⟨x, hx⟩ u hu
  have hstableJ : StableUnder L J := fun x hx u hu => hπ₂.2.2.2.1 ⟨x, hx⟩ u hu
  obtain ⟨e, he⟩ := hIso
  exact CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_SecIsoOn_of_mulEquiv
    hstableI hstableJ e (fun g hg x => he g hg x (hstableI g hg (x : W) x.2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
