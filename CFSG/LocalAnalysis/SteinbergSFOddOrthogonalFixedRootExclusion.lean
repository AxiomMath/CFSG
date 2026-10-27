module

public import CFSG.LocalAnalysis.SteinbergSFOddSymplecticRootCentralizer
public import CFSG.LocalAnalysis.SteinbergSFOddOrthogonalScalarQuotientSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalDescent
  CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace OddOrthogonalRoot

section Pullback

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem exists_component_pullback {Q : QuadraticForm F V} {C : Subgroup (V ≃ₗ[F] V)}
    {H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hH : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, g ∈ H ↔ (g : V ≃ₗ[F] V) ∈ C)
    {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ C)) :
    ∃ (Y₁ : Subgroup H) (ι : Y₁ ≃* Y), CFSG.IsComponent Y₁ ∧
      ∀ y : Y₁, ((ι y : Y) : V ≃ₗ[F] V) = ((y : H) : TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hY.1.trans inf_le_left
  have h := OddClassSelector.isComponentOf_comap_of_le_range
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective hY
    (by rw [Subgroup.range_subtype]; exact inf_le_left)
  have hC : (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ C).comap
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = H := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_inf, hH]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  rw [hC] at h
  exact ⟨_, (Subgroup.subgroupOfEquivOfLe h.1).trans (Subgroup.subgroupOfEquivOfLe hYO),
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).mp h,
    fun _ => rfl⟩

end Pullback

theorem orth_component_quotient {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {q : QuadraticForm k W}
    (hq : q.polarBilin.Nondegenerate) {H : Type*} [Group H]
    (Φ : H ≃* TauCeti.QuadraticMap.orthogonalGroup q) {Y : Subgroup H} (hY : CFSG.IsComponent Y)
    (A : Subgroup Y) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ∀ w,
      ((Φ a : TauCeti.QuadraticMap.orthogonalGroup q) : W ≃ₗ[k] W) w = c • w)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Nat.card k = 5 ∧ (finrank k W = 3 ∨ finrank k W = 4 ∧ Nat.card A = 2) := by
  set ι : Y ≃* Y.map Φ.toMonoidHom := Y.equivMapOfInjective Φ.toMonoidHom Φ.injective
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hB := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent Φ hY
  have hscal : ∀ a ∈ A.map ι.toMonoidHom, ∃ c : k, ∀ w,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : W ≃ₗ[k] W) w = c • w := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA a ha
  obtain ⟨-, h5, hcases⟩ := odd_orthogonal_component_scalar_quotients_even_SL2_small_exceptions
    hk q hq hB (A.map ι.toMonoidHom) hscal hn K hK ⟨eQ'⟩
  refine ⟨h5, ?_⟩
  rcases hcases with ⟨h3, -⟩ | ⟨h4, -, -, hcA, -⟩
  · exact Or.inl h3
  · refine Or.inr ⟨h4, ?_⟩
    rw [← hcA, card_map_of_injective ι.injective]

theorem exists_nondegenerate_sub {k : Type*} [Field k] {W : Type*} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0) (Q : QuadraticForm k W)
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : m ≤ finrank k W) :
    ∃ U U' : Submodule k W, IsCompl U U' ∧ (∀ u ∈ U, ∀ w ∈ U', polar Q u w = 0) ∧
      finrank k U = m ∧ (Q.comp U.subtype).polarBilin.Nondegenerate := by
  classical
  let : Invertible (2 : k) := invertibleOfNonzero h2
  have hsymm : Q.polarBilin.IsSymm := ⟨fun x y => polar_comm Q x y⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set f : Fin m → Fin (finrank k W) := Fin.castLE hdim
  set s : Set (Fin (finrank k W)) := Set.range f with hs
  set U := Submodule.span k (v '' s) with hU
  set U' := Submodule.span k (v '' sᶜ) with hU'
  have hUW : IsCompl U U' := v.linearIndependent.isCompl_span_image v.span_eq isCompl_compl
  have hortho : ∀ i j, i ≠ j → polar Q (v i) (v j) = 0 := fun i j hij => hv hij
  have horth : ∀ u ∈ U, ∀ w ∈ U', polar Q u w = 0 := by
    intro u hu w hw
    have h1 : ∀ i ∈ s, polar Q (v i) w = 0 := by
      intro i hi
      have hle : U' ≤ LinearMap.ker (Q.polarBilin (v i)) := by
        rw [hU', Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        exact hortho i j fun h => hj (h ▸ hi)
      exact LinearMap.mem_ker.mp (hle hw)
    have hle : U ≤ LinearMap.ker (Q.polarBilin.flip w) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact h1 i hi
    exact LinearMap.mem_ker.mp (hle hu)
  have hfin : finrank k U = m := by
    rw [hU, hs, ← Set.range_comp,
      finrank_span_eq_card (v.linearIndependent.comp f (Fin.castLE_injective hdim)),
      Fintype.card_fin]
  refine ⟨U, U', hUW, horth, hfin, ?_⟩
  have hrefl : (Q.comp U.subtype).polarBilin.IsRefl := fun x y hxy => by
    change polar (Q.comp U.subtype) y x = 0
    rw [polar_comm]
    exact hxy
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr fun x hx => ?_
  apply Subtype.ext
  apply hQ.1
  intro z
  obtain ⟨u, w, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hUW z
  have hxu : polar Q x u = 0 := hx u
  change polar Q x (u + w) = 0
  rw [polar_add_right, hxu, horth x x.2 w w.2, add_zero]

theorem semilinear_case_false {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 5 ≤ finrank F V) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) (σ : F ≃+* F) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (τ₀ : V ≃+ V) (μ lam : Fˣ) (hsemi : ∀ (a : F) x, τ₀ (a • x) = σ a • τ₀ x)
    (hform : ∀ x y, Q.polarBilin (τ₀ x) (τ₀ y) = (μ : F) * σ (Q.polarBilin x y))
    (hsquare : ∀ x, τ₀ (τ₀ x) = (lam : F) • x) {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ commutant τ₀))
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : CharP F ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F ℓ]; exact hℓ2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨-, -, -, ⟨b, c', hb, hc'⟩, hall⟩ := odd_orthogonal_quadratic_semilinear_descent σ hσ2
    hσ1 h2 (by omega) Q.polarBilin
    (LocalAnalysis.ComponentInitial.OddOrthogonal.isSymm_polarBilin Q) hQ τ₀ μ lam hsemi hform
    hsquare
  obtain ⟨-, -, -, -, hfin, hrank, -, hB0nd, -, -, hQ0pol, -, -, eD, -, -, heD, -⟩ :=
    hall b c' hb hc'
  obtain ⟨hcard0, -⟩ := CatalogueBOrthogonalInvolutionRepresentation.field_involution_facts hℓ he
    hF hσ2 hσ1
  have hk₀ : Nat.card (fixedSubfield F σ) = Nat.card {c : F // σ c = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight (mem_fixedSubfield F σ))
  have hodd₀ : Odd (Nat.card (fixedSubfield F σ)) := by
    have hFodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
    rw [hcard0, ← hk₀] at hFodd
    exact (Nat.odd_pow_iff two_ne_zero).mp hFodd
  have := hfin
  have hQ0nd : (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform
      hc').polarBilin.Nondegenerate := by
    rw [hQ0pol]
    exact hB0nd
  have hQQ : originalQuadratic Q.polarBilin = Q := by
    ext x
    rw [originalQuadratic_apply, QuadraticMap.polarBilin_apply_apply, polar_self, two_smul]
    field_simp
    ring
  have hY' : CFSG.Assembly.IsComponentOf Y
      (TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin) ⊓ commutant τ₀) := by
    rw [hQQ]
    exact hY
  obtain ⟨Y₁, ι, hY₁, hι⟩ := exists_component_pullback (H := semilinearOrthogonalCentralizer
    (originalQuadratic Q.polarBilin) τ₀) (fun g => by
      rw [mem_semilinearOrthogonalCentralizer_iff, mem_commutant]) hY'
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map ι.symm A eQ
  have hA₁ : ∀ a ∈ A.map ι.symm.toMonoidHom, ∃ c : fixedSubfield F σ, ∀ w,
      ((eD a : TauCeti.QuadraticMap.orthogonalGroup _) :
        originalFixedSubspace σ τ₀ b hsemi ≃ₗ[fixedSubfield F σ]
          originalFixedSubspace σ τ₀ b hsemi) w = c • w := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc⟩ := hA a ha
    have hval : ∀ w : originalFixedSubspace σ τ₀ b hsemi,
        (((eD (ι.symm.toMonoidHom a) : TauCeti.QuadraticMap.orthogonalGroup _) :
          originalFixedSubspace σ τ₀ b hsemi ≃ₗ[fixedSubfield F σ]
            originalFixedSubspace σ τ₀ b hsemi) w : V) = c • (w : V) := fun w => by
      rw [heD, ← hι, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hc]
    have hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hY.1.trans inf_le_left
    rcases OddOrthogonalQuotient.eq_one_or_eq_neg_one_of_smul Q hQ
        (g := ⟨(a : V ≃ₗ[F] V), hYO (a : Y).2⟩) hc with h1 | h1
    · exact ⟨1, fun w => Subtype.ext (by rw [hval, h1, one_smul, one_smul])⟩
    · exact ⟨-1, fun w => Subtype.ext (by
        rw [hval, h1, neg_one_smul, neg_one_smul, Submodule.coe_neg])⟩
  obtain ⟨-, hdim⟩ := orth_component_quotient hodd₀ hQ0nd eD hY₁ _ hA₁ hn hK eQ₁
  rw [hrank] at hdim
  omega

section Linear

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [Finite F] [FiniteDimensional F V] in
theorem commute_of_isCompl {M N : Submodule F V} (hMN : IsCompl M N) {z : V ≃ₗ[F] V}
    (hzM : ∀ m ∈ M, z m = m) (hzN : ∀ x ∈ N, z x ∈ N) :
    (∀ y : V ≃ₗ[F] V, (∀ x ∈ N, y x = x) → (∀ m ∈ M, y m ∈ M) → y * z = z * y) ∧
      ∀ (T : V ≃ₗ[F] V) (lM lN : F), (∀ m ∈ M, T m = lM • m) → (∀ x ∈ N, T x = lN • x) →
        ∀ v, z (T v) = T (z v) := by
  refine ⟨fun y hyN hyM => LinearEquiv.ext fun v => ?_, fun T lM lN hTM hTN v => ?_⟩
  · obtain ⟨m, x, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMN v
    change y (z (m + x)) = z (y (m + x))
    rw [map_add, map_add, map_add, map_add, hzM m m.2, hzM _ (hyM m m.2), hyN x x.2,
      hyN _ (hzN x x.2)]
  · obtain ⟨m, x, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMN v
    rw [map_add, map_add, map_add, map_add, hTM m m.2, hTN x x.2, map_smul, map_smul,
      hzM m m.2, hTM m m.2, hTN _ (hzN x x.2)]

theorem paired_case_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 7 ≤ finrank F V) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) (T : V ≃ₗ[F] V) (d μ : Fˣ)
    (hsquare : ∀ x, T (T x) = (d : F) • x)
    (hsim : ∀ x y, Q.polarBilin (T x) (T y) = (μ : F) * Q.polarBilin x y)
    (hnonscalar : ∀ c : F, T.toLinearMap ≠ c • (1 : Module.End F V)) (b : Fˣ)
    (hb : (d : F) = (b : F) ^ 2) (hμ : (μ : F) / (d : F) = -1)
    {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer T.toLinearMap))
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hF (by omega) Q hQ T d μ hsquare hsim hnonscalar
  obtain ⟨hc, -, -, -, hneg⟩ := hsq b hb
  obtain ⟨-, -, -, hdimeq, -, -, E, -, -, hE, -, -⟩ := hneg hμ
  obtain ⟨m, hm⟩ : ∃ m, finrank F (positiveSquareKernel T b) = m := ⟨_, rfl⟩
  have hdimV : m + m = finrank F V := by
    rw [← Submodule.finrank_add_eq_of_isCompl hc, ← hdimeq, hm]
  obtain ⟨bP⟩ : Nonempty (Basis (Fin m) F (positiveSquareKernel T b)) :=
    ⟨Module.finBasisOfFinrankEq F _ hm⟩
  set Φ : orthogonalOperatorCentralizer Q T.toLinearMap ≃* GL (Fin m) F :=
    E.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv F _).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
  obtain ⟨Y₁, ι, hY₁, hι⟩ := exists_component_pullback
    (H := orthogonalOperatorCentralizer Q T.toLinearMap) (fun _ => Iff.rfl) hY
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map ι.symm A eQ
  have hA₁ : ∀ a ∈ A.map ι.symm.toMonoidHom, ∃ c : F,
      ((Φ a : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = c • 1 := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hcv⟩ := hA a ha
    have hlin : ((E (ι.symm.toMonoidHom a) : positiveSquareKernel T b ≃ₗ[F]
        positiveSquareKernel T b) : positiveSquareKernel T b →ₗ[F] positiveSquareKernel T b) =
          c • LinearMap.id := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      rw [LinearEquiv.coe_coe, hE, ← hι, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hcv]
      rfl
    refine ⟨c, ?_⟩
    change LinearMap.toMatrixAlgEquiv bP ((E (ι.symm.toMonoidHom a) : positiveSquareKernel T b ≃ₗ[F]
        positiveSquareKernel T b) : positiveSquareKernel T b →ₗ[F] positiveSquareKernel T b) = _
    rw [hlin, map_smul]
    congr 1
    exact map_one (LinearMap.toMatrixAlgEquiv bP)
  obtain ⟨hm2, -, -⟩ := gl_component_quotient hodd (by omega) Φ hY₁ _ hA₁ hn hK eQ₁
  omega

theorem ext_case_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 7 ≤ finrank F V) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) (T : V ≃ₗ[F] V) (d μ : Fˣ)
    (hsquare : ∀ x, T (T x) = (d : F) • x)
    (hsim : ∀ x y, Q.polarBilin (T x) (T y) = (μ : F) * Q.polarBilin x y)
    (hnonscalar : ∀ c : F, T.toLinearMap ≠ c • (1 : Module.End F V))
    (hnsq : ¬ IsSquare (d : F)) (hμ : (μ : F) / (d : F) = 1)
    {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer T.toLinearMap))
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  obtain ⟨-, -, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hF (by omega) Q hQ T d μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  let : Field (CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap) :=
    CatalogueBOrthogonalScalarSquareField.scalarField T.toLinearMap d hnsq
      (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square T d hsquare)
  let : Module (CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap) V :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule T.toLinearMap
  obtain ⟨⟨-, hfin, -, -, -, -, -, -, hcard, -, -, -, -, -, -, -, -, halg, -, hfinE, -, -⟩,
    hpos, -⟩ := h4
  obtain ⟨-, -, -, hQEnd, -, -, eO, heO, -, -, -⟩ := hpos hμ
  have := hfin
  have : FiniteDimensional (CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap) V :=
    hfinE
  have hoddE : Odd (Nat.card (CatalogueBOrthogonalScalarSquareField.scalarAlgebra
      T.toLinearMap)) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  obtain ⟨Y₁, ι, hY₁, hι⟩ := exists_component_pullback
    (H := orthogonalOperatorCentralizer Q T.toLinearMap) (fun _ => Iff.rfl) hY
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map ι.symm A eQ
  have hA₁ : ∀ a ∈ A.map ι.symm.toMonoidHom,
      ∃ c : CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap, ∀ v,
        ((eO a : TauCeti.QuadraticMap.orthogonalGroup _) :
          V ≃ₗ[CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap] V) v =
            c • v := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hcv⟩ := hA a ha
    refine ⟨algebraMap F _ c, fun v => ?_⟩
    rw [heO, ← hι, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hcv, halg]
  obtain ⟨h5, -⟩ := orth_component_quotient hoddE hQEnd eO hY₁ _ hA₁ hn hK eQ₁
  rw [hcard] at h5
  rcases (show ℓ ^ e ≤ 2 ∨ 3 ≤ ℓ ^ e by omega) with h | h <;> nlinarith

theorem unitary_case_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 7 ≤ finrank F V) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) (T : V ≃ₗ[F] V) (d μ : Fˣ)
    (hsquare : ∀ x, T (T x) = (d : F) • x)
    (hsim : ∀ x y, Q.polarBilin (T x) (T y) = (μ : F) * Q.polarBilin x y)
    (hnonscalar : ∀ c : F, T.toLinearMap ≠ c • (1 : Module.End F V))
    (hnsq : ¬ IsSquare (d : F)) (hμ : (μ : F) / (d : F) = -1)
    {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer T.toLinearMap))
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  obtain ⟨-, -, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hF (by omega) Q hQ T d μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  let : Field (CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap) :=
    CatalogueBOrthogonalScalarSquareField.scalarField T.toLinearMap d hnsq
      (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square T d hsquare)
  let : Module (CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap) V :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule T.toLinearMap
  obtain ⟨⟨-, hfin, -, -, -, -, -, -, hcard, -, -, -, -, -, hpow, -, -, halg, -, hfinE,
    hfinrank, -⟩, -, hneg⟩ := h4
  obtain ⟨hsym, hnd, -, -, -, -, eU, heU, -, -, -⟩ := hneg hμ
  have := hfin
  have : FiniteDimensional (CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap) V :=
    hfinE
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Y₁, ι, hY₁, hι⟩ := exists_component_pullback
    (H := orthogonalOperatorCentralizer Q T.toLinearMap) (fun _ => Iff.rfl) hY
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map ι.symm A eQ
  have hA₁ : ∀ a ∈ A.map ι.symm.toMonoidHom,
      ∃ c : CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap, ∀ v,
        ((eU a : CatalogueBUnitaryIsometry.isometryGroup _) :
          V ≃ₗ[CatalogueBOrthogonalScalarSquareField.scalarAlgebra T.toLinearMap] V) v =
            c • v := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hcv⟩ := hA a ha
    refine ⟨algebraMap F _ c, fun v => ?_⟩
    rw [heU, ← hι, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hcv, halg]
  obtain ⟨h2, -⟩ := unitary_component_quotient hℓ2 he hcard (fun z => hpow z) _ hsym hnd
    (by omega) eU hY₁ _ hA₁ hn hK eQ₁
  omega

end Linear

end OddOrthogonalRoot

end CFSG.LocalAnalysis.SymplecticFourStandard
