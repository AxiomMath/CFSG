module

public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE (adjEmb adjEmb_apply)

abbrev diagQ (L : Type) [Field L] : ModGL Tag.E6 L := diagramMap TwistTag.E6 L

theorem exists_frobenius_pow_eq' {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (τ : K ≃+* K) : ∃ j < f, ∀ x, τ x = x ^ ℓ ^ j := by
  obtain ⟨σ, hσ, hord, hz, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hfin : IsOfFinOrder σ := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2
    (by rw [hz]; exact Subgroup.mem_top τ))
  have hτ : τ = σ ^ (k % f) := by rw [← hk, ← hord, pow_mod_orderOf]
  exact ⟨k % f, Nat.mod_lt _ (by omega), fun x => by
    rw [hτ, ringAut_pow_apply_of_frobenius hσ]⟩

theorem entrywise_baseChange_comm {τ : Tag} {K L : Type} [Field K] [Field L]
    [Algebra K L] (σ : K →+* K) (ς : L →+* L)
    (hσς : ∀ c, ς (algebraMap K L c) = algebraMap K L (σ c)) (g : ModGL τ K) :
    Units.map (entrywiseHom ς) (baseChangeGL (algebraMap K L) g) =
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ) g) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
  congr 2
  exact RingHom.ext hσς

@[expose] def diagL {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (a : Fin Tag.E6.rank → Kˣ) : ModGL Tag.E6 L :=
  rootDiagUnit Tag.E6 fun i => Units.map (algebraMap K L).toMonoidHom (a i)

theorem phi6_normal_form_L {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [CharP L ℓ]
    (η : MulAut (adjointGroup Tag.E6 K)) :
    ∃ j < f, ∃ ε < 2, ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      ∀ h : adjointGroup Tag.E6 K,
        adjEmb Tag.E6 K L (η h) =
          (adjEmb Tag.E6 K L g * diagL L a * (diagQ L) ^ ε) *
            Units.map (entrywiseHom (iterateFrobenius L ℓ j)) (adjEmb Tag.E6 K L h) *
          (adjEmb Tag.E6 K L g * diagL L a * (diagQ L) ^ ε)⁻¹ := by
  classical
  obtain ⟨g, a, σ, ε, hη⟩ := (ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl)
    K).2.2 η
  obtain ⟨j, hj, hσj⟩ := exists_frobenius_pow_eq' (Fact.out : ℓ.Prime) hf hK σ
  have hε : (ε : ℕ) < 2 := by
    have := ε.2
    simpa [exactE] using this
  refine ⟨j, hj, ε, hε, g, a, fun h => ?_⟩
  have hς : ∀ c, iterateFrobenius L ℓ j (algebraMap K L c) = algebraMap K L (σ.toRingHom c) :=
    fun c => by
      rw [iterateFrobenius_def, ← map_pow, ← hσj c]
      rfl
  have h1 := congrArg (baseChangeGL (algebraMap K L)) (hη h)
  have hQ : baseChangeGL (algebraMap K L) (exactQ Tag.E6 K (ε : ℕ)) = (diagQ L) ^ (ε : ℕ) := by
    change baseChangeGL (algebraMap K L) ((diagramMap TwistTag.E6 K : ModGL Tag.E6 K) ^ (ε : ℕ)) =
      _
    rw [map_pow]
    exact congrArg (· ^ (ε : ℕ)) (baseChangeGL_diagramMap _ TwistTag.E6)
  simp only [adjEmb_apply]
  rw [h1]
  simp only [map_mul, map_inv, baseChangeGL_rootDiagUnit, hQ, mul_inv_rev,
    entrywise_baseChange_comm σ.toRingHom (iterateFrobenius L ℓ j) hς, diagL, mul_assoc]

end CFSG.RankThree.PartOne.KE6
