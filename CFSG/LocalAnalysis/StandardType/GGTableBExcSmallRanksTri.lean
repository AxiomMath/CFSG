module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

namespace TableBExcSmallRanks

theorem factorization_triD4_le {q : ℕ} (hq : 2 ≤ q) (h3 : q % 3 = 1) :
    (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)).factorization 3 ≤
      ((q ^ 3 - 1) * (q - 1)).factorization 3 + 1 := by
  set R := q ^ 12 * (q + 1) * (q ^ 3 + 1) * (q ^ 8 + q ^ 4 + 1) with hR
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3' : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have e : q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) =
      ((q ^ 3 - 1) * (q - 1)) * R := by
    rw [hR]
    zify [h1, h2, h3', h6]
    ring
  have hA : (q ^ 3 - 1) * (q - 1) ≠ 0 := by
    have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    exact mul_ne_zero (by omega) (by omega)
  have hR0 : R ≠ 0 := by positivity
  have hR9 : R % 9 = 3 := by
    have hq9 : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
    rw [hR]
    rcases hq9 with h | h | h <;>
      simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, h]
  have hRfac : R.factorization 3 ≤ 1 := by
    by_contra hcon
    have h9 : 3 ^ 2 ∣ R :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hR0).mpr (by omega)
    omega
  rw [e, Nat.factorization_mul hA hR0, Finsupp.add_apply]
  omega

section Weyl


theorem orbitReflection_mul_pow_six_D4 :
    (TwistTag.D4.orbitReflection ⟨0, by decide⟩ *
      TwistTag.D4.orbitReflection ⟨1, by decide⟩) ^ 6 = 1 := by
  set r₀ : relWeylTwist TwistTag.D4 :=
    ⟨_, TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩⟩ with hr₀
  set r₁ : relWeylTwist TwistTag.D4 :=
    ⟨_, TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩⟩ with hr₁
  have hM : (CFSG.LieType.RootSystem.coxeterMatrix
      (isFiniteType_cartan TwistTag.D4.foldedTag)).M ⟨0, by decide⟩ ⟨1, by decide⟩ = 6 := by
    have e01 : TwistTag.D4.foldedTag.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ *
        TwistTag.D4.foldedTag.cartan ⟨1, by decide⟩ ⟨0, by decide⟩ = 3 := by decide
    simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
      e01, TauCeti.coxeterOrder_three]
  have h : (r₀ * r₁) ^ 6 = 1 := by
    apply (foldedWeylEquiv TwistTag.D4).injective
    rw [map_pow, map_mul, map_one, hr₀, hr₁, foldedWeylEquiv_orbitReflection,
      foldedWeylEquiv_orbitReflection]
    have h6 := (coxeterSystem TwistTag.D4.foldedTag).simple_mul_simple_pow ⟨0, by decide⟩
      ⟨1, by decide⟩
    rwa [hM] at h6
  have h' := congrArg Subtype.val h
  rwa [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] at h'

end Weyl

section BaseChange


theorem baseChangeGL_twistHom (t : TwistTag) {K K' : Type} [Field K] [Field K'] (f : K →+* K')
    (σ : K →+* K) (σ' : K' →+* K') (hfσ : ∀ c, f (σ c) = σ' (f c)) (g : ModGL t.tag K) :
    baseChangeGL f (twistHom t K σ g) = twistHom t K' σ' (baseChangeGL f g) := by
  apply Units.ext
  have hP : BaseChange f ((diagramMap t K : ModGL t.tag K) : Module.End K (RootModule t.tag K))
      ((diagramMap t K' : ModGL t.tag K') : Module.End K' (RootModule t.tag K')) := fun b => by
    simp [diagramMap]
  have hX : BaseChange f (entrywise σ (g : Module.End K (RootModule t.tag K)))
      (entrywise σ' (baseChangeEnd f (g : Module.End K (RootModule t.tag K)))) := fun b => by
    rw [entrywise_single, entrywise_single, baseChangeEnd_single]
    ext l
    simp [hfσ]
  have h1 := hP.mul (hX.mul hP.units_inv)
  rw [coe_baseChangeGL, coe_twistHom, coe_twistHom, coe_baseChangeGL]
  refine ((baseChange_baseChangeEnd f _).unique ?_)
  rw [mul_assoc, mul_assoc]
  exact h1

theorem baseChangeGL_mem_adjointGroup {τ : Tag} {K K' : Type} [Field K] [Field K']
    (f : K →+* K') {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    baseChangeGL f g ∈ adjointGroup τ K' := by
  have h1 : baseChangeGL f g ∈ (adjointGroup τ K).map (baseChangeGL f) :=
    Subgroup.mem_map_of_mem _ hg
  rw [map_baseChangeGL_adjointGroup] at h1
  refine (Subgroup.closure_le _).mpr ?_ h1
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact xUnit_mem_adjointGroup i (f c)
  · exact yUnit_mem_adjointGroup i (f c)

theorem baseChangeGL_mem_twistedFixedGroup (t : TwistTag) {K K' : Type} [Field K] [Field K']
    (f : K →+* K') (σ : K →+* K) (σ' : K' →+* K') (hfσ : ∀ c, f (σ c) = σ' (f c))
    {g : ModGL t.tag K} (hg : g ∈ twistedFixedGroup t K σ) :
    baseChangeGL f g ∈ twistedFixedGroup t K' σ' := by
  refine ⟨baseChangeGL_mem_adjointGroup f hg.1, ?_⟩
  have h2 : twistHom t K σ g = g := hg.2
  show twistHom t K' σ' (baseChangeGL f g) = baseChangeGL f g
  rw [← baseChangeGL_twistHom t f σ σ' hfσ, h2]

end BaseChange

section Torus


theorem trialityNorm_fixedUnit_eq_one {K : Type} [Field K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1)
    {b : (trialityFixedField K σ.toRingHom)ˣ} (hb : b ^ 3 = 1) :
    trialityNorm σ hσ (trialityFixedUnit K σ b) = 1 := by
  apply Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
    (Subtype.val_injective)
  rw [map_one]
  apply Units.ext
  change ((trialityFixedUnit K σ (trialityNorm σ hσ (trialityFixedUnit K σ b)) : Kˣ) : K) = 1
  rw [coe_trialityNorm, sigma_trialityFixedUnit, sigma_trialityFixedUnit]
  have h := congrArg (fun u : (trialityFixedField K σ.toRingHom)ˣ =>
    ((trialityFixedUnit K σ u : Kˣ) : K)) hb
  simp only [map_pow, Units.val_pow_eq_pow_val, map_one, Units.val_one] at h
  rw [← h]
  ring

theorem trialityMiddleTorus_one {K : Type} [Field K] (σ : K ≃+* K) :
    trialityMiddleTorus K σ 1 = 1 := by
  rw [trialityMiddleTorus, map_one, torusElt_one]

theorem conj_trialityMiddleTorus_sq {K : Type} [Field K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1)
    {b : (trialityFixedField K σ.toRingHom)ˣ} (hb : b ^ 3 = 1) :
    (trialityOuterRep K * trialityMiddleRep K) ^ 2 * trialityMiddleTorus K σ b *
        ((trialityOuterRep K * trialityMiddleRep K) ^ 2)⁻¹ =
      trialityMiddleTorus K σ b * trialityOuterTorus K σ (trialityFixedUnit K σ b) *
        trialityOuterTorus K σ (trialityFixedUnit K σ b) := by
  set o := trialityOuterRep K
  set m := trialityMiddleRep K
  have hconj : ∀ g x y : ModGL TwistTag.D4.tag K, g * (x * y) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) := fun g x y => by group
  have hnest : (o * m) ^ 2 * trialityMiddleTorus K σ b * ((o * m) ^ 2)⁻¹ =
      o * (m * (o * (m * trialityMiddleTorus K σ b * m⁻¹) * o⁻¹) * m⁻¹) * o⁻¹ := by
    rw [sq, mul_inv_rev]
    group
  have hbinv : b⁻¹ ^ 3 = 1 := by rw [inv_pow, hb, inv_one]
  have s1 : m * trialityMiddleTorus K σ b * m⁻¹ = trialityMiddleTorus K σ b⁻¹ :=
    trialityMiddleRep_conj_middle b
  have s2 : o * trialityMiddleTorus K σ b⁻¹ * o⁻¹ =
      trialityMiddleTorus K σ b⁻¹ * trialityOuterTorus K σ (trialityFixedUnit K σ b⁻¹) :=
    trialityOuterRep_conj_middle b⁻¹
  have s3 : m * (trialityMiddleTorus K σ b⁻¹ *
      trialityOuterTorus K σ (trialityFixedUnit K σ b⁻¹)) * m⁻¹ =
      trialityMiddleTorus K σ b * trialityOuterTorus K σ (trialityFixedUnit K σ b⁻¹) := by
    rw [hconj, trialityMiddleRep_conj_middle, trialityMiddleRep_conj_outer hσ,
      trialityNorm_fixedUnit_eq_one hσ hbinv, trialityMiddleTorus_one, mul_one, inv_inv]
  have s4 : o * (trialityMiddleTorus K σ b *
      trialityOuterTorus K σ (trialityFixedUnit K σ b⁻¹)) * o⁻¹ =
      trialityMiddleTorus K σ b * trialityOuterTorus K σ (trialityFixedUnit K σ b) *
        trialityOuterTorus K σ (trialityFixedUnit K σ b) := by
    rw [hconj, trialityOuterRep_conj_middle, trialityOuterRep_conj_outer, map_inv, inv_inv]
  rw [hnest, s1, s2, s3, s4]

end Torus

section Split


theorem sigma_pow_three_eq_one {n : ℕ} {K : Type} [Field K] [Fintype K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n) : σ ^ 3 = 1 := by
  ext c
  have h3 : σ (σ (σ c)) = c := by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have hpc := FiniteField.pow_card c
    rw [Fintype.card_eq_nat_card, hK] at hpc
    rw [show 2 ^ n * (2 ^ n * 2 ^ n) = (2 ^ n) ^ 3 by ring]
    exact hpc
  rw [ringEquiv_pow_three_apply, h3]
  rfl

theorem card_lt_of_isElemAbelian_triD4_of_dvd {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : IsElemAbelian 3 E) :
    Nat.card E < 3 ^ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * n) hK3
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ ^ 3 = 1 := sigma_pow_three_eq_one hK hσ
  have hq2 : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨-, ⟨e, he⟩, -, -, -, -⟩ := even_triality_faithful_torus_coordinates K σ hσ3
  obtain ⟨hC0, hH1, -⟩ := triality_both_orientations_exact_finite_order 2 n Nat.prime_two hn K hK
    1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  have hH₁C₀ : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := inf_le_right
  have hH₁N₁ : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial TwistTag.D4 K σ.toRingHom)
  have hN₁C₀ : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := inf_le_right
  have hho1 : trialityOuterTorus K σ 1 = 1 := by
    have h1 := he 1 1
    rw [trialityMiddleTorus_one, mul_one] at h1
    rw [← h1]
    exact congrArg Subtype.val (map_one e)
  have hhoe : ∀ a : Kˣ, trialityOuterTorus K σ a = (e (a, 1) : ModGL TwistTag.D4.tag K) :=
    fun a => by rw [he, trialityMiddleTorus_one, mul_one]
  have ho : trialityOuterRep K ∈ graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    canonicalRep_mem_graphFixedRootMonomial TwistTag.D4 K σ.toRingHom
      (TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩)
  have hm : trialityMiddleRep K ∈ graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    canonicalRep_mem_graphFixedRootMonomial TwistTag.D4 K σ.toRingHom
      (TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩)
  set O : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom := ⟨_, ho⟩ with hO
  set Mm : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom := ⟨_, hm⟩ with hMm
  set W : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom := (O * Mm) ^ 2 with hW
  have hWval : (W : ModGL TwistTag.D4.tag K) = (trialityOuterRep K * trialityMiddleRep K) ^ 2 :=
    rfl
  have hOw : graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom O =
      TwistTag.D4.orbitReflection ⟨0, by decide⟩ :=
    graphFixedRootWeylHom_canonicalRep TwistTag.D4 K σ.toRingHom
      (TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩)
  have hMw : graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom Mm =
      TwistTag.D4.orbitReflection ⟨1, by decide⟩ :=
    graphFixedRootWeylHom_canonicalRep TwistTag.D4 K σ.toRingHom
      (TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩)
  have hW3 : ((W ^ 3 : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    have hk : W ^ 3 ∈ (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom).ker := by
      rw [MonoidHom.mem_ker, hW, map_pow, map_pow, map_mul, hOw, hMw, ← pow_mul]
      exact orbitReflection_mul_pow_six_D4
    rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hnorm : ∀ g ∈ graphFixedRootMonomial TwistTag.D4 K σ.toRingHom,
      ∀ x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
        g * x * g⁻¹ ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    intro g hg x hx
    have h1 := (graphFixedRootTorus_subgroupOf_normal TwistTag.D4 K σ.toRingHom).conj_mem
      ⟨x, hH₁N₁ hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have hmemT : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      x ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ↔
      (x : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    fun x => Subgroup.mem_subgroupOf
  let ι : Kˣ × (trialityFixedField K σ.toRingHom)ˣ →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.inclusion hH₁C₀).comp e.toMonoidHom
  have hιval : ∀ ab, ((ι ab : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = (e ab : ModGL TwistTag.D4.tag K) := fun ab => rfl
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hH₁C₀).comp e.injective
  have hιT : ∀ x ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∃ ab, ι ab = x := by
    intro x hx
    obtain ⟨ab, hab⟩ := e.surjective ⟨x, (hmemT x).mp hx⟩
    exact ⟨ab, Subtype.ext (by rw [hιval, hab])⟩
  have hιmem : ∀ ab, ι ab ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun ab => (hmemT _).mpr (e ab).2
  have hTc : ∀ x ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ y ∈ (graphFixedRootTorus TwistTag.D4 K
        σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hιT x hx
    obtain ⟨b, rfl⟩ := hιT y hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hTb : ∀ A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      A ≤ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
      (∀ x ∈ A, x ^ 3 = 1) → Nat.card A ≤ 3 ^ 2 := by
    intro A hA hA3
    refine card_le_sq_of_le_range (by norm_num) ι hι (fun x hx => ?_) hA3
    obtain ⟨ab, hab⟩ := hιT x (hA hx)
    exact ⟨ab, hab⟩
  have hkcard : Nat.card (trialityFixedField K σ.toRingHom)ˣ = 2 ^ n - 1 := by
    have h1 : Nat.card (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) =
        Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) := Nat.card_congr e.toEquiv
    rw [Nat.card_prod, hH1, Nat.card_units, hK] at h1
    have hpos : 0 < (2 ^ n) ^ 3 - 1 := by
      have : 1 < (2 ^ n) ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K σ.toRingHom)ˣ) 3
    (by rw [hkcard]; exact h3)
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  set h₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ι (1, ζ) with hh₀def
  have hh₀3 : h₀ ^ 3 = 1 := by
    rw [hh₀def, ← map_pow]
    have h1 : ((1 : Kˣ), ζ) ^ 3 = 1 := by rw [Prod.pow_mk, one_pow, hζ3]; rfl
    rw [h1, map_one]
  have hval0 : (h₀ : ModGL TwistTag.D4.tag K) = trialityMiddleTorus K σ ζ := by
    rw [hh₀def, hιval, he, hho1, one_mul]
  set nC : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨(W : ModGL TwistTag.D4.tag K),
    hN₁C₀ W.2⟩ with hnC
  have hnN : nC ∈ Subgroup.normalizer (((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmemT, hmemT]
    show (h : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ↔
      (W : ModGL TwistTag.D4.tag K) * h * (W : ModGL TwistTag.D4.tag K)⁻¹ ∈
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom
    constructor
    · exact hnorm _ W.2 _
    · intro hx
      have h1 := hnorm _ ((graphFixedRootMonomial TwistTag.D4 K σ.toRingHom).inv_mem W.2) _ hx
      have e1 : (W : ModGL TwistTag.D4.tag K)⁻¹ * ((W : ModGL TwistTag.D4.tag K) *
          (h : ModGL TwistTag.D4.tag K) * (W : ModGL TwistTag.D4.tag K)⁻¹) *
          ((W : ModGL TwistTag.D4.tag K)⁻¹)⁻¹ = h := by group
      rwa [e1] at h1
  have hnp : nC ^ 3 ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [hmemT]
    exact hW3
  have hnh : nC * h₀ ≠ h₀ * nC := by
    intro hcomm
    have h1 : (W : ModGL TwistTag.D4.tag K) * (h₀ : ModGL TwistTag.D4.tag K) *
        (W : ModGL TwistTag.D4.tag K)⁻¹ = (h₀ : ModGL TwistTag.D4.tag K) := by
      have h2 := congrArg Subtype.val hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
      rw [show ((nC : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = W from rfl] at h2
      rw [h2, mul_inv_cancel_right]
    rw [hval0, hWval, conj_trialityMiddleTorus_sq hσ3 hζ3, mul_assoc, mul_eq_left] at h1
    rw [hhoe, ← Subgroup.coe_mul, ← map_mul] at h1
    have h3 : (trialityFixedUnit K σ ζ, (1 : (trialityFixedField K σ.toRingHom)ˣ)) *
        (trialityFixedUnit K σ ζ, 1) = 1 :=
      e.injective (Subtype.ext (by rw [h1, map_one]; rfl))
    have h4 : ζ ^ 2 = 1 := by
      apply Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
        Subtype.val_injective
      rw [map_pow, map_one, sq]
      exact congrArg Prod.fst h3
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hζ] at h5
    norm_num at h5
  have hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization 3 ≤
      (Nat.card ((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).factorization 3 + 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₁C₀).toEquiv, hC0, hH1]
    exact factorization_triD4_le hq2 (by omega)
  have := card_lt_of_normalizer_pow_mem (k := 2) Nat.prime_three hTc hTb hnN hnp (hιmem _)
    hh₀3 hnh hord hE
  simpa using this

end Split

section All


theorem card_lt_of_isElemAbelian_triD4 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : IsElemAbelian 3 E) :
    Nat.card E < 3 ^ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * n) hK3
  have : Fintype K := Fintype.ofFinite K
  have hσ3 : σ ^ 3 = 1 := sigma_pow_three_eq_one hK hσ
  let K' := FiniteField.Extension K 2 4
  have hK' : Nat.card K' = (2 ^ (4 * n)) ^ 3 := by
    rw [FiniteField.natCard_extension, hK]
    ring
  have : CharP K' 2 := charP_of_injective_algebraMap (algebraMap K K').injective 2
  have : Fintype K' := Fintype.ofFinite K'
  let f : K →+* K' := algebraMap K K'
  let σ' : K' ≃+* K' := iterateFrobeniusEquiv K' 2 (4 * n)
  have hσ' : ∀ c, σ' c = c ^ 2 ^ (4 * n) := fun c => by
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσ'3 : σ' ^ 3 = 1 := sigma_pow_three_eq_one hK' hσ'
  have hfσ : ∀ c, f (σ.toRingHom c) = σ'.toRingHom (f c) := by
    intro c
    show f (σ c) = σ' (f c)
    rw [hσ, hσ', ← map_pow]
    congr 1
    have hpc : c ^ 2 ^ (3 * n) = c := by
      have h1 := FiniteField.pow_card c
      rwa [Fintype.card_eq_nat_card, hK3] at h1
    rw [show 4 * n = 3 * n + n by ring, pow_add, pow_mul, hpc]
  have hΓ := (even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ
    (fun c => by rw [← ringEquiv_pow_three_apply, hσ3]; rfl)).1
  have hΓ' := (even_triality_fixed_group_eq_root_group K' (ringChar.eq K' 2) σ'
    (fun c => by rw [← ringEquiv_pow_three_apply, hσ'3]; rfl)).1
  have hmap : ∀ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      baseChangeGL f g ∈ graphFixedRootGroup TwistTag.D4 K' σ'.toRingHom := by
    intro g hg
    rw [← hΓ']
    rw [← hΓ] at hg
    exact baseChangeGL_mem_twistedFixedGroup TwistTag.D4 f σ.toRingHom σ'.toRingHom hfσ hg
  let ψ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      graphFixedRootGroup TwistTag.D4 K' σ'.toRingHom :=
    ((baseChangeGL f).comp (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).codRestrict
      _ (fun g => hmap g g.2)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    apply baseChangeGL_injective f
    exact congrArg Subtype.val hxy
  have h3' : 3 ∣ 2 ^ (4 * n) - 1 := by
    have h1 : 2 ^ (4 * n) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    omega
  have h1 := card_lt_of_isElemAbelian_triD4_of_dvd (by omega : 1 ≤ 4 * n) h3' K' hK' σ' hσ'
    (TableB.isElemAbelian_map hE ψ)
  rwa [Subgroup.card_map_of_injective hψ] at h1

theorem ggTriD4ThreeRankInput_holds : TableBExcSmallRest.GGTriD4ThreeRankInput :=
  fun _ hn _ K _ _ hK σ hσ _ hE => card_lt_of_isElemAbelian_triD4 hn K hK σ hσ hE

end All

end TableBExcSmallRanks

end CFSG.StandardType
