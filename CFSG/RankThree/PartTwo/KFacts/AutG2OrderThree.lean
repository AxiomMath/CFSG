module

public import CFSG.RankThree.PartTwo.KFacts.AutG2
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
import CFSG.LieType.Chevalley.ChevalleyFrobeniusFixedNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem conj_mul_pow_three {S : Type*} [Group S] (g : S) (Φ : MulAut S) :
    (MulAut.conj g * Φ) ^ 3 = MulAut.conj (g * Φ g * Φ (Φ g)) * Φ ^ 3 := by
  have e1 : Φ * MulAut.conj g * Φ⁻¹ = MulAut.conj (Φ g) := mul_mulAutConj_mul_inv Φ g
  have e2 : Φ ^ 2 * MulAut.conj g * (Φ ^ 2)⁻¹ = MulAut.conj (Φ (Φ g)) := by
    rw [mul_mulAutConj_mul_inv, pow_two, MulAut.mul_apply]
  calc (MulAut.conj g * Φ) ^ 3 = MulAut.conj g * (Φ * MulAut.conj g * Φ⁻¹) *
        (Φ ^ 2 * MulAut.conj g * (Φ ^ 2)⁻¹) * Φ ^ 3 := by rw [pow_three]; group
    _ = MulAut.conj (g * Φ g * Φ (Φ g)) * Φ ^ 3 := by rw [e1, e2, map_mul, map_mul]

section Lang

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exists_conj_mul_eq_of_norm_eq_one_aux (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] {p m : ℕ} [Fact p.Prime] [CharP L p] (hm : 1 ≤ m)
    (hK : Nat.card K = p ^ (3 * m)) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ p ^ m)
    {Φ : MulAut (adjointGroup τ K)}
    (hΦ : ∀ h, (Φ h : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))
    {g : adjointGroup τ K} (hN : g * Φ g * Φ (Φ g) = 1) :
    ∃ β : MulAut (adjointGroup τ K), MulAut.conj g * Φ = β * Φ * β⁻¹ := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set ι : K →+* L := algebraMap K L with hι
  set Fr0 : L →+* L := iterateFrobenius L p m with hFr0
  have hFr0ι : Fr0.comp ι = ι.comp σ.toRingHom := by
    ext c
    simp only [RingHom.comp_apply, hFr0, iterateFrobenius_def, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, hσ, map_pow]
  set Fr : L →+* L := Fr0.comp (Fr0.comp Fr0) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    simp only [hFrdef, hFr0, RingHom.comp_apply, iterateFrobenius_def, hK, ← pow_mul]
    congr 1
    ring
  obtain ⟨S, hS, hLang⟩ :=
    (CFSG.LieType.AlgebraicGroups.exceptional_all_characteristic_field_Lang_surjectivity p L m
      hm).1 τ
  have hS' : ∀ y : adjointGroup τ L, (S y : ModGL τ L) = baseChangeGL Fr0 (y : ModGL τ L) :=
    fun y => hS y
  let J : adjointGroup τ K →* adjointGroup τ L :=
    ((baseChangeGL ι).comp (adjointGroup τ K).subtype).codRestrict (adjointGroup τ L)
      fun x => CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  have hJ : ∀ x, (J x : ModGL τ L) = baseChangeGL ι (x : ModGL τ K) := fun x => rfl
  have hJinj : Function.Injective J := fun x y hxy =>
    Subtype.ext (baseChangeGL_injective ι (by rw [← hJ, ← hJ, hxy]))
  have hSJ : ∀ x, S (J x) = J (Φ x) := by
    intro x
    refine Subtype.ext ?_
    rw [hS', hJ, hJ, hΦ, baseChangeGL_baseChangeGL]
    change _ = baseChangeGL ι (baseChangeGL σ.toRingHom (x : ModGL τ K))
    rw [baseChangeGL_baseChangeGL, hFr0ι]
  obtain ⟨h, hh⟩ := hLang (J g)
  have hS3 : S (S (S h)) = h := by
    have h1 : J g * S (J g) * S (S (J g)) = 1 := by
      rw [hSJ, hSJ, ← map_mul, ← map_mul, hN, map_one]
    simp only [hh, map_mul, map_inv] at h1
    have h2 : h⁻¹ * S (S (S h)) = 1 := by
      rw [← h1]
      group
    exact (inv_mul_eq_one.mp h2).symm
  obtain ⟨-, -, hnorm⟩ := Chevalley_Frobenius_fixed_ambient_normalizer τ K L Fr hFr
  have hFh : Units.map (entrywiseHom Fr) (h : ModGL τ L) = (h : ModGL τ L) := by
    change baseChangeGL Fr (h : ModGL τ L) = (h : ModGL τ L)
    have h1 := congrArg (fun y : adjointGroup τ L => (y : ModGL τ L)) hS3
    simp only [hS'] at h1
    rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL] at h1
    rw [hFrdef, ← RingHom.comp_assoc]
    exact h1
  have hhN := hnorm ⟨h.2, hFh⟩
  have hmemJ : ∀ z : adjointGroup τ L, z ∈ J.range ↔
      (z : ModGL τ L) ∈ (adjointGroup τ K).map (baseChangeGL ι) := by
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, hxz⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  have hhJ : h⁻¹ ∈ Subgroup.normalizer (J.range : Set (adjointGroup τ L)) := by
    refine inv_mem (Subgroup.mem_normalizer_iff.mpr fun z => ?_)
    rw [hmemJ, hmemJ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hhN z
  let ιJ : adjointGroup τ K ≃* J.range := MonoidHom.ofInjective hJinj
  let β : MulAut (adjointGroup τ K) :=
    MulAut.congr ιJ.symm (J.range.normalizerMonoidHom ⟨h⁻¹, hhJ⟩)
  have hJβ : ∀ x, J (β x) = h⁻¹ * J x * h := by
    intro x
    have h1 : ιJ (β x) = J.range.normalizerMonoidHom ⟨h⁻¹, hhJ⟩ (ιJ x) := by
      simp only [β, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      MonoidHom.ofInjective_apply, inv_inv] at h2
    exact h2
  refine ⟨β, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  refine MulEquiv.ext fun x => hJinj ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulAut.mul_apply, hJβ, ← hSJ, ← hSJ, hJβ, hh]
  simp only [map_mul, map_inv]
  group

theorem exists_conj_mul_eq_of_norm_eq_one {p m : ℕ} [Fact p.Prime] [CharP K p] (hm : 1 ≤ m)
    (hK : Nat.card K = p ^ (3 * m)) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ p ^ m)
    {Φ : MulAut (adjointGroup τ K)}
    (hΦ : ∀ h, (Φ h : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))
    {g : adjointGroup τ K} (hN : g * Φ g * Φ (Φ g) = 1) :
    ∃ β : MulAut (adjointGroup τ K), MulAut.conj g * Φ = β * Φ * β⁻¹ :=
  exists_conj_mul_eq_of_norm_eq_one_aux (AlgebraicClosure K) hm hK hσ hΦ hN

end Lang

variable {K : Type} [Field K] [Finite K]

theorem g2_conj_mul_eq_of_frobenius (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {p m : ℕ}
    [Fact p.Prime] [CharP K p] (hm : 1 ≤ m) (hK : Nat.card K = p ^ (3 * m)) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ p ^ m) {g : adjointGroup Tag.G2 K}
    (hα : (MulAut.conj g * g2FieldHom K σ) ^ 3 = 1) :
    ∃ k : adjointGroup Tag.G2 K,
      MulAut.conj g * g2FieldHom K σ = MulAut.conj k * g2FieldHom K σ * (MulAut.conj k)⁻¹ := by
  obtain ⟨hdec, -⟩ := g2_automorphism_normal_form hK3 hK4
  have hσ3 : σ ^ 3 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    ext c
    simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply, hσ, ← pow_mul]
    rw [show p ^ m * p ^ m * p ^ m = Fintype.card K by
      rw [← Nat.card_eq_fintype_card, hK]; ring]
    exact FiniteField.pow_card c
  have hN : g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g) = 1 := by
    rw [conj_mul_pow_three, ← map_pow, hσ3, map_one, mul_one] at hα
    have hz : g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g) ∈
        Subgroup.center (adjointGroup Tag.G2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.G2 K) => φ y) hα
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * (g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g)) =
          g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g) * y *
            (g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g))⁻¹ *
              (g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g)) := by rw [h1]
        _ = g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g) * y := by group
    rw [center_adjointGroup_eq_bot] at hz
    exact hz
  obtain ⟨β, hβ⟩ := exists_conj_mul_eq_of_norm_eq_one hm hK hσ
    (fun h => coe_g2FieldHom σ h) hN
  obtain ⟨k, ρ, rfl⟩ := hdec β
  refine ⟨k, ?_⟩
  rw [hβ]
  have hcomm : g2FieldHom K ρ * g2FieldHom K σ = g2FieldHom K σ * g2FieldHom K ρ := by
    rw [← map_mul, ← map_mul, ringAut_mul_comm K ρ σ]
  calc MulAut.conj k * g2FieldHom K ρ * g2FieldHom K σ * (MulAut.conj k * g2FieldHom K ρ)⁻¹ =
      MulAut.conj k * (g2FieldHom K ρ * g2FieldHom K σ) * (g2FieldHom K ρ)⁻¹ *
        (MulAut.conj k)⁻¹ := by group
    _ = MulAut.conj k * g2FieldHom K σ * (MulAut.conj k)⁻¹ := by rw [hcomm]; group

theorem g2_order_three_field_descent (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {α : MulAut (adjointGroup Tag.G2 K)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ k : adjointGroup Tag.G2 K,
      α = MulAut.conj k * g2FieldHom K σ * (MulAut.conj k)⁻¹ := by
  classical
  obtain ⟨hdec, hfaith⟩ := g2_automorphism_normal_form hK3 hK4
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  have hKn : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp n.pos hKn
  obtain ⟨g, σ, rfl⟩ := hdec α
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hout
    exact hout (isInnerAut_conj g)
  have hσ3 : σ ^ 3 = 1 := by
    apply hfaith
    rw [map_pow]
    have h1 := hα
    rw [conj_mul_pow_three] at h1
    refine ⟨(g * g2FieldHom K σ g * g2FieldHom K σ (g2FieldHom K σ g))⁻¹, ?_⟩
    rw [map_inv, inv_eq_iff_mul_eq_one]
    exact h1
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨⟨m, hm⟩, hσf⟩ :=
    eq_frobenius_pow_of_orderOf_eq_three hp n.pos hKn hσo
  have hm1 : 1 ≤ m := by
    have := n.pos
    omega
  have hK3m : Nat.card K = p ^ (3 * m) := by rw [hKn, hm]
  have hm3 : (n : ℕ) / 3 = m := by omega
  have hm23 : 2 * (n : ℕ) / 3 = 2 * m := by omega
  rw [hm3, hm23] at hσf
  refine ⟨σ, hσo, ?_⟩
  rcases hσf with hσf | hσf
  · exact g2_conj_mul_eq_of_frobenius hK3 hK4 hm1 hK3m hσf hα
  ·
    have hσinv : ∀ c, (σ⁻¹ : K ≃+* K) c = c ^ p ^ m := by
      intro c
      change σ.symm c = _
      rw [RingEquiv.symm_apply_eq, hσf, ← pow_mul, ← pow_add,
        show m + 2 * m = 3 * m by ring, ← hK3m, Nat.card_eq_fintype_card,
        FiniteField.pow_card]
    have hinv : (MulAut.conj g * g2FieldHom K σ)⁻¹ =
        MulAut.conj ((g2FieldHom K σ)⁻¹ g⁻¹) * g2FieldHom K σ⁻¹ := by
      rw [map_inv (g2FieldHom K) σ, ← mul_mulAutConj_mul_inv (g2FieldHom K σ)⁻¹ g⁻¹, inv_inv,
        mul_inv_rev, map_inv MulAut.conj g]
      group
    obtain ⟨k, hk⟩ := g2_conj_mul_eq_of_frobenius hK3 hK4 hm1 hK3m hσinv
      (by rw [← hinv, inv_pow, hα, inv_one])
    refine ⟨k, ?_⟩
    rw [← inv_inv (MulAut.conj g * g2FieldHom K σ), hinv, hk, map_inv (g2FieldHom K) σ]
    group

theorem isField_g2_of_pow_three_eq_one (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {α : MulAut (adjointGroup Tag.G2 K)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (stdPinnedG2 K).IsField α := by
  obtain ⟨-, hfaith⟩ := g2_automorphism_normal_form hK3 hK4
  obtain ⟨σ, hσo, k, rfl⟩ := g2_order_three_field_descent hK3 hK4 hα hout
  refine ⟨g2FieldHom K σ, ⟨σ, rfl⟩, fun h1 => ?_, MulAut.conj k, ⟨k, rfl⟩, rfl⟩
  have h2 := hfaith σ (by rw [h1]; exact ⟨1, map_one _⟩)
  rw [h2, orderOf_one] at hσo
  omega

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindG2_field (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {x : G}
    (hx3 : x ^ 3 = 1) (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K) :
    InducesKindG2 K L x .field := by
  obtain ⟨hx, -⟩ := id hout
  exact ⟨e, hx, isField_g2_of_pow_three_eq_one hK3 hK4 (inducedAutHom_pow_eq_one L e hx hx3)
    ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout)⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
