module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaGroup
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.LocalAnalysis.StandardType.GGTableBPositionToral

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)

namespace CoverPSp

theorem conj_inv_mul_apply_conj {R : Type*} [Group R] (ρ₁ x : R) {t : R} {φ : MulAut R}
    (ht : φ t = t) :
    ((MulAut.conj (ρ₁ * φ x * x⁻¹))⁻¹ * (MulAut.conj ρ₁ * φ)) (x * t * x⁻¹) =
      x * t * x⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have h1 : (MulAut.conj (ρ₁ * φ x * x⁻¹))⁻¹
      (MulAut.conj ρ₁ (φ (x * t * x⁻¹))) =
      (ρ₁ * φ x * x⁻¹)⁻¹ * (ρ₁ * φ (x * t * x⁻¹) * ρ₁⁻¹) *
        (ρ₁ * φ x * x⁻¹) := by
    rw [MulAut.inv_apply, MulAut.conj_symm_apply, MulAut.conj_apply]
  rw [h1]
  simp only [map_mul, map_inv, ht]
  group

private theorem ne_zero_of_card {K : Type} [Finite K] [Nontrivial K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : n ≠ 0 := by
  rintro rfl
  exact (Finite.one_lt_card (α := K)).ne' (by simpa using hK)

theorem exists_eq_conj_mul_fieldAut {K : Type} [Field K] [Finite K] {m n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))} {k : ℕ} (ha : a ^ p ^ k = 1) :
    ∃ (ρ : LargeEvenProj (LargeEvenSpGroup K m)) (σ : K ≃+* K) (s : ℕ), σ ^ p ^ s = 1 ∧
      a = MulAut.conj ρ * (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
  rcases Nat.eq_zero_or_pos k with rfl | _
  · exact ⟨1, 1, 0, by simp, by rw [show a = 1 by simpa using ha]; simp⟩
  · have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := charP_two_of_card hK
    obtain ⟨u, hu, f, hf, haeq⟩ :=
      (NbrGraphSymplectic.ggOddAutInnField_symplectic (K := K) (m := m) hm
        (p := p ^ k) (hp.odd_of_ne_two hp2).pow) a ha
    have hcl : Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) ≤
        (fieldAut m K).range := by
      rw [Subgroup.closure_le]
      rintro φ hφ
      obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hφ
      exact ⟨σ, rfl⟩
    obtain ⟨σ₀, hσ₀⟩ := hcl hf
    have hσ₀n : σ₀ ^ n = 1 := by
      rw [← (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        Nat.prime_two K hK).1]
      exact pow_card_eq_one'
    obtain ⟨ρ, j, e, hdiv, haeq'⟩ :=
      exists_eq_conj_mul_pow_of_eq_mul hp (ne_zero_of_card hK)
        (RecipeFieldSp.mem_conjImage_iff_inn.mp hu) ha haeq
    obtain ⟨t, ht⟩ := hdiv
    have hfpow : f ^ j = (fieldAut m K (σ₀ ^ j) :
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
      rw [← hσ₀, ← map_pow]
    have hσpow : (σ₀ ^ j) ^ p ^ e = 1 := by
      rw [← pow_mul, mul_comm j (p ^ e), ht, pow_mul, hσ₀n, one_pow]
    exact ⟨ρ, σ₀ ^ j, e, hσpow, by rw [haeq', hfpow]⟩

private theorem exists_conj_map_eq_range_spTorus {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (E' : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)))
    (hE' : IsElemAbelian p E') (hcard : p ^ m ≤ Nat.card E') :
    ∃ g, E'.map (MulAut.conj g).toMonoidHom = (spTorus (m := m) hζ).range := by
  obtain ⟨x, hx1, hx2⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hE' hcard
  refine ⟨x⁻¹, ?_⟩
  have hEq : E' = (spTorus (m := m) hζ).range.map (MulAut.conj x).toMonoidHom := by
    apply le_antisymm
    · intro e he
      obtain ⟨f, hf⟩ := hx2 e he
      exact Subgroup.mem_map.mpr ⟨spTorus hζ f, ⟨f, rfl⟩, hf⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hv
      exact hx1 f
  rw [hEq, Subgroup.map_map]
  have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id (LargeEvenProj (LargeEvenSpGroup K m)) := by
    ext r
    change (MulAut.conj x⁻¹) ((MulAut.conj x) r) = r
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

private theorem fieldAut_spTorus_fixed {K : Type} [Field K] {m p : ℕ} (hp : p.Prime)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p)) :
    ∀ (σ : K ≃+* K) (s : ℕ), σ ^ p ^ s = 1 →
      (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) (spTorus hζ f) =
        spTorus hζ f := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro σ s hσ
  have hζK : (ζ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have hσζ : σ (ζ : K) = (ζ : K) := fieldAut_fixes_pow_eq_one hp hσ hζK
  have hc : σ (ζ : K) = (ζ : K) ^ 1 := by rw [pow_one]; exact hσζ
  rw [ReflSp.fieldAut_spTorus σ hζ hc f, pow_one]

theorem exists_conj_of_position {K : Type} [Field K] [Finite K] {m n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hP : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) θ hE) :
    ∃ x : LargeEvenProj (LargeEvenSpGroup K m), ∀ e : E, ∃ t : LargeEvenProj (LargeEvenSpGroup K m),
      (∀ (σ : K ≃+* K) (s : ℕ), σ ^ p ^ s = 1 →
        (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) t = t) ∧
      ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj (x * t * x⁻¹) := by
  have hp2 : p ≠ 2 :=
    ne_two_of_dvd_two_pow_sub_one (Nat.one_le_iff_ne_zero.mpr (ne_zero_of_card hK)) hpn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero m := ⟨by omega⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hL : GGTorusLift p m (LargeEvenProj (LargeEvenSpGroup K m)) :=
    TableBSymp.ggTorusLift_symplectic hp hp2 hpq (by omega)
  set V : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) := (spTorus (m := m) hζ).range with hV
  have hT : ∀ E' : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)),
      IsElemAbelian p E' → p ^ m ≤ Nat.card E' →
        ∃ g, E'.map (MulAut.conj g).toMonoidHom = V :=
    fun E' hE' hcard => exists_conj_map_eq_range_spTorus hp hp2 hζo hζ E' hE' hcard
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot
  have hinn : ∀ e : E, ggLAut L' θ ⟨e, hE e.2⟩ ∈
      (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _).range :=
    fun e => TableBSymp.sp_I_subset_inn (hP.2.2.2.1 e)
  obtain ⟨g, hg⟩ := exists_conj_of_position_toral hZ hp V hL hT hP hinn
  refine ⟨g⁻¹, fun e => ?_⟩
  obtain ⟨v, hv, hve⟩ := hg e
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp (hV ▸ hv)
  exact ⟨spTorus hζ f, fieldAut_spTorus_fixed hp hζ f, by simpa using hve⟩

theorem ggCoverPTableB_symplectic {K : Type} [Field K] [Finite K] {m n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    GGCoverPTableB p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro M _ _ L' E θ hE hP a ha
  obtain ⟨k, hk⟩ := ha
  have hp2 : p ≠ 2 :=
    ne_two_of_dvd_two_pow_sub_one (Nat.one_le_iff_ne_zero.mpr (ne_zero_of_card hK)) hpn
  obtain ⟨x, hx⟩ := exists_conj_of_position hK hm hp hpn hP
  obtain ⟨ρ₁, σ, s, hσ, ha'⟩ := exists_eq_conj_mul_fieldAut hK hm hp hp2 (k := k) hk
  refine ⟨ρ₁ * (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) x * x⁻¹,
    fun e => ?_⟩
  obtain ⟨t, htfix, hte⟩ := hx e
  rw [hte, ha']
  exact commute_conj_of_apply_eq (conj_inv_mul_apply_conj ρ₁ x (htfix σ s hσ))

theorem largeEvenLabelAll_coverP_symplectic {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBSympLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hpn' : p ∣ 2 ^ n - 1 := by simpa using hpn
  intro Q hQ
  rcases htag with ht | ht <;> dsimp only at ht <;> subst ht
  all_goals
    dsimp only [LargeEvenInLambda2] at hlab
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK =>
      ggCoverPTableB_symplectic hK hlab.2.1 hp hpn') hQ

end CoverPSp

end CFSG.StandardType
