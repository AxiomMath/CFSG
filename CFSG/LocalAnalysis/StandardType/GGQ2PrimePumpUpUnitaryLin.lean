module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
public import CFSG.Open.StatedDefs
import CFSG.RankThree.OddKernel.SectionRep
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Projection
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.GGQ2Prime

open Module CFSG.RankThree.OddKernel
open scoped commutatorElement

private structure IsHerm4 {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    (B : X → X → F) : Prop where
  add_left : ∀ x y z, B (x + y) z = B x z + B y z
  smul_left : ∀ (c : F) x y, B (c • x) y = c ^ 2 * B x y
  add_right : ∀ x y z, B x (y + z) = B x y + B x z
  smul_right : ∀ (c : F) x y, B x (c • y) = c * B x y
  herm : ∀ x y, B y x = B x y ^ 2
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0

private theorem IsHerm4.zero_left {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {B : X → X → F} (hB : IsHerm4 B) (y : X) : B 0 y = 0 := by
  have := hB.smul_left 0 0 y
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at this

private theorem IsHerm4.zero_right {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {B : X → X → F} (hB : IsHerm4 B) (x : X) : B x 0 = 0 := by
  have := hB.smul_right 0 x 0
  rwa [zero_smul, zero_mul] at this

private theorem IsHerm4.neg_left {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {B : X → X → F} (hB : IsHerm4 B) (x y : X) : B (-x) y = B x y := by
  have := hB.smul_left (-1) x y
  rwa [neg_one_smul, neg_one_sq, one_mul] at this

private theorem IsHerm4.sub_left {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {B : X → X → F} (hB : IsHerm4 B) (x x' y : X) : B (x - x') y = B x y + B x' y := by
  rw [sub_eq_add_neg, hB.add_left, hB.neg_left]

private theorem IsHerm4.sub_right {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {B : X → X → F} (hB : IsHerm4 B) (h2 : (2 : F) = 0) (x y y' : X) :
    B x (y - y') = B x y + B x y' := by
  rw [sub_eq_add_neg, hB.add_right, ← neg_one_smul F y', hB.smul_right, neg_one_mul,
    neg_eq_of_add_eq_zero_left]
  rw [← two_mul, h2, zero_mul]

private theorem involution_facts {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {B : X → X → F}
    (hB : IsHerm4 B) (h2 : (2 : F) = 0) {t : X ≃ₗ[F] X} (hu : ∀ x y, B (t x) (t y) = B x y)
    (ht : ∀ x, t (t x) = x) :
    (∀ x, t (t x - x) - (t x - x) = 0) ∧ (∀ x y, B (t x - x) y = B x (t y - y)) ∧
      (∀ x y, B (t x - x) (t y - y) = 0) ∧
      (∀ x, t x - x = 0 ↔ ∀ y, B x (t y - y) = 0) := by
  have hX2 : ∀ x : X, x + x = 0 := fun x => by rw [← two_smul F x, h2, zero_smul]
  have hF2 : ∀ c : F, c + c = 0 := fun c => by rw [← two_mul, h2, zero_mul]
  have hN : ∀ x y, B (t x - x) y = B x (t y - y) := fun x y => by
    have h1 : B (t x) y = B x (t y) := by
      have := hu x (t y)
      rw [ht] at this
      exact this
    rw [hB.sub_left, hB.sub_right h2, h1]
  refine ⟨fun x => ?_, hN, fun x y => ?_, fun x => ⟨fun h y => ?_, fun h => ?_⟩⟩
  · rw [map_sub, ht, show x - t x - (t x - x) = (x - t x) + (x - t x) by abel]
    exact hX2 _
  · have key : B (x + (t x - x)) (y + (t y - y)) = B x y := by
      rw [add_sub_cancel, add_sub_cancel]
      exact hu x y
    rw [hB.add_left, hB.add_right, hB.add_right, hN x y] at key
    have : B x (t y - y) + B x (t y - y) + B (t x - x) (t y - y) = 0 := by
      calc B x (t y - y) + B x (t y - y) + B (t x - x) (t y - y)
          = B x y + B x (t y - y) + (B x (t y - y) + B (t x - x) (t y - y)) - B x y := by ring
        _ = 0 := by rw [key, sub_self]
    rwa [hF2, zero_add] at this
  · rw [← hN, h, hB.zero_left]
  · apply hB.nondeg
    intro y
    rw [hN]
    exact h y

private theorem exists_line_of_involution {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    [FiniteDimensional F X] (hX : finrank F X ≤ 3) {t : X ≃ₗ[F] X}
    (hNN : ∀ x, t (t x - x) - (t x - x) = 0) {x₀ : X} (hx₀ : t x₀ ≠ x₀) :
    ∀ x, ∃ a : F, t x - x = a • (t x₀ - x₀) := by
  set N : X →ₗ[F] X := (t : X →ₗ[F] X) - LinearMap.id
  have hNx : ∀ x, N x = t x - x := fun x => rfl
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hNx, hNx]
    exact hNN x
  have hrk := LinearMap.finrank_range_add_finrank_ker N
  have hmono := Submodule.finrank_mono hle
  have hu : N x₀ ≠ 0 := by rw [hNx]; exact sub_ne_zero.2 hx₀
  have hsp : (F ∙ N x₀) ≤ LinearMap.range N :=
    (Submodule.span_singleton_le_iff_mem _ _).2 ⟨x₀, rfl⟩
  have heq : (F ∙ N x₀) = LinearMap.range N :=
    Submodule.eq_of_le_of_finrank_le hsp (by rw [finrank_span_singleton hu]; omega)
  intro x
  have hx : N x ∈ (F ∙ N x₀) := heq ▸ ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx
  exact ⟨a, by rw [← hNx, ← hNx, ha]⟩

private theorem eq_of_commute_unitary_involutions {F X : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (hX : finrank F X ≤ 3) {B : X → X → F} (hB : IsHerm4 B) {t₁ t₂ : X ≃ₗ[F] X}
    (hu₁ : ∀ x y, B (t₁ x) (t₁ y) = B x y) (hu₂ : ∀ x y, B (t₂ x) (t₂ y) = B x y)
    (ht₁ : ∀ x, t₁ (t₁ x) = x) (ht₂ : ∀ x, t₂ (t₂ x) = x)
    (h₁ : ∃ x, t₁ x ≠ x) (h₂ : ∃ x, t₂ x ≠ x) (hc : ∀ x, t₁ (t₂ x) = t₂ (t₁ x)) :
    ∀ x, t₁ x = t₂ x := by
  classical
  have h2 : (2 : F) = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [hF]; norm_num)
    exact_mod_cast CharP.cast_eq_zero F 2
  have h4 : ∀ c : F, c ^ 4 = c := fun c => by rw [← hF]; exact FiniteField.pow_card c
  have hsq : ∀ c : F, c ^ 2 = c → c = 0 ∨ c = 1 := fun c hc => by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hc, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨hNN₁, hS₁, hI₁, hK₁⟩ := involution_facts hB h2 hu₁ ht₁
  obtain ⟨hNN₂, hS₂, hI₂, hK₂⟩ := involution_facts hB h2 hu₂ ht₂
  have hl₁ := exists_line_of_involution hX hNN₁ hx₁
  have hl₂ := exists_line_of_involution hX hNN₂ hx₂
  set u₁ := t₁ x₁ - x₁ with hu₁def
  set u₂ := t₂ x₂ - x₂ with hu₂def
  have hu₁0 : u₁ ≠ 0 := sub_ne_zero.2 hx₁
  have hu₂0 : u₂ ≠ 0 := sub_ne_zero.2 hx₂
  by_cases hdep : ∃ c : F, c • u₁ = u₂
  ·
    obtain ⟨c, hc'⟩ := hdep
    have hl₂' : ∀ x, ∃ a : F, t₂ x - x = a • u₁ := fun x => by
      obtain ⟨a, ha⟩ := hl₂ x
      exact ⟨a * c, by rw [ha, ← hc', smul_smul]⟩
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, B u₁ y₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu₁0 (hB.nondeg _ hcon)
    obtain ⟨y₁, hy₁⟩ : ∃ y₁, B u₁ y₁ = 1 :=
      ⟨(B u₁ y₀)⁻¹ • y₀, by rw [hB.smul_right, inv_mul_cancel₀ hy₀]⟩
    have key : ∀ {t : X ≃ₗ[F] X}, (∀ x, ∃ a : F, t x - x = a • u₁) →
        (∀ x y, B (t x - x) y = B x (t y - y)) → (∃ x, t x ≠ x) →
        ∀ x, t x - x = B u₁ x • u₁ := fun {t} hl hS hne => by
      choose a ha using hl
      have hax : ∀ x, a x = a y₁ ^ 2 * B u₁ x := fun x => by
        have h := hS x y₁
        rw [ha x, ha y₁, hB.smul_left, hB.smul_right, hy₁, mul_one, hB.herm u₁ x] at h
        have h' : (a x ^ 2) ^ 2 = (a y₁ * B u₁ x ^ 2) ^ 2 := by rw [h]
        rw [← pow_mul, h4, mul_pow, ← pow_mul, h4] at h'
        exact h'
      have hκ : a y₁ ^ 2 = a y₁ := by
        have := hax y₁
        rw [hy₁, mul_one] at this
        exact this.symm
      rcases hsq _ hκ with h0 | h1
      · exfalso
        obtain ⟨x, hx⟩ := hne
        apply hx
        have : t x - x = 0 := by rw [ha x, hax x, h0, zero_pow two_ne_zero, zero_mul, zero_smul]
        exact sub_eq_zero.1 this
      · intro x
        rw [ha x, hax x, h1]
        simp
    intro x
    have e1 := key hl₁ hS₁ ⟨x₁, hx₁⟩ x
    have e2 := key hl₂' hS₂ ⟨x₂, hx₂⟩ x
    have := e1.trans e2.symm
    exact sub_left_inj.1 this
  ·
    exfalso
    push Not at hdep
    have hN₁u₂ : t₁ u₂ - u₂ = 0 := by
      obtain ⟨a, ha⟩ := hl₁ u₂
      obtain ⟨b, hb⟩ := hl₁ x₂
      obtain ⟨b', hb'⟩ := hl₂ u₁
      have hcomm : t₁ u₂ - u₂ = t₂ (t₁ x₂ - x₂) - (t₁ x₂ - x₂) := by
        rw [hu₂def, map_sub, map_sub, hc]
        abel
      have e : t₁ u₂ - u₂ = (b * b') • u₂ := by
        rw [hcomm, hb, map_smul, ← smul_sub, hb', smul_smul]
      have ha' : (b * b') • u₂ = a • u₁ := e.symm.trans ha
      by_cases ha0 : a = 0
      · rw [e, ha', ha0, zero_smul]
      · exfalso
        by_cases hbb : b * b' = 0
        · rw [hbb, zero_smul] at ha'
          exact hu₁0 ((smul_eq_zero.1 ha'.symm).resolve_left ha0)
        · apply hdep ((b * b')⁻¹ * a)
          rw [← smul_smul, ← ha', smul_smul, inv_mul_cancel₀ hbb, one_smul]
    have h21 : B u₂ u₁ = 0 := (hK₁ u₂).1 hN₁u₂ x₁
    have h12 : B u₁ u₂ = 0 := by rw [hB.herm u₂ u₁, h21, zero_pow two_ne_zero]
    have h11 : B u₁ u₁ = 0 := hI₁ x₁ x₁
    have h22 : B u₂ u₂ = 0 := hI₂ x₂ x₂
    let L : X → X →ₗ[F] F := fun u =>
      { toFun := B u, map_add' := hB.add_right u, map_smul' := fun c y => hB.smul_right c u y }
    let Φ : X →ₗ[F] (Fin 2 → F) := LinearMap.pi ![L u₁, L u₂]
    have hΦ : ∀ x, Φ x = ![B u₁ x, B u₂ x] := fun x => by
      ext i
      fin_cases i <;> rfl
    have hind : LinearIndependent F ![u₁, u₂] := (LinearIndependent.pair_iff' hu₁0).2 hdep
    have hker : Submodule.span F (Set.range ![u₁, u₂]) ≤ LinearMap.ker Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · show Φ u₁ = 0
        rw [hΦ, h11, h21]
        ext j; fin_cases j <;> rfl
      · show Φ u₂ = 0
        rw [hΦ, h12, h22]
        ext j; fin_cases j <;> rfl
    have h2dim := finrank_span_eq_card hind
    simp only [Fintype.card_fin] at h2dim
    have hkdim := Submodule.finrank_mono hker
    have hrk := LinearMap.finrank_range_add_finrank_ker Φ
    have hr1 : finrank F (LinearMap.range Φ) ≤ 1 := by omega
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, Φ x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hu₁0 (hB.nondeg _ fun y => ?_)
      have := congrFun (hcon y) 0
      rw [hΦ] at this
      exact this
    have hsp : (F ∙ Φ x₀) = LinearMap.range Φ :=
      Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨x₀, rfl⟩)
        (by rw [finrank_span_singleton hx₀]; exact hr1)
    set p := B u₁ x₀
    set q := B u₂ x₀
    have hline : ∀ x, q * B u₁ x = p * B u₂ x := fun x => by
      have hx : Φ x ∈ (F ∙ Φ x₀) := hsp ▸ ⟨x, rfl⟩
      obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hx
      have e0 := congrFun hl 0
      have e1 := congrFun hl 1
      rw [hΦ, hΦ] at e0 e1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at e0 e1
      rw [← e0, ← e1]
      ring
    set v := q ^ 2 • u₁ - p ^ 2 • u₂
    have hv : v = 0 := hB.nondeg v fun x => by
      rw [hB.sub_left, hB.smul_left, hB.smul_left, ← pow_mul, ← pow_mul,
        show 2 * 2 = 4 by norm_num, h4, h4, hline x, ← two_mul, h2, zero_mul]
    rw [sub_eq_zero] at hv
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by
        intro hq
        apply hx₀
        rw [hΦ]
        ext j; fin_cases j
        · exact hp
        · exact hq
      rw [hp, zero_pow two_ne_zero, zero_smul] at hv
      exact hu₁0 ((smul_eq_zero.1 hv).resolve_left (pow_ne_zero 2 hq))
    · apply hdep ((p ^ 2)⁻¹ * q ^ 2)
      rw [← smul_smul, hv, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hp), one_smul]

private theorem card_linearEquiv_of_card_four {F M : Type*} [Field F] [Finite F] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] (hF : Nat.card F = 4) :
    Nat.card (M ≃ₗ[F] M) = ∏ i : Fin (finrank F M), (4 ^ finrank F M - 4 ^ (i : ℕ)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let b : Module.Basis (Fin (finrank F M)) F M := Module.finBasisOfFinrankEq F M rfl
  let e : GL (Fin (finrank F M)) F ≃* (M ≃ₗ[F] M) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F M)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF]

private theorem not_dvd_card_GL_four {n : ℕ} (hn : n ≤ 3) :
    ¬ 3 ^ 5 ∣ ∏ i : Fin n, (4 ^ n - 4 ^ (i : ℕ)) := by
  interval_cases n <;> simp [Fin.prod_univ_succ]

private theorem not_eleven_dvd_card_GL_four {n : ℕ} (hn : n ≤ 4) :
    ¬ 11 ∣ ∏ i : Fin n, (4 ^ n - 4 ^ (i : ℕ)) := by
  interval_cases n <;> simp [Fin.prod_univ_succ]

private theorem eq_one_of_central_of_not_prime4 {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) {a : Y} (ha : ∀ b, a * b = b * a) : a = 1 := by
  by_contra hne
  have hN : (Subgroup.zpowers a).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * a ^ k = a ^ k * g := ((Commute.zpow_left (ha g : Commute a g) k).eq).symm
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers a k⟩
  have htop := hN.eq_bot_or_eq_top.resolve_left (Subgroup.zpowers_ne_bot.2 hne)
  have hcomm : ∀ x y : Y, x * y = y * x := fun x y => by
    obtain ⟨i, rfl⟩ :=
      Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top x : x ∈ Subgroup.zpowers a)
    obtain ⟨j, rfl⟩ :=
      Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top y : y ∈ Subgroup.zpowers a)
    rw [← zpow_add, ← zpow_add, add_comm]
  have h1 : 1 < Nat.card Y := Finite.one_lt_card_iff_nontrivial.2 IsSimpleGroup.toNontrivial
  haveI : Fact (Nat.card Y).minFac.Prime := ⟨Nat.minFac_prime h1.ne'⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (Nat.card Y).minFac (Nat.minFac_dvd _)
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc
    exact (Fact.out : (Nat.card Y).minFac.Prime).one_lt.ne hc
  have hM : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    rw [hcomm g n, mul_inv_cancel_right]
    exact hn⟩
  have htop' := hM.eq_bot_or_eq_top.resolve_left (Subgroup.zpowers_ne_bot.2 hc1)
  have hcard : Nat.card (Subgroup.zpowers c) = Nat.card Y := by rw [htop', Subgroup.card_top]
  rw [Nat.card_zpowers, hc] at hcard
  exact hY (hcard ▸ Fact.out)

private theorem add_add_eq_zero_of_fpf4 {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {z : V ≃ₗ[F] V} (hz : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) (v : V) :
    z (z v) + z v + v = 0 := by
  have hz3 : z (z (z v)) = v := by
    have h := LinearEquiv.congr_fun hz v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  apply hfix
  rw [map_add, map_add, hz3]
  abel

private theorem eq_one_of_chain4 {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (hF : (2 : F) = 0)
    {g : V ≃ₗ[F] V} (hg : g ^ 3 = 1) {U₁ U₂ : Submodule F V} (h₁ : ∀ v ∈ U₁, g v = v)
    (h₂ : ∀ v ∈ U₂, g v - v ∈ U₁) (h₃ : ∀ v, g v - v ∈ U₂) : g = 1 := by
  have h2 : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul F x, hF, zero_smul]
  have hneg : ∀ x : V, -x = x := fun x => by rw [neg_eq_iff_add_eq_zero, h2]
  have hg3 : ∀ v, g (g (g v)) = v := fun v => by
    have h := LinearEquiv.congr_fun hg v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hfix2 : ∀ a, g (g a) = a → g a = a := fun a ha => by
    have := hg3 a
    rw [ha] at this
    exact this
  have hstep : ∀ a, g (g a - a) = g a - a → g a = a := fun a ha => by
    apply hfix2
    rw [map_sub] at ha
    have : g (g a) = g a + (g a - a) := by rw [← ha]; abel
    rw [this, ← add_sub_assoc, h2, zero_sub, hneg]
  refine LinearEquiv.ext fun v => ?_
  have ha := h₃ v
  have hb := h₂ _ ha
  have hc := h₁ _ hb
  exact hstep v (hstep _ hc)

private theorem sub_mem_of_simple_section4 {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 4) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V)) {z : V ≃ₗ[F] V}
    (hz : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) (hzα : ∀ y, z * α y = α y * z)
    {U U' : Submodule F V} (hU : ∀ y, ∀ v ∈ U, α y v ∈ U) (hU' : ∀ y, ∀ v ∈ U', α y v ∈ U')
    (hzU : ∀ v ∈ U, z v ∈ U) (hzU' : ∀ v ∈ U', z v ∈ U') (hle : U ≤ U')
    (hdim : finrank F U' ≤ finrank F U + 3) (y : Y) {v : V} (hv : v ∈ U') : α y v - v ∈ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2F : (2 : F) = 0 := by
    letI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
      (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
    exact_mod_cast CharP.cast_eq_zero F 2
  have hmap : ∀ {g : V ≃ₗ[F] V} {S : Submodule F V}, (∀ v ∈ S, g v ∈ S) →
      S.map (g : V →ₗ[F] V) = S := fun {g S} h => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq g S)
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have hinv : ∀ {g : V ≃ₗ[F] V} {S : Submodule F V}, (∀ v ∈ S, g v ∈ S) →
      ∀ v ∈ S, g⁻¹ v ∈ S := fun {g S} h v hv => by
    have hv' : v ∈ S.map (g : V →ₗ[F] V) := (hmap h).symm ▸ hv
    obtain ⟨u, hu, rfl⟩ := hv'
    simpa using hu
  let H : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {g | (∀ w ∈ U, g w ∈ U) ∧ ∀ w ∈ U', g w ∈ U'}
      one_mem' := ⟨fun w hw => hw, fun w hw => hw⟩
      mul_mem' := fun {a b} ha hb => ⟨fun w hw => ha.1 _ (hb.1 w hw),
        fun w hw => ha.2 _ (hb.2 w hw)⟩
      inv_mem' := fun {a} ha => ⟨hinv ha.1, hinv ha.2⟩ }
  have hmemU : ∀ h : H, ∀ w ∈ U, (h : V ≃ₗ[F] V) w ∈ U := fun h w hw => h.2.1 w hw
  have hmemU' : ∀ h : H, ∀ w ∈ U', (h : V ≃ₗ[F] V) w ∈ U' := fun h w hw => h.2.2 w hw
  have hαH : ∀ y, α y ∈ H := fun y => ⟨hU y, hU' y⟩
  have hzH : z ∈ H := ⟨hzU, hzU'⟩
  let σ := sectionRep H.subtype (fun h w hw => hmemU h w hw) (fun h w hw => hmemU' h w hw)
  let ρH := Representation.asGroupHom σ
  let αH : Y →* H := α.codRestrict H hαH
  let ρ : Y →* (Module.End F (U' ⧸ U.comap U'.subtype))ˣ := ρH.comp αH
  have hρ : ∀ y (w : U'), (((ρ y : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ) :
      Module.End F (U' ⧸ U.comap U'.subtype)) (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk w ↔ α y w - w ∈ U) := fun y w =>
    sectionRep_mk_eq_mk_iff H.subtype _ _ (αH y) w
  by_cases htriv : ∀ y, ρ y = 1
  · exact (hρ y ⟨v, hv⟩).1 (by rw [htriv y]; rfl)
  exfalso
  push Not at htriv
  obtain ⟨y₀, hy₀⟩ := htriv
  have hker : ρ.ker = ⊥ :=
    (ρ.normal_ker.eq_bot_or_eq_top).resolve_right fun h =>
      hy₀ (h ▸ Subgroup.mem_top y₀ : y₀ ∈ ρ.ker)
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  let zb := ρH ⟨z, hzH⟩
  have hzb3 : zb ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one ρH
    exact Subtype.ext hz
  have hcomm : ∀ y, ρ y * zb = zb * ρ y := fun y => by
    change ρH (αH y) * ρH ⟨z, hzH⟩ = ρH ⟨z, hzH⟩ * ρH (αH y)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzα y).symm
  have hzb1 : zb ≠ 1 := by
    intro h1
    have hsub : ∀ w ∈ U', w ∈ U := fun w hw => by
      have hfixb : ∀ x ∈ U', z x - x ∈ U := fun x hx => by
        have h' : σ ⟨z, hzH⟩ (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨x, hx⟩ :=
          congrArg (fun u : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ =>
            (u : Module.End F (U' ⧸ U.comap U'.subtype)) (Submodule.Quotient.mk ⟨x, hx⟩)) h1
        exact (sectionRep_mk_eq_mk_iff H.subtype _ _ ⟨z, hzH⟩ ⟨x, hx⟩).1 h'
      have h2' := hfixb (z w) (hzU' w hw)
      have h0 := add_add_eq_zero_of_fpf4 hz hfix w
      have e1 : z w + z w = 0 := by rw [← two_smul F (z w), h2F, zero_smul]
      have key : w = (z (z w) + z w + w) - (z (z w) - z w) - (z w + z w) := by abel
      rw [key, h0, e1]
      exact U.sub_mem (U.sub_mem U.zero_mem h2') U.zero_mem
    obtain ⟨s, hs⟩ : ∃ s, ((ρ y₀ : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ) :
        Module.End F (U' ⧸ U.comap U'.subtype)) s ≠ s := by
      by_contra hcon
      push Not at hcon
      exact hy₀ (Units.ext (LinearMap.ext fun s => (hcon s).trans rfl))
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ s
    have hwU : (w : V) ∈ U := hsub w w.2
    have h0 : (Submodule.Quotient.mk w : U' ⧸ U.comap U'.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hwU
    rw [h0, map_zero] at hs
    exact hs rfl
  have hord : orderOf zb = 3 := orderOf_eq_prime hzb3 hzb1
  have hcomm' : ∀ (y : Y) (c : Subgroup.zpowers zb), Commute (ρ y)
    ((Subgroup.zpowers zb).subtype c) :=
    fun y c => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 c.2
      rw [Subgroup.coe_subtype, ← hk]
      exact (Commute.zpow_right (hcomm y) k)
  let Ψ := ρ.noncommCoprod (Subgroup.zpowers zb).subtype hcomm'
  have hYp : ¬ (Nat.card Y).Prime := fun hp => by
    have h81 : 81 ∣ Nat.card Y := by simpa using hY
    rcases (Nat.dvd_prime hp).1 h81 with h | h
    · norm_num at h
    · rw [← h] at hp
      rcases hp.eq_one_or_self_of_dvd 3 (by norm_num) with h3 | h3 <;> norm_num at h3
  have hcenter : ∀ a : Y, (∀ b : Y, a * b = b * a) → a = 1 := fun a ha =>
    eq_one_of_central_of_not_prime4 hYp ha
  have hΨ : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, c⟩ hac
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hac
    have hρa : ρ a = ((c : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hac
    have ha1 : a = 1 := hcenter a fun b => by
      apply hρinj
      rw [map_mul, map_mul, hρa]
      exact ((hcomm' b c).inv_right).eq.symm
    subst ha1
    rw [map_one, one_mul] at hac
    exact (Prod.mk_eq_one.2 ⟨rfl, Subtype.ext hac⟩ : ((1 : Y), c) = 1) ▸ Subgroup.one_mem ⊥
  have hdvd : Nat.card (Y × Subgroup.zpowers zb) ∣
      Nat.card (Module.End F (U' ⧸ U.comap U'.subtype))ˣ := by
    rw [Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_prod, Nat.card_zpowers, hord,
    Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv F _).toEquiv,
    card_linearEquiv_of_card_four hF] at hdvd
  have hfin : finrank F (U' ⧸ U.comap U'.subtype) ≤ 3 := by
    have h1 := Submodule.finrank_quotient_add_finrank (U.comap U'.subtype)
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at h1
    omega
  exact not_dvd_card_GL_four hfin ((pow_succ 3 4 ▸ Nat.mul_dvd_mul_right hY 3).trans hdvd)

private theorem sub_mem_of_section4 {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 4) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V)) {U U' : Submodule F V}
    (hU : ∀ y, ∀ v ∈ U, α y v ∈ U) (hU' : ∀ y, ∀ v ∈ U', α y v ∈ U') (hle : U ≤ U')
    (hdim : finrank F U' ≤ finrank F U + 3) (y : Y) {v : V} (hv : v ∈ U') : α y v - v ∈ U := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ)
    (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
      exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hc0, hc1⟩ := hc
  have hc3 : c ^ 3 = 1 := by
    have h4 : c ^ 4 = c := by
      have := FiniteField.pow_card c
      rwa [← Nat.card_eq_fintype_card, hF] at this
    have : c * (c ^ 3 - 1) = 0 := by rw [mul_sub, ← pow_succ', h4, mul_one, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc0)
  let z : V ≃ₗ[F] V := LinearEquiv.smulOfNeZero F V c hc0
  have hz : ∀ v, z v = c • v := fun v => rfl
  refine sub_mem_of_simple_section4 hF hY α (z := z) ?_ ?_ ?_ hU hU' ?_ ?_ hle hdim y hv
  · refine LinearEquiv.ext fun v => ?_
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hz, hz, hz, smul_smul, smul_smul,
      ← pow_three', hc3, one_smul]
    rfl
  · intro v hv'
    rw [hz] at hv'
    have : (c - 1) • v = 0 := by rw [sub_smul, one_smul, hv', sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc1)
  · intro y'
    exact LinearEquiv.ext fun v => by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hz, hz, map_smul]
  · intro v hv'
    rw [hz]
    exact U.smul_mem c hv'
  · intro v hv'
    rw [hz]
    exact U'.smul_mem c hv'

private theorem false_of_commute_unitary {F V : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 4)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {B : V → V → F} (hB : IsHerm4 B)
    {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y)
    (α : Y →* (V ≃ₗ[F] V)) (hα : Function.Injective α) {U X : Submodule F V} (hUX : IsCompl U X)
    (hBUX : ∀ u ∈ U, ∀ x ∈ X, B u x = 0) (hU : finrank F U = 4) (hX : finrank F X ≤ 3)
    (hαU : ∀ y, ∀ u ∈ U, α y u ∈ U) (hαX : ∀ y, ∀ x ∈ X, α y x = x)
    {t₁ t₂ : V ≃ₗ[F] V} (hu₁ : ∀ x y, B (t₁ x) (t₁ y) = B x y)
    (hu₂ : ∀ x y, B (t₂ x) (t₂ y) = B x y) (ht₁ : ∀ v, t₁ (t₁ v) = v) (ht₂ : ∀ v, t₂ (t₂ v) = v)
    (h₁ : t₁ ≠ 1) (h₂ : t₂ ≠ 1) (h₁₂ : t₁ ≠ t₂) (hc : ∀ v, t₁ (t₂ v) = t₂ (t₁ v))
    (hα₁ : ∀ y, t₁ * α y = α y * t₁) (hα₂ : ∀ y, t₂ * α y = α y * t₂) : False := by
  classical
  have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have h2F : (2 : F) = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [hF]; norm_num)
    exact_mod_cast CharP.cast_eq_zero F 2
  have h2V : ∀ v : V, v + v = 0 := fun v => by rw [← two_smul F v, h2F, zero_smul]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₃, hy₃⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3
    ((dvd_pow_self 3 (by norm_num : 4 ≠ 0)).trans hY)
  have hy₃1 : α y₃ ≠ 1 := fun h => by
    have : y₃ = 1 := hα (h.trans (map_one α).symm)
    rw [this, orderOf_one] at hy₃
    norm_num at hy₃
  have hg3 : α y₃ ^ 3 = 1 := by rw [← map_pow, ← hy₃, pow_orderOf_eq_one, map_one]
  have hdecomp : ∀ v : V, ∃ u ∈ U, ∃ x ∈ X, v = u + x := fun v => by
    have : v ∈ U ⊔ X := hUX.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨u, hu, x, hx, rfl⟩
  have hchain : ∀ U₁ U₂ : Submodule F V, (∀ v ∈ U₁, α y₃ v = v) → (∀ v ∈ U₂, α y₃ v - v ∈ U₁) →
      (∀ u ∈ U, α y₃ u - u ∈ U₂) → False := fun U₁ U₂ h₁' h₂' h₃' => by
    apply hy₃1
    refine eq_one_of_chain4 h2F hg3 h₁' h₂' fun v => ?_
    obtain ⟨u, hu, x, hx, rfl⟩ := hdecomp v
    rw [map_add, hαX y₃ x hx, add_sub_add_right_eq_sub]
    exact h₃' u hu
  have hbot : ∀ y, ∀ v ∈ (⊥ : Submodule F V), α y v ∈ (⊥ : Submodule F V) := fun y v hv => by
    rw [(Submodule.mem_bot F).1 hv, map_zero]
    exact Submodule.zero_mem _
  let C : Submodule F V := U ⊓ ⨅ y : Y, LinearMap.ker ((α y : V →ₗ[F] V) - LinearMap.id)
  have hmemC : ∀ v, v ∈ C ↔ v ∈ U ∧ ∀ y, α y v = v := fun v => by
    simp [C, Submodule.mem_iInf, sub_eq_zero]
  have hC : C = ⊥ := by
    by_contra hne
    have hCpos : 0 < finrank F C := Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
    have hCinv : ∀ y, ∀ v ∈ C, α y v ∈ C := fun y v hv => by
      rw [((hmemC v).1 hv).2 y]
      exact hv
    refine hchain C C (fun v hv => ((hmemC v).1 hv).2 y₃) (fun v hv => ?_) (fun u hu => ?_)
    · rw [((hmemC v).1 hv).2 y₃, sub_self]
      exact Submodule.zero_mem _
    · exact sub_mem_of_section4 hF' hY α hCinv hαU inf_le_left (by omega) y₃ hu
  have hfixX : ∀ v, (∀ y, α y v = v) → v ∈ X := fun v hv => by
    obtain ⟨u, hu, x, hx, rfl⟩ := hdecomp v
    have hu' : u ∈ C := (hmemC u).2 ⟨hu, fun y => by
      have h := hv y
      rw [map_add, hαX y x hx] at h
      exact add_right_cancel h⟩
    rw [hC] at hu'
    rw [(Submodule.mem_bot F).1 hu', zero_add]
    exact hx
  have hpresX : ∀ {t : V ≃ₗ[F] V}, (∀ y, t * α y = α y * t) → ∀ x ∈ X, t x ∈ X :=
    fun {t} htα x hx => hfixX _ fun y => by
      have := LinearEquiv.congr_fun (htα y) x
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hαX y x hx] at this
      exact this.symm
  have hpresU : ∀ {t : V ≃ₗ[F] V}, (∀ x y, B (t x) (t y) = B x y) → (∀ v, t (t v) = v) →
      (∀ y, t * α y = α y * t) → ∀ u ∈ U, t u ∈ U := fun {t} hu ht htα u hu' => by
    obtain ⟨u', hu'', x', hx', he⟩ := hdecomp (t u)
    suffices x' = 0 by
      rw [he, this, add_zero]
      exact hu''
    apply hB.nondeg
    intro v
    obtain ⟨u₀, hu₀, x₀, hx₀, rfl⟩ := hdecomp v
    rw [hB.add_right]
    have e1 : B x' u₀ = 0 := by rw [hB.herm u₀ x', hBUX u₀ hu₀ x' hx', zero_pow two_ne_zero]
    have e2 : B x' x₀ = 0 := by
      have h0 : B (t u) x₀ = 0 := by
        have := hu u (t x₀)
        rw [ht] at this
        rw [this]
        exact hBUX u hu' _ (hpresX htα x₀ hx₀)
      rw [he, hB.add_left, hBUX u' hu'' x₀ hx₀, zero_add] at h0
      exact h0
    rw [e1, e2, add_zero]
  have htrivU : ∀ {t : V ≃ₗ[F] V}, (∀ x y, B (t x) (t y) = B x y) → (∀ v, t (t v) = v) →
      (∀ y, t * α y = α y * t) → ∀ u ∈ U, t u = u := fun {t} hu ht htα => by
    have hUt := hpresU hu ht htα
    have hcomm : ∀ y v, t (α y v) = α y (t v) := fun y v => by
      have := LinearEquiv.congr_fun (htα y) v
      rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    let N : U →ₗ[F] V := ((t : V →ₗ[F] V) - LinearMap.id).comp U.subtype
    have hN : ∀ u : U, N u = t u - u := fun u => rfl
    let I : Submodule F V := LinearMap.range N
    let Kr : Submodule F V := (LinearMap.ker N).map U.subtype
    have hmemI : ∀ v, v ∈ I ↔ ∃ u ∈ U, t u - u = v := fun v =>
      ⟨fun ⟨u, hu'⟩ => ⟨u, u.2, hu'⟩, fun ⟨u, hu', h⟩ => ⟨⟨u, hu'⟩, h⟩⟩
    have hmemKr : ∀ v, v ∈ Kr ↔ v ∈ U ∧ t v = v := fun v => by
      constructor
      · rintro ⟨u, hu', rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, hN, sub_eq_zero] at hu'
        exact ⟨u.2, hu'⟩
      · rintro ⟨hv, htv⟩
        exact ⟨⟨v, hv⟩, by rw [SetLike.mem_coe, LinearMap.mem_ker, hN, sub_eq_zero]; exact htv, rfl⟩
    have hrk : finrank F I + finrank F Kr = 4 := by
      rw [← hU, ← LinearMap.finrank_range_add_finrank_ker N,
        LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype U.injective_subtype
          (LinearMap.ker N)).symm]
    have hIK : I ≤ Kr := by
      intro v hv
      obtain ⟨u, hu', rfl⟩ := (hmemI v).1 hv
      refine (hmemKr _).2 ⟨U.sub_mem (hUt u hu') hu', ?_⟩
      rw [map_sub, ht, ← sub_eq_zero,
        show u - t u - (t u - u) = (u - t u) + (u - t u) by abel]
      exact h2V _
    by_contra hne
    push Not at hne
    obtain ⟨u₀, hu₀, hne₀⟩ := hne
    have hI0 : I ≠ ⊥ := fun h => by
      have : t u₀ - u₀ ∈ I := (hmemI _).2 ⟨u₀, hu₀, rfl⟩
      rw [h, Submodule.mem_bot, sub_eq_zero] at this
      exact hne₀ this
    have hIpos : 0 < finrank F I := Nat.pos_of_ne_zero fun h => hI0 (Submodule.finrank_eq_zero.1 h)
    have hIle := Submodule.finrank_mono hIK
    have hIinv : ∀ y, ∀ v ∈ I, α y v ∈ I := fun y v hv => by
      obtain ⟨u, hu', rfl⟩ := (hmemI v).1 hv
      exact (hmemI _).2 ⟨α y u, hαU y u hu', by rw [map_sub, hcomm]⟩
    have hKrinv : ∀ y, ∀ v ∈ Kr, α y v ∈ Kr := fun y v hv => by
      obtain ⟨hvU, htv⟩ := (hmemKr v).1 hv
      exact (hmemKr _).2 ⟨hαU y v hvU, by rw [hcomm, htv]⟩
    refine hchain I Kr (fun v hv => ?_) (fun v hv => ?_) (fun u hu' => ?_)
    · have h := sub_mem_of_section4 hF' hY α hbot hIinv bot_le (by simp; omega) y₃ hv
      rwa [Submodule.mem_bot, sub_eq_zero] at h
    · exact sub_mem_of_section4 hF' hY α hIinv hKrinv hIK (by omega) y₃ hv
    · exact sub_mem_of_section4 hF' hY α hKrinv hαU (fun v hv => ((hmemKr v).1 hv).1)
        (by omega) y₃ hu'
  have hU₁ := htrivU hu₁ ht₁ hα₁
  have hU₂ := htrivU hu₂ ht₂ hα₂
  have hmapX : ∀ {t : V ≃ₗ[F] V}, (∀ x ∈ X, t x ∈ X) → X.map (t : V →ₗ[F] V) = X :=
    fun {t} h => by
      refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq t X)
      rintro _ ⟨w, hw, rfl⟩
      exact h w hw
  let s₁ : X ≃ₗ[F] X := LinearEquiv.ofSubmodules t₁ X X (hmapX (hpresX hα₁))
  let s₂ : X ≃ₗ[F] X := LinearEquiv.ofSubmodules t₂ X X (hmapX (hpresX hα₂))
  have hs₁ : ∀ x : X, (s₁ x : V) = t₁ x := fun x => rfl
  have hs₂ : ∀ x : X, (s₂ x : V) = t₂ x := fun x => rfl
  let B' : X → X → F := fun a b => B a b
  have hB' : IsHerm4 B' :=
    { add_left := fun a b c => by
        simp only [B', Submodule.coe_add]
        exact hB.add_left _ _ _
      smul_left := fun c a b => by
        simp only [B', Submodule.coe_smul]
        exact hB.smul_left _ _ _
      add_right := fun a b c => by
        simp only [B', Submodule.coe_add]
        exact hB.add_right _ _ _
      smul_right := fun c a b => by
        simp only [B', Submodule.coe_smul]
        exact hB.smul_right _ _ _
      herm := fun a b => hB.herm _ _
      nondeg := fun a ha => by
        have : (a : V) = 0 := hB.nondeg _ fun v => by
          obtain ⟨u, hu, x, hx, rfl⟩ := hdecomp v
          have hx' : B a x = 0 := ha ⟨x, hx⟩
          rw [hB.add_right, hx', add_zero, hB.herm u a, hBUX u hu a a.2, zero_pow two_ne_zero]
        exact Subtype.ext this }
  have hne : ∀ {t : V ≃ₗ[F] V}, t ≠ 1 → (∀ u ∈ U, t u = u) → ∃ x ∈ X, t x ≠ x :=
    fun {t} h1 hUt => by
      by_contra hcon
      push Not at hcon
      apply h1
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨u, hu, x, hx, rfl⟩ := hdecomp v
      rw [map_add, hUt u hu, hcon x hx]
      rfl
  obtain ⟨x₁, hx₁, hx₁'⟩ := hne h₁ hU₁
  obtain ⟨x₂, hx₂, hx₂'⟩ := hne h₂ hU₂
  have heq := eq_of_commute_unitary_involutions hF hX hB' (t₁ := s₁) (t₂ := s₂)
    (fun a b => hu₁ a b) (fun a b => hu₂ a b) (fun a => Subtype.ext (ht₁ a))
    (fun a => Subtype.ext (ht₂ a))
    ⟨⟨x₁, hx₁⟩, fun h => hx₁' (congrArg Subtype.val h)⟩
    ⟨⟨x₂, hx₂⟩, fun h => hx₂' (congrArg Subtype.val h)⟩ (fun a => Subtype.ext (hc a))
  apply h₁₂
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, x, hx, rfl⟩ := hdecomp v
  have hxx : t₁ x = t₂ x := by
    have := congrArg Subtype.val (heq ⟨x, hx⟩)
    rwa [hs₁, hs₂] at this
  rw [map_add, map_add, hU₁ u hu, hU₂ u hu, hxx]

private def cubeProj {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (g : V →ₗ[F] V) (c : F) : V →ₗ[F] V :=
  LinearMap.id + c ^ 2 • g + c • (g ∘ₗ g)

private theorem cubeProj_apply {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (g : V →ₗ[F] V) (c : F) (v : V) :
    cubeProj g c v = v + c ^ 2 • g v + c • g (g v) := rfl

private theorem apply_cubeProj {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {g : V →ₗ[F] V} (hg : ∀ v, g (g (g v)) = v) {c : F} (hc : c ^ 3 = 1)
    (v : V) : g (cubeProj g c v) = c • cubeProj g c v := by
  rw [cubeProj_apply, map_add, map_add, map_smul, map_smul, hg, smul_add, smul_add, smul_smul,
    smul_smul, show c * c ^ 2 = c ^ 3 by ring, hc, one_smul, show c * c = c ^ 2 by ring]
  abel

private theorem cubeProj_of_eigen {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : (2 : F) = 0) {g : V →ₗ[F] V} {c : F} (hc : c ^ 3 = 1) {v : V}
    (hv : g v = c • v) : cubeProj g c v = v := by
  have h2V : v + v = 0 := by rw [← two_smul F v, h2, zero_smul]
  rw [cubeProj_apply, hv, map_smul, hv, smul_smul, smul_smul, smul_smul,
    show c ^ 2 * c = c ^ 3 by ring, show c * c * c = c ^ 3 by ring, hc, one_smul, add_assoc,
    h2V, add_zero]

private theorem cubeProj_idem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : (2 : F) = 0) {g : V →ₗ[F] V} (hg : ∀ v, g (g (g v)) = v) {c : F}
    (hc : c ^ 3 = 1) (v : V) : cubeProj g c (cubeProj g c v) = cubeProj g c v :=
  cubeProj_of_eigen h2 hc (apply_cubeProj hg hc v)

private theorem isIdempotentElem_cubeProj {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : (2 : F) = 0) {g : V →ₗ[F] V} (hg : ∀ v, g (g (g v)) = v)
    {c : F} (hc : c ^ 3 = 1) : IsIdempotentElem (cubeProj g c) :=
  LinearMap.ext fun v => cubeProj_idem h2 hg hc v

private theorem cubeProj_sum {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : (2 : F) = 0) {g : V →ₗ[F] V} {ω : F} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (v : V) : cubeProj g 1 v + cubeProj g ω v + cubeProj g (ω ^ 2) v = v := by
  have hs : 1 + ω + ω ^ 2 = 0 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  have h4 : ω ^ 4 = ω := by linear_combination ω * hω
  have h3V : ∀ x : V, x + x + x = x := fun x => by
    rw [← two_smul F x, h2, zero_smul, zero_add]
  simp only [cubeProj_apply]
  have e1 : (1 : F) ^ 2 • g v + ω ^ 2 • g v + (ω ^ 2) ^ 2 • g v = (1 + ω + ω ^ 2) • g v := by
    rw [← add_smul, ← add_smul, one_pow, show (ω ^ 2) ^ 2 = ω ^ 4 by ring, h4]
    congr 1
    ring
  have e2 : (1 : F) • g (g v) + ω • g (g v) + ω ^ 2 • g (g v) = (1 + ω + ω ^ 2) • g (g v) := by
    rw [← add_smul, ← add_smul]
  calc v + (1 : F) ^ 2 • g v + (1 : F) • g (g v) + (v + ω ^ 2 • g v + ω • g (g v)) +
        (v + (ω ^ 2) ^ 2 • g v + ω ^ 2 • g (g v))
      = (v + v + v) + ((1 : F) ^ 2 • g v + ω ^ 2 • g v + (ω ^ 2) ^ 2 • g v) +
        ((1 : F) • g (g v) + ω • g (g v) + ω ^ 2 • g (g v)) := by abel
    _ = v := by rw [e1, e2, hs, zero_smul, zero_smul, add_zero, add_zero, h3V]

private theorem cubeProj_comm {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {g h : V →ₗ[F] V} (hgh : ∀ v, h (g v) = g (h v)) (c : F) (v : V) :
    h (cubeProj g c v) = cubeProj g c (h v) := by
  rw [cubeProj_apply, cubeProj_apply, map_add, map_add, map_smul, map_smul, hgh, hgh, hgh]

private theorem cubeProj_adjoint {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {B : V → V → F} (hB : IsHerm4 B) {g : V →ₗ[F] V}
    (hg : ∀ v, g (g (g v)) = v) (hgu : ∀ x y, B (g x) (g y) = B x y) {c : F} (hc : c ^ 3 = 1)
    (x y : V) : B (cubeProj g c x) y = B x (cubeProj g c y) := by
  have e1 : B (g x) y = B x (g (g y)) := by
    conv_lhs => rw [← hg y]
    exact hgu x (g (g y))
  have e2 : B (g (g x)) y = B x (g y) := by
    conv_lhs => rw [← hg y]
    rw [hgu, hgu]
  rw [cubeProj_apply, cubeProj_apply, hB.add_left, hB.add_left, hB.smul_left, hB.smul_left,
    hB.add_right, hB.add_right, hB.smul_right, hB.smul_right, e1, e2,
    show (c ^ 2) ^ 2 = c * c ^ 3 by ring, hc, mul_one]
  ring

private theorem eq_of_mem_of_not_dvd {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 4) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] {d : ℕ} (hd : d ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V))
    {E : Submodule F V} (hE : ∀ y, ∀ v ∈ E, α y v ∈ E)
    (hGL : ¬ d ∣ ∏ i : Fin (finrank F E), (4 ^ finrank F E - 4 ^ (i : ℕ))) (y : Y) {v : V}
    (hv : v ∈ E) : α y v = v := by
  classical
  have hmap : ∀ y, E.map ((α y : V ≃ₗ[F] V) : V →ₗ[F] V) = E := fun y => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq (α y) E)
    rintro _ ⟨w, hw, rfl⟩
    exact hE y w hw
  let ρ : Y →* (E ≃ₗ[F] E) :=
    { toFun := fun y => LinearEquiv.ofSubmodules (α y) E E (hmap y)
      map_one' := by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        rw [LinearEquiv.ofSubmodules_apply, map_one]
        rfl
      map_mul' := fun a b => by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        rw [LinearEquiv.ofSubmodules_apply, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          LinearEquiv.ofSubmodules_apply, LinearEquiv.ofSubmodules_apply] }
  have hρ : ∀ y (x : E), ((ρ y x : E) : V) = α y x := fun y x => rfl
  by_cases htriv : ∀ y, ρ y = 1
  · have := congrArg (fun e : E ≃ₗ[F] E => ((e ⟨v, hv⟩ : E) : V)) (htriv y)
    simpa [hρ] using this
  exfalso
  push Not at htriv
  obtain ⟨y₀, hy₀⟩ := htriv
  have hker : ρ.ker = ⊥ := (ρ.normal_ker.eq_bot_or_eq_top).resolve_right fun h =>
    hy₀ (h ▸ Subgroup.mem_top y₀ : y₀ ∈ ρ.ker)
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  have hdvd : Nat.card Y ∣ Nat.card (E ≃ₗ[F] E) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [card_linearEquiv_of_card_four hF] at hdvd
  exact hGL (hd.trans hdvd)

private theorem det_smul_add_one_sub {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {e : V →ₗ[F] V} (he : IsIdempotentElem e) (c : F) :
    LinearMap.det (c • e + (1 - e)) = c ^ finrank F (LinearMap.range e) := by
  set f : V →ₗ[F] V := c • e + (1 - e)
  have hcompl := LinearMap.IsIdempotentElem.isCompl he
  let eq := Submodule.prodEquivOfIsCompl _ _ hcompl
  have heR : ∀ x ∈ LinearMap.range e, e x = x := fun x hx =>
    (LinearMap.IsIdempotentElem.mem_range_iff he).1 hx
  have hconj : eq.symm.toLinearMap ∘ₗ f ∘ₗ eq.symm.symm.toLinearMap =
      LinearMap.prodMap (c • LinearMap.id) LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨a, b⟩ := p
    rw [LinearEquiv.symm_symm, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl',
      LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl']
    have ha : e a = a := heR a a.2
    have hb : e b = 0 := LinearMap.mem_ker.1 b.2
    simp only [f, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_add, ha, hb, LinearMap.id_apply, Submodule.coe_smul, smul_zero,
      zero_add]
    abel
  have := LinearMap.det_conj f eq.symm
  rw [hconj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id,
    mul_one, mul_one] at this
  exact this.symm

private theorem false_of_unitary_blocks {F V : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 4)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (hV : finrank F V ≤ 7)
    {B : V → V → F} (hB : IsHerm4 B) {z : V ≃ₗ[F] V} (hzu : ∀ x y, B (z x) (z y) = B x y)
    (hz3 : ∀ v, z (z (z v)) = v) (hzs : ∀ c : F, ∃ v, z v ≠ c • v)
    {Y₀ : Type*} [Group Y₀] [Finite Y₀] [IsSimpleGroup Y₀] (h11 : 11 ∣ Nat.card Y₀)
    (h3 : 3 ∣ Nat.card Y₀) (β : Y₀ →* (V ≃ₗ[F] V)) (hβ : Function.Injective β)
    (hβz : ∀ y v, β y (z v) = z (β y v)) {w : Y₀} (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hwu : ∀ x x', B (β w x) (β w x') = B x x')
    {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y)
    (γ : Y →* Y₀) (hγ : Function.Injective γ) (hγw : ∀ y, γ y * w = w * γ y)
    {t₁ t₂ : V ≃ₗ[F] V} (hu₁ : ∀ x y, B (t₁ x) (t₁ y) = B x y)
    (hu₂ : ∀ x y, B (t₂ x) (t₂ y) = B x y) (ht₁ : ∀ v, t₁ (t₁ v) = v) (ht₂ : ∀ v, t₂ (t₂ v) = v)
    (h₁ : t₁ ≠ 1) (h₂ : t₂ ≠ 1) (h₁₂ : t₁ ≠ t₂) (hc : ∀ v, t₁ (t₂ v) = t₂ (t₁ v))
    (hα₁ : ∀ y, t₁ * β (γ y) = β (γ y) * t₁) (hα₂ : ∀ y, t₂ * β (γ y) = β (γ y) * t₂) :
    False := by
  classical
  have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have h2F : (2 : F) = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [hF]; norm_num)
    exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ)
    (by rw [Finset.card_univ, hF]; exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨hω0, hω1⟩ := hω
  have hcube : ∀ c : F, c ≠ 0 → c ^ 3 = 1 := fun c hc0 => by
    have h4 : c ^ 4 = c := by
      have := FiniteField.pow_card c
      rwa [hF] at this
    have : c * (c ^ 3 - 1) = 0 := by rw [mul_sub, ← pow_succ', h4, mul_one, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc0)
  have hω3 := hcube ω hω0
  have hω23 : (ω ^ 2) ^ 3 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  have h13 : (1 : F) ^ 3 = 1 := one_pow 3
  let α : Y →* (V ≃ₗ[F] V) := β.comp γ
  have hα : Function.Injective α := hβ.comp hγ
  have hαβ : ∀ y, α y = β (γ y) := fun y => rfl
  have hwh3 : ∀ v, β w (β w (β w v)) = v := fun v => by
    have : β w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
    have h := LinearEquiv.congr_fun this v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hwz : ∀ v, β w (z v) = z (β w v) := hβz w
  have hαw : ∀ y v, α y (β w v) = β w (α y v) := fun y v => by
    have := LinearEquiv.congr_fun (congrArg β (hγw y)) v
    rwa [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
  let zl : V →ₗ[F] V := z
  let wl : V →ₗ[F] V := β w
  have hzl : ∀ v, zl v = z v := fun v => rfl
  have hwl : ∀ v, wl v = β w v := fun v => rfl
  have hPz : ∀ c : F, c ^ 3 = 1 → ∀ v, z (cubeProj zl c v) = c • cubeProj zl c v :=
    fun c hc v => apply_cubeProj hz3 hc v
  have hPw : ∀ c : F, c ^ 3 = 1 → ∀ v, β w (cubeProj wl c v) = c • cubeProj wl c v :=
    fun c hc v => apply_cubeProj hwh3 hc v
  have hPidem : ∀ c : F, c ^ 3 = 1 → ∀ v, cubeProj zl c (cubeProj zl c v) = cubeProj zl c v :=
    fun c hc v => cubeProj_idem h2F hz3 hc v
  have hQidem : ∀ c : F, c ^ 3 = 1 → ∀ v, cubeProj wl c (cubeProj wl c v) = cubeProj wl c v :=
    fun c hc v => cubeProj_idem h2F hwh3 hc v
  have hPβ : ∀ y c v, β y (cubeProj zl c v) = cubeProj zl c (β y v) := fun y c v =>
    cubeProj_comm (h := (β y : V →ₗ[F] V)) (fun u => hβz y u) c v
  have hPα : ∀ y c v, α y (cubeProj zl c v) = cubeProj zl c (α y v) := fun y c v => hPβ (γ y) c v
  have hQα : ∀ y c v, α y (cubeProj wl c v) = cubeProj wl c (α y v) := fun y c v =>
    cubeProj_comm (h := (α y : V →ₗ[F] V)) (fun u => hαw y u) c v
  have hQw : ∀ c v, β w (cubeProj wl c v) = cubeProj wl c (β w v) := fun c v =>
    cubeProj_comm (h := (β w : V →ₗ[F] V)) (fun u => rfl) c v
  have hPw' : ∀ c v, β w (cubeProj zl c v) = cubeProj zl c (β w v) := fun c v => hPβ w c v
  have hPQ : ∀ c d v, cubeProj wl d (cubeProj zl c v) = cubeProj zl c (cubeProj wl d v) :=
    fun c d v => cubeProj_comm (h := cubeProj wl d)
      (fun u => (cubeProj_comm (h := zl) (fun x => (hwz x).symm) d u).symm) c v
  have hbot : ∀ y, ∀ v ∈ (⊥ : Submodule F V), α y v ∈ (⊥ : Submodule F V) := fun y v hv => by
    rw [(Submodule.mem_bot F).1 hv, map_zero]
    exact Submodule.zero_mem _
  have hsmall11 : ∀ E : Submodule F V, (∀ y, ∀ v ∈ E, β y v ∈ E) → finrank F E ≤ 4 →
      ∀ y, ∀ v ∈ E, β y v = v := fun E hE hd y v hv =>
    eq_of_mem_of_not_dvd hF' h11 β hE (not_eleven_dvd_card_GL_four hd) y hv
  have hsmall3 : ∀ E : Submodule F V, (∀ y, ∀ v ∈ E, α y v ∈ E) → finrank F E ≤ 3 →
      ∀ y, ∀ v ∈ E, α y v = v := fun E hE hd y v hv => by
    have h := sub_mem_of_section4 hF' hY α hbot hE bot_le (by simp; omega) y hv
    rwa [Submodule.mem_bot, sub_eq_zero] at h
  have hY₀nt : ∃ y v, β y v ≠ v := by
    obtain ⟨y, hy⟩ := exists_ne (1 : Y₀)
    have : β y ≠ 1 := fun h => hy (hβ (h.trans (map_one β).symm))
    by_contra hcon
    push Not at hcon
    exact this (LinearEquiv.ext fun v => (hcon y v).trans rfl)
  have hPinv : ∀ c y, ∀ v ∈ LinearMap.range (cubeProj zl c),
      β y v ∈ LinearMap.range (cubeProj zl c) := fun c y v hv => by
    obtain ⟨u, rfl⟩ := hv
    exact ⟨β y u, (hPβ y c u).symm⟩
  obtain ⟨c₀, hc₀3, y₀, v₀, hv₀, hβv₀⟩ : ∃ c₀ : F, c₀ ^ 3 = 1 ∧
      ∃ y, ∃ v ∈ LinearMap.range (cubeProj zl c₀), β y v ≠ v := by
    obtain ⟨y, v, hv⟩ := hY₀nt
    have hsum := cubeProj_sum h2F (g := zl) hω3 hω1 v
    by_contra hcon
    push Not at hcon
    apply hv
    have e1 := hcon 1 h13 y _ ⟨v, rfl⟩
    have e2 := hcon ω hω3 y _ ⟨v, rfl⟩
    have e3 := hcon (ω ^ 2) hω23 y _ ⟨v, rfl⟩
    calc β y v = β y (cubeProj zl 1 v + cubeProj zl ω v + cubeProj zl (ω ^ 2) v) := by
          rw [hsum]
      _ = v := by rw [map_add, map_add, e1, e2, e3, hsum]
  have hS₀ : 5 ≤ finrank F (LinearMap.range (cubeProj zl c₀)) := by
    by_contra hlt
    exact hβv₀ (hsmall11 _ (hPinv c₀) (by omega) y₀ v₀ hv₀)
  have hP₀idem : IsIdempotentElem (cubeProj zl c₀) := isIdempotentElem_cubeProj h2F hz3 hc₀3
  have hdimP₀ := Submodule.finrank_add_eq_of_isCompl (LinearMap.IsIdempotentElem.isCompl hP₀idem)
  have hK₀ : LinearMap.ker (cubeProj zl c₀) ≠ ⊥ := by
    intro h
    obtain ⟨v, hv⟩ := hzs c₀
    apply hv
    have hinj : Function.Injective (cubeProj zl c₀) := LinearMap.ker_eq_bot.1 h
    have hPv : cubeProj zl c₀ v = v := hinj (hPidem c₀ hc₀3 v)
    rw [← hPv]
    exact hPz c₀ hc₀3 v
  have hK₀pos : 1 ≤ finrank F (LinearMap.ker (cubeProj zl c₀)) :=
    Nat.one_le_iff_ne_zero.2 fun h => hK₀ (Submodule.finrank_eq_zero.1 h)
  have hK₀inv : ∀ y, ∀ v ∈ LinearMap.ker (cubeProj zl c₀),
      β y v ∈ LinearMap.ker (cubeProj zl c₀) := fun y v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hPβ, hv, map_zero]
  have hβK₀ : ∀ y, ∀ v ∈ LinearMap.ker (cubeProj zl c₀), β y v = v := fun y v hv =>
    hsmall11 _ hK₀inv (by omega) y v hv
  have hsubK : ∀ v, v - cubeProj zl c₀ v ∈ LinearMap.ker (cubeProj zl c₀) := fun v => by
    rw [LinearMap.mem_ker, map_sub, hPidem c₀ hc₀3, sub_self]
  have hYnt : ∃ y v, α y v ≠ v := by
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    have : α y ≠ 1 := fun h => hy (hα (h.trans (map_one α).symm))
    by_contra hcon
    push Not at hcon
    exact this (LinearEquiv.ext fun v => (hcon y v).trans rfl)
  obtain ⟨μ₁, hμ₁3, y₁, v₁, hv₁⟩ : ∃ μ : F, μ ^ 3 = 1 ∧ ∃ y v,
      α y (cubeProj wl μ (cubeProj zl c₀ v)) ≠ cubeProj wl μ (cubeProj zl c₀ v) := by
    obtain ⟨y, v, hv⟩ := hYnt
    have hk : α y (v - cubeProj zl c₀ v) = v - cubeProj zl c₀ v := hβK₀ (γ y) _ (hsubK v)
    have hsum := cubeProj_sum h2F (g := wl) hω3 hω1 (cubeProj zl c₀ v)
    by_contra hcon
    push Not at hcon
    apply hv
    have e1 := hcon 1 h13 y v
    have e2 := hcon ω hω3 y v
    have e3 := hcon (ω ^ 2) hω23 y v
    have hP : α y (cubeProj zl c₀ v) = cubeProj zl c₀ v := by
      rw [← hsum, map_add, map_add, e1, e2, e3]
    calc α y v = α y (cubeProj zl c₀ v + (v - cubeProj zl c₀ v)) := by rw [add_sub_cancel]
      _ = v := by rw [map_add, hP, hk, add_sub_cancel]
  let R : V →ₗ[F] V := cubeProj wl μ₁ ∘ₗ cubeProj zl c₀
  have hR : ∀ v, R v = cubeProj wl μ₁ (cubeProj zl c₀ v) := fun v => rfl
  have hRidem : IsIdempotentElem R := LinearMap.ext fun v => by
    show R (R v) = R v
    rw [hR, hR, ← hPQ, hPidem c₀ hc₀3, hQidem μ₁ hμ₁3]
  have hRcompl := LinearMap.IsIdempotentElem.isCompl hRidem
  have hdimR := Submodule.finrank_add_eq_of_isCompl hRcompl
  have hRα : ∀ y v, α y (R v) = R (α y v) := fun y v => by rw [hR, hR, hQα, hPα]
  have hUinv : ∀ y, ∀ v ∈ LinearMap.range R, α y v ∈ LinearMap.range R := fun y v hv => by
    obtain ⟨u, rfl⟩ := hv
    exact ⟨α y u, (hRα y u).symm⟩
  have hU4 : 4 ≤ finrank F (LinearMap.range R) := by
    by_contra hlt
    exact hv₁ (hsmall3 _ hUinv (by omega) y₁ _ ⟨v₁, rfl⟩)
  have hUS₀ : LinearMap.range R ≤ LinearMap.range (cubeProj zl c₀) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨cubeProj wl μ₁ u, by rw [hR, hPQ]⟩
  have hUle := Submodule.finrank_mono hUS₀
  have hwU : ∀ x ∈ LinearMap.range R, β w x = μ₁ • x := by
    rintro _ ⟨u, rfl⟩
    rw [hR]
    exact hPw μ₁ hμ₁3 _
  have hY₀p : ¬ (Nat.card Y₀).Prime := fun hp => by
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h
    · norm_num at h
    · rw [← h] at h11
      norm_num at h11
  have hU : finrank F (LinearMap.range R) = 4 := by
    by_contra hne
    by_cases heq : finrank F (LinearMap.range R) = finrank F (LinearMap.range (cubeProj zl c₀))
    ·
      have hUeq := Submodule.eq_of_le_of_finrank_eq hUS₀ heq
      apply hw1
      refine eq_one_of_central_of_not_prime4 hY₀p fun y => hβ ?_
      refine LinearEquiv.ext fun v => ?_
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have hsplit : v = cubeProj zl c₀ v + (v - cubeProj zl c₀ v) := by rw [add_sub_cancel]
      have hS : ∀ x ∈ LinearMap.range (cubeProj zl c₀), β w x = μ₁ • x := fun x hx =>
        hwU x (hUeq ▸ hx)
      rw [hsplit, map_add, map_add, map_add, map_add, hS _ ⟨v, rfl⟩,
        hβK₀ w _ (hsubK v), hS _ (hPinv c₀ y _ ⟨v, rfl⟩), hβK₀ w _ (hK₀inv y _ (hsubK v)),
        map_smul]
    ·
      have h5 : finrank F (LinearMap.range R) = 5 := by omega
      have h6 : finrank F (LinearMap.range (cubeProj zl c₀)) = 6 := by omega
      let E' : V →ₗ[F] V := cubeProj zl c₀ - R
      have hE' : ∀ v, E' v = cubeProj zl c₀ v - R v := fun v => rfl
      have hRP : ∀ v, R (cubeProj zl c₀ v) = R v := fun v => by rw [hR, hR, hPidem c₀ hc₀3]
      have hPR : ∀ v, cubeProj zl c₀ (R v) = R v := fun v => by
        rw [hR, ← hPQ, hPidem c₀ hc₀3]
      have hRR : ∀ v, R (R v) = R v := fun v => by
        rw [hR, hR, ← hPQ, hPidem c₀ hc₀3, hQidem μ₁ hμ₁3]
      have hRE : ∀ v, R (E' v) = 0 := fun v => by
        rw [hE', map_sub, hRP, hRR, sub_self]
      have hE'idem : IsIdempotentElem E' := LinearMap.ext fun v => by
        show E' (E' v) = E' v
        have h1 : E' (E' v) = cubeProj zl c₀ (E' v) - R (E' v) := rfl
        rw [h1, hRE, sub_zero, hE', map_sub, hPidem c₀ hc₀3, hPR]
      have hLU : LinearMap.range E' ⊓ LinearMap.range R = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
        have : R (E' a) = E' a := by
          rw [← hb, hRR]
        rw [Submodule.mem_bot, ← this, hRE]
      have hLS₀ : LinearMap.range E' ≤ LinearMap.range (cubeProj zl c₀) := by
        rintro _ ⟨a, rfl⟩
        exact ⟨E' a, by rw [hE', map_sub, hPidem c₀ hc₀3, hPR]⟩
      have hsupS₀ : LinearMap.range E' ⊔ LinearMap.range R ≤ LinearMap.range (cubeProj zl c₀) :=
        sup_le hLS₀ hUS₀
      have hsum' := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range E')
        (LinearMap.range R)
      rw [hLU, finrank_bot, add_zero] at hsum'
      have hsuple := Submodule.finrank_mono hsupS₀
      have hL1 : finrank F (LinearMap.range E') ≤ 1 := by omega
      have hL0 : E' ≠ 0 := by
        intro h0
        have : cubeProj zl c₀ = R := sub_eq_zero.1 h0
        rw [this] at h6
        omega
      have hLpos : 1 ≤ finrank F (LinearMap.range E') := by
        refine Nat.one_le_iff_ne_zero.2 fun h => hL0 ?_
        rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
        exact h
      have hL : finrank F (LinearMap.range E') = 1 := le_antisymm hL1 hLpos
      have hwE' : ∀ v, β w (E' v) = E' (β w v) := fun v => by
        rw [hE', hE', map_sub, hPw', hR, hR, hQw, hPw']
      obtain ⟨ℓ, hℓ0, hℓ⟩ := finrank_eq_one_iff'.1 hL
      obtain ⟨ν, hν⟩ := hℓ ⟨β w ℓ, by
        obtain ⟨a, ha⟩ := ℓ.2
        exact ⟨β w a, by rw [← hwE', ha]⟩⟩
      have hwL : ∀ v, β w (E' v) = ν • E' v := fun v => by
        obtain ⟨a, ha⟩ := hℓ ⟨E' v, ⟨v, rfl⟩⟩
        have ha' : E' v = a • (ℓ : V) := (congrArg Subtype.val ha).symm
        have hν' : β w ℓ = ν • (ℓ : V) := (congrArg Subtype.val hν).symm
        rw [ha', map_smul, hν', smul_comm]
      have hνμ : ν ≠ μ₁ := by
        intro hνμ
        apply hℓ0
        obtain ⟨a, ha⟩ := ℓ.2
        have hl : (ℓ : V) = E' a := ha.symm
        have hw : β w (ℓ : V) = μ₁ • (ℓ : V) := by rw [hl, hwL, hνμ]
        have hQ : cubeProj wl μ₁ (ℓ : V) = ℓ := cubeProj_of_eigen h2F hμ₁3 hw
        have hPl : cubeProj zl c₀ (ℓ : V) = ℓ := by
          rw [hl, hE', map_sub, hPidem c₀ hc₀3, hPR]
        have hRl : R (ℓ : V) = ℓ := by rw [hR, hPl, hQ]
        apply Subtype.ext
        rw [Submodule.coe_zero, ← hRl, hl, hRE]
      have hfac : (β w : V →ₗ[F] V) = (μ₁ • R + (1 - R)) ∘ₗ (ν • E' + (1 - E')) := by
        refine LinearMap.ext fun v => ?_
        have hsplit : v = R v + E' v + (v - cubeProj zl c₀ v) := by rw [hE']; abel
        have hRv : R (ν • E' v + (v - E' v)) = R v := by
          rw [map_add, map_smul, map_sub, hRE, smul_zero, zero_add, sub_zero]
        have hrhs : ((μ₁ • R + (1 - R)) ∘ₗ (ν • E' + (1 - E'))) v =
            μ₁ • R v + (ν • E' v + (v - E' v) - R v) := by
          simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
            LinearMap.sub_apply, Module.End.one_apply]
          rw [hRv]
        rw [hrhs, LinearEquiv.coe_coe]
        conv_lhs => rw [hsplit]
        rw [map_add, map_add, hwU _ ⟨v, rfl⟩, hwL, hβK₀ w _ (hsubK v), hE']
        abel
      have hdet1 : LinearMap.det (β w : V →ₗ[F] V) = 1 := by
        have hker : ⁅(⊤ : Subgroup Y₀), (⊤ : Subgroup Y₀)⁆ = ⊤ := by
          refine (Subgroup.commutator_normal (⊤ : Subgroup Y₀) ⊤).eq_bot_or_eq_top.resolve_left
            fun h => hY₀p ?_
          have hc : ∀ a b : Y₀, a * b = b * a := fun a b => by
            have : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Y₀), (⊤ : Subgroup Y₀)⁆ :=
              Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
            rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
            exact this
          letI : CommGroup Y₀ := { ‹Group Y₀› with mul_comm := hc }
          exact IsSimpleGroup.prime_card
        have hmem : w ∈ (LinearEquiv.det.comp β).ker := by
          have := Abelianization.commutator_subset_ker (LinearEquiv.det.comp β)
          rw [commutator_def, hker] at this
          exact this (Subgroup.mem_top w)
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hmem
        rw [← LinearEquiv.coe_det, hmem, Units.val_one]
      rw [hfac, LinearMap.det_comp, det_smul_add_one_sub hRidem, det_smul_add_one_sub hE'idem,
        h5, hL, pow_one] at hdet1
      apply hνμ
      linear_combination (-ν * (μ₁ ^ 3 + 1)) * hμ₁3 + μ₁ * hdet1
  have hX3 : finrank F (LinearMap.ker R) ≤ 3 := by omega
  have hXinv : ∀ y, ∀ v ∈ LinearMap.ker R, α y v ∈ LinearMap.ker R := fun y v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hRα, hv, map_zero]
  have hRadj : ∀ x x', B (R x) x' = B x (R x') := fun x x' => by
    rw [hR, hR, cubeProj_adjoint hB hwh3 hwu hμ₁3, cubeProj_adjoint hB hz3 hzu hc₀3, hPQ]
  refine false_of_commute_unitary hF hB hY α hα hRcompl ?_ hU hX3 hUinv
    (fun y v hv => hsmall3 _ hXinv hX3 y v hv) hu₁ hu₂ ht₁ ht₂ h₁ h₂ h₁₂ hc hα₁ hα₂
  rintro _ ⟨u, rfl⟩ x hx
  rw [hRadj, LinearMap.mem_ker.1 hx, hB.zero_right]

private theorem trivial_of_perfect_of_commute {F V : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V ≤ 7) {z : V ≃ₗ[F] V} (hz3 : ∀ v, z (z (z v)) = v)
    (hzs : ∀ c : F, ∃ v, z v ≠ c • v) {H : Type*} [Group H] [Finite H]
    (hH : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) (ρ : H →* (V ≃ₗ[F] V))
    (hρz : ∀ h v, ρ h (z v) = z (ρ h v)) {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (π : H →* Q) (hπ : Function.Surjective π) (h11 : 11 ∣ Nat.card Q)
    (hN : ∀ n ∈ π.ker, ∃ c : F, ∀ v, ρ n v = c • v) : ∀ n ∈ π.ker, ρ n = 1 := by
  classical
  have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have h2F : (2 : F) = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [hF]; norm_num)
    exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ)
    (by rw [Finset.card_univ, hF]; exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨hω0, hω1⟩ := hω
  have hω3 : ω ^ 3 = 1 := by
    have h4 : ω ^ 4 = ω := by
      have := FiniteField.pow_card ω
      rwa [hF] at this
    have : ω * (ω ^ 3 - 1) = 0 := by rw [mul_sub, ← pow_succ', h4, mul_one, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0)
  have hω23 : (ω ^ 2) ^ 3 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  let zl : V →ₗ[F] V := z
  obtain ⟨E, hEinv, hE0, hE4⟩ : ∃ E : Submodule F V, (∀ h, ∀ v ∈ E, ρ h v ∈ E) ∧ E ≠ ⊥ ∧
      finrank F E ≤ 4 := by
    obtain ⟨v, hv⟩ := hzs 0
    rw [zero_smul] at hv
    have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
    have hsum := cubeProj_sum h2F (g := zl) hω3 hω1 v
    obtain ⟨c, hc3, hcv⟩ : ∃ c : F, c ^ 3 = 1 ∧ cubeProj zl c v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hv0
      rw [← hsum, hcon 1 (one_pow 3), hcon ω hω3, hcon (ω ^ 2) hω23, add_zero, add_zero]
    have hPρ : ∀ h u, ρ h (cubeProj zl c u) = cubeProj zl c (ρ h u) := fun h u =>
      cubeProj_comm (h := (ρ h : V →ₗ[F] V)) (fun x => hρz h x) c u
    have hidem := isIdempotentElem_cubeProj (g := zl) h2F hz3 hc3
    have hdim := Submodule.finrank_add_eq_of_isCompl (LinearMap.IsIdempotentElem.isCompl hidem)
    by_cases hd : finrank F (LinearMap.range (cubeProj zl c)) ≤ 4
    · refine ⟨LinearMap.range (cubeProj zl c), ?_, ?_, hd⟩
      · rintro h _ ⟨u, rfl⟩
        exact ⟨ρ h u, (hPρ h u).symm⟩
      · intro hbot
        apply hcv
        have : cubeProj zl c v ∈ LinearMap.range (cubeProj zl c) := ⟨v, rfl⟩
        rw [hbot] at this
        exact (Submodule.mem_bot F).1 this
    · refine ⟨LinearMap.ker (cubeProj zl c), ?_, ?_, by omega⟩
      · intro h u hu
        rw [LinearMap.mem_ker] at hu ⊢
        rw [← hPρ, hu, map_zero]
      · intro h
        obtain ⟨u, hu⟩ := hzs c
        apply hu
        have hinj : Function.Injective (cubeProj zl c) := LinearMap.ker_eq_bot.1 h
        have hPu : cubeProj zl c u = u := hinj (cubeProj_idem h2F hz3 hc3 u)
        rw [← hPu]
        exact apply_cubeProj hz3 hc3 u
  have hmap : ∀ h, E.map ((ρ h : V ≃ₗ[F] V) : V →ₗ[F] V) = E := fun h => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq (ρ h) E)
    rintro _ ⟨w, hw, rfl⟩
    exact hEinv h w hw
  let ρE : H →* (E ≃ₗ[F] E) :=
    { toFun := fun h => LinearEquiv.ofSubmodules (ρ h) E E (hmap h)
      map_one' := by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        rw [LinearEquiv.ofSubmodules_apply, map_one]
        rfl
      map_mul' := fun a b => by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        rw [LinearEquiv.ofSubmodules_apply, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          LinearEquiv.ofSubmodules_apply, LinearEquiv.ofSubmodules_apply] }
  have hρE : ∀ h (x : E), ((ρE h x : E) : V) = ρ h x := fun h x => rfl
  have hkertop : ρE.ker = ⊤ := by
    have hMn : (ρE.ker ⊔ π.ker).Normal := Subgroup.sup_normal _ _
    rcases (hMn.map π hπ).eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hle : ρE.ker ≤ π.ker := le_sup_left.trans ((Subgroup.map_eq_bot_iff _).1 hbot)
      have hdvd1 : π.ker.index ∣ ρE.ker.index := Subgroup.index_dvd_of_le hle
      rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective π hπ,
        Subgroup.card_top] at hdvd1
      have hdvd2 : Nat.card ρE.range ∣ Nat.card (E ≃ₗ[F] E) := Subgroup.card_subgroup_dvd_card _
      rw [card_linearEquiv_of_card_four hF'] at hdvd2
      exact not_eleven_dvd_card_GL_four hE4 ((h11.trans hdvd1).trans hdvd2)
    · have hMtop : ρE.ker ⊔ π.ker = ⊤ := by
        have h1 := Subgroup.comap_map_eq π (ρE.ker ⊔ π.ker)
        rw [htop, Subgroup.comap_top] at h1
        rw [h1]
        exact (sup_eq_left.2 le_sup_right).symm
      have hscal : ∀ h, ∃ c : F, ∀ x : E, ρE h x = c • x := fun h => by
        obtain ⟨k, hk, n, hn, rfl⟩ :=
          Subgroup.mem_sup_of_normal_right.1 (hMtop ▸ Subgroup.mem_top h : h ∈ ρE.ker ⊔ π.ker)
        obtain ⟨c, hc⟩ := hN n hn
        refine ⟨c, fun x => ?_⟩
        rw [map_mul, LinearEquiv.mul_apply, (MonoidHom.mem_ker).1 hk]
        apply Subtype.ext
        show ((ρE n x : E) : V) = _
        rw [hρE, hc, Submodule.coe_smul]
      have hcomm : ∀ a b : H, ρE a * ρE b = ρE b * ρE a := fun a b => by
        obtain ⟨c, hc⟩ := hscal a
        obtain ⟨d, hd⟩ := hscal b
        refine LinearEquiv.ext fun x => ?_
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc, hd, hd, hc, smul_comm]
      rw [eq_top_iff, ← hH, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        hcomm a b]
      group
  have htriv : ∀ h, ∀ v ∈ E, ρ h v = v := fun h v hv => by
    have h1 : ρE h = 1 := (MonoidHom.mem_ker).1 (hkertop ▸ Subgroup.mem_top h)
    have := congrArg (fun e : E ≃ₗ[F] E => ((e ⟨v, hv⟩ : E) : V)) h1
    simpa [hρE] using this
  intro n hn
  obtain ⟨c, hc⟩ := hN n hn
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
  have hc1 : c = 1 := by
    have h1 := htriv n e he
    rw [hc] at h1
    have : (c - 1) • e = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right he0)
  refine LinearEquiv.ext fun v => ?_
  rw [hc, hc1, one_smul]
  rfl

section MatrixForm

open Matrix CFSG.Open CFSG.Fischer CFSG.LinearGroups
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4)

private noncomputable def glLin (n : ℕ) :
    GL (Fin n) F4 ≃* ((Fin n → F4) ≃ₗ[F4] (Fin n → F4)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F4 _)

private theorem glLin_apply {n : ℕ} (A : GL (Fin n) F4) (v : Fin n → F4) :
    glLin n A v = (A : Matrix (Fin n) (Fin n) F4) *ᵥ v := by
  simp [glLin, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply]

private theorem isHerm4_stdHermForm (n : ℕ) :
    IsHerm4 (fun x y : Fin n → F4 => stdHermForm hF4 n x y) where
  add_left x y z := by rw [map_add, LinearMap.add_apply]
  smul_left c x y := by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hF4.bar_apply, pow_one]
  add_right x y z := map_add _ _ _
  smul_right c x y := by rw [map_smul, smul_eq_mul]
  herm x y := by
    rw [← (stdHermForm_isSymm hF4 n).eq x y, hF4.bar_apply, pow_one]
  nondeg x hx := by
    funext i
    have h := hx (Pi.single i 1)
    rw [stdHermForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
      (by simp)] at h
    simp only [Pi.single_eq_same, mul_one, hF4.bar_apply, pow_one] at h
    exact (pow_eq_zero_iff (by norm_num)).1 h

private theorem stdHermForm_mulVec_of_mem {n : ℕ} {u : GL (Fin n) F4}
    (hu : u ∈ StatedSU n (2 ^ 1) F4)
    (x y : Fin n → F4) :
    stdHermForm hF4 n ((u : Matrix (Fin n) (Fin n) F4) *ᵥ x)
      ((u : Matrix (Fin n) (Fin n) F4) *ᵥ y) = stdHermForm hF4 n x y :=
  ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry hF4).1 hu).2 x y

private theorem exists_smul_of_mem_statedScalars {n : ℕ} {s : GL (Fin n) F4}
    (hs : s ∈ StatedScalars (Fin n) F4) :
    ∃ c : F4, ∀ v, (s : Matrix (Fin n) (Fin n) F4) *ᵥ v = c • v := by
  obtain ⟨c, rfl⟩ := hs
  refine ⟨(c : F4), fun v => ?_⟩
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem mul_comm_of_mem_statedScalars {n : ℕ} {s : GL (Fin n) F4}
    (hs : s ∈ StatedScalars (Fin n) F4) (g : GL (Fin n) F4) : s * g = g * s := by
  have : s ∈ Subgroup.center (GL (Fin n) F4) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hs
  exact ((Subgroup.mem_center_iff.1 this) g).symm

private theorem commutator_eq_self_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ ∀ a b : G, a * b = b * a) : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  refine (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top.resolve_left
    fun hb => h fun a b => ?_
  have : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

private theorem commutator_subgroup_eq_self {G : Type*} [Group G] (H : Subgroup G) [IsSimpleGroup H]
    (h : ¬ ∀ a b : H, a * b = b * a) : ⁅H, H⁆ = H := by
  have h1 := commutator_eq_self_of_isSimpleGroup h
  have h2 := congrArg (Subgroup.map H.subtype) h1
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

private theorem not_comm_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G] [Finite G]
    (hp : ¬ (Nat.card G).Prime) : ¬ ∀ a b : G, a * b = b * a := fun hc => by
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  exact hp IsSimpleGroup.prime_card

private theorem commutatorElement_mul_central {G : Type*} [Group G] {a b s t : G}
    (hs : ∀ g, s * g = g * s) (ht : ∀ g, t * g = g * t) : ⁅a * s, b * t⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc a * s * (b * t) * (s⁻¹ * a⁻¹) * (t⁻¹ * b⁻¹)
      = a * (s * b) * t * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = a * b * (s * t * s⁻¹) * a⁻¹ * t⁻¹ * b⁻¹ := by rw [hs b]; group
    _ = a * b * t * a⁻¹ * t⁻¹ * b⁻¹ := by rw [show s * t * s⁻¹ = t by rw [hs t]; group]
    _ = a * b * (t * a⁻¹) * t⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [ht a⁻¹]; group

private theorem pow_three_of_mem_statedScalars {n : ℕ} {s : GL (Fin n) F4}
    (hs : s ∈ StatedScalars (Fin n) F4) : s ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := hs
  have hc : c ^ 3 = 1 := by
    have h := pow_card_eq_one (G := F4ˣ) (x := c)
    rwa [Fintype.card_units, F4.card] at h
  rw [← map_pow, hc, map_one]

private theorem sq_sq_eq_one_of_comm {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1)
    (hc : (a * b * a * b) * a = a * (a * b * a * b)) : (a * b * a * b) * (a * b * a * b) = 1 :=
  calc (a * b * a * b) * (a * b * a * b) = ((a * b * a * b) * a) * (b * a * b) := by group
    _ = (a * (a * b * a * b)) * (b * a * b) := by rw [hc]
    _ = (a * a) * b * a * (b * b) * a * b := by group
    _ = b * a * a * b := by rw [ha, hb]; group
    _ = b * (a * a) * b := by group
    _ = 1 := by rw [ha, mul_one, hb]

private theorem false_of_matrix_config {n : ℕ} (hn : n ≤ 7) {z : GL (Fin n) F4}
    (hzu : ∀ x y, stdHermForm hF4 n ((z : Matrix (Fin n) (Fin n) F4) *ᵥ x)
      ((z : Matrix (Fin n) (Fin n) F4) *ᵥ y) = stdHermForm hF4 n x y)
    (hz3 : ∃ c : F4ˣ, z ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hz504 : ∀ c : F4ˣ, c ≠ 1 → z ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c →
      ∀ J : Subgroup (StatedSU n (2 ^ 1) F4), (∀ u ∈ J, (u : GL (Fin n) F4) * z = z * u) →
        ⁅J, J⁆ = J → Nat.card J ∣ 504)
    (hzs : ∀ c : F4, ∃ v, (z : Matrix (Fin n) (Fin n) F4) *ᵥ v ≠ c • v)
    (hzM : ∀ u ∈ StatedSU n (2 ^ 1) F4, z * u * z⁻¹ ∈ StatedSU n (2 ^ 1) F4)
    {W Wk : Subgroup (StatedProj (StatedSU n (2 ^ 1) F4))} [IsSimpleGroup W] [IsSimpleGroup Wk]
    (hWc : Nat.card W = 13685760) (hWkc : Nat.card Wk = 25920) (hWk : Wk ≤ W)
    (hzW : ∀ u : StatedSU n (2 ^ 1) F4,
      (QuotientGroup.mk u : StatedProj (StatedSU n (2 ^ 1) F4)) ∈ W →
      (QuotientGroup.mk ⟨z * u * z⁻¹, hzM u u.2⟩ : StatedProj (StatedSU n (2 ^ 1) F4)) =
        QuotientGroup.mk u)
    {w : StatedProj (StatedSU n (2 ^ 1) F4)} (hwW : w ∈ W) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hwWk : ∀ x ∈ Wk, w * x = x * w)
    {P : Subgroup (StatedProj (StatedSU n (2 ^ 1) F4))} (hP : Nat.card P = 4)
    (hP2 : ∀ p ∈ P, p ^ 2 = 1) (hPWk : ∀ p ∈ P, ∀ x ∈ Wk, p * x = x * p) : False := by
  classical
  let M : Subgroup (GL (Fin n) F4) := StatedSU n (2 ^ 1) F4
  let Z : Subgroup M := (StatedScalars (Fin n) F4).subgroupOf M
  let π : M →* StatedProj M := QuotientGroup.mk' Z
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπ1 : ∀ u : M, π u = 1 ↔ (u : GL (Fin n) F4) ∈ StatedScalars (Fin n) F4 := fun u => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ u v : M, π u = π v ↔
      (u : GL (Fin n) F4)⁻¹ * v ∈ StatedScalars (Fin n) F4 := fun u v => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hZc : ∀ s : M, (s : GL (Fin n) F4) ∈ StatedScalars (Fin n) F4 → ∀ g : M, s * g = g * s :=
    fun s hs g => Subtype.ext (mul_comm_of_mem_statedScalars hs g)
  have hnp : ∀ {m : ℕ}, 2 ∣ m → m ≠ 2 → ¬ m.Prime := fun {m} h2 hm hp => by
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · exact hm h.symm
  have hWnc : ¬ ∀ a b : W, a * b = b * a :=
    not_comm_of_isSimpleGroup (hnp (by rw [hWc]; norm_num) (by rw [hWc]; norm_num))
  have hWknc : ¬ ∀ a b : Wk, a * b = b * a :=
    not_comm_of_isSimpleGroup (hnp (by rw [hWkc]; norm_num) (by rw [hWkc]; norm_num))
  have hWp : ⁅W, W⁆ = W := commutator_subgroup_eq_self W hWnc
  let G : Subgroup M := W.comap π
  let G' : Subgroup M := ⁅G, G⁆
  have hG'G : G' ≤ G := Subgroup.commutator_le.2 fun a ha b hb =>
    G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha)) (G.inv_mem hb)
  have hπG : G.map π = W := Subgroup.map_comap_eq_self_of_surjective hπs W
  have hπG' : G'.map π = W := by
    show (⁅G, G⁆).map π = W
    rw [Subgroup.map_commutator, hπG, hWp]
  have hzG : ∀ a ∈ G, ∃ s ∈ StatedScalars (Fin n) F4,
      z * (a : GL (Fin n) F4) * z⁻¹ = a * s := fun a ha => by
    have h1 : π ⟨z * a * z⁻¹, hzM a a.2⟩ = π a := hzW a (Subgroup.mem_comap.1 ha)
    exact ⟨_, (hπeq a _).1 h1.symm, by rw [mul_inv_cancel_left]⟩
  have hzG' : ∀ u ∈ G', (u : GL (Fin n) F4) * z = z * u := by
    have hle : G' ≤ (Subgroup.centralizer ({z} : Set (GL (Fin n) F4))).subgroupOf M := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨s, hs, hsa⟩ := hzG a ha
      obtain ⟨t, ht, htb⟩ := hzG b hb
      have hconj : z * ⁅(a : GL (Fin n) F4), (b : GL (Fin n) F4)⁆ * z⁻¹ =
          ⁅z * (a : GL (Fin n) F4) * z⁻¹, z * (b : GL (Fin n) F4) * z⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hsa, htb, commutatorElement_mul_central (mul_comm_of_mem_statedScalars hs)
        (mul_comm_of_mem_statedScalars ht)] at hconj
      have hcoe : ((⁅a, b⁆ : M) : GL (Fin n) F4) = ⁅(a : GL (Fin n) F4), (b : GL (Fin n) F4)⁆ := by
        simp [commutatorElement_def]
      rw [hcoe]
      calc ⁅(a : GL (Fin n) F4), (b : GL (Fin n) F4)⁆ * z =
            z * ⁅(a : GL (Fin n) F4), (b : GL (Fin n) F4)⁆ * z⁻¹ * z := by rw [hconj]
        _ = z * ⁅(a : GL (Fin n) F4), (b : GL (Fin n) F4)⁆ := by group
    intro u hu
    have := hle hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hlift : ∀ a ∈ G, ∃ a' ∈ G', ∃ s : M, (s : GL (Fin n) F4) ∈ StatedScalars (Fin n) F4 ∧
      a = a' * s := fun a ha => by
    have : π a ∈ G'.map π := hπG' ▸ ha
    obtain ⟨a', ha', he⟩ := this
    exact ⟨a', ha', a'⁻¹ * a, by
      have := (hπeq a' a).1 he
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this, by group⟩
  have hG'p : ⁅G', G'⁆ = G' := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb =>
      G'.mul_mem (G'.mul_mem (G'.mul_mem ha hb) (G'.inv_mem ha)) (G'.inv_mem hb)) ?_
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨a', ha', s, hs, rfl⟩ := hlift a ha
    obtain ⟨b', hb', t, ht, rfl⟩ := hlift b hb
    rw [commutatorElement_mul_central (hZc s hs) (hZc t ht)]
    exact Subgroup.commutator_mem_commutator ha' hb'
  have hG'card : Nat.card W ∣ Nat.card G' := by
    rw [← hπG']
    exact Subgroup.card_map_dvd (H := G') π
  have hz31 : z ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := hz3
    by_contra hne
    have hc1 : c ≠ 1 := fun h => hne (by rw [hc, h, map_one])
    have h504 := hz504 c hc1 hc G' hzG' hG'p
    have : 11 ∣ 504 := ((show 11 ∣ Nat.card W by rw [hWc]; norm_num).trans hG'card).trans h504
    norm_num at this
  let lin := glLin n
  have hlin : ∀ A v, lin A v = (A : Matrix (Fin n) (Fin n) F4) *ᵥ v := glLin_apply
  have hlininj : Function.Injective lin := lin.injective
  let zl : (Fin n → F4) ≃ₗ[F4] (Fin n → F4) := lin z
  have hz3' : ∀ v, zl (zl (zl v)) = v := fun v => by
    have : lin (z ^ 3) = 1 := by rw [hz31, map_one]
    have h := LinearEquiv.congr_fun this v
    simpa [map_pow, pow_succ, LinearEquiv.mul_apply] using h
  have hzs' : ∀ c : F4, ∃ v, zl v ≠ c • v := fun c => by
    obtain ⟨v, hv⟩ := hzs c
    exact ⟨v, by rw [hlin]; exact hv⟩
  have hzu' : ∀ x y, stdHermForm hF4 n (zl x) (zl y) = stdHermForm hF4 n x y := fun x y => by
    rw [hlin, hlin]
    exact hzu x y
  let ρ : G' →* ((Fin n → F4) ≃ₗ[F4] (Fin n → F4)) :=
    lin.toMonoidHom.comp (M.subtype.comp G'.subtype)
  have hρ : ∀ g : G', ρ g = lin ((g : M) : GL (Fin n) F4) := fun g => rfl
  have hρinj : Function.Injective ρ :=
    hlininj.comp (M.subtype_injective.comp G'.subtype_injective)
  have hρz : ∀ g v, ρ g (zl v) = zl (ρ g v) := fun g v => by
    rw [hρ, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hzG' _ g.2]
  let π' : G' →* W :=
    (π.comp G'.subtype).codRestrict W fun g => Subgroup.mem_comap.1 (hG'G g.2)
  have hπ'apply : ∀ g : G', ((π' g : W) : StatedProj M) = π g := fun g => rfl
  have hπ's : Function.Surjective π' := fun x => by
    have : (x : StatedProj M) ∈ G'.map π := hπG'.symm ▸ x.2
    obtain ⟨g, hg, he⟩ := this
    exact ⟨⟨g, hg⟩, Subtype.ext he⟩
  have hG'perf : ⁅(⊤ : Subgroup G'), (⊤ : Subgroup G')⁆ = ⊤ := by
    apply Subgroup.map_injective G'.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hG'p
  have hsplit := trivial_of_perfect_of_commute F4.card
    (by rw [Module.finrank_fin_fun]; exact hn) hz3' hzs' hG'perf ρ hρz π' hπ's
    (by rw [hWc]; norm_num) (fun g hg => by
      have h1 : π g = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hg)
      obtain ⟨c, hc⟩ := exists_smul_of_mem_statedScalars ((hπ1 g).1 h1)
      exact ⟨c, fun v => by rw [hρ, hlin]; exact hc v⟩)
  have hπ'inj : Function.Injective π' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have h1 := hsplit g hg
    exact Subgroup.mem_bot.2 (hρinj (h1.trans (map_one ρ).symm))
  let e' : G' ≃* W := MulEquiv.ofBijective π' ⟨hπ'inj, hπ's⟩
  have he' : ∀ x : W, π ((e'.symm x : G') : M) = x := fun x => by
    have : π' (e'.symm x) = x := e'.apply_symm_apply x
    exact congrArg Subtype.val this
  let β : W →* ((Fin n → F4) ≃ₗ[F4] (Fin n → F4)) := ρ.comp e'.symm.toMonoidHom
  have hβ : ∀ x : W, β x = lin (((e'.symm x : G') : M) : GL (Fin n) F4) := fun x => rfl
  have hβinj : Function.Injective β := hρinj.comp e'.symm.injective
  let γ : Wk →* W := Subgroup.inclusion hWk
  have hγinj : Function.Injective γ := Subgroup.inclusion_injective hWk
  let wW : W := ⟨w, hwW⟩
  have hwW1 : wW ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hwW3 : wW ^ 3 = 1 := Subtype.ext (by simp [wW, hw3])
  have hγw : ∀ y, γ y * wW = wW * γ y := fun y => Subtype.ext (hwWk y y.2).symm
  have hwu : ∀ x x', stdHermForm hF4 n (β wW x) (β wW x') = stdHermForm hF4 n x x' :=
    fun x x' => by rw [hβ, hlin, hlin]; exact stdHermForm_mulVec_of_mem (e'.symm wW : G').1.2 x x'
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.1 (by rw [hP]; norm_num)
  obtain ⟨p₁, hp₁1⟩ := exists_ne (1 : P)
  obtain ⟨p₂, -, hp₂⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, p₁} : Finset P)) (t := Finset.univ)
    (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hP]
      exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₂
  obtain ⟨hp₂1, hp₁₂⟩ := hp₂
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => by
    have hxy := hP2 (x * y) (P.mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hP2 x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hP2 y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hxy)).symm
      _ = y * x := by rw [_root_.mul_inv_rev, hx', hy']
  have hlift : ∀ p : P, ∃ t : M, π t = p ∧ (t : GL (Fin n) F4) * t = 1 := fun p => by
    obtain ⟨u, hu⟩ := hπs (p : StatedProj M)
    have hu2 : ((u ^ 2 : M) : GL (Fin n) F4) ∈ StatedScalars (Fin n) F4 := by
      rw [← hπ1, map_pow, hu]
      exact hP2 p p.2
    refine ⟨u ^ 3, ?_, ?_⟩
    · rw [map_pow, hu, pow_succ, hP2 p p.2, one_mul]
    · have h3 := pow_three_of_mem_statedScalars hu2
      rw [← Subgroup.coe_mul, ← pow_two, ← pow_mul]
      rw [Subgroup.coe_pow, ← pow_mul] at h3
      rw [show 3 * 2 = 2 * 3 by rfl]
      rw [Subgroup.coe_pow]
      exact h3
  obtain ⟨t₁, ht₁π, ht₁2⟩ := hlift p₁
  obtain ⟨t₂, ht₂π, ht₂2⟩ := hlift p₂
  have htne : ∀ {t : M} {p : P}, π t = p → p ≠ 1 → lin (t : GL (Fin n) F4) ≠ 1 :=
    fun {t p} htp hp1 h => by
      have : (t : GL (Fin n) F4) = 1 := hlininj (h.trans (map_one lin).symm)
      apply hp1
      apply Subtype.ext
      rw [← htp, show t = 1 from Subtype.ext this, map_one]
      rfl
  have ht12 : lin (t₁ : GL (Fin n) F4) ≠ lin (t₂ : GL (Fin n) F4) := fun h => by
    have : t₁ = t₂ := Subtype.ext (hlininj h)
    apply hp₁₂
    apply Subtype.ext
    rw [← ht₁π, ← ht₂π, this]
  have hcomm12 : (t₁ : GL (Fin n) F4) * t₂ = t₂ * t₁ := by
    have hπc : π (t₂ * t₁) = π (t₁ * t₂) := by
      rw [map_mul, map_mul, ht₁π, ht₂π]
      exact (hPcomm _ p₂.2 _ p₁.2)
    have hν := (hπeq _ _).1 hπc
    simp only [Subgroup.coe_mul] at hν
    set a : GL (Fin n) F4 := (t₁ : GL (Fin n) F4)
    set b : GL (Fin n) F4 := (t₂ : GL (Fin n) F4)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ht₁2
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right ht₂2
    have hνe : (b * a)⁻¹ * (a * b) = a * b * a * b := by
      rw [_root_.mul_inv_rev, ha', hb']
      group
    rw [hνe] at hν
    have hνa := mul_comm_of_mem_statedScalars hν a
    have hν2 := sq_sq_eq_one_of_comm ht₁2 ht₂2 hνa
    have hν3 := pow_three_of_mem_statedScalars hν
    have hν1 : a * b * a * b = 1 := by
      rw [pow_three, hν2, mul_one] at hν3
      exact hν3
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hν1)
    rw [← hab, _root_.mul_inv_rev, ha', hb']
  let φ : Wk →* GL (Fin n) F4 := M.subtype.comp (G'.subtype.comp (e'.symm.toMonoidHom.comp γ))
  have hφ : ∀ y, φ y = (((e'.symm (γ y) : G') : M) : GL (Fin n) F4) := fun y => rfl
  have hπφ : ∀ y : Wk, π ((e'.symm (γ y) : G') : M) = (y : StatedProj M) := fun y => he' (γ y)
  have hWkperf : ⁅(⊤ : Subgroup Wk), (⊤ : Subgroup Wk)⁆ = ⊤ :=
    commutator_eq_self_of_isSimpleGroup hWknc
  have hcent : ∀ (t : M) (p : P), π t = p → ∀ y : Wk,
      (t : GL (Fin n) F4) * φ y = φ y * t := by
    intro t p htp
    have hsc : ∀ y : Wk, ∃ s ∈ StatedScalars (Fin n) F4,
        (t : GL (Fin n) F4) * φ y * (t : GL (Fin n) F4)⁻¹ = φ y * s := fun y => by
      set g : M := ((e'.symm (γ y) : G') : M) with hg
      have h1 : π (t * g * t⁻¹) = π g := by
        rw [map_mul, map_mul, map_inv, htp, hπφ]
        rw [hPWk p p.2 y y.2]
        group
      refine ⟨_, (hπeq g (t * g * t⁻¹)).1 h1.symm, ?_⟩
      rw [hφ, ← hg, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hle : ⁅(⊤ : Subgroup Wk), (⊤ : Subgroup Wk)⁆ ≤
        (Subgroup.centralizer {(t : GL (Fin n) F4)}).comap φ := by
      refine Subgroup.commutator_le.2 fun y₁ _ y₂ _ => ?_
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, map_commutatorElement]
      obtain ⟨s₁, hs₁, h₁⟩ := hsc y₁
      obtain ⟨s₂, hs₂, h₂⟩ := hsc y₂
      have hconj : (t : GL (Fin n) F4) * ⁅φ y₁, φ y₂⁆ * (t : GL (Fin n) F4)⁻¹ =
          ⁅(t : GL (Fin n) F4) * φ y₁ * (t : GL (Fin n) F4)⁻¹,
            (t : GL (Fin n) F4) * φ y₂ * (t : GL (Fin n) F4)⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [h₁, h₂, commutatorElement_mul_central (mul_comm_of_mem_statedScalars hs₁)
        (mul_comm_of_mem_statedScalars hs₂)] at hconj
      calc ⁅φ y₁, φ y₂⁆ * (t : GL (Fin n) F4) =
            (t : GL (Fin n) F4) * ⁅φ y₁, φ y₂⁆ * (t : GL (Fin n) F4)⁻¹ * t := by rw [hconj]
        _ = (t : GL (Fin n) F4) * ⁅φ y₁, φ y₂⁆ := by group
    intro y
    have := hle (hWkperf ▸ Subgroup.mem_top y)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  have hα : ∀ (t : M) (p : P), π t = p → ∀ y,
      lin (t : GL (Fin n) F4) * β (γ y) = β (γ y) * lin (t : GL (Fin n) F4) :=
    fun t p htp y => by
      rw [hβ, ← map_mul, ← map_mul]
      exact congrArg lin (hcent t p htp y)
  have htu : ∀ t : M, ∀ x x', stdHermForm hF4 n (lin (t : GL (Fin n) F4) x)
      (lin (t : GL (Fin n) F4) x') = stdHermForm hF4 n x x' := fun t x x' => by
    rw [hlin, hlin]
    exact stdHermForm_mulVec_of_mem t.2 x x'
  have hinv : ∀ t : M, (t : GL (Fin n) F4) * t = 1 →
      ∀ v, lin (t : GL (Fin n) F4) (lin (t : GL (Fin n) F4) v) = v := fun t ht v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, ht, map_one]
    rfl
  have hcomm' : ∀ v, lin (t₁ : GL (Fin n) F4) (lin (t₂ : GL (Fin n) F4) v) =
      lin (t₂ : GL (Fin n) F4) (lin (t₁ : GL (Fin n) F4) v) := fun v => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hcomm12]
  exact false_of_unitary_blocks F4.card (by rw [Module.finrank_fin_fun]; exact hn)
    (isHerm4_stdHermForm n) (z := zl) hzu' hz3' hzs' (Y₀ := W) (by rw [hWc]; norm_num)
    (by rw [hWc]; norm_num) β hβinj (fun y v => hρz _ v) hwW1 hwW3 hwu (Y := Wk)
    (by rw [hWkc]; norm_num) γ hγinj hγw (t₁ := lin t₁) (t₂ := lin t₂) (htu t₁) (htu t₂)
    (hinv t₁ ht₁2) (hinv t₂ ht₂2) (htne ht₁π hp₁1) (htne ht₂π hp₂1) ht12 hcomm'
    (hα t₁ p₁ ht₁π) (hα t₂ p₂ ht₂π)

theorem false_of_psu_le_seven_pumpUp_config {n : ℕ} (hn : n ≤ 7) {L : Type} [Group L]
    (e : L ≃* StatedProj (StatedSU n (2 ^ 1) F4)) {ζ : MulAut L} (hζ1 : ζ ≠ 1)
    {z : GL (Fin n) F4}
    (hzu : ∀ x y, stdHermForm hF4 n ((z : Matrix (Fin n) (Fin n) F4) *ᵥ x)
      ((z : Matrix (Fin n) (Fin n) F4) *ᵥ y) = stdHermForm hF4 n x y)
    (hz3 : ∃ c : F4ˣ, z ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hz504 : ∀ c : F4ˣ, c ≠ 1 → z ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c →
      ∀ J : Subgroup (StatedSU n (2 ^ 1) F4), (∀ u ∈ J, (u : GL (Fin n) F4) * z = z * u) →
        ⁅J, J⁆ = J → Nat.card J ∣ 504)
    (hzM : ∀ u ∈ StatedSU n (2 ^ 1) F4, z * u * z⁻¹ ∈ StatedSU n (2 ^ 1) F4)
    (hzζ : ∀ u : StatedSU n (2 ^ 1) F4,
      (QuotientGroup.mk ⟨z * u * z⁻¹, hzM u u.2⟩ : StatedProj (StatedSU n (2 ^ 1) F4)) =
        e (ζ (e.symm (QuotientGroup.mk u))))
    {W Wk : Subgroup L} [IsSimpleGroup W] [IsSimpleGroup Wk]
    (hWc : Nat.card W = 13685760) (hWkc : Nat.card Wk = 25920) (hWk : Wk ≤ W)
    (hζW : ∀ x ∈ W, ζ x = x) {w : L} (hwW : w ∈ W) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hwWk : ∀ x ∈ Wk, w * x = x * w) {P : Subgroup L} (hP : Nat.card P = 4)
    (hP2 : ∀ p ∈ P, p ^ 2 = 1) (hPWk : ∀ p ∈ P, ∀ x ∈ Wk, p * x = x * p) : False := by
  classical
  haveI : IsSimpleGroup (W.map e.toMonoidHom) := (e.subgroupMap W).symm.isSimpleGroup
  haveI : IsSimpleGroup (Wk.map e.toMonoidHom) := (e.subgroupMap Wk).symm.isSimpleGroup
  have hcard : ∀ H : Subgroup L, Nat.card (H.map e.toMonoidHom) = Nat.card H := fun H =>
    Subgroup.card_map_of_injective e.injective
  have hzs : ∀ c : F4, ∃ v, (z : Matrix (Fin n) (Fin n) F4) *ᵥ v ≠ c • v := by
    intro c
    by_contra hcon
    push Not at hcon
    apply hζ1
    have hcomm : ∀ u : GL (Fin n) F4, z * u * z⁻¹ = u := fun u => by
      have h1 : glLin n (z * u) = glLin n (u * z) := LinearEquiv.ext fun v => by
        rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, glLin_apply,
          glLin_apply, glLin_apply, glLin_apply, hcon, hcon, Matrix.mulVec_smul]
      rw [(glLin n).injective h1, mul_inv_cancel_right]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e x)
    have h := hzζ u
    have hu' : (⟨z * u * z⁻¹, hzM u u.2⟩ : StatedSU n (2 ^ 1) F4) = u := Subtype.ext (hcomm u)
    rw [hu', hu, MulEquiv.symm_apply_apply] at h
    exact (e.injective h).symm
  refine false_of_matrix_config hn hzu hz3 hz504 hzs hzM (W := W.map e.toMonoidHom)
    (Wk := Wk.map e.toMonoidHom) (by rw [hcard, hWc]) (by rw [hcard, hWkc])
    (Subgroup.map_mono hWk) ?_ (w := e w) ⟨w, hwW, rfl⟩ (by rwa [Ne, map_eq_one_iff e e.injective])
    (by rw [← map_pow, hw3, map_one]) ?_ (P := P.map e.toMonoidHom) (by rw [hcard, hP]) ?_ ?_
  · intro u hu
    obtain ⟨x, hx, hxu⟩ := hu
    rw [hzζ u, ← hxu, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hζW x hx]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hwWk x hx]
  · rintro _ ⟨p, hp, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hP2 p hp, map_one]
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hPWk p hp x hx]

end MatrixForm

end CFSG.GGQ2Prime
