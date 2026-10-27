module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.SteinbergCD

section Setup

variable {K : Type*} [Field K] [CharP K 2] {H : Type*} [Group H] {A : Subgroup H}

theorem sq_eq_one_of_mulEquiv (α : A ≃* Multiplicative K) (a : A) : a ^ 2 = 1 := by
  apply α.injective
  apply Multiplicative.toAdd.injective
  rw [map_pow, toAdd_pow, map_one, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero]

theorem sq_mem_of_mulEquiv [A.Normal] (β : H ⧸ A ≃* Multiplicative K) (h : H) : h ^ 2 ∈ A := by
  rw [← QuotientGroup.eq_one_iff]
  apply β.injective
  apply Multiplicative.toAdd.injective
  rw [QuotientGroup.mk_pow, map_pow, toAdd_pow, map_one, toAdd_one, two_nsmul,
    CharTwo.add_self_eq_zero]

theorem sq_eq_sq_of_mk_eq [A.Normal] (hAZ : A ≤ Subgroup.center H) (α : A ≃* Multiplicative K)
    {h h' : H} (hh : (h : H ⧸ A) = h') : h ^ 2 = h' ^ 2 := by
  have ha : h⁻¹ * h' ∈ A := QuotientGroup.eq.1 hh
  set a := h⁻¹ * h' with hadef
  have hh' : h' = h * a := by rw [hadef]; group
  have hc : h * a = a * h := Subgroup.mem_center_iff.1 (hAZ ha) h
  have ha2 : a * a = 1 := by
    have := congrArg Subtype.val (sq_eq_one_of_mulEquiv α ⟨a, ha⟩)
    simpa [pow_two] using this
  rw [hh', pow_two, pow_two]
  calc h * h = h * h * (a * a) := by rw [ha2, mul_one]
    _ = h * (h * a) * a := by simp only [mul_assoc]
    _ = h * (a * h) * a := by rw [hc]
    _ = h * a * (h * a) := by simp only [mul_assoc]

end Setup

theorem scalar_equivariant_central_two_extension_square_map (n : ℕ) (K : Type*) [Field K]
    [CharP K 2] (hK : Nat.card K = 2 ^ n) (H : Type*) [Group H] [Finite H] (A : Subgroup H)
    [A.Normal] (hAZ : A ≤ Subgroup.center H) (α : A ≃* Multiplicative K)
    (β : H ⧸ A ≃* Multiplicative K) (θ : Kˣ →* MulAut H)
    (hα : ∀ (l : Kˣ) (a a' : A), (a' : H) = θ l a →
      Multiplicative.toAdd (α a') = l * Multiplicative.toAdd (α a))
    (hβ : ∀ (l : Kˣ) (h : H),
      Multiplicative.toAdd (β (θ l h : H ⧸ A)) = l * Multiplicative.toAdd (β h)) :
    (∀ x y : H, x * y = y * x) ∧ Nat.card H = (2 ^ n) ^ 2 ∧ (∀ h : H, h ^ 2 ∈ A) ∧
      ∃ c : K, (∀ (h : H) (a : A), (a : H) = h ^ 2 →
          Multiplicative.toAdd (α a) = c * Multiplicative.toAdd (β h)) ∧
        (∀ c' : K, (∀ (h : H) (a : A), (a : H) = h ^ 2 →
          Multiplicative.toAdd (α a) = c' * Multiplicative.toAdd (β h)) → c' = c) ∧
        (c = 0 → IsElementaryAbelian 2 H) ∧
        (c ≠ 0 → Subgroup.closure {x | ∃ h : H, x = h ^ 2} = A ∧ {h : H | h ^ 2 = 1} = A ∧
          ∃ g : Fin n → H, (∀ i, orderOf (g i) = 4) ∧
            ∃ φ : Multiplicative (Fin n → ZMod 4) ≃* H, ∀ e : Fin n → ZMod 4,
              φ (Multiplicative.ofAdd e) = (List.ofFn fun i => g i ^ (e i).val).prod) := by
  classical
  have hsqA := sq_mem_of_mulEquiv (A := A) β
  set s : H → K := fun h => Multiplicative.toAdd (α ⟨h ^ 2, hsqA h⟩) with hs
  set v : H → K := fun h => Multiplicative.toAdd (β (h : H ⧸ A)) with hv
  have hsv : ∀ h h', v h = v h' → s h = s h' := by
    intro h h' hvv
    have hmk : (h : H ⧸ A) = h' := β.injective (Multiplicative.toAdd.injective hvv)
    have : (⟨h ^ 2, hsqA h⟩ : A) = ⟨h' ^ 2, hsqA h'⟩ :=
      Subtype.ext (sq_eq_sq_of_mk_eq hAZ α hmk)
    simp only [hs, this]
  have hsθ : ∀ (l : Kˣ) (h : H), s (θ l h) = l * s h := fun l h =>
    hα l ⟨h ^ 2, hsqA h⟩ ⟨(θ l h) ^ 2, hsqA _⟩ (by simp [map_pow])
  have hv0 : ∀ h, v h = 0 ↔ h ∈ A := by
    intro h
    rw [← QuotientGroup.eq_one_iff, ← β.injective.eq_iff, map_one, ← toAdd_one,
      Multiplicative.toAdd.injective.eq_iff]
  have hs0 : ∀ h, s h = 0 ↔ h ^ 2 = 1 := by
    intro h
    constructor
    · intro h0
      have h1 : α ⟨h ^ 2, hsqA h⟩ = 1 := Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
      have := congrArg Subtype.val (α.injective (h1.trans (map_one α).symm))
      simpa using this
    · intro h2
      have : (⟨h ^ 2, hsqA h⟩ : A) = 1 := Subtype.ext h2
      simp only [hs, this, map_one, toAdd_one]
  have hvsurj : ∀ w : K, ∃ h : H, v h = w := by
    intro w
    obtain ⟨q, hq⟩ := β.surjective (Multiplicative.ofAdd w)
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨h, by simp [hv, hq]⟩
  obtain ⟨h₁, hh₁⟩ := hvsurj 1
  set c := s h₁ with hc
  have hsc : ∀ h, s h = c * v h := by
    intro h
    by_cases h0 : v h = 0
    · rw [h0, mul_zero]
      have hA : h ∈ A := (hv0 h).1 h0
      exact (hs0 h).2 (by
        simpa using congrArg Subtype.val (sq_eq_one_of_mulEquiv α ⟨h, hA⟩))
    · set l : Kˣ := Units.mk0 (v h) h0
      have hvl : v (θ l h₁) = v h := by
        show Multiplicative.toAdd (β (θ l h₁ : H ⧸ A)) = v h
        rw [hβ, show Multiplicative.toAdd (β (h₁ : H ⧸ A)) = v h₁ from rfl, hh₁, mul_one]
        rfl
      rw [← hsv _ _ hvl, hsθ, ← hc, mul_comm]
      rfl
  have hcomm : ∀ x y : H, x * y = y * x := by
    intro x y
    have hvm : v (x * y) = v x + v y := by
      simp only [hv, QuotientGroup.mk_mul, map_mul, toAdd_mul]
    have h2 : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
      have : (⟨(x * y) ^ 2, hsqA _⟩ : A) = ⟨x ^ 2, hsqA x⟩ * ⟨y ^ 2, hsqA y⟩ := by
        apply α.injective
        apply Multiplicative.toAdd.injective
        rw [map_mul, toAdd_mul]
        change s (x * y) = s x + s y
        rw [hsc, hsc, hsc, hvm, mul_add]
      simpa using congrArg Subtype.val this
    rw [pow_two, pow_two, pow_two] at h2
    have e1 : x * (y * x * y) = x * (x * y * y) := by
      calc x * (y * x * y) = x * y * (x * y) := by simp only [mul_assoc]
        _ = x * x * (y * y) := h2
        _ = x * (x * y * y) := by simp only [mul_assoc]
    exact (mul_right_cancel (mul_left_cancel e1)).symm
  have hcardA : Nat.card A = 2 ^ n := by
    rw [Nat.card_congr α.toEquiv, ← hK]
    exact Nat.card_congr Multiplicative.toAdd
  have hcardQ : Nat.card (H ⧸ A) = 2 ^ n := by
    rw [Nat.card_congr β.toEquiv, ← hK]
    exact Nat.card_congr Multiplicative.toAdd
  have hcardH : Nat.card H = (2 ^ n) ^ 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup A, hcardA, hcardQ, pow_two]
  have hformula : ∀ (h : H) (a : A), (a : H) = h ^ 2 →
      Multiplicative.toAdd (α a) = c * Multiplicative.toAdd (β h) := by
    intro h a ha
    have : a = ⟨h ^ 2, hsqA h⟩ := Subtype.ext ha
    rw [this]
    exact hsc h
  refine ⟨hcomm, hcardH, hsqA, c, hformula, fun c' hc' => ?_, fun hc0 => ?_, fun hc0 => ?_⟩
  · have h1 := hc' h₁ ⟨h₁ ^ 2, hsqA h₁⟩ rfl
    change s h₁ = c' * v h₁ at h1
    rw [hh₁, mul_one] at h1
    exact h1.symm
  ·
    exact
      { is_comm := ⟨hcomm⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun h =>
          (hs0 h).1 (by rw [hsc, hc0, zero_mul]) }
  have hsq_onto : ∀ a ∈ A, ∃ h : H, h ^ 2 = a := by
    intro a ha
    obtain ⟨h, hh⟩ := hvsurj (c⁻¹ * Multiplicative.toAdd (α ⟨a, ha⟩))
    refine ⟨h, ?_⟩
    have : (⟨h ^ 2, hsqA h⟩ : A) = ⟨a, ha⟩ := by
      apply α.injective
      apply Multiplicative.toAdd.injective
      change s h = _
      rw [hsc, hh, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    exact congrArg Subtype.val this
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨h, rfl⟩
      exact hsqA h
    · intro a ha
      obtain ⟨h, rfl⟩ := hsq_onto a ha
      exact Subgroup.subset_closure ⟨h, rfl⟩
  · ext h
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    rw [← hs0, hsc, mul_eq_zero, or_iff_right hc0, hv0]
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) K = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) K hfin
  let a : Fin n → A := fun i => α.symm (Multiplicative.ofAdd (b i))
  have hg : ∀ i, ∃ g : H, g ^ 2 = a i := fun i => hsq_onto _ (a i).2
  choose g hgi using hg
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  have hmemA : ∀ f : Fin n → ℕ, ∏ i, (a i : H) ^ f i ∈ A := fun f =>
    Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (a i).2 _
  have hαprod : ∀ (f : Fin n → ℕ) (hmem : ∏ i, (a i : H) ^ f i ∈ A),
      Multiplicative.toAdd (α ⟨∏ i, (a i : H) ^ f i, hmem⟩) = ∑ i, f i • b i := by
    intro f hmem
    have heq : (⟨∏ i, (a i : H) ^ f i, hmem⟩ : A) = ∏ i, a i ^ f i := by
      apply Subtype.ext
      simp
    rw [heq, map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, toAdd_pow]
    simp [a]
  have heven : ∀ f : Fin n → ℕ, ∑ i, f i • b i = 0 → ∀ i, 2 ∣ f i := by
    intro f hf i
    have hli := Fintype.linearIndependent_iff.1 b.linearIndependent (fun i => (f i : ZMod 2))
      (by simpa [Nat.cast_smul_eq_nsmul] using hf) i
    exact (ZMod.natCast_eq_zero_iff (f i) 2).1 hli
  have hg4 : ∀ i, g i ^ 4 = 1 := fun i => by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hgi]
    simpa using congrArg Subtype.val (sq_eq_one_of_mulEquiv α (a i))
  have hga : ∀ i, (a i : H) ≠ 1 := fun i h1 => by
    have : a i = 1 := Subtype.ext h1
    apply b.ne_zero i
    have h2 := congrArg (fun x => Multiplicative.toAdd (α x)) this
    simpa [a] using h2
  have hord : ∀ i, orderOf (g i) = 4 := fun i => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g i)
      (by rw [pow_one, hgi]; exact hga i) (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact hg4 i)
    rw [h]
    norm_num
  let ψ : Multiplicative (Fin n → ZMod 4) →* H :=
    { toFun := fun e => ∏ i, g i ^ (Multiplicative.toAdd e i).val
      map_one' := by simp
      map_mul' := fun e e' => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have h4 := pow_mod_orderOf (g i)
          ((Multiplicative.toAdd e i).val + (Multiplicative.toAdd e' i).val)
        rw [hord i] at h4
        rw [toAdd_mul, Pi.add_apply, ZMod.val_add, h4, pow_add] }
  have hψ : ∀ e, ψ e = ∏ i, g i ^ (Multiplicative.toAdd e i).val := fun e => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    set E : Fin n → ℕ := fun i => (Multiplicative.toAdd e i).val
    have hE : ∏ i, g i ^ E i = 1 := he
    have hsq : ∏ i, (a i : H) ^ E i = 1 := by
      have := congrArg (· ^ 2) hE
      simp only [one_pow, ← Finset.prod_pow] at this
      rw [← this]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_mul, mul_comm, pow_mul, hgi]
    have h0 : ∑ i, E i • b i = 0 := by
      rw [← hαprod E (hmemA E)]
      have : (⟨∏ i, (a i : H) ^ E i, hmemA E⟩ : A) = 1 := Subtype.ext hsq
      rw [this, map_one, toAdd_one]
    have hE2 := heven E h0
    choose F hF using hE2
    have hsq' : ∏ i, (a i : H) ^ F i = 1 := by
      rw [← hE]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hF i, pow_mul, hgi]
    have h0' : ∑ i, F i • b i = 0 := by
      rw [← hαprod F (hmemA F)]
      have : (⟨∏ i, (a i : H) ^ F i, hmemA F⟩ : A) = 1 := Subtype.ext hsq'
      rw [this, map_one, toAdd_one]
    have hF2 := heven F h0'
    apply Multiplicative.toAdd.injective
    funext i
    have hEi : E i < 4 := ZMod.val_lt _
    have hEi0 : E i = 0 := by
      obtain ⟨k, hk⟩ := hF2 i
      rw [hF i, hk] at hEi ⊢
      omega
    have : (Multiplicative.toAdd e i).val = (0 : ZMod 4).val := by
      rw [ZMod.val_zero]
      exact hEi0
    exact ZMod.val_injective 4 this
  have hbij : Function.Bijective ψ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcardH, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
      ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  refine ⟨g, hord, MulEquiv.ofBijective ψ hbij, fun e => ?_⟩
  rw [MulEquiv.ofBijective_apply, hψ, List.prod_ofFn]
  rfl

end CFSG.LocalAnalysis.SteinbergCD
