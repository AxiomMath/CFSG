module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.GroupTheory.CommutatorProductCard
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section FieldPart

private theorem iterate_semilinear {F : Type} [Field F] (σ : RingAut F) (a : F) (k : ℕ)
    (y : F) :
    (fun x => a * σ x)^[k] y = (∏ j ∈ Finset.range k, (σ ^ j) a) * (σ ^ k) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, Finset.prod_range_succ, map_mul, pow_succ,
      RingAut.mul_apply]
    ring

private theorem norm_fixed {F : Type} [Field F] (σ : RingAut F) {a : F} (ha : a ≠ 0) {s : ℕ}
    (hs : σ ^ s = 1) :
    σ (∏ j ∈ Finset.range s, (σ ^ j) a) = ∏ j ∈ Finset.range s, (σ ^ j) a := by
  rw [map_prod]
  have h1 : ∀ j : ℕ, σ ((σ ^ j) a) = (σ ^ (j + 1)) a := fun j => by
    rw [pow_succ', RingAut.mul_apply]
  simp_rw [h1]
  have h2 := Finset.prod_range_succ' (fun j => (σ ^ j) a) s
  have h3 := Finset.prod_range_succ (fun j => (σ ^ j) a) s
  rw [hs, RingAut.one_apply] at h3
  rw [pow_zero, RingAut.one_apply] at h2
  exact mul_right_cancel₀ ha (h2.symm.trans h3)

private theorem mul_pred_add_one_lt_pow {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    s * (r - 1) + 1 < r ^ s := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by omega⟩
  induction s, hs using Nat.le_induction with
  | base =>
    have : t + 2 - 1 = t + 1 := by omega
    rw [this]
    nlinarith
  | succ s hs ih =>
    have e : t + 2 - 1 = t + 1 := by omega
    rw [e] at ih ⊢
    rw [pow_succ]
    have h0 : s * (t + 1) + 2 ≤ (t + 2) ^ s := by omega
    have h1 := Nat.mul_le_mul_right (t + 2) h0
    nlinarith [Nat.zero_le (s * t * t), Nat.zero_le (s * t)]

private theorem ringAut_eq_one_of_iterate {F : Type} [Field F] [Finite F] (σ : RingAut F)
    {a : F} (ha : a ≠ 0)
    (hT : ∀ k : ℕ, (∀ y : F, (fun x => a * σ x)^[k] y = y) → Nat.card F - 1 ∣ k) :
    σ = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (RingAut F) :=
    Finite.of_injective (fun τ : RingAut F => (τ : F → F)) DFunLike.coe_injective
  by_contra hσ
  set s := orderOf σ with hsdef
  have hs0 : 0 < s := (isOfFinOrder_of_finite σ).orderOf_pos
  have hs1 : s ≠ 1 := fun h => hσ (orderOf_eq_one_iff.mp h)
  have hs2 : 2 ≤ s := by omega
  set H : Subgroup (RingAut F) := Subgroup.zpowers σ with hH
  haveI : Fintype H := Fintype.ofFinite H
  set F₀ : Subfield F := FixedPoints.subfield H F with hF₀
  have hrank : Module.finrank F₀ F = s := by
    rw [hF₀, FixedPoints.finrank_eq_card H F, Fintype.card_eq_nat_card, hH, Nat.card_zpowers]
  have hcardF : Nat.card F = Nat.card F₀ ^ s := by
    rw [← hrank]
    exact Module.natCard_eq_pow_finrank
  set N : F := ∏ j ∈ Finset.range s, (σ ^ j) a with hNdef
  have hNσ : σ N = N := norm_fixed σ ha (pow_orderOf_eq_one σ)
  have hNF₀ : N ∈ F₀ := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    show (σ ^ k) N = N
    have hpow : ∀ m : ℕ, (σ ^ m) N = N := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ', RingAut.mul_apply, ih, hNσ]
    rcases k with m | m
    · simpa using hpow m
    · rw [zpow_negSucc]
      have h1 := hpow (m + 1)
      calc ((σ ^ (m + 1))⁻¹) N = ((σ ^ (m + 1))⁻¹) ((σ ^ (m + 1)) N) := by rw [h1]
        _ = N := by rw [← RingAut.mul_apply, inv_mul_cancel, RingAut.one_apply]
  have hN0 : N ≠ 0 := by
    rw [hNdef, Finset.prod_ne_zero_iff]
    intro j _
    exact (map_ne_zero _).mpr ha
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  have hNr : N ^ (Nat.card F₀ - 1) = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨N, hNF₀⟩ : F₀)
      (fun h => hN0 (congrArg Subtype.val h))
    rw [Fintype.card_eq_nat_card] at h1
    exact congrArg Subtype.val h1
  have hiter : ∀ (j : ℕ) (y : F), (fun x => a * σ x)^[s * j] y = N ^ j * y := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      have hσs : σ ^ s = 1 := pow_orderOf_eq_one σ
      rw [Nat.mul_succ, Function.iterate_add_apply, ih, iterate_semilinear, hσs,
        RingAut.one_apply, ← hNdef, pow_succ]
      ring
  have hdvd := hT (s * (Nat.card F₀ - 1)) fun y => by rw [hiter, hNr, one_mul]
  have hr2 : 2 ≤ Nat.card F₀ := by
    haveI : Nontrivial F₀ := inferInstance
    exact Finite.one_lt_card
  have hpos : 0 < s * (Nat.card F₀ - 1) := Nat.mul_pos hs0 (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  rw [hcardF] at hle
  have key := mul_pred_add_one_lt_pow hr2 hs2
  omega

end FieldPart

end CFSG.RankThree.GF2n.Smith81
