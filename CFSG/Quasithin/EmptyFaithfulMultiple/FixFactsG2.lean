module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Props
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open Matrix CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Assembly.LowTwoRank
open CFSG.Open (quasithinG2 quasithinZorn)
open scoped commutatorElement

namespace FFL

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def g2T₂₁ (K : Type) [Field K] : SL3 K :=
  SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) 1

@[expose] noncomputable def g2τ (K : Type) [Field K] [CharP K 2] : ↥(quasithinG2 K) :=
  cayleyEquivG2 K (g2A (g2A₁ K) * g2X ![0, 0, 1] * g2Y ![0, 1, 0] * g2X ![0, 0, 1] *
    g2A (g2A₁ K) * g2Y ![0, 1, 0])

theorem g2τ_zmk (r a b c d e f s : K) :
    g2E (g2τ K) (zmk r a b c d e f s) =
      zmk (r + c + d) (r + a + b + e + s) c (b + d) d (r + b + c + d + f + s) (c + d + e)
        (c + d + s) := by
  change gAFun ((g2A₁ K : SL3 K) : Matrix (Fin 3) (Fin 3) K)
    (xaFun ![0, 0, 1] (ybFun ![0, 1, 0] (xaFun ![0, 0, 1]
      (gAFun ((g2A₁ K : SL3 K) : Matrix (Fin 3) (Fin 3) K)
        (ybFun ![0, 1, 0] (zmk r a b c d e f s)))))) = _
  have hneg : ∀ x : K, -x = x := CharTwo.neg_eq
  simp only [ybFun_zmk, gAFun_zmk, xaFun_zmk]
  apply zmk_congr <;>
    simp [g2A₁, Matrix.SpecialLinearGroup.transvection, Matrix.transvection,
      Matrix.adjugate_fin_three, sub_eq_add_neg, hneg] <;> ring_nf <;> reduce_mod_char!

theorem g2τ_pow_four_zmk (r a b c d e f s : K) :
    g2E (g2τ K) (g2E (g2τ K) (g2E (g2τ K) (g2E (g2τ K) (zmk r a b c d e f s)))) =
      zmk r (a + b + c) b c d (d + e) (d + f) s := by
  simp only [g2τ_zmk]
  apply zmk_congr <;> ring_nf <;> reduce_mod_char!

theorem g2τ_pow_eight : g2τ K ^ 8 = 1 := by
  have key : ∀ x, g2E (g2τ K) (g2E (g2τ K) (g2E (g2τ K) (g2E (g2τ K) (g2E (g2τ K)
      (g2E (g2τ K) (g2E (g2τ K) (g2E (g2τ K) x))))))) = x := by
    intro x
    rw [zorn_eta x, g2τ_pow_four_zmk, g2τ_pow_four_zmk]
    apply zmk_congr <;> ring_nf <;> reduce_mod_char!
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h8 : ((g2τ K ^ 8 : ↥(quasithinG2 K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x =
      (⇑(g2E (g2τ K)))^[8] x := by
    rw [Subgroup.coe_pow, LinearEquiv.coe_pow]
  rw [h8]
  show _ = x
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_zero_apply]
  exact key x

theorem transvection_inv_one {i j : Fin 3} (hij : i ≠ j) :
    (SpecialLinearGroup.transvection hij (1 : K))⁻¹ = SpecialLinearGroup.transvection hij 1 := by
  rw [SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]

theorem g2τ_word_eq_commutator :
    g2A (g2A₁ K) * g2X ![0, 0, 1] * g2Y ![0, 1, 0] * g2X ![0, 0, 1] * g2A (g2A₁ K) *
      g2Y ![0, 1, 0] = ⁅g2A (g2A₁ K) * g2X ![0, 0, 1], g2Y ![0, 1, 0]⁆ := by
  have hX : (g2X (F := K) ![0, 0, 1])⁻¹ = g2X ![0, 0, 1] :=
    inv_eq_of_mul_eq_one_right (g2X_mul_self _)
  have hY : (g2Y (F := K) ![0, 1, 0])⁻¹ = g2Y ![0, 1, 0] :=
    inv_eq_of_mul_eq_one_right (g2Y_mul_self _)
  have hA : (g2A (g2A₁ K))⁻¹ = g2A (g2A₁ K) := by
    rw [← map_inv, g2A₁, transvection_inv_one]
  rw [commutatorElement_def, _root_.mul_inv_rev, hX, hY, hA]
  group

theorem g2τ_eq_commutator :
    g2τ K = ⁅cayleyEquivG2 K (g2A (g2A₁ K) * g2X ![0, 0, 1]),
      cayleyEquivG2 K (g2Y ![0, 1, 0])⁆ := by
  rw [← map_commutatorElement, ← g2τ_word_eq_commutator]
  rfl

theorem coe_commutator_mem {G : Type*} [Group G] {H : Subgroup G} (g h : ↥H) :
    ((⁅g, h⁆ : ↥H) : G) ∈ ⁅H, H⁆ := by
  rw [show ((⁅g, h⁆ : ↥H) : G) = ⁅(g : G), (h : G)⁆ from map_commutatorElement H.subtype g h]
  exact Subgroup.commutator_mem_commutator g.2 h.2

theorem g2τ_mem : (g2τ K : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
    ⁅quasithinG2 K, quasithinG2 K⁆ := by
  rw [g2τ_eq_commutator]
  exact coe_commutator_mem _ _

theorem g2A₃_pow_three : g2A₃ K ^ 3 = 1 := by
  apply (specialLinearGroupEquivStatedSL 3 K).injective
  rw [map_pow, g2A₃_eq, map_one]
  exact slGamma_pow_three _

theorem g2γ_eq_commutator_sq :
    g2γ K = ⁅cayleyEquivG2 K (g2A (g2A₁ K)), cayleyEquivG2 K (g2A (g2T₂₁ K))⁆ *
      ⁅cayleyEquivG2 K (g2A (g2A₁ K)), cayleyEquivG2 K (g2A (g2T₂₁ K))⁆ := by
  set x := cayleyEquivG2 K (g2A (g2A₁ K)) with hx
  set y := cayleyEquivG2 K (g2A (g2T₂₁ K)) with hy
  have hxi : x⁻¹ = x := by
    rw [hx, ← map_inv, ← map_inv, g2A₁, transvection_inv_one]
  have hyi : y⁻¹ = y := by
    rw [hy, ← map_inv, ← map_inv, g2T₂₁, transvection_inv_one]
  have hxy : x * y = g2γ K := by
    rw [hx, hy, ← map_mul, ← map_mul, g2γ]
    rfl
  have h3 : (x * y) ^ 3 = 1 := by
    rw [hxy]
    exact g2γ_pow_three
  rw [commutatorElement_def, hxi, hyi, ← hxy]
  calc x * y = (x * y) ^ 3 * (x * y) := by rw [h3, one_mul]
    _ = x * y * x * y * (x * y * x * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem g2γ_mem : (g2γ K : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
    ⁅quasithinG2 K, quasithinG2 K⁆ := by
  rw [g2γ_eq_commutator_sq, Subgroup.coe_mul]
  exact Subgroup.mul_mem _ (coe_commutator_mem _ _) (coe_commutator_mem _ _)

theorem g2γ_ne_one : g2γ K ≠ 1 := by
  obtain ⟨m, -, hγ⟩ := g2γ_moves (K := K)
  intro h
  apply hγ
  have h1 : (FFModel.zornQ (quasithinG2 K)).act (g2γ K) m = m := by
    rw [h]
    rfl
  rw [h1, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem fixesFixed_of_zmk {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (τ γ : ↥Γ)
    (hτ : ∀ r a b c d e f s : K, (τ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (zmk r a b c d e f s) = zmk (r + c + d) (r + a + b + e + s) c (b + d) d
        (r + b + c + d + f + s) (c + d + e) (c + d + s))
    (hγ : ∀ r a s : K, (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (zmk r a 0 0 0 0 0 s) =
      zmk r a 0 0 0 0 0 s) :
    FixesFixed (FFModel.zornQ Γ) (Subgroup.zpowers τ) γ := by
  intro m hm0 hm
  obtain ⟨x, rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hm _ (Subgroup.mem_zpowers _)
  have htr : x.1 + x.2.2.2 = 0 := hm0
  have ht2 : (τ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = x + (t, 0, 0, t) := by
    have h0 : (τ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x + -x = (t, 0, 0, t) := ht
    rw [← h0]
    abel
  obtain ⟨r, a, b, c, d, e, f, s, rfl⟩ :
      ∃ r a b c d e f s : K, x = zmk r a b c d e f s := ⟨_, _, _, _, _, _, _, _, zorn_eta x⟩
  have hz : ((t, 0, 0, t) : quasithinZorn K) = zmk t 0 0 0 0 0 0 t := by
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;> fin_cases i <;> rfl
  rw [hτ, hz, zmk_add] at ht2
  obtain ⟨-, ha, hb, hc, -, he, hf, -⟩ := zmk_inj ht2
  have htr' : r + s = 0 := htr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd : d = 0 := by linear_combination hc - hb + (c - b) * h2
  have hb0 : b = 0 := by linear_combination he + hf - htr' - (c + d) * h2
  have hc0 : c = 0 := by linear_combination hb + hb0
  have he0 : e = 0 := by linear_combination ha - htr' - hb0
  have hf0 : f = 0 := by linear_combination -hf + hc0 + hd + he0
  refine ⟨0, ?_⟩
  change (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (zmk r a b c d e f s) +
    -zmk r a b c d e f s = (0, 0, 0, 0)
  rw [hb0, hc0, hd, he0, hf0, hγ, add_neg_cancel]
  rfl

theorem fixesFixed_g2Derived :
    FixesFixed (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆)
      (Subgroup.zpowers ⟨_, g2τ_mem (K := K)⟩) ⟨_, g2γ_mem (K := K)⟩ :=
  fixesFixed_of_zmk _ _ g2τ_zmk g2γ_zmk

end FFL

open FFL

theorem fixG2Derived_holds : FixG2Derived := by
  intro K _ _ hK
  have : CharP K 2 := charP_two_of_card (n := 1) (by rw [hK, pow_one])
  refine ⟨Subgroup.zpowers ⟨_, g2τ_mem (K := K)⟩, ?_, ⟨_, g2γ_mem (K := K)⟩, ?_, ?_,
    fixesFixed_g2Derived⟩
  · rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨3, Subtype.ext ?_⟩
    have h8 : (⟨_, g2τ_mem (K := K)⟩ : ↥⁅quasithinG2 K, quasithinG2 K⁆) ^ 8 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact congrArg Subtype.val (g2τ_pow_eight (K := K))
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      show ((2 ^ 3 : ℕ) : ℤ) = ((8 : ℕ) : ℤ) from rfl, zpow_natCast, h8, _root_.one_zpow]
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact congrArg Subtype.val (g2γ_pow_three (K := K))
  · intro h
    apply g2γ_ne_one (K := K)
    apply Subtype.ext
    exact congrArg (fun z : ↥⁅quasithinG2 K, quasithinG2 K⁆ =>
      (z : quasithinZorn K ≃ₗ[K] quasithinZorn K)) h

end CFSG.Quasithin.EmptyFaithfulMultiple
