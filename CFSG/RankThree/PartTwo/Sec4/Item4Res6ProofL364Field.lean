module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.QuadraticAlgebra.Basic
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

abbrev K64 : Type := GaloisField 2 6

noncomputable instance : Fintype K64 := Fintype.ofFinite _

theorem card_K64 : Nat.card K64 = 64 := by
  rw [GaloisField.card 2 6 (by norm_num)]; norm_num

theorem pow_sixtyfour (x : K64) : x ^ 64 = x := by
  have := FiniteField.pow_card x
  rwa [Fintype.card_eq_nat_card, card_K64] at this

theorem card_units_K64 : Nat.card K64ˣ = 63 := by
  rw [Nat.card_units, card_K64]

theorem two_eq_zero : (2 : K64) = 0 := CharTwo.two_eq_zero

theorem exists_unit_orderOf (p : ℕ) [Fact p.Prime] (h : p ∣ 63) :
    ∃ u : K64ˣ, orderOf u = p := by
  have : p ∣ Nat.card K64ˣ := by rw [card_units_K64]; exact h
  exact exists_prime_orderOf_dvd_card' p this

theorem exists_omega : ∃ ω : K64, ω ^ 2 + ω + 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_unit_orderOf 3 (by norm_num)
  refine ⟨u, ?_⟩
  have h3 : (u : K64) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have h1 : (u : K64) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hsub : (u : K64) - 1 ≠ 0 := sub_ne_zero.mpr h1
  have : ((u : K64) - 1) * ((u : K64) ^ 2 + u + 1) = 0 := by
    linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left hsub

noncomputable def ω : K64 := Classical.choose exists_omega

theorem omega_sq_add : ω ^ 2 + ω + 1 = 0 := Classical.choose_spec exists_omega

theorem omega_cube : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * omega_sq_add

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have := omega_sq_add
  rw [h] at this
  have h3 : (3 : K64) = 1 := by
    have : (3 : K64) = 2 + 1 := by norm_num
    rw [this, two_eq_zero, zero_add]
  norm_num at this
  rw [h3] at this
  exact one_ne_zero this

theorem omega_ne_zero : ω ≠ 0 := by
  intro h
  have := omega_cube
  rw [h] at this
  norm_num at this

theorem exists_seventh : ∃ b : K64, b ^ 7 = 1 ∧ b ≠ 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unit_orderOf 7 (by norm_num)
  refine ⟨u, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    norm_num at hu

noncomputable def b7 : K64 := Classical.choose exists_seventh

theorem b7_pow : b7 ^ 7 = 1 := (Classical.choose_spec exists_seventh).1

theorem b7_ne_one : b7 ≠ 1 := (Classical.choose_spec exists_seventh).2

theorem b7_ne_zero : b7 ≠ 0 := by
  intro h
  have := b7_pow
  rw [h] at this
  norm_num at this

theorem seven_dvd_of_pow_eq_one {β : K64} (h7 : β ^ 7 = 1) (h1 : β ≠ 1) {k : ℕ}
    (hk : β ^ k = 1) : 7 ∣ k := by
  have hd : Nat.gcd k 7 ∣ 7 := Nat.gcd_dvd_right k 7
  have hβ : β ^ Nat.gcd k 7 = 1 := pow_gcd_eq_one.mpr ⟨hk, h7⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
  · rw [h, pow_one] at hβ
    exact absurd hβ h1
  · rw [← h]; exact Nat.gcd_dvd_left k 7

noncomputable def σ4 : K64 ≃+* K64 := iterateFrobeniusEquiv K64 2 2

theorem σ4_apply (x : K64) : σ4 x = x ^ 4 := by
  rw [σ4, iterateFrobeniusEquiv_def]; norm_num

theorem σ4_cube : σ4 ^ 3 = 1 := by
  ext x
  rw [pow_three, RingAut.mul_apply, RingAut.mul_apply, σ4_apply, σ4_apply, σ4_apply,
    RingAut.one_apply, ← pow_mul, ← pow_mul]
  exact pow_sixtyfour x

theorem σ4_omega : σ4 ω = ω := by
  rw [σ4_apply, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, omega_cube, one_mul]

theorem σ4_b7 : σ4 b7 = b7 ^ 4 := σ4_apply b7

theorem σ4_ne_one : σ4 ≠ 1 := by
  intro h
  have h1 : σ4 b7 = b7 := by rw [h]; rfl
  rw [σ4_b7] at h1
  have h3 : b7 ^ 3 = 1 := by
    have : b7 ^ 4 = b7 ^ 3 * b7 := pow_succ b7 3
    rw [this] at h1
    exact (mul_eq_right₀ b7_ne_zero).mp h1
  have := seven_dvd_of_pow_eq_one b7_pow b7_ne_one h3
  norm_num at this

theorem orderOf_σ4 : orderOf σ4 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime σ4_cube σ4_ne_one

theorem eq_σ4_or_sq {τ : K64 ≃+* K64} (hτ : orderOf τ = 3) : τ = σ4 ∨ τ = σ4 * σ4 := by
  obtain ⟨-, h | h⟩ := CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
    Nat.prime_two (by norm_num : 1 ≤ 6) card_K64 hτ
  · left
    ext x
    rw [h x, σ4_apply]
    norm_num
  · right
    ext x
    rw [h x, RingAut.mul_apply, σ4_apply, σ4_apply, ← pow_mul]
    norm_num

theorem eq_of_add_eq_zero {x y : K64} (h : x + y = 0) : x = y := by
  have : x = -y := eq_neg_of_add_eq_zero_left h
  rw [this, CharTwo.neg_eq]

theorem eq_of_σ4_fixed {x : K64} (hx : σ4 x = x) : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := by
  rw [σ4_apply] at hx
  have key : (x * (x + 1)) * ((x + ω) * (x + ω + 1)) = 0 := by
    linear_combination hx + (x ^ 3 + ω * x ^ 3 + ω * x ^ 2) * two_eq_zero +
      (x * (x + 1)) * omega_sq_add
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (eq_of_add_eq_zero h))
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl (eq_of_add_eq_zero h)))
    · exact Or.inr (Or.inr (Or.inr (eq_of_add_eq_zero (by rw [← add_assoc]; exact h))))

abbrev F4 : Type := QuadraticAlgebra (ZMod 2) 1 1

instance : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩

instance : Fintype F4 := Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm

theorem card_F4 : Fintype.card F4 = 4 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (1 : ZMod 2) 1)]
  simp

@[expose] def ω4 : F4 := ⟨0, 1⟩

theorem omega_mul_omega : ω * ω = (1 : ZMod 2) • (1 : K64) + (1 : ZMod 2) • ω := by
  rw [one_smul, one_smul]
  have h := omega_sq_add
  have : ω * ω = -(ω + 1) := by linear_combination h
  rw [this, CharTwo.neg_eq, add_comm]

noncomputable def ι : F4 →+* K64 :=
  (QuadraticAlgebra.lift (A := K64) ⟨ω, omega_mul_omega⟩).toRingHom

theorem ι_apply (x : F4) : ι x = x.re • (1 : K64) + x.im • ω := by
  simp [ι]

theorem ι_ω4 : ι ω4 = ω := by
  rw [ι_apply]
  simp [ω4]

theorem ι_injective : Function.Injective ι := ι.injective

theorem σ4_smul (r : ZMod 2) (y : K64) : σ4 (r • y) = r • σ4 y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  have := RingHom.ext_zmod (σ4.toRingHom.comp (algebraMap (ZMod 2) K64))
    (algebraMap (ZMod 2) K64)
  exact congrArg (fun f => f r) this

theorem σ4_ι (x : F4) : σ4 (ι x) = ι x := by
  rw [ι_apply, map_add, σ4_smul, σ4_smul, map_one, σ4_omega]

theorem exists_ι_of_σ4_fixed {x : K64} (hx : σ4 x = x) : ∃ y : F4, ι y = x := by
  rcases eq_of_σ4_fixed hx with rfl | rfl | rfl | rfl
  · exact ⟨0, map_zero ι⟩
  · exact ⟨1, map_one ι⟩
  · exact ⟨ω4, ι_ω4⟩
  · exact ⟨ω4 + 1, by rw [map_add, map_one, ι_ω4]⟩

theorem ι_pow_three {x : F4} (hx : x ≠ 0) : ι x ^ 3 = 1 := by
  have : x ^ 3 = 1 := by revert x; decide
  rw [← map_pow, this, map_one]

theorem exists_cube_root {l : K64} (hl : l ^ 21 = 1) : ∃ μ : K64, μ ^ 3 = l := by
  have hl0 : l ≠ 0 := by
    intro h; rw [h] at hl; norm_num at hl
  set u : K64ˣ := Units.mk0 l hl0 with hu
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K64ˣ)
  have hord : orderOf g = 63 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_K64]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
  have hu21 : u ^ 21 = 1 := Units.ext (by simpa [hu] using hl)
  have h21 : g ^ (k * 21) = 1 := by
    rw [zpow_mul, hk]; exact_mod_cast hu21
  have hdvd : (63 : ℤ) ∣ k * 21 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h21
    rwa [hord] at this
  obtain ⟨m, hm⟩ : (3 : ℤ) ∣ k := by omega
  refine ⟨((g ^ m : K64ˣ) : K64), ?_⟩
  have hgm : (g ^ m) ^ 3 = u := by
    rw [← hk, hm, ← zpow_natCast, ← zpow_mul, mul_comm]; norm_num
  rw [← Units.val_pow_eq_pow_val, hgm, hu, Units.val_mk0]

@[expose] def gensSet (ζ β : K64) : Set K64 := {x | ∃ i j : ℕ, x = ζ ^ i * β ^ j}

theorem mul_mem_closure_gensSet {ζ β x y : K64} (hx : x ∈ AddSubgroup.closure (gensSet ζ β))
    (hy : y ∈ AddSubgroup.closure (gensSet ζ β)) : x * y ∈ AddSubgroup.closure (gensSet ζ β) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, j, rfl⟩ := hx
      obtain ⟨k, l, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨i + k, j + l, by ring⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem closure_gensSet_eq_top {ζ β : K64} (hζ : ζ ^ 2 + ζ + 1 = 0) (h7 : β ^ 7 = 1)
    (h1 : β ≠ 1) : AddSubgroup.closure (gensSet ζ β) = ⊤ := by
  classical
  set S := AddSubgroup.closure (gensSet ζ β) with hS
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ3; norm_num at hζ3
  have hβ0 : β ≠ 0 := by intro h; rw [h] at h7; norm_num at h7
  have hζ1 : ζ ≠ 1 := by
    intro h; rw [h] at hζ
    have : (1 : K64) ^ 2 + 1 + 1 = 1 := by
      rw [one_pow, add_assoc, ← two_mul, two_eq_zero, zero_mul, add_zero]
    rw [this] at hζ; exact one_ne_zero hζ
  have hmem : ∀ i j : ℕ, ζ ^ i * β ^ j ∈ S := fun i j => AddSubgroup.subset_closure ⟨i, j, rfl⟩
  let U : Subgroup K64ˣ :=
    { carrier := {u | (u : K64) ∈ S}
      mul_mem' := fun {a b} ha hb => by
        show ((a * b : K64ˣ) : K64) ∈ S
        rw [Units.val_mul]; exact mul_mem_closure_gensSet ha hb
      one_mem' := by
        show ((1 : K64ˣ) : K64) ∈ S
        rw [Units.val_one, show (1 : K64) = ζ ^ 0 * β ^ 0 by simp]; exact hmem 0 0
      inv_mem' := fun {a} ha => by
        show ((a⁻¹ : K64ˣ) : K64) ∈ S
        have h63 : a ^ 63 = 1 := by
          rw [← card_units_K64]; exact pow_card_eq_one'
        have hinv : a⁻¹ = a ^ 62 := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv]; rw [← pow_succ, h63]
        rw [hinv, Units.val_pow_eq_pow_val]
        have : ∀ n : ℕ, (a : K64) ^ (n + 1) ∈ S := by
          intro n
          induction n with
          | zero => rw [zero_add, pow_one]; exact ha
          | succ n ih => rw [pow_succ]; exact mul_mem_closure_gensSet ih ha
        exact this 61 }
  have hζU : Units.mk0 ζ hζ0 ∈ U := by
    show ζ ∈ S
    rw [show ζ = ζ ^ 1 * β ^ 0 by simp]; exact hmem 1 0
  have hβU : Units.mk0 β hβ0 ∈ U := by
    show β ∈ S
    rw [show β = ζ ^ 0 * β ^ 1 by simp]; exact hmem 0 1
  have h3 : 3 ∣ Nat.card U := by
    have : orderOf (Units.mk0 ζ hζ0) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime (Units.ext (by simpa using hζ3)) ?_
      intro h; exact hζ1 (by simpa using congrArg Units.val h)
    rw [← this, ← Subgroup.orderOf_mk _ hζU]
    exact orderOf_dvd_natCard _
  have h7' : 7 ∣ Nat.card U := by
    have : orderOf (Units.mk0 β hβ0) = 7 := by
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine orderOf_eq_prime (Units.ext (by simpa using h7)) ?_
      intro h; exact h1 (by simpa using congrArg Units.val h)
    rw [← this, ← Subgroup.orderOf_mk _ hβU]
    exact orderOf_dvd_natCard _
  have hcardU : Nat.card U + 1 = Nat.card S := by
    have e : U ≃ {x : S // x ≠ 0} :=
      { toFun := fun u => ⟨⟨(u : K64ˣ), u.2⟩, fun h => (u : K64ˣ).ne_zero (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨Units.mk0 (x : S) (fun h => x.2 (Subtype.ext h)), (x : S).2⟩
        left_inv := fun u => by ext; rfl
        right_inv := fun x => by ext; rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card S := Fintype.card_pos
    omega
  have hdvd : Nat.card S ∣ 64 := by
    rw [← card_K64]; exact AddSubgroup.card_addSubgroup_dvd_card S
  have h21 : 21 ∣ Nat.card S - 1 := by
    have : Nat.card S - 1 = Nat.card U := by omega
    rw [this]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7'
  have hS64 : Nat.card S = 64 := by
    have hpos : 0 < Nat.card S := Nat.card_pos
    have hle : Nat.card S ≤ 64 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card S <;> simp_all
  rw [← AddSubgroup.card_eq_iff_eq_top, hS64, card_K64]

end CFSG.RankThree.PartTwo.Sec4.Res6L364
