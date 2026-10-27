module

public import CFSG.LocalAnalysis.StandardType.GGResITransport
public import CFSG.LocalAnalysis.StandardType.GGResIIClassify
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.LocalAnalysis.StandardType.GGResIShapeAsm

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

theorem ggResI_finite_vec {ι : Type} [Fintype ι] {A : Matrix ι ι ℤ} (hA : TauCeti.IsFiniteType A)
    (u : ι → ℕ) (hu : ∃ i, u i ≠ 0) (hAu : ∀ i, u i ≠ 0 → ∑ j, A i j * (u j : ℤ) ≤ 0) : False := by
  obtain ⟨d, hd, hpd⟩ := hA.exists_symmetrizer
  set x : ι → ℚ := fun i => (u i : ℚ)
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hu
    intro h0
    have := congrFun h0 i
    simp only [x, Pi.zero_apply, Nat.cast_eq_zero] at this
    exact hi this
  have hpos := hpd.dotProduct_mulVec_pos hx
  have hle : star x ⬝ᵥ ((Matrix.of fun i j => d i * (A i j : ℚ)) *ᵥ x) ≤ 0 := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply]
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : u i = 0
    · simp [x, hi]
    · have h1 : (∑ j, A i j * (u j : ℤ) : ℤ) ≤ 0 := hAu i hi
      have h2 : (∑ j, (A i j : ℚ) * (u j : ℚ)) ≤ 0 := by exact_mod_cast h1
      have h3 : ∑ j, d i * (A i j : ℚ) * x j = d i * ∑ j, (A i j : ℚ) * (u j : ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [x]
        ring
      rw [h3]
      have hxi : 0 ≤ x i := by simp [x]
      exact mul_nonpos_of_nonneg_of_nonpos hxi (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hd i)) h2)
  linarith

theorem ggResI_no_cycle {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : TauCeti.IsFiniteType A) (S : Finset ι) (hS : S.Nonempty)
    (hdeg : ∀ i ∈ S, 2 ≤ (S.filter fun j => j ≠ i ∧ A i j ≠ 0).card) : False := by
  refine ggResI_finite_vec hA (fun i => if i ∈ S then 1 else 0) ?_ ?_
  · obtain ⟨i, hi⟩ := hS
    exact ⟨i, by simp [hi]⟩
  · intro i hi
    have hiS : i ∈ S := by
      by_contra h
      simp [h] at hi
    have hsplit : ∑ j, A i j * (((if j ∈ S then 1 else 0 : ℕ) : ℕ) : ℤ) = ∑ j ∈ S, A i j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ S)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => j ∉ S) (fun j hj => by
        simp only [Finset.mem_filter] at hj
        simp [hj.2]), add_zero]
      have : Finset.univ.filter (fun j => j ∈ S) = S := by ext j; simp
      rw [this]
      exact Finset.sum_congr rfl fun j hj => by simp [hj]
    rw [hsplit, ← Finset.add_sum_erase S _ hiS, hA.apply_self]
    have hle : ∑ j ∈ S.erase i, A i j ≤
        ∑ j ∈ S.erase i, (if A i j ≠ 0 then (-1 : ℤ) else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have h0 := hA.apply_le_zero_of_ne (Ne.symm hji)
      split_ifs with hne
      · omega
      · omega
    have hf : (S.erase i).filter (fun j => A i j ≠ 0) = S.filter (fun j => j ≠ i ∧ A i j ≠ 0) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    have hcount : ∑ j ∈ S.erase i, (if A i j ≠ 0 then (-1 : ℤ) else 0) =
        -((S.filter fun j => j ≠ i ∧ A i j ≠ 0).card : ℤ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hf]
      simp
    have := hdeg i hiS
    omega

@[expose] def ggCartanPairs : List (ℤ × ℤ) :=
  [(0, 0), (-1, -1), (-1, -2), (-2, -1), (-1, -3), (-3, -1)]

@[expose] def ggCartanPairsNZ : List (ℤ × ℤ) := [(-1, -1), (-1, -2), (-2, -1), (-1, -3), (-3, -1)]

theorem ggCartanPair_mem {Γ : Type} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {i j : Γ} (hij : i ≠ j) : (C i j, C j i) ∈ ggCartanPairs := by
  rcases hC.2 i j hij with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
  · simp [ggCartanPairs, h1, h2]
  · simp [ggCartanPairs, h1, h2]
  · generalize C i j = a at h1 h2 h3
    generalize C j i = c at h1 h2 h3
    have ha : -2 ≤ a := by nlinarith
    have hc : -2 ≤ c := by nlinarith
    interval_cases a <;> interval_cases c <;> simp_all [ggCartanPairs]
  · generalize C i j = a at h1 h2 h3
    generalize C j i = c at h1 h2 h3
    have ha : -3 ≤ a := by nlinarith
    have hc : -3 ≤ c := by nlinarith
    interval_cases a <;> interval_cases c <;> simp_all [ggCartanPairs]

theorem ggCartanPair_bounds {a b : ℤ} (h : (a, b) ∈ ggCartanPairs) :
    -3 ≤ a ∧ a ≤ 0 ∧ -3 ≤ b ∧ b ≤ 0 := by
  simp only [ggCartanPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num

theorem ggCartanPair_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b c d : ℤ}
    (hab : (a, b) ∈ ggCartanPairs) (hcd : (c, d) ∈ ggCartanPairs) (h1 : (a : ZMod p) = c)
    (h2 : (b : ZMod p) = d) : a = c ∧ b = d := by
  have hdvd : ∀ x y : ℤ, (x : ZMod p) = y → (p : ℤ) ∣ x - y := by
    intro x y hxy
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxy, sub_self]
  have hd1 := hdvd a c h1
  have hd2 := hdvd b d h2
  by_cases hp3 : p = 3
  · subst hp3
    simp only [ggCartanPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hab hcd
    push_cast at hd1 hd2
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    omega
  · have hpp : p.Prime := Fact.out
    have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      all_goals first
        | exact absurd rfl hp2
        | exact absurd rfl hp3
        | exact absurd hpp (by norm_num)
    have key : ∀ x y : ℤ, -3 ≤ x → x ≤ 0 → -3 ≤ y → y ≤ 0 → (p : ℤ) ∣ x - y → x = y := by
      intro x y hx1 hx2 hy1 hy2 hxy
      have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      have : |x - y| < p := by
        rw [abs_lt]
        constructor <;> omega
      exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hxy this)
    obtain ⟨ha1, ha2, hb1, hb2⟩ := ggCartanPair_bounds hab
    obtain ⟨hc1, hc2, hd1', hd2'⟩ := ggCartanPair_bounds hcd
    exact ⟨key a c ha1 ha2 hc1 hc2 hd1, key b d hb1 hb2 hd1' hd2' hd2⟩

end CFSG.StandardType
