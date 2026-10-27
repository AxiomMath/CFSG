module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem exists_rep_of_ker_le {J B L : Type*} [Group J] [Group B] [Group L] (f : J →* B)
    (hf : Function.Surjective f) (ρ : J →* L) (hker : ∀ j : J, f j = 1 → ρ j = 1) :
    ∃ ρ' : B →* L, ∀ j : J, ρ' (f j) = ρ j := by
  have hle : f.ker ≤ ρ.ker := fun j hj =>
    MonoidHom.mem_ker.mpr (hker j (MonoidHom.mem_ker.mp hj))
  refine ⟨f.liftOfSurjective hf ⟨ρ, hle⟩, fun j => ?_⟩
  exact MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨ρ, hle⟩ j

theorem exists_noncomm_of_sup_eq_top {X : Type} [Group X] {A B : Subgroup X}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (htop : A ⊔ B = ⊤) (hX : ∃ a b : X, a * b ≠ b * a) : ∃ a ∈ A, ∃ b ∈ B, a * b ≠ b * a := by
  by_contra h
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    by_contra hne
    exact h ⟨a, ha, b, hb, hne⟩
  have hAcenter : A ≤ Subgroup.center X := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro x
    have hAc : A ≤ Subgroup.centralizer ({a} : Set X) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hA y hy a ha).symm
    have hBc : B ≤ Subgroup.centralizer ({a} : Set X) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm a ha b hb
    have hle := sup_le hAc hBc
    rw [htop] at hle
    exact ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top x))) a
      (Set.mem_singleton a)).symm
  have hBcenter : B ≤ Subgroup.center X := by
    intro b hb
    rw [Subgroup.mem_center_iff]
    intro x
    have hAc : A ≤ Subgroup.centralizer ({b} : Set X) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm y hy b hb).symm
    have hBc : B ≤ Subgroup.centralizer ({b} : Set X) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hB c hc b hb).symm
    have hle := sup_le hAc hBc
    rw [htop] at hle
    exact ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top x))) b
      (Set.mem_singleton b)).symm
  have hcenter : Subgroup.center X = ⊤ :=
    top_le_iff.mp (by rw [← htop]; exact sup_le hAcenter hBcenter)
  obtain ⟨a, b, hab⟩ := hX
  have ham : a ∈ Subgroup.center X := by rw [hcenter]; exact Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ham b).symm

theorem exists_mem_of_mem_closure {G : Type} [Group G] (𝒞 : Set (Subgroup G)) (hne : 𝒞.Nonempty)
    (hmul : ∀ A ∈ 𝒞, ∀ B ∈ 𝒞, ∀ a ∈ A, ∀ b ∈ B, ∃ C ∈ 𝒞, a * b ∈ C) {j : G}
    (hj : j ∈ Subgroup.closure (⋃ A ∈ 𝒞, (A : Set G))) : ∃ C ∈ 𝒞, j ∈ C := by
  refine Subgroup.closure_induction (p := fun x _ => ∃ C ∈ 𝒞, x ∈ C) ?_ ?_ ?_ ?_ hj
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
    exact ⟨A, hA, hxA⟩
  · rcases hne with ⟨C, hC⟩
    exact ⟨C, hC, C.one_mem⟩
  · intro x y _ _ ihx ihy
    rcases ihx with ⟨A, hA, hxA⟩
    rcases ihy with ⟨B, hB, hyB⟩
    exact hmul A hA B hB x hxA y hyB
  · intro x _ ihx
    rcases ihx with ⟨C, hC, hxC⟩
    exact ⟨C, hC, C.inv_mem hxC⟩

theorem card_eq_of_partition {G : Type} [Group G] [Finite G] {J : Subgroup G}
    {𝒞 : Set (Subgroup G)} {q : ℕ} (hle : ∀ A ∈ 𝒞, A ≤ J) (hcard : ∀ A ∈ 𝒞, Nat.card A = q)
    (hti : ∀ A ∈ 𝒞, ∀ B ∈ 𝒞, A ≠ B → A ⊓ B = ⊥) (hcov : ∀ j ∈ J, ∃ A ∈ 𝒞, j ∈ A) :
    Nat.card J = 𝒞.ncard * (q - 1) + 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let S : Finset (Subgroup G) := (Set.toFinite 𝒞).toFinset
  let t : Subgroup G → Finset G := fun A => ((A : Set G).toFinset).erase 1
  have ht : ∀ A ∈ S, (t A).card = q - 1 := by
    intro A hA
    have hA' : A ∈ 𝒞 := (Set.Finite.mem_toFinset _).mp hA
    rw [Finset.card_erase_of_mem (by simp), Set.toFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
    rw [← hcard A hA']
    rfl
  have hpair : (S : Set (Subgroup G)).PairwiseDisjoint t := by
    intro A hA B hB hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxA hxB
    simp only [t, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hxA hxB
    have h := hti A ((Set.Finite.mem_toFinset _).mp hA) B ((Set.Finite.mem_toFinset _).mp hB)
      hne
    have hx : x ∈ A ⊓ B := ⟨hxA.2, hxB.2⟩
    rw [h, mem_bot] at hx
    exact hxA.1 hx
  have hsub : S.biUnion t = ((J : Set G).toFinset).erase 1 := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe]
    constructor
    · rintro ⟨A, hA, hxA⟩
      simp only [t, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hxA
      exact ⟨hxA.1, hle A ((Set.Finite.mem_toFinset _).mp hA) hxA.2⟩
    · rintro ⟨hxne, hxJ⟩
      obtain ⟨A, hA, hxA⟩ := hcov x hxJ
      refine ⟨A, (Set.Finite.mem_toFinset _).mpr hA, ?_⟩
      simp only [t, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe]
      exact ⟨hxne, hxA⟩
  have hcardS : (S.biUnion t).card = S.card * (q - 1) := by
    rw [Finset.card_biUnion hpair, Finset.sum_congr rfl ht, Finset.sum_const, smul_eq_mul]
  have hcardJ : (((J : Set G).toFinset).erase 1).card = Nat.card J - 1 := by
    rw [Finset.card_erase_of_mem (by simp), Set.toFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
    rfl
  have hmain : S.card * (q - 1) = Nat.card J - 1 := by
    rw [← hcardS, hsub, hcardJ]
  have hS : S.card = 𝒞.ncard := by
    rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
    rfl
  have hJ1 : 1 ≤ Nat.card J := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨1, J.one_mem⟩⟩
  rw [← Nat.sub_add_cancel hJ1, ← hmain, hS]

theorem not_two_pow_of_partition {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1) + 1 ≠ 2 ^ k := by
  intro h
  generalize hq : 2 ^ n = q at h
  have hq2 : 2 ≤ q := by
    rw [← hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hn
  have hq1 : 1 ≤ q := by omega
  set r : ℕ := q - 1 with hr
  have hq_eq : q = r + 1 := by rw [hr]; exact (Nat.sub_add_cancel hq1).symm
  have hq3sub : q ^ 3 - q ^ 2 = q ^ 2 * r := by
    have h1 : q ^ 2 * r = q ^ 2 * (q - 1) := by rw [hr]
    rw [h1, Nat.mul_sub_left_distrib, show q ^ 2 * q = q ^ 3 by ring, mul_one]
  have hm_eq : q ^ 3 - q ^ 2 + 1 = q ^ 2 * r + 1 := by rw [hq3sub]
  have hfac : (q ^ 3 + 1) * (q - 1) + 1 = q * (q ^ 3 - q ^ 2 + 1) := by
    rw [hm_eq, hq_eq, show (r + 1) - 1 = r by omega]
    ring
  have hm5 : 5 ≤ q ^ 3 - q ^ 2 + 1 := by
    rw [hm_eq]
    have hq22 : 2 ^ 2 ≤ q ^ 2 := pow_le_pow_left' hq2 2
    have hr1 : 1 ≤ r := by rw [hr]; omega
    have h4 : 4 ≤ q ^ 2 * r := by
      calc 4 = 2 ^ 2 * 1 := by norm_num
        _ ≤ q ^ 2 * r := Nat.mul_le_mul hq22 hr1
    omega
  have hodd : ¬ 2 ∣ q ^ 3 - q ^ 2 + 1 := by
    rw [hm_eq]
    intro h2
    have hqdvd : 2 ∣ q := by
      rw [← hq]
      exact dvd_pow_self 2 (by omega : n ≠ 0)
    have h2q2 : 2 ∣ q ^ 2 := by
      have h' := hqdvd.mul_right q
      rwa [← pow_two] at h'
    have h2qr : 2 ∣ q ^ 2 * r := h2q2.mul_right r
    obtain ⟨d, hd⟩ := h2qr
    obtain ⟨c, hc⟩ := h2
    omega
  have hdvd : q ^ 3 - q ^ 2 + 1 ∣ 2 ^ k := by
    refine ⟨q, ?_⟩
    rw [← h, hfac, Nat.mul_comm]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases i with _ | i
  · rw [hi] at hm5
    omega
  · apply hodd
    rw [hi]
    exact ⟨2 ^ i, by rw [pow_succ, mul_comm]⟩

end CFSG.LocalAnalysis.WeakClosure81

end
