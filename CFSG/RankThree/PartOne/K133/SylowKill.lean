module

public import CFSG.RankThree.PartOne.K133.TwoLoc

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open scoped Pointwise

theorem exists_sylow_two_normalized {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (P : Subgroup (MulAut X)) (hP : IsPGroup p P) (hn : ¬ p ∣ Nat.card (Sylow 2 X)) :
    ∃ U : Sylow 2 X, ∀ φ ∈ P, ∀ u ∈ (U : Subgroup X), φ u ∈ (U : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  let _inst : MulAction ↥P (Sylow 2 X) := Sylow.pointwiseMulAction
  have hmod := hP.card_modEq_card_fixedPoints (Sylow 2 X)
  have hne : (MulAction.fixedPoints ↥P (Sylow 2 X)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hn
    have h0 : Nat.card (MulAction.fixedPoints ↥P (Sylow 2 X)) = 0 := by
      rw [hemp]; simp
    rw [h0] at hmod
    exact (Nat.modEq_zero_iff_dvd).1 hmod
  obtain ⟨U, hU⟩ := hne
  refine ⟨U, fun φ hφ u hu => ?_⟩
  have h1 : (⟨φ, hφ⟩ : ↥P) • U = U := hU ⟨φ, hφ⟩
  have h2 : ((⟨φ, hφ⟩ : ↥P) • U : Sylow 2 X) = U := h1
  have h3 : ((⟨φ, hφ⟩ : ↥P) • (U : Subgroup X)) = (U : Subgroup X) := by
    have := congrArg (fun V : Sylow 2 X => (V : Subgroup X)) h2
    exact this
  have hmem : φ u ∈ ((⟨φ, hφ⟩ : ↥P) • (U : Subgroup X)) := Subgroup.smul_mem_pointwise_smul u _ _ hu
  rw [h3] at hmem
  exact hmem

theorem dead_of_not_dvd_sylow_card {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hev : Even (Nat.card X)) (hn : ¬ p ∣ Nat.card (Sylow 2 X)) : Dead p X := by
  intro Ē hE hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup p Ē := IsElementaryAbelian.isPGroup p Ē
  obtain ⟨U, hU⟩ := exists_sylow_two_normalized hp Ē hEp hn
  refine ⟨(U : Subgroup X), ?_, U.isPGroup', hU⟩
  intro hbot
  have hcard : Nat.card (U : Subgroup X) = 2 ^ (Nat.card X).factorization 2 := U.card_eq_multiplicity
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.1 hev
  have hf : 1 ≤ (Nat.card X).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hX0).1 h2
  rw [hbot] at hcard
  simp only [Subgroup.card_bot] at hcard
  have : 2 ^ 1 ∣ 2 ^ (Nat.card X).factorization 2 := pow_dvd_pow 2 hf
  rw [← hcard] at this
  omega

theorem not_dvd_card_sylow_of_le_normalizer {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (U : Sylow 2 X) (H : Subgroup X) (hH : H ≤ Subgroup.normalizer (U : Set X))
    (hcard : ∀ k : ℕ, p ^ k ∣ Nat.card X → p ^ k ∣ Nat.card H) : ¬ p ∣ Nat.card (Sylow 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  have hidx : Nat.card (Sylow 2 X) = (Subgroup.normalizer (U : Set X)).index :=
    U.card_eq_index_normalizer
  have hN := Subgroup.card_mul_index (Subgroup.normalizer (U : Set X))
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  set v := (Nat.card X).factorization p with hv
  have h1 : p ^ v ∣ Nat.card X := Nat.ordProj_dvd _ _
  have h2 : p ^ v ∣ Nat.card H := hcard v h1
  have h3 : Nat.card H ∣ Nat.card (Subgroup.normalizer (U : Set X)) := Subgroup.card_dvd_of_le hH
  have h4 : p ^ (v + 1) ∣ Nat.card X := by
    rw [← hN, pow_succ]
    exact mul_dvd_mul (h2.trans h3) (hidx ▸ hdvd)
  have h5 := (Nat.Prime.pow_dvd_iff_le_factorization hp hX0).1 h4
  omega

end CFSG.RankThree.PartOne.K133
