module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Core
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

variable {G : Type} [Group G] [Finite G]

structure Cfg (L K : Subgroup G) (a b : G) : Prop where
  hKL : K ≤ L
  hKb : K ≤ Subgroup.centralizer ({b} : Set G)
  ha3 : a ^ 3 = 1
  hb3 : b ^ 3 = 1
  hab : a * b = b * a
  haL : a ∈ Subgroup.normalizer (L : Set G)
  hbL : b ∈ Subgroup.normalizer (L : Set G)
  haK : a ∈ Subgroup.normalizer (K : Set G)
  hβ1 : rho L ⟨b, hbL⟩ ≠ 1
  hαβ : ∀ j : ℤ, rho L ⟨a, haL⟩ * rho L ⟨b, hbL⟩ ^ j ≠ 1
  hout : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) ∉
    (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
      MulAut (K ⧸ aschbacherSolvableCore 3 K)).range

namespace Cfg

variable {L K : Subgroup G} {a b : G} (c : Cfg L K a b)

noncomputable abbrev alpha : MulAut (L ⧸ aschbacherSolvableCore 3 L) := rho L ⟨a, c.haL⟩

noncomputable abbrev beta : MulAut (L ⧸ aschbacherSolvableCore 3 L) := rho L ⟨b, c.hbL⟩

theorem alpha_pow_three : c.alpha ^ 3 = 1 := by
  rw [alpha, ← map_pow]
  have : (⟨a, c.haL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simp [c.ha3])
  rw [this, map_one]

theorem beta_pow_three : c.beta ^ 3 = 1 := by
  rw [beta, ← map_pow]
  have : (⟨b, c.hbL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simp [c.hb3])
  rw [this, map_one]

theorem alpha_mul_beta : c.alpha * c.beta = c.beta * c.alpha := by
  rw [alpha, beta, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext c.hab

include c in
theorem hbC : b ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (c.hKb hx)

include c in
theorem hbK : b ∈ Subgroup.normalizer (K : Set G) :=
  Subgroup.centralizer_le_normalizer (K : Set G) c.hbC

theorem alpha_ne_one : c.alpha ≠ 1 := by
  intro h
  refine rho_pow_mul_ne c.hKL c.hKb c.ha3 c.haL c.hbL c.haK c.hout (i := 1) (j := 0)
    (by norm_num) (k := 1) K.one_mem ?_
  rw [pow_one, pow_zero, mul_one]
  change rho L ⟨a, c.haL⟩ = rho L ⟨1, L.le_normalizer (c.hKL K.one_mem)⟩
  rw [show (⟨1, L.le_normalizer (c.hKL K.one_mem)⟩ : Subgroup.normalizer (L : Set G)) = 1 from
    rfl, map_one]
  exact h

theorem beta_notMem_zpowers : c.beta ∉ Subgroup.zpowers c.alpha := by
  rintro ⟨i, hi⟩
  replace hi : c.alpha ^ i = c.beta := hi
  have h3 := c.alpha_pow_three
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hα : c.alpha ^ i = c.alpha ^ (i % 3) := zpow_eq_zpow_emod i (by exact_mod_cast h3)
  rw [hα] at hi
  have key : ∀ j : ℤ, c.alpha * c.beta ^ j ≠ 1 := c.hαβ
  rcases hcases with h | h | h
  · rw [h, zpow_zero] at hi
    exact c.hβ1 hi.symm
  · rw [h, zpow_one] at hi
    refine key (-1) ?_
    rw [zpow_neg_one, ← hi, mul_inv_cancel]
  · rw [h] at hi
    have hbe : c.beta = c.alpha ^ (2 : ℤ) := hi.symm
    refine key (-2) ?_
    rw [zpow_neg, hbe, ← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add,
      show c.alpha ^ (3 : ℤ) = 1 by exact_mod_cast h3, one_mul, zpow_one, mul_inv_cancel]

theorem rho_ne_one_of_orderOf_three {x : G} (hxK : x ∈ K) (hx : orderOf x = 3)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) :
    rho L ⟨x, L.le_normalizer (c.hKL hxK)⟩ ≠ 1 := by
  intro h1
  have hK1 := thetaQuot_eq_one_of_rho_eq_one c.hKL (L.le_normalizer (c.hKL hxK))
    (K.le_normalizer hxK) h1
  rw [thetaQuot_eq_conj K hxK] at hK1
  have hcen := mem_center_of_conj_eq_one hK1
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have h2 : orderOf x ∣ Nat.card (aschbacherSolvableCore 3 K) := by
    have := orderOf_dvd_natCard (⟨⟨x, hxK⟩, hcen⟩ : aschbacherSolvableCore 3 K)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
  rw [hx] at h2
  exact hθ3 h2

theorem exists_xi (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (h3K : 3 ∣ Nat.card K) :
    ∃ ξ : MulAut (L ⧸ aschbacherSolvableCore 3 L), ξ ∈ innBar L ∧ ξ ^ 3 = 1 ∧
      c.alpha * ξ = ξ * c.alpha ∧ c.beta * ξ = ξ * c.beta ∧
      ξ ∉ Subgroup.closure ({c.alpha, c.beta} : Set (MulAut (L ⧸ aschbacherSolvableCore 3 L))) := by
  obtain ⟨x, hxK, hx3, hax⟩ := exists_orderOf_three_commute c.haK c.ha3 h3K
  have hxL : x ∈ L := c.hKL hxK
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := L.le_normalizer hxL
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  refine ⟨rho L ⟨x, hxN⟩, rho_mem_innBar L hxL, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simp [hx3'])
    rw [this, map_one]
  · change rho L ⟨a, c.haL⟩ * rho L ⟨x, hxN⟩ = rho L ⟨x, hxN⟩ * rho L ⟨a, c.haL⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hax
  · change rho L ⟨b, c.hbL⟩ * rho L ⟨x, hxN⟩ = rho L ⟨x, hxN⟩ * rho L ⟨b, c.hbL⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (c.hKb hxK)).symm
  · intro hmem
    have hcomm : Commute c.alpha c.beta := c.alpha_mul_beta
    obtain ⟨i, j, hij⟩ := (mem_closure_pair_iff hcomm).mp hmem
    have hα3 := c.alpha_pow_three
    have hβ3 := c.beta_pow_three
    have hi : c.alpha ^ i = c.alpha ^ (i % 3).toNat := by
      rw [zpow_eq_zpow_emod i (n := 3) (by exact_mod_cast hα3), ← zpow_natCast,
        Int.toNat_of_nonneg (by omega)]
    have hj : c.beta ^ j = c.beta ^ (j % 3).toNat := by
      rw [zpow_eq_zpow_emod j (n := 3) (by exact_mod_cast hβ3), ← zpow_natCast,
        Int.toNat_of_nonneg (by omega)]
    rw [hi, hj] at hij
    set i' := (i % 3).toNat with hi'
    set j' := (j % 3).toNat with hj'
    have hi3 : i' < 3 := by omega
    have hj3 : j' < 3 := by omega
    have hxξ : rho L ⟨x, hxN⟩ = c.alpha ^ i' * c.beta ^ j' := hij
    by_cases hi0 : i' = 0
    · by_cases hj0 : j' = 0
      · rw [hi0, hj0, pow_zero, pow_zero, mul_one] at hxξ
        exact c.rho_ne_one_of_orderOf_three hxK hx3 hZ hxξ
      · refine rho_pow_ne_of_center_eq_bot c.hKL c.hKb c.hb3 c.hbL c.hβ1 hZ (j := j')
          (by omega) hxK ?_
        rw [hi0, pow_zero, one_mul] at hxξ
        exact hxξ.symm
    · exact rho_pow_mul_ne c.hKL c.hKb c.ha3 c.haL c.hbL c.haK c.hout (i := i') (j := j')
        (by omega) hxK hxξ.symm

@[expose] def E27 : Prop :=
  ∃ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), CFSG.Open.IsElemAbelian 3 F ∧
    27 ≤ Nat.card F ∧ F ≤ innBar L ⊔ Subgroup.zpowers c.alpha ⊔ Subgroup.zpowers c.beta

theorem e27_of_center_eq_bot (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (h3K : 3 ∣ Nat.card K) : c.E27 := by
  obtain ⟨ξ, hξi, hξ3, hαξ, hβξ, hξ⟩ := c.exists_xi hZ h3K
  obtain ⟨hF, h27⟩ := isElemAbelian_closure_three c.alpha_pow_three c.beta_pow_three hξ3
    c.alpha_ne_one c.alpha_mul_beta hαξ hβξ c.beta_notMem_zpowers hξ
  refine ⟨_, hF, h27, ?_⟩
  rw [Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hξi)

theorem false_of_e27 (h : c.E27) {N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))}
    (hinn : innBar L ≤ N) (hα : c.alpha ∈ N) (hβ : c.beta ∈ N)
    (hN : ∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), CFSG.Open.IsElemAbelian 3 F →
      F ≤ N → Nat.card F ≤ 9) : False := by
  obtain ⟨F, hF, h27, hle⟩ := h
  have hFN : F ≤ N := hle.trans (sup_le (sup_le hinn (Subgroup.zpowers_le.mpr hα))
    (Subgroup.zpowers_le.mpr hβ))
  have := hN F hF hFN
  omega

end Cfg

end CFSG.RankThree.PartTwo.Sec8.Hering418
