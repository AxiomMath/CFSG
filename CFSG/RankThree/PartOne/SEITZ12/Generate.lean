module

public import CFSG.RankThree.PartOne.SEITZ12.TConj
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi4gen_szW_roots_check :
    (relWord (kFour 3)).foldr (reflect F4.tag) (orbitCertRoot F4.tag 38) =
        -Pi.single largeReeI4 1 ∧
      (relWord (kFour 3)).foldr (reflect F4.tag) (orbitCertRoot F4.tag 42) =
        -Pi.single largeReeI1 1 := by
  decide +kernel

theorem phi4gen_szNw_conj_sylowK (k : K) :
    szNw K * sylowK m K k * (szNw K)⁻¹ =
      yUnit F4.tag K largeReeI4 k * yUnit F4.tag K largeReeI1 (largeReeSigma m k) := by
  obtain ⟨h38, h42⟩ := phi4gen_szW_roots_check
  have e38 := conj_relElt_pinnedX (K := K) (k := kFour 3)
    (sylowRoot_pos (r := 38) (by norm_num) (by norm_num)).1 k
  have e42 := conj_relElt_pinnedX (K := K) (k := kFour 3)
    (sylowRoot_pos (r := 42) (by norm_num) (by norm_num)).1 (largeReeSigma m k)
  rw [h38, pinnedX_neg_single] at e38
  rw [h42, pinnedX_neg_single] at e42
  rw [sylowK, weyl_conj_mul]
  exact congrArg₂ (· * ·) e38 e42

theorem phi4gen_szNw_conj_sylowL (k : K) :
    szNw K * sylowL m K k * (szNw K)⁻¹ = sylowJ m K k := by
  rw [szNw_eq_weyl]
  calc weylOne K * weylTwo K * weylOne K * sylowL m K k * (weylOne K * weylTwo K * weylOne K)⁻¹
      = weylOne K * (weylTwo K * (weylOne K * sylowL m K k * (weylOne K)⁻¹) * (weylTwo K)⁻¹) *
          (weylOne K)⁻¹ := by group
    _ = sylowJ m K k := by
      rw [weylOne_conj_sylowL, weylTwo_conj_sylowL, weylOne_conj_sylowK]

theorem phi4gen_weylTwo_mem : weylTwo K ∈ rankOneGroupTwo K m :=
  Subgroup.subset_closure (.inr rfl)

theorem phi4gen_sylowA_eq_stdTwoG (a : K) : sylowA m K a = stdTwoG m a := by
  have h : stdTwoRoot 0 = orbitCertRoot F4.tag 24 ∧ stdTwoRoot 1 = orbitCertRoot F4.tag 33 := by
    decide +kernel
  rw [stdTwoG, sylowA, sylowX, sylowX, h.1, h.2]

theorem phi4gen_U₁_le (hK : Nat.card K = 2 ^ (2 * m + 1)) (D : Subgroup (ModGL F4.tag K))
    (hA : ∀ a : K, sylowA m K a ∈ D) : F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ ≤ D := by
  intro g hg
  obtain ⟨s, rfl⟩ := exists_stdTwoG_eq hK hg
  rw [← phi4gen_sylowA_eq_stdTwoG]
  exact hA s

theorem phi4gen_Y₁_le (hK : Nat.card K = 2 ^ (2 * m + 1)) (D : Subgroup (ModGL F4.tag K))
    (hY : ∀ k : K, szNw K * sylowK m K k * (szNw K)⁻¹ ∈ D) :
    F4.reeFixedOrbitNegUnipotent K m ⟨0, by decide⟩ ≤ D := by
  intro g hg
  have hg' : g ∈ (largeReeA1Y K m : Set (ModGL F4.tag K)) := hg
  rw [coe_largeReeA1Y hK] at hg'
  obtain ⟨c, rfl⟩ := hg'
  have h := hY (c ^ 2 ^ m)
  rw [phi4gen_szNw_conj_sylowK, largeReeSigma_pow hK, ← (largeRee_commute_yy c _).eq] at h
  exact h

theorem phi4gen_localBlock_two_le :
    F4.reeLocalBlock K m ⟨1, by decide⟩ ≤ rankOneGroupTwo K m := by
  have hU : F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ ≤ rankOneGroupTwo K m := fun g hg =>
    Subgroup.subset_closure (.inl (.inl hg))
  refine sup_le hU fun y hy => ?_
  rw [← map_conj_reeFixedOrbitUnipotent] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact mul_mem (mul_mem phi4gen_weylTwo_mem (hU hx)) (inv_mem phi4gen_weylTwo_mem)

theorem reeGamma_le_of_K (_hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    (D : Subgroup (ModGL F4.tag K)) (hX₂ : rankOneGroupTwo K m ≤ D) (ht : szNw K ∈ D)
    (hKk : ∀ k : K, sylowK m K k ∈ D) : F4.reeGamma K m ≤ D := by
  have hn : weylTwo K ∈ D := hX₂ phi4gen_weylTwo_mem
  have hL : ∀ k : K, sylowL m K k ∈ D := fun k => by
    rw [← weylTwo_conj_sylowK]
    exact mul_mem (mul_mem hn (hKk k)) (inv_mem hn)
  have hJ : ∀ k : K, sylowJ m K k ∈ D := fun k => by
    rw [← phi4gen_szNw_conj_sylowL]
    exact mul_mem (mul_mem ht (hL k)) (inv_mem ht)
  have hA : ∀ k : K, sylowA m K k ∈ D := fun k => by
    rw [← weylTwo_conj_sylowJ]
    exact mul_mem (mul_mem hn (hJ k)) (inv_mem hn)
  have hY : ∀ k : K, szNw K * sylowK m K k * (szNw K)⁻¹ ∈ D := fun k =>
    mul_mem (mul_mem ht (hKk k)) (inv_mem ht)
  rw [large_Ree_simple_pair_generation m K hK]
  exact sup_le (sup_le (phi4gen_U₁_le hK D hA) (phi4gen_Y₁_le hK D hY))
    (phi4gen_localBlock_two_le.trans hX₂)

end CFSG.RankThree.PartOne.SEITZ12
