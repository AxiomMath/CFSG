module

public import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingScalarKernelHyperplane
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator

public section

namespace CFSG.RankThree.PartOne.FTL

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBM CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

theorem scalar_of_minimal_two_action (hTwo : TwoActionInputs) {G : Type} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (heG : evenRank G = 3) (hsig : p ∈ sigmaA G)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {A R D : Subgroup G}
    (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hAR : A ≤ normalizer (R : Set G)) (hR2 : IsPGroup 2 R) (hRA : ⁅R, A⁆ = R) (hR1 : R ≠ ⊥)
    (hRAD : R ⊔ A ≤ normalizer (D : Set G)) (hDq : IsPGroup q D) (hDexp : ∀ x ∈ D, x ^ q = 1)
    (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hBcard : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p ^ 2)
    (hmin : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U → ⁅U, D⁆ = ⊥)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) :
    ∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), ∃ k : ℕ, ∀ d ∈ D,
      (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := by
  have hrel : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = p :=
    Sec9B.relIndex_inf_centralizer_eq hp hAcard hBcard
  have hRD' : R ≤ normalizer (D : Set G) := le_sup_left.trans hRAD
  have hAD : A ≤ normalizer (D : Set G) := le_sup_right.trans hRAD
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hbD : ∀ b ∈ B, b ∈ normalizer (D : Set G) := fun b hb => hAD hb.1
  have hbR : ∀ b ∈ B, ∀ r ∈ R, b * r = r * b := fun b hb r hr =>
    (Subgroup.mem_centralizer_iff.mp hb.2 r hr).symm
  have hmin' : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (D : Set G) := fun U hU hAU hUA =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hmin U hU hAU hUA)
  have hone : ∀ (b : G) (k : ℕ) (d : G), b * d * b⁻¹ = d ^ k →
      (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := fun b k d h => by
    rw [h, inv_mul_cancel]
    exact one_mem _
  by_cases hp7 : p = 7
  ·
    intro b hb
    obtain ⟨a, b₀, haA, haB, hb₀B, hb₀1, hA₀A, hA₀elem, hA₀card, hfac, hker⟩ :=
      exists_plane_of_index_prime_subgroup hp hAe hAcard hBA hrel
    set A₀ := zpowers a ⊔ zpowers b₀ with hA₀
    have hset : MinTwoActionSetting p q A₀ D R :=
      minTwoActionSetting_of_plane hp hq hp3 hq2 hqp hA₀elem hA₀card hA₀A hfac hRAD hDexp hDcl
        hR2 hAR hRA hR1 hRD hmin
    have hA₀R : A₀ ≤ normalizer (R : Set G) := hA₀A.trans hAR
    have hA₀D : A₀ ≤ normalizer (D : Set G) := hA₀A.trans hAD
    obtain ⟨hAlt, -, hlift⟩ := hTwo
    obtain ⟨hRe, hRcard⟩ : IsElementaryAbelian 2 R ∧ Nat.card R = 8 := by
      rcases hAlt G p q A₀ D R hset hrank with
        ⟨⟨⟨h5, -⟩ | ⟨-, hRe, hRcard⟩, -⟩⟩ | ⟨h5, -⟩ | ⟨h5, -⟩
      · omega
      · exact ⟨hRe, hRcard⟩
      · omega
      · omega
    have hkerA₀ : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (R : Set G)) = p := by
      rw [← hker, hB, ← inf_assoc, inf_eq_left.mpr hA₀A]
    have hfrR : inSubgroup frattini R = ⊥ := by
      have : Fact (IsPGroup 2 ↥R) := ⟨hRe.isPGroup 2 ↥R⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
    have hodd : ¬ 2 ∣ Nat.card A₀ := by
      rw [hA₀card, hp7]
      decide
    have hmin₀ : ∀ U : Subgroup G, U < R → A₀ ≤ normalizer (U : Set G) → ⁅U, A₀⁆ = U →
        ⁅U, D⁆ = ⊥ := fun U hU hA₀U hUA₀ =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hset.R_min U hU hA₀U hUA₀)
    have hirrR : ∀ Y : Subgroup G, Y ≤ R → A₀ ≤ normalizer (Y : Set G) → Y = ⊥ ∨ Y = R := by
      intro Y hYR hA₀Y
      by_cases hYe : Y = R
      · exact Or.inr hYe
      refine Or.inl ?_
      have h := le_inSubgroup_frattini_of_proper_invariant hR2 hR1 hodd hA₀R hA₀D hset.R_comm
        hRD hmin₀ Y (lt_of_le_of_ne hYR hYe) hA₀Y
      rw [hfrR] at h
      exact le_bot_iff.mp h
    have hRA₀D : R ⊔ A₀ ≤ normalizer (D : Set G) := sup_le hRD' hA₀D
    obtain ⟨hfaith, hDe, hDcard, -, -, ⟨-, -, hirrD⟩, -⟩ := hlift G p q 3 A₀ D R hp hq hq2 hqp
      (Or.inl ⟨hp7, rfl⟩) hA₀elem hA₀card hA₀R hRe (by rw [hRcard]; norm_num) hkerA₀ hirrR
      hRA₀D hDq hDexp hDcl hRD hrank
    have : IsElementaryAbelian p A := hAe
    have hbA₀ : ∀ y ∈ A₀, b * y = y * b := fun y hy =>
      mul_comm_of_isMulCommutative hb.1 (hA₀A hy)
    obtain ⟨k, hk⟩ := scalar_action_of_plane_action hp hq hq2 hDe hDcard hRe (by omega) hRD' hA₀D
      hA₀R hfaith hA₀card hkerA₀ hirrD (hbD b hb) (hbR b hb) hbA₀
    exact ⟨k, fun d hd => hone b k d (hk d hd)⟩
  ·
    have hgood : GoodGlobalRank G p := fun h => absurd h hp7
    have hcardB : p ≤ Nat.card B := by
      rw [hBcard]
      exact Nat.le_self_pow two_ne_zero p
    obtain ⟨hp_le, hred⟩ := hTwo.2.1 G heG p hp hsig hp3 q hq hq2 hqp A R D hAe hAR hR2 hRA hR1
      hRAD hDq hDexp hDcl hRD hrel hcardB hmin' hgood
    have hp5 : p = 5 := by
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      have h6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
      omega
    rcases hred with hBD | ⟨-, ⟨e⟩, hfaith, -, -, -, -, hshape⟩
    · intro b hb
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBD hb
      refine ⟨1, fun d hd => ?_⟩
      have h := Subgroup.mem_centralizer_iff.mp hc d hd
      refine hone b 1 d ?_
      rw [pow_one, ← h]
      group
    · intro b hb
      exact scalar_action_of_qd32_action hq hq2 hDq hRD' hfaith e
        (card_quotient_frattini_of_isQDShape hq hshape) (hbD b hb) (hbR b hb)

end CFSG.RankThree.PartOne.FTL
