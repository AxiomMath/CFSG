module

public import CFSG.RankThree.PartOne.SEITZ12.ModuleLam
public import CFSG.RankThree.PartOne.SEITZ12.ModuleAct
public import CFSG.RankThree.PartOne.SEITZ12.TConj
public import CFSG.RankThree.PartOne.SEITZ12.Defs

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi4ml_sylowH_mem_S1 (hK : Nat.card K = 2 ^ (2 * m + 1)) (h i : K) :
    sylowH m K h i ∈ conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) := by
  have ht : (szNw K)⁻¹ = szNw K := inv_eq_of_mul_eq_one_right szNw_mul_self
  rw [mem_conjSub, ht]
  have := szNw_conj_sylowH (m := m) (K := K) h i
  rw [ht] at this
  rw [this]
  exact sylowB_mem_U2 hK h i

theorem phi4ml_V2_coords (hK : Nat.card K = 2 ^ (2 * m + 1)) {w : ModGL F4.tag K}
    (hw : w ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) :
    ∃ a d e f g h₁ i₁ j k l : K, w = sylowV m K a 0 0 d e f g h₁ i₁ j k l := by
  obtain ⟨x, -, hx⟩ := (bijOn_sylowVec hK).2.2 (reeFixedOrbitComplementUnipotent_le _ hw)
  have h01 : x 1 = 0 ∧ x 2 = 0 := by
    refine coord_one_two_eq hK (b := 0) (c := 0) hw ?_
    rw [hx, sylowB_zero_zero, one_mul]
  refine ⟨x 0, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, ?_⟩
  rw [← hx, sylowVec, h01.1, h01.2]

theorem phi4ml_sylowV_DF (e g : K) :
    sylowV m K 0 0 0 0 e 0 g 0 0 0 0 0 = sylowD m K 0 e * sylowF m K 0 g := by
  simp [sylowV, sylowA, sylowB, sylowH, sylowJ, sylowK, sylowL, sylowX, largeReeSigma_zero,
    pinnedX_zero]

theorem phi4ml_beta (hK : Nat.card K = 2 ^ (2 * m + 1)) (e g h₁ i₁ k l : K) :
    (sylowH m K h₁ 0)⁻¹ * sylowV m K 0 0 0 0 e 0 g h₁ i₁ 0 k l = phi4ml_vt m K e k l g i₁ := by
  have hs := phi4ml_comm_H_vt hK 0 0 e 0 g 0 0 0 0 0 h₁
  simp only [zero_mul, mul_zero, add_zero, largeReeSigma_zero, phi4ml_sylowV_DF] at hs
  have hs' : (sylowD m K 0 e * sylowF m K 0 g) * sylowH m K h₁ 0 =
      sylowH m K h₁ 0 * (sylowD m K 0 e * sylowF m K 0 g) := by
    rw [phi4ml_vt_zero] at hs
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hs)
  have hw : sylowV m K 0 0 0 0 e 0 g h₁ i₁ 0 k l =
      sylowD m K 0 e * sylowF m K 0 g * (sylowH m K h₁ 0 * sylowH m K 0 i₁) *
        sylowK m K k * sylowL m K l := by
    rw [← phi4ml_sylowH_split hK]
    simp [sylowV, sylowA, sylowB, sylowJ, sylowX, largeReeSigma_zero, pinnedX_zero, mul_assoc]
  rw [hw, phi4ml_vt]
  calc (sylowH m K h₁ 0)⁻¹ * (sylowD m K 0 e * sylowF m K 0 g * (sylowH m K h₁ 0 *
          sylowH m K 0 i₁) * sylowK m K k * sylowL m K l)
      = (sylowH m K h₁ 0)⁻¹ * (sylowD m K 0 e * sylowF m K 0 g * sylowH m K h₁ 0) *
          sylowH m K 0 i₁ * sylowK m K k * sylowL m K l := by group
    _ = (sylowH m K h₁ 0)⁻¹ * (sylowH m K h₁ 0 * (sylowD m K 0 e * sylowF m K 0 g)) *
          sylowH m K 0 i₁ * sylowK m K k * sylowL m K l := by rw [hs']
    _ = sylowD m K 0 e * sylowF m K 0 g * sylowH m K 0 i₁ * sylowK m K k * sylowL m K l := by
      group

theorem module_lemma (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    (W : Subgroup (ModGL F4.tag K))
    (hWV : W ≤ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩)
    (hS₁ : conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ≤ W)
    (hX₂ : ∀ x ∈ rankOneGroupTwo K m, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hne : ¬ W ≤ conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K)) :
    ∀ k : K, sylowK m K k ∈ W := by
  classical
  have _ := hm
  have hHW : ∀ h i : K, sylowH m K h i ∈ W := fun h i => hS₁ (phi4ml_sylowH_mem_S1 hK h i)
  have hH : ∀ i : K, sylowH m K 0 i ∈ W := fun i => hHW 0 i
  have hB : ∀ x ∈ W, sylowB m K 1 0 * x * (sylowB m K 1 0)⁻¹ ∈ W := fun x hx =>
    hX₂ _ (phi4ml_B_mem hK 1 0) x hx
  obtain ⟨w, hwW, hwS⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  obtain ⟨a, d, e, f, g, h₁, i₁, j, k, l, rfl⟩ := phi4ml_V2_coords hK (hWV hwW)
  have hstart : ∃ e' k' l' g' i' : K, phi4ml_Lam m W e' k' l' g' i' ∧
      (e' ≠ 0 ∨ k' ≠ 0 ∨ l' ≠ 0 ∨ g' ≠ 0) := by
    by_cases habdj : a = 0 ∧ d = 0 ∧ f = 0 ∧ j = 0
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := habdj
      have hLam : phi4ml_Lam m W e k l g i₁ := by
        rw [phi4ml_Lam, ← phi4ml_beta hK]
        exact W.mul_mem (W.inv_mem (hHW h₁ 0)) hwW
      refine ⟨e, k, l, g, i₁, hLam, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcon
      apply hwS
      have h1 := phi4ml_beta hK 0 0 h₁ i₁ 0 0
      rw [phi4ml_vt_i] at h1
      have h2 : sylowV m K 0 0 0 0 0 0 0 h₁ i₁ 0 0 0 = sylowH m K h₁ 0 * sylowH m K 0 i₁ := by
        rw [← h1, mul_inv_cancel_left]
      rw [h2, ← phi4ml_sylowH_split hK]
      exact phi4ml_sylowH_mem_S1 hK h₁ i₁
    · obtain ⟨h, hh⟩ := exists_ne (0 : K)
      have hc : sylowV m K a 0 0 d e f g h₁ i₁ j k l * sylowH m K h 0 *
          (sylowV m K a 0 0 d e f g h₁ i₁ j k l)⁻¹ * (sylowH m K h 0)⁻¹ ∈ W :=
        W.mul_mem (W.mul_mem (W.mul_mem hwW (hHW h 0)) (W.inv_mem hwW)) (W.inv_mem (hHW h 0))
      rw [phi4ml_comm_H_vt hK] at hc
      refine ⟨a * h, d * h, f * h, j * h, _, hc, ?_⟩
      by_contra hcon
      push Not at hcon
      apply habdj
      exact ⟨(mul_eq_zero.mp hcon.1).resolve_right hh, (mul_eq_zero.mp hcon.2.1).resolve_right hh,
        (mul_eq_zero.mp hcon.2.2.1).resolve_right hh, (mul_eq_zero.mp hcon.2.2.2).resolve_right hh⟩
  obtain ⟨e', k', l', g', i', hLam, hne'⟩ := hstart
  obtain ⟨g₀, hg₀, hG₀⟩ := phi4ml_Lam_descent hK hB hH hLam hne'
  have hTor : ∀ (u : Kˣ) (g : K), phi4ml_Lam m W 0 0 0 g 0 →
      phi4ml_Lam m W 0 0 0 ((u : K) ^ 2 ^ m * g) 0 := by
    intro u g hg
    obtain ⟨τ, hτ, hτF⟩ := phi4ml_torus_F hK u
    rw [phi4ml_Lam, phi4ml_vt_g] at hg ⊢
    rw [← hτF g]
    exact hX₂ τ hτ _ hg
  have hG := phi4ml_Lam_gline hTor hg₀ hG₀
  obtain ⟨n, hn, hnF⟩ := phi4ml_weyl_F hK
  have hE : ∀ e : K, phi4ml_Lam m W e 0 0 0 0 := by
    intro e
    have := hX₂ n hn _ (show sylowF m K 0 e ∈ W by
      have := hG e
      rwa [phi4ml_Lam, phi4ml_vt_g] at this)
    rw [hnF] at this
    rwa [phi4ml_Lam, phi4ml_vt_e]
  intro k
  have := phi4ml_Lam_kline hK hB hH hE hG k
  rwa [phi4ml_Lam, phi4ml_vt_k] at this

end CFSG.RankThree.PartOne.SEITZ12
