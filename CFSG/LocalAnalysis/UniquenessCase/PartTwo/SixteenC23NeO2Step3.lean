module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AStep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_mem_cTilde_iff {M V₀ V : Subgroup G} {x : G} :
    x ∈ F11.CTilde M V₀ V ↔
      x ∈ M ∧ x ∈ Subgroup.normalizer (V₀ : Set G) ∧
        ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀ := by
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    have h1 := h 1 V.one_mem
    exact ⟨h1.1, h1.2.1, fun v hv => (h v hv).2.2⟩
  · rintro ⟨h1, h2, h3⟩ v hv
    exact ⟨h1, h2, h3 v hv⟩

theorem c23ne_mQuot_eq_one_of_cTilde {M V₀ V N₁ N₂ Y : Subgroup G}
    (hP : C23NePair M V₀ V N₁ N₂ Y) {c : G} (hc : c ∈ F11.CTilde M Y V)
    (hnot : ¬ V ≤ centralizer ({c} : Set G)) :
    E3.mQuot V (V ⊓ centralizer ({c} : Set G)) = 1 := by
  have hcM : c ∈ M := (c23ne_mem_cTilde_iff.1 hc).1
  have hcY : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ Y := (c23ne_mem_cTilde_iff.1 hc).2.2
  have hcN : c ∈ normalizer (V : Set G) := hP.norm hcM
  have hleV : commElt V c ≤ V := by
    rw [commElt, Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    have hu : c⁻¹ * w * c ∈ V := (Subgroup.mem_normalizer_iff''.1 hcN w).1 hw
    have hmem := V.mul_mem (V.inv_mem hw) hu
    simpa only [SetLike.mem_coe, mul_assoc] using hmem
  have hle : commElt V c ≤ Y := by
    rw [commElt, Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    have hu : c⁻¹ * w * c ∈ V := (Subgroup.mem_normalizer_iff''.1 hcN w).1 hw
    have hY : c * (c⁻¹ * w * c) * c⁻¹ * (c⁻¹ * w * c)⁻¹ ∈ Y := hcY _ hu
    have h2 : c * (c⁻¹ * w * c) * c⁻¹ * (c⁻¹ * w * c)⁻¹ =
        w * (c⁻¹ * w * c)⁻¹ := by group
    rw [h2] at hY
    have hcomm : (c⁻¹ * w * c) * w⁻¹ = w⁻¹ * (c⁻¹ * w * c) :=
      congrArg Subtype.val
        (hP.elem.1.is_comm.comm ⟨c⁻¹ * w * c, hu⟩ ⟨w⁻¹, V.inv_mem hw⟩)
    have h3 : (w * (c⁻¹ * w * c)⁻¹)⁻¹ = w⁻¹ * c⁻¹ * w * c := by
      rw [mul_inv_rev, inv_inv, hcomm]
      group
    rw [← h3]
    exact Y.inv_mem hY
  have hne : commElt V c ≠ ⊥ := by
    intro hbot
    refine hnot fun w hw => ?_
    have hgen : w⁻¹ * c⁻¹ * w * c ∈ commElt V c := Subgroup.subset_closure ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hgen
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c⁻¹ * w * c = w := by
      calc c⁻¹ * w * c = w * (w⁻¹ * c⁻¹ * w * c) := by group
        _ = w * 1 := by rw [hgen]
        _ = w := by group
    calc w * c = c * (c⁻¹ * w * c) := by group
      _ = c * w := by rw [h1]
  have hpg : IsPGroup 2 (commElt V c) := hP.elem.isPGroup.to_le hleV
  have hrk1 : rk ↥(commElt V c) = 1 := by
    have hle' : rk ↥(commElt V c) ≤ rk ↥Y := rk_mono hle
    have hYrk : rk ↥Y = 1 := by simpa only [mSub] using hP.rank_Y
    have hge1 : 1 ≤ rk ↥(commElt V c) := by
      have h0 : rk ↥(commElt V c) ≠ 0 := by
        intro hzero
        exact hne ((rk_eq_zero_iff_of_isPGroup hpg).1 hzero)
      omega
    omega
  have hmadd := c23a_mSub_commElt_add hP.elem hcN
  have hV8 : rk ↥V = 8 := by simpa only [mSub] using hP.rank_V
  have hrkC : rk ↥(V ⊓ centralizer ({c} : Set G)) = 7 := by
    simp only [mSub] at hmadd
    omega
  have hquot :=
    c23a_o2_mQuot_eq_rk_sub (V := V) (U := V ⊓ centralizer ({c} : Set G)) inf_le_left
  rw [hquot, hV8, hrkC]

variable {M V₀ V N₁ N₂ Y : Subgroup G} {g : G}

theorem c23ne_step3 (h : C23NeO2 M V₀ V N₁ N₂ Y g)
    (h1 : E3.mQuot V (conjSubgroup M g) = 2)
    (h2 : E3.mQuot (V ⊓ conjSubgroup M g)
      (F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) ≤ 2)
    (h1' : E3.mQuot (conjSubgroup V g) M = 2) : False := by
  have hUV : V ⊓ conjSubgroup M g ≤ V := inf_le_left
  have hmU : E3.mQuot V (V ⊓ conjSubgroup M g) = 2 := by
    rw [c23a_o2_mQuot_inf_left]; exact h1
  have hrkU := c23a_o2_mQuot_eq_rk_sub hUV
  have hrkV : rk ↥V = 8 := by simpa only [mSub] using h.pair.rank_V
  have hmC : E3.mQuot (V ⊓ conjSubgroup M g)
      ((V ⊓ conjSubgroup M g) ⊓
        F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) ≤ 2 := by
    rw [c23a_o2_mQuot_inf_left]; exact h2
  have hrkC := c23a_o2_mQuot_eq_rk_sub
    (V := V ⊓ conjSubgroup M g)
    (U := (V ⊓ conjSubgroup M g) ⊓
      F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) inf_le_left
  have hCV : (V ⊓ conjSubgroup M g) ⊓
      F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g) ≤ V :=
    inf_le_left.trans hUV
  have hrkle : rk ↥((V ⊓ conjSubgroup M g) ⊓
      F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) ≤
        rk ↥(V ⊓ conjSubgroup M g) := rk_mono inf_le_left
  have hne : ((V ⊓ conjSubgroup M g) ⊓
      F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) ⊓ N₁ ≠ ⊥ := by
    intro hbot
    have h3 := c23ne_mSub_le_three h.pair hCV hbot
    simp only [mSub] at h3
    omega
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcC := (Subgroup.mem_inf.1 c.2).1
  have hcN₁ : (c : G) ∈ N₁ := (Subgroup.mem_inf.1 c.2).2
  have hcCT := (Subgroup.mem_inf.1 hcC).2
  have hc1' : (c : G) ≠ 1 := fun h' => hc1 (Subtype.ext h')
  have hcentM : centralizer ({(c : G)} : Set G) ≤ M := h.pair.cent (c : G) (Or.inl hcN₁) hc1'
  have hnot : ¬ conjSubgroup V g ≤ centralizer ({(c : G)} : Set G) :=
    fun hle => h.notLe (hle.trans hcentM)
  have hm1 := c23ne_mQuot_eq_one_of_cTilde h.pair' hcCT hnot
  have hle : conjSubgroup V g ⊓ centralizer ({(c : G)} : Set G) ≤ M := inf_le_right.trans hcentM
  have h4 := E3.mQuot_mono (V := conjSubgroup V g) hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
