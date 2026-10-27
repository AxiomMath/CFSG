module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Gen
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23ne_mem_of_orbit {M V₀ V N₁ N₂ Y : Subgroup G} (hP : C23NePair M V₀ V N₁ N₂ Y)
    {U E : Subgroup G} (hUV : U ≤ V) (hmU : E3.mQuot V U ≤ 2) (hE : Nat.card E ≤ 4) {w : G}
    (hw : ∀ u ∈ U, u * w * u⁻¹ * w⁻¹ ∈ E) : w ∈ M := by
  have hU : IsPGroup 2 U := hP.elem.isPGroup.to_le hUV
  have h1 := c23ne_mQuot_le_two_of_orbit hU hE hw
  have h1' : E3.mQuot U (U ⊓ centralizer ({w} : Set G)) ≤ 2 := by
    rw [c23a_o2_mQuot_inf_left]; exact h1
  have hC'U : U ⊓ centralizer ({w} : Set G) ≤ U := inf_le_left
  have hC'V : U ⊓ centralizer ({w} : Set G) ≤ V := hC'U.trans hUV
  have e1 := c23a_o2_mQuot_eq_rk_sub hUV
  have e2 := c23a_o2_mQuot_eq_rk_sub hC'U
  have e3 := c23a_o2_mQuot_eq_rk_sub hC'V
  have e4 : rk ↥(U ⊓ centralizer ({w} : Set G)) ≤ rk ↥U := rk_mono hC'U
  have e5 : rk ↥U ≤ rk ↥V := rk_mono hUV
  have h2 : E3.mQuot V (U ⊓ centralizer ({w} : Set G)) ≤ 4 := by omega
  have h3 := c23ne_cent_le_of_mQuot_le hP h2
  refine h3 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hcw : c ∈ centralizer ({w} : Set G) := (Subgroup.mem_inf.1 hc).2
  exact Subgroup.mem_centralizer_singleton_iff.1 hcw

variable {M V₀ V N₁ N₂ Y : Subgroup G} {g : G}

theorem c23ne_card_conj_V₀ (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    Nat.card ↥(conjSubgroup V₀ g) = 4 := by
  have hle : conjSubgroup V₀ g ≤ conjSubgroup V g := by
    rw [← h.pair'.inf]
    exact inf_le_left.trans h.pair'.le₁
  have hp : IsPGroup 2 ↥(conjSubgroup V₀ g) := h.pair'.elem.isPGroup.to_le hle
  rw [card_eq_two_pow_mSub hp, h.pair'.rank_V₀]
  norm_num

private theorem c23ne_mQuot_inf_le (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    E3.mQuot V (V ⊓ conjSubgroup M g) ≤ 2 := by
  rw [c23a_o2_mQuot_inf_left]; exact h.mU

private theorem c23ne_comm_mem_conj_V₀ (h : C23NeO2 M V₀ V N₁ N₂ Y g) {u w : G}
    (hu : u ∈ conjSubgroup M g) (hw : w ∈ conjSubgroup V₀ g) :
    u * w * u⁻¹ * w⁻¹ ∈ conjSubgroup V₀ g :=
  (conjSubgroup V₀ g).mul_mem
    ((Subgroup.mem_normalizer_iff.1 (h.pair'.normV₀ hu) w).1 hw) ((conjSubgroup V₀ g).inv_mem hw)

theorem c23ne_step0_le (h : C23NeO2 M V₀ V N₁ N₂ Y g) : conjSubgroup V₀ g ≤ M := by
  intro w hw
  exact c23ne_mem_of_orbit h.pair (U := V ⊓ conjSubgroup M g) (E := conjSubgroup V₀ g)
    inf_le_left (c23ne_mQuot_inf_le h) (c23ne_card_conj_V₀ h).le
    (fun u hu => c23ne_comm_mem_conj_V₀ h (Subgroup.mem_inf.1 hu).2 hw)

theorem c23ne_step0_comm (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    ∀ u ∈ V ⊓ conjSubgroup M g, ∀ w ∈ conjSubgroup V₀ g, u * w = w * u := by
  intro u hu w hw
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup N₁ g := by
    rw [← h.pair'.inf]; exact inf_le_left
  have hwVg : w ∈ conjSubgroup V g := h.pair'.le₁ (hV₀g hw)
  have hwM : w ∈ M := c23ne_step0_le h hw
  have hcD : u * w * u⁻¹ * w⁻¹ ∈ V ⊓ conjSubgroup V g :=
    c23ne_comm_mem_inf h hu (Subgroup.mem_inf.2 ⟨hwVg, hwM⟩)
  have hcV₀ : u * w * u⁻¹ * w⁻¹ ∈ conjSubgroup V₀ g :=
    c23ne_comm_mem_conj_V₀ h (Subgroup.mem_inf.1 hu).2 hw
  have hbot : (V ⊓ conjSubgroup V g) ⊓ conjSubgroup N₁ g = ⊥ :=
    (c23ne_inf_blocks_eq_bot h.pair' h.notLe' (A := V) (X := V ⊓ conjSubgroup V g)
      (fun x hx a ha => h.pair.elem.comm ha hx.1)).1
  have hmem : u * w * u⁻¹ * w⁻¹ ∈ (V ⊓ conjSubgroup V g) ⊓ conjSubgroup N₁ g :=
    Subgroup.mem_inf.2 ⟨hcD, hV₀g hcV₀⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : u * w * u⁻¹ = w := by
    have h2 : (u * w * u⁻¹ * w⁻¹) * w = 1 * w := by rw [hmem]
    simpa [mul_assoc] using h2
  calc u * w = u * w * u⁻¹ * u := by group
    _ = w * u := by rw [h1]

theorem c23ne_step0_cent (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    ∀ w ∈ conjSubgroup V₀ g, w ≠ 1 →
      V ⊓ centralizer ({w} : Set G) = V ⊓ conjSubgroup M g := by
  intro w hw hw1
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup N₁ g := by
    rw [← h.pair'.inf]; exact inf_le_left
  have hcent : centralizer ({w} : Set G) ≤ conjSubgroup M g :=
    h.pair'.cent w (Or.inl (hV₀g hw)) hw1
  refine le_antisymm (inf_le_inf_left V hcent) fun u hu => ?_
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hu).1,
    Subgroup.mem_centralizer_singleton_iff.2 (c23ne_step0_comm h u hu w hw)⟩

theorem c23ne_step0_le' (h : C23NeO2 M V₀ V N₁ N₂ Y g) : V₀ ≤ conjSubgroup M g := by
  simpa only [conjSubgroup_conjSubgroup_inv] using c23ne_step0_le h.swap

theorem c23ne_step0_comm' (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    ∀ u ∈ conjSubgroup V g ⊓ M, ∀ w ∈ V₀, u * w = w * u := by
  simpa only [conjSubgroup_conjSubgroup_inv] using c23ne_step0_comm h.swap

theorem c23ne_step0_cent' (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    ∀ w ∈ V₀, w ≠ 1 → conjSubgroup V g ⊓ centralizer ({w} : Set G) = conjSubgroup V g ⊓ M := by
  simpa only [conjSubgroup_conjSubgroup_inv] using c23ne_step0_cent h.swap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
