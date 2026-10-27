module

public import CFSG.Milestones.ASVolI.F429.One
public import CFSG.Milestones.ASVolI.F429.Base
public import CFSG.Milestones.ASVolI.F429.C8
public import CFSG.Milestones.ASVolI.F429.Defs

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G H : Type} [Group G] [Group H]

theorem burnsideF429_oTwoRes_map_le (φ : G →* H) (P : Subgroup G) :
    (oTwoRes P).map φ ≤ oTwoRes (P.map φ) := by
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxP, m, hm, hxm⟩, rfl⟩
  exact ⟨⟨x, hxP, rfl⟩, m, hm, by rw [← map_pow, hxm, map_one]⟩

theorem burnsideF429_mem_oTwoRes {P : Subgroup G} {x : G} (hx : x ∈ P) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) : x ∈ oTwoRes P :=
  Subgroup.subset_closure ⟨hx, m, hm, hxm⟩

end Generic

section L3Two

@[expose] def burnsideF429_l3_e01 : burnsideF4c_SL :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩
@[expose] def burnsideF429_l3_e02 : burnsideF4c_SL :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide +kernel⟩
@[expose] def burnsideF429_l3_e12 : burnsideF4c_SL :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide +kernel⟩
@[expose] def burnsideF429_l3_y1 : burnsideF4c_SL :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide +kernel⟩
@[expose] def burnsideF429_l3_y2 : burnsideF4c_SL :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 1, 0], by decide +kernel⟩
@[expose] def burnsideF429_l3_y3 : burnsideF4c_SL :=
  ⟨!![1, 0, 1; 0, 1, 1; 0, 1, 0], by decide +kernel⟩
@[expose] def burnsideF429_l3_w1 : burnsideF4c_SL :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide +kernel⟩
@[expose] def burnsideF429_l3_w2 : burnsideF4c_SL :=
  ⟨!![1, 1, 1; 1, 0, 0; 0, 0, 1], by decide +kernel⟩

theorem burnsideF429_l3_facts :
    burnsideF429_l3_y1 ∈ burnsideF4c_P ∧ burnsideF429_l3_y1 ^ 3 = 1 ∧
    burnsideF429_l3_y2 ∈ burnsideF4c_P ∧ burnsideF429_l3_y2 ^ 3 = 1 ∧
    burnsideF429_l3_y3 ∈ burnsideF4c_P ∧ burnsideF429_l3_y3 ^ 3 = 1 ∧
    burnsideF429_l3_w1 ∈ burnsideF4c_L ∧ burnsideF429_l3_w1 ^ 3 = 1 ∧
    burnsideF429_l3_w2 ∈ burnsideF4c_L ∧ burnsideF429_l3_w2 ^ 3 = 1 ∧
    burnsideF429_l3_e01 = burnsideF429_l3_y1 * burnsideF429_l3_y2 ∧
    burnsideF429_l3_e02 = burnsideF429_l3_y1 * burnsideF429_l3_y3 ∧
    burnsideF429_l3_e12 = burnsideF429_l3_w1 * burnsideF429_l3_w2 ∧
    burnsideF429_l3_e01 ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
    burnsideF429_l3_e02 ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
    burnsideF429_l3_e12 ∈ burnsideF4c_P ⊓ burnsideF4c_L := by
  decide +kernel

theorem burnsideF429_l3_borel_elements :
    ∀ x : burnsideF4c_SL, x ∈ burnsideF4c_P ⊓ burnsideF4c_L →
      ∃ i j k : Fin 2, x = burnsideF429_l3_e01 ^ (i : ℕ) * burnsideF429_l3_e02 ^ (j : ℕ) *
        burnsideF429_l3_e12 ^ (k : ℕ) := by
  decide +kernel

theorem burnsideF429_L3two_model :
    burnsideF4c_P ⊓ burnsideF4c_L ≤
      (burnsideF4c_P ⊓ burnsideF4c_L ⊓ oTwoRes burnsideF4c_P) ⊔
        (burnsideF4c_P ⊓ burnsideF4c_L ⊓ oTwoRes burnsideF4c_L) := by
  obtain ⟨hy1, hy1o, hy2, hy2o, hy3, hy3o, hw1, hw1o, hw2, hw2o, h01, h02, h12, hm01, hm02, hm12⟩ :=
    burnsideF429_l3_facts
  have hodd : Odd 3 := by decide
  have e01 : burnsideF429_l3_e01 ∈ burnsideF4c_P ⊓ burnsideF4c_L ⊓ oTwoRes burnsideF4c_P := by
    refine ⟨hm01, ?_⟩
    rw [h01]
    exact Subgroup.mul_mem _ (burnsideF429_mem_oTwoRes hy1 hodd hy1o)
      (burnsideF429_mem_oTwoRes hy2 hodd hy2o)
  have e02 : burnsideF429_l3_e02 ∈ burnsideF4c_P ⊓ burnsideF4c_L ⊓ oTwoRes burnsideF4c_P := by
    refine ⟨hm02, ?_⟩
    rw [h02]
    exact Subgroup.mul_mem _ (burnsideF429_mem_oTwoRes hy1 hodd hy1o)
      (burnsideF429_mem_oTwoRes hy3 hodd hy3o)
  have e12 : burnsideF429_l3_e12 ∈ burnsideF4c_P ⊓ burnsideF4c_L ⊓ oTwoRes burnsideF4c_L := by
    refine ⟨hm12, ?_⟩
    rw [h12]
    exact Subgroup.mul_mem _ (burnsideF429_mem_oTwoRes hw1 hodd hw1o)
      (burnsideF429_mem_oTwoRes hw2 hodd hw2o)
  intro x hx
  obtain ⟨i, j, k, rfl⟩ := burnsideF429_l3_borel_elements x hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.mem_sup_left e01) _)
    (Subgroup.pow_mem _ (Subgroup.mem_sup_left e02) _))
    (Subgroup.pow_mem _ (Subgroup.mem_sup_right e12) _)

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_L3two_sbar (hyp : HypF_4_4 .L3 2 1 Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤
      ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) := by
  obtain ⟨θ, h1, h2⟩ := burnsideF429_L3_marking hyp.toHypF_4_4g
  set φ : burnsideF4c_SL →* E := Gp.subtype.comp θ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Gp.subtype_injective.comp θ.injective
  have hP : Gp ⊓ M₁ = burnsideF4c_P.map φ := burnsideF429_inf_eq_map θ h1.symm
  have hL : Gp ⊓ M₂ = burnsideF4c_L.map φ := burnsideF429_inf_eq_map θ h2.symm
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (burnsideF4c_P ⊓ burnsideF4c_L).map φ := by
    have e : Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) := by
      ext y
      simp only [Subgroup.mem_inf]
      tauto
    rw [e, hP, hL, Subgroup.map_inf_eq _ _ _ hφinj]
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  refine hSB.trans ?_
  rw [hB]
  refine (Subgroup.map_mono burnsideF429_L3two_model).trans ?_
  rw [Subgroup.map_sup]
  have hBM : (burnsideF4c_P ⊓ burnsideF4c_L).map φ ≤ M₁ ⊓ M₂ := hB ▸ inf_le_right
  refine sup_le_sup (le_inf ?_ ?_) (le_inf ?_ ?_)
  · exact (Subgroup.map_mono (inf_le_left.trans le_rfl)).trans hBM
  · rw [hP]
    exact (Subgroup.map_mono inf_le_right).trans (burnsideF429_oTwoRes_map_le φ _)
  · exact (Subgroup.map_mono (inf_le_left.trans le_rfl)).trans hBM
  · rw [hL]
    exact (Subgroup.map_mono inf_le_right).trans (burnsideF429_oTwoRes_map_le φ _)

theorem burnsideF429_c8_L3two (hyp : HypF_4_4 .L3 2 1 Gp M₁ M₂) :
    burnsideF429_C8 .L3 1 Gp M₁ M₂ := by
  have hb := burnsideF429_L3two_sbar hyp
  exact burnsideF429_c8_of (κ := .L3) (f := 1) (inf_le_left.trans hb) (Or.inl hb)

end L3Two

end CFSG.ASVolI
