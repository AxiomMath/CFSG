module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.EmptyFaithful.S153Plus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Unique

variable {G : Type} [Group G]

theorem isUniqueM_mono {X X' M : Subgroup G} (hU : IsUniqueM X M) (hXX : X ≤ X') (hX' : X' ≤ M) :
    IsUniqueM X' M :=
  ⟨⟨hU.1.1, hX'⟩, fun M' hM' => hU.2 M' ⟨hM'.1, hXX.trans hM'.2⟩⟩

theorem conjSub_inv_eq_conjSubgroup (g : G) (A : Subgroup G) : conjSub g⁻¹ A = conjSubgroup A g := by
  ext x
  rw [mem_conjSub, mem_conjSubgroup_iff]
  simp

end Unique

namespace Decomp153

variable {G : Type} [Group G] [Finite G] {T M V₁ V₂ : Subgroup G} {t : G}

theorem swapPlanes (D : Decomp153 T M V₁ V₂ t) : Decomp153 T M V₂ V₁ t where
  le₁ := D.le₂
  le₂ := D.le₁
  inf := by rw [inf_comm]; exact D.inf
  sup := by rw [sup_comm]; exact D.sup
  card₁ := D.card₂
  card₂ := D.card₁
  definite := by
    obtain ⟨q, h1, h2, h3, h4, h5⟩ := D.definite
    exact ⟨q, h1, h2, h3, h4, fun v hv => by rw [h5 v hv, or_comm]⟩
  t_mem := D.t_mem
  swap₁ := D.swap₂
  swap₂ := D.swap₁
  t_sq := D.t_sq
  t_ne := D.t_ne
  comm₁ := D.comm₂
  comm₂ := D.comm₁
  iso₁ := D.iso₂
  iso₂ := D.iso₁
  inf_aut := by rw [inf_comm]; exact D.inf_aut
  comm_aut := fun a ha b hb => (D.comm_aut b hb a ha).symm
  conj_aut := by
    intro ht
    have h1 := D.conj_aut ht
    have hsq : conjAct (VZ T M) ⟨t, ht⟩ * conjAct (VZ T M) ⟨t, ht⟩ = 1 := by
      rw [← map_mul]
      exact A4.conjAct_eq_one_iff.mpr D.t_sq
    set c := conjAct (VZ T M) ⟨t, ht⟩ with hc
    rw [← h1, Subgroup.map_map]
    have : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      calc c * (c * x * c⁻¹) * c⁻¹ = (c * c) * x * (c * c)⁻¹ := by group
        _ = x := by rw [hsq]; group
    rw [this, Subgroup.map_id]
  factor := by
    intro ht
    rw [D.factor ht, sup_comm (autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M))]
  model := by
    obtain ⟨hV, L₁, L₂, tb, hS, h1, h2, ht⟩ := D.model
    exact ⟨hV, L₂, L₁, tb, hS.symm, h2, h1, ht⟩

end Decomp153

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Sgp153_eq_inf_normalizer_V₂ (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    Sgp153 T V₂ = Sgp153 T V₁ := by
  have h1 : Sgp153 T V₁ ≤ Sgp153 T V₂ :=
    le_inf inf_le_left (h.Sgp153_le_normalizer_V₂ D)
  have hi1 : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS h
  have hi2 : (Sgp153 T V₂).relIndex T = 2 := D.swapPlanes.relIndex_nS h
  refine le_antisymm ?_ h1
  have hS₂T : Sgp153 T V₂ ≤ T := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (Sgp153 T V₁) (Sgp153 T V₂) T h1 hS₂T
  rw [hi1, hi2] at hmul
  have h3 : (Sgp153 T V₁).relIndex (Sgp153 T V₂) = 1 := by omega
  exact Subgroup.relIndex_eq_one.mp h3

theorem exists_ne_one_mem_centralizer_Sgp153 (h : Hyp153 G T Mc M)
    {W : Subgroup G} (hWV : W ≤ VZ T M) (hW : W ≠ ⊥)
    (hS : Sgp153 T V₁ ≤ Subgroup.normalizer (W : Set G)) :
    ∃ z ∈ W, z ≠ 1 ∧ ∀ y ∈ Sgp153 T V₁, y * z = z * y := by
  have hT : IsPGroup 2 T := h.qtfe.sylow.1
  have hWT : W ≤ T := hWV.trans h.VZ_le_T
  have hST : Sgp153 T V₁ ⊔ W ≤ T := sup_le inf_le_left hWT
  obtain ⟨z, hzW, hz1, hz⟩ := exists_ne_one_mem_center_of_normalized (T := Sgp153 T V₁ ⊔ W)
    (hT.to_le hST) le_sup_right hW (sup_le hS Subgroup.le_normalizer)
  exact ⟨z, hzW, hz1, fun y hy => hz y (Subgroup.mem_sup_left hy)⟩

end Hyp153

end CFSG.Quasithin
