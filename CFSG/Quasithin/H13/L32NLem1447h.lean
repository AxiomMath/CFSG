module

public import CFSG.Quasithin.H13.L32NLem1447g
public import CFSG.Quasithin.H13.L32N1447Model
public import CFSG.Quasithin.H13.L32NLem14410b
public import CFSG.Quasithin.H13.L32NLem14412d

public section

namespace CFSG.Quasithin.H13.L1447

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M
  Q1447Cert

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

theorem facts_of_ctx4
    (B : Base G T L V V₂ g) (h12213 : Stmt12_2_13) {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (C : L14411.Ctx G T L V V₂ g D e) : F1 T V V₂ ∧ F2 T V V₂ g ∧ F3 T V V₂ g := by
  obtain ⟨a, ha, haV⟩ := B.abs.exists_mem_not_mem
  refine ⟨B.F1_of_coords D e (matOf e) (matOf_mulVec e) fun γ hγ h1 h2 => ?_,
    B.F2_of_coords D e (matOf e) h12213 (matOf_mulVec e) ha haV fun γ hγ h1 h2 => ?_,
    B.F3_of_map D (matOf e) (matOf_injective e) ?_⟩
  · have hγ' : γ ∈ img8 D e (l32nH T V) := hγ
    rw [C.imgH] at hγ'
    exact s7_big hγ' h1 h2
  · have hγ' : γ ∈ img8 D e (l32nH T V) := img8_mono D e B.WgH hγ
    rw [C.imgH] at hγ'
    exact Or.inl (s7_big hγ' h1 h2)
  · have h := s7_oTwoUpper_le
    rw [← C.imgH, ← C.img_Wg] at h
    exact h

theorem facts_of_ctx5
    (h12213 : Stmt12_2_13) {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (C : L14410.Ctx5 G T L V V₂ g D e) : F1 T V V₂ ∧ F2 T V V₂ g ∧ F3 T V V₂ g := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  refine ⟨C.base.F1_of_coords D e (matOf e) (matOf_mulVec e) fun γ hγ h1 h2 => ?_,
    C.base.F2_of_coords D e (matOf e) h12213 (matOf_mulVec e) ha haV fun γ hγ h1 h2 => ?_,
    C.base.F3_of_map D (matOf e) (matOf_injective e) ?_⟩
  · have hγ' : γ ∈ img8 D e (l32nH T V) := hγ
    rw [C.imgH] at hγ'
    exact g5_big hγ' h1 h2
  · have hγ' : γ ∈ img8 D e (l32nH T V) := img8_mono D e C.base.WgH hγ
    rw [C.imgH] at hγ'
    exact Or.inl (g5_big hγ' h1 h2)
  · have h := g5_oTwoUpper_le
    rw [← C.imgH] at h
    refine h.trans (Subgroup.closure_mono ?_)
    rintro y ⟨k, hk, z, hz, rfl⟩
    exact ⟨k, hk, z, C.mem_img_Wg_of_central hz, rfl⟩

theorem facts_of_ctx6
    (h12213 : Stmt12_2_13) {e : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)}
    (C : L14412.Ctx6 G T L V V₂ g D e) : F1 T V V₂ ∧ F2 T V V₂ g ∧ F3 T V V₂ g := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  refine ⟨C.base.F1_of_coords D e (matOfN e) (matOfN_mulVec e) fun γ hγ h1 h2 => ?_,
    C.base.F2_of_coords D e (matOfN e) h12213 (matOfN_mulVec e) ha haV fun γ hγ h1 h2 => ?_,
    C.base.F3_of_map D (matOfN e) (matOfN_injective e) ?_⟩
  · have hγ' : γ ∈ imgN D e (l32nH T V) := hγ
    rw [C.imgH] at hγ'
    exact m22_big hγ' h1 h2
  · have hγ' : γ ∈ imgN D e (l32nH T V) := imgN_mono D e C.base.WgH hγ
    rw [C.imgH] at hγ'
    exact Or.inl (m22_big hγ' h1 h2)
  · have h := m22_oTwoUpper_le
    rw [← C.imgH, ← C.img_Wg_eq] at h
    exact h

end CFSG.Quasithin.H13.L1447
