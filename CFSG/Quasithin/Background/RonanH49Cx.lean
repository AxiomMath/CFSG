module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrV5

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr

@[expose] def wreathCongr {N N' Q : Type*} [Group N] [Group N'] [Group Q] (e : N ≃* N') :
    (N ≀ᵣ Q) ≃* (N' ≀ᵣ Q) where
  toFun w := ⟨fun q => e (w.left q), w.right⟩
  invFun w := ⟨fun q => e.symm (w.left q), w.right⟩
  left_inv w := RegularWreathProduct.ext (funext fun q => by simp) rfl
  right_inv w := RegularWreathProduct.ext (funext fun q => by simp) rfl
  map_mul' a b := RegularWreathProduct.ext (funext fun q => by simp [map_mul]) rfl

theorem stabE_eq : stabE = (P1.prod P1).map rho ⊔ Subgroup.zpowers tau := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨w, rfl⟩
    have hP : rho (((w.left 1 : ↥P1) : ↥SL32), ((w.left tq : ↥P1) : ↥SL32)) ∈
        (P1.prod P1).map rho :=
      Subgroup.mem_map_of_mem rho (Subgroup.mem_prod.2 ⟨(w.left 1).2, (w.left tq).2⟩)
    have hT : tauPow w.right ∈ Subgroup.zpowers tau := by
      rcases mz2_cases w.right with h | h
      · rw [h, map_one tauPow]
        exact one_mem _
      · rw [h, tauPow_tq]
        exact Subgroup.mem_zpowers tau
    rw [thetaW_apply]
    exact mul_mem (Subgroup.mem_sup_left hP) (Subgroup.mem_sup_right hT)
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr (mem_stabE_iff.2 ⟨tau_mem_norm, tau_eW_diag 0⟩))
    rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.1 hab
    exact mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img _), rho_fix_E00 ha hb⟩

theorem cent_x_eq_stabE : GW ⊓ centSub (Subgroup.zpowers (eW 0 0)) = stabE := by
  ext x
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    have h1' : x ∈ norm := by
      rw [GW_eq_norm] at h1
      exact h1
    exact mem_stabE_iff.2 ⟨h1', mem_centSub_zpowers_iff.1 h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := mem_stabE_iff.1 h
    refine Subgroup.mem_inf.2 ⟨?_, mem_centSub_zpowers_iff.2 h2⟩
    rw [GW_eq_norm]
    exact h1

theorem closure_V5 :
    Subgroup.closure ({eW 0 0, eW 0 1, eW 0 2, eW 1 0, eW 2 0} : Set WMod) = V5 := by
  refine le_antisymm ((Subgroup.closure_le V5).2 ?_) ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact eW00_mem_V5
    · exact eW_mem_V5_row 1
    · exact eW_mem_V5_row 2
    · exact eW_mem_V5_col 1
    · exact eW_mem_V5_col 2
  · have g00 : eW 0 0 ∈ Subgroup.closure ({eW 0 0, eW 0 1, eW 0 2, eW 1 0, eW 2 0} : Set WMod) :=
      Subgroup.subset_closure (by simp)
    have g01 : eW 0 1 ∈ Subgroup.closure ({eW 0 0, eW 0 1, eW 0 2, eW 1 0, eW 2 0} : Set WMod) :=
      Subgroup.subset_closure (by simp)
    have g02 : eW 0 2 ∈ Subgroup.closure ({eW 0 0, eW 0 1, eW 0 2, eW 1 0, eW 2 0} : Set WMod) :=
      Subgroup.subset_closure (by simp)
    have g10 : eW 1 0 ∈ Subgroup.closure ({eW 0 0, eW 0 1, eW 0 2, eW 1 0, eW 2 0} : Set WMod) :=
      Subgroup.subset_closure (by simp)
    have g20 : eW 2 0 ∈ Subgroup.closure ({eW 0 0, eW 0 1, eW 0 2, eW 1 0, eW 2 0} : Set WMod) :=
      Subgroup.subset_closure (by simp)
    intro Y hY
    have hY' := eq_of_isV5 _ hY
    have e : Y = Multiplicative.ofAdd (Multiplicative.toAdd Y 0 0 • Matrix.single 0 0 1) *
        Multiplicative.ofAdd (Multiplicative.toAdd Y 0 1 • Matrix.single 0 1 1) *
        Multiplicative.ofAdd (Multiplicative.toAdd Y 0 2 • Matrix.single 0 2 1) *
        Multiplicative.ofAdd (Multiplicative.toAdd Y 1 0 • Matrix.single 1 0 1) *
        Multiplicative.ofAdd (Multiplicative.toAdd Y 2 0 • Matrix.single 2 0 1) := by
      apply Multiplicative.toAdd.injective
      simpa only [toAdd_mul, toAdd_ofAdd] using hY'
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (ofAdd_smul_mem _ g00) (ofAdd_smul_mem _ g01))
      (ofAdd_smul_mem _ g02)) (ofAdd_smul_mem _ g10)) (ofAdd_smul_mem _ g20)

end CFSG.Quasithin.RonanH49
