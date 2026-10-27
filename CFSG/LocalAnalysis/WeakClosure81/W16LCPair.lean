module

public import CFSG.LocalAnalysis.WeakClosure81.W16LCPairA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W3Lem71Holds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.LinearAlgebra CFSG.Open Subgroup
open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open SemidirectProduct

variable {L : Type} [Group L] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : L →* LGL 2 W} {A : Subgroup L} {Z : Submodule (ZMod 2) W}

section Certified


private theorem w16l_comm_ne_bot [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    ⁅a1L ρ Z A, CFSG.Quasithin.conjSubgroup (a1L ρ Z A)
      (SemidirectProduct.inr l⁻¹)⁆ ≠ ⊥ := by
  classical
  intro hbot
  set Z₁ : Submodule (ZMod 2) W :=
    Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) with hZ₁
  have hcent : a1L ρ Z A ≤ Subgroup.centralizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  apply hA.ne_bot_A
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have hfix : ∀ z₁ ∈ Z₁, ρ a z₁ = z₁ := by
    intro z₁ hz₁
    have hmemV' : (SemidirectProduct.inl (Multiplicative.ofAdd z₁) : VGL ρ) ∈
        CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :=
      (w16l_mem_conjSubgroup_a1L_iff' hA l).mpr ⟨z₁, hz₁, 1, A.one_mem, by simp⟩
    have hmemVa : (SemidirectProduct.inr a : VGL ρ) ∈ a1L ρ Z A := by
      rw [a1L]
      exact Subgroup.mem_sup_right (w16l_mem_aHatL_iff.mpr ⟨a, ha, rfl⟩)
    have hcz := (Subgroup.mem_centralizer_iff.mp (hcent hmemVa))
      (SemidirectProduct.inl (Multiplicative.ofAdd z₁) : VGL ρ) hmemV'
    rw [w16l_inr_mul_inl] at hcz
    have h2 : Multiplicative.ofAdd z₁ = glAct ρ a (Multiplicative.ofAdd z₁) :=
      SemidirectProduct.inl_injective (mul_right_cancel hcz)
    rw [glAct_apply] at h2
    exact h2.symm
  have hmap : Z₁.map ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z₁ := by
    refine le_antisymm ?_ ?_
    · intro w hw
      obtain ⟨z₁, hz₁, rfl⟩ := Submodule.mem_map.mp hw
      rw [show (ρ a : W →ₗ[ZMod 2] W) z₁ = z₁ from hfix z₁ hz₁]; exact hz₁
    · intro w hw
      rw [← hfix w hw]
      exact Submodule.mem_map_of_mem hw
  exact he a ha (by simpa only [hZ₁] using hmap)

private theorem w16l_conj_not_mem_normalizer [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    (SemidirectProduct.inr l⁻¹ : VGL ρ) ∉
      Subgroup.normalizer (a1L ρ Z A : Set (VGL ρ)) := by
  intro hgmem
  refine w16l_comm_ne_bot hA l he ?_
  rw [CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hgmem]
  exact Subgroup.commutator_self_eq_bot_iff.mpr (LiftHyp.isElemAbelian_a1L hA).1

theorem LiftHyp.inf_normalizer_a1L [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1)
    (he' : ∀ a ∈ A, (Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    a1L ρ Z A ⊓ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
          Subgroup (VGL ρ)) : Set (VGL ρ)) = zHat ρ Z ∧
      CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) ⊓
        Subgroup.normalizer ((a1L ρ Z A : Subgroup (VGL ρ)) : Set (VGL ρ)) =
        zHat ρ (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) := by
  classical
  set Z₁ : Submodule (ZMod 2) W :=
    Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) with hZ₁
  have hfst : a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ)) = zHat ρ Z := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxV, hxN⟩ := hx
      obtain ⟨z, hz, a, ha, rfl⟩ := (LiftHyp.mem_a1L_iff hA).mp hxV
      have hle : Z₁.map ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) ≤ Z₁ := by
        intro w hw
        obtain ⟨w₀, hw₀, rfl⟩ := Submodule.mem_map.mp hw
        have hmemV' : (SemidirectProduct.inl (Multiplicative.ofAdd w₀) : VGL ρ) ∈
            CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :=
          (w16l_mem_conjSubgroup_a1L_iff' hA l).mpr ⟨w₀, hw₀, 1, A.one_mem, by simp⟩
        have hconj : (SemidirectProduct.inl (Multiplicative.ofAdd (ρ a w₀)) : VGL ρ) ∈
            CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) := by
          have h := (Subgroup.mem_normalizer_iff.mp hxN) _ |>.mp hmemV'
          rwa [w16l_conj_a1L_inl z w₀ a] at h
        rw [w16l_mem_conjSubgroup_a1L_iff' hA l] at hconj
        obtain ⟨z₂, hz₂, a₂, ha₂, heq⟩ := hconj
        have hright : MulAut.conj l a₂ = 1 := by
          have h := congrArg (SemidirectProduct.rightHom : VGL ρ →* L) heq
          simpa using h.symm
        have ha₂1 : a₂ = 1 := (MulAut.conj l).injective (by simpa using hright)
        subst ha₂1
        have hleft : (SemidirectProduct.inl (Multiplicative.ofAdd (ρ a w₀)) : VGL ρ) =
            SemidirectProduct.inl (Multiplicative.ofAdd z₂) := by simpa using heq
        have hzw : (ρ a : W →ₗ[ZMod 2] W) w₀ = z₂ := by
          have h := Multiplicative.ofAdd.injective (SemidirectProduct.inl_injective hleft)
          simpa only [LinearEquiv.coe_coe] using h
        have hz₂' : z₂ ∈ Z₁ := by rw [hZ₁]; exact hz₂
        simpa only [hzw] using hz₂'
      have hsq : (ρ a : W ≃ₗ[ZMod 2] W) * ρ a = 1 := by
        have ha2 : a * a = 1 := by simpa [pow_two] using hA.elemAbelian.2 a ha
        have := congrArg ρ ha2
        simpa using this
      have heqZ : Z₁.map ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z₁ :=
        w16l_submodule_map_eq_of_le_of_sq hsq hle
      have ha1 : a = 1 := he a ha (by simpa only [hZ₁] using heqZ)
      subst ha1
      rw [show (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) *
          SemidirectProduct.inr 1 = SemidirectProduct.inl (Multiplicative.ofAdd z) by simp]
      exact w16l_mem_zHat_iff.mpr ⟨z, hz, rfl⟩
    · refine le_inf ?_ ?_
      · rw [a1L]; exact le_sup_left
      · refine w16l_le_normalizer_of_conj_mem (fun x hx y hy => ?_)
        obtain ⟨z, hz, rfl⟩ := w16l_mem_zHat_iff.mp hx
        obtain ⟨w, hw, a, ha, rfl⟩ := (w16l_mem_conjSubgroup_a1L_iff' hA l).mp hy
        rw [w16l_mem_conjSubgroup_a1L_iff' hA l]
        exact ⟨w - (ρ (MulAut.conj l a) z - z),
          sub_mem hw (w16l_rho_conj_sub_mem hA l ha z), a, ha,
          w16l_conj_inl_mul_inr' z w (MulAut.conj l a)⟩
  have hsnd : CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) ⊓
      Subgroup.normalizer ((a1L ρ Z A : Subgroup (VGL ρ)) : Set (VGL ρ)) = zHat ρ Z₁ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxV', hxN⟩ := hx
      obtain ⟨z₁, hz₁, a, ha, rfl⟩ := (w16l_mem_conjSubgroup_a1L_iff' hA l).mp hxV'
      have hle : Z.map ((ρ (MulAut.conj l a) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) ≤ Z := by
        intro w hw
        obtain ⟨w₀, hw₀, rfl⟩ := Submodule.mem_map.mp hw
        have hmemV : (SemidirectProduct.inl (Multiplicative.ofAdd w₀) : VGL ρ) ∈ a1L ρ Z A := by
          rw [a1L]
          exact Subgroup.mem_sup_left (w16l_mem_zHat_iff.mpr ⟨w₀, hw₀, rfl⟩)
        have hconj : (SemidirectProduct.inl
            (Multiplicative.ofAdd (ρ (MulAut.conj l a) w₀)) : VGL ρ) ∈ a1L ρ Z A := by
          have h := (Subgroup.mem_normalizer_iff.mp hxN) _ |>.mp hmemV
          rwa [w16l_conj_a1L_inl z₁ w₀ (MulAut.conj l a)] at h
        rw [LiftHyp.mem_a1L_iff hA] at hconj
        obtain ⟨z', hz', a', ha', heq⟩ := hconj
        have hright : a' = 1 := by
          have h := congrArg (SemidirectProduct.rightHom : VGL ρ →* L) heq
          simpa using h.symm
        subst hright
        have hleft : (SemidirectProduct.inl
            (Multiplicative.ofAdd (ρ (MulAut.conj l a) w₀)) : VGL ρ) =
            SemidirectProduct.inl (Multiplicative.ofAdd z') := by
          simpa only [map_one, mul_one] using heq
        have hzw : (ρ (MulAut.conj l a) : W →ₗ[ZMod 2] W) w₀ = z' := by
          have h := Multiplicative.ofAdd.injective (SemidirectProduct.inl_injective hleft)
          simpa only [LinearEquiv.coe_coe] using h
        simpa only [hzw] using hz'
      have hsq : (ρ (MulAut.conj l a) : W ≃ₗ[ZMod 2] W) * ρ (MulAut.conj l a) = 1 := by
        have ha2 : (MulAut.conj l a) * (MulAut.conj l a) = 1 := by
          rw [← map_mul, show a * a = 1 by simpa [pow_two] using hA.elemAbelian.2 a ha,
            map_one]
        have := congrArg ρ ha2
        simpa using this
      have hZmap : Z.map ((ρ (MulAut.conj l a) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z :=
        w16l_submodule_map_eq_of_le_of_sq hsq hle
      have hmap : (Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
          ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
          Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := by
        have h1 := congrArg (fun q : Submodule (ZMod 2) W =>
          q.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) hZmap
        rw [← Submodule.map_comp] at h1
        have hcomp : ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W).comp
            ((ρ (MulAut.conj l a) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
            ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W).comp
              ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := by
          ext w
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
          simp
        rw [hcomp] at h1
        rwa [Submodule.map_comp] at h1
      have ha1 : a = 1 := he' a ha (by simpa only [hZ₁] using hmap)
      subst ha1
      rw [show (SemidirectProduct.inl (Multiplicative.ofAdd z₁) : VGL ρ) *
          SemidirectProduct.inr (MulAut.conj l 1) =
          SemidirectProduct.inl (Multiplicative.ofAdd z₁) by simp]
      exact w16l_mem_zHat_iff.mpr ⟨z₁, hz₁, rfl⟩
    · refine le_inf ?_ ?_
      · rw [w16l_conjSubgroup_a1L, a1L]; exact le_sup_left
      · refine w16l_le_normalizer_of_conj_mem (fun x hx y hy => ?_)
        obtain ⟨z₁, hz₁, rfl⟩ := w16l_mem_zHat_iff.mp hx
        obtain ⟨w, hw, a, ha, rfl⟩ := (LiftHyp.mem_a1L_iff hA).mp hy
        rw [LiftHyp.mem_a1L_iff hA]
        exact ⟨w - (ρ a z₁ - z₁), sub_mem hw (hA.comm_le a ha z₁), a, ha,
          w16l_conj_inl_mul_inr' z₁ w a⟩
  exact ⟨hfst, hsnd⟩

private theorem w16l_pair_inf_ne_bot [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1)
    (he' : ∀ a ∈ A, (Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    a1L ρ Z A ⊓ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
          Subgroup (VGL ρ)) : Set (VGL ρ)) ≠ ⊥ := by
  rw [(LiftHyp.inf_normalizer_a1L hA l he he').1]
  exact w16l_zHat_ne_bot hA.ne_bot_Z

private theorem w16l_pair_inf_ne_self [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1)
    (he' : ∀ a ∈ A, (Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    a1L ρ Z A ⊓ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
          Subgroup (VGL ρ)) : Set (VGL ρ)) ≠ a1L ρ Z A := by
  rw [(LiftHyp.inf_normalizer_a1L hA l he he').1]
  intro heq
  apply hA.ne_bot_A
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  by_contra ha1
  have hmem : (SemidirectProduct.inr a : VGL ρ) ∈ zHat ρ Z := by
    rw [heq, a1L]
    exact Subgroup.mem_sup_right (w16l_mem_aHatL_iff.mpr ⟨a, ha, rfl⟩)
  rw [w16l_mem_zHat_iff] at hmem
  obtain ⟨z, hz, heq2⟩ := hmem
  exact ha1 (by
    have := congrArg (SemidirectProduct.rightHom : VGL ρ →* L) heq2
    simpa using this)


theorem LiftHyp.pair_projection [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1)
    (he' : ∀ a ∈ A, (Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    (a1L ρ Z A ⊔ CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹)).map
        (SemidirectProduct.rightHom : VGL ρ →* L) =
      A ⊔ A.map (MulAut.conj l).toMonoidHom ∧
    ∀ x ∈ a1L ρ Z A ⊔ CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹),
      (SemidirectProduct.rightHom x = 1 ↔ x ∈ pCoreOf 2
        (a1L ρ Z A ⊔ CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹))) := by
  classical
  set Z₁ : Submodule (ZMod 2) W :=
    Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) with hZ₁
  have hcomm : ⁅a1L ρ Z A, CFSG.Quasithin.conjSubgroup (a1L ρ Z A)
      (SemidirectProduct.inr l⁻¹)⁆ ≠ ⊥ := w16l_comm_ne_bot hA l he
  have hg : (SemidirectProduct.inr l⁻¹ : VGL ρ) ∉
      Subgroup.normalizer (a1L ρ Z A : Set (VGL ρ)) := w16l_conj_not_mem_normalizer hA l he
  have hW3 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.w3Lem71_holds (G := VGL ρ)
    (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) hA.hyp7_a1L hg
    (w16l_pair_inf_ne_bot hA l he he') (w16l_pair_inf_ne_self hA l he he') hcomm
  obtain ⟨hO2, hUB, hcommUB, hshape, hodd, hnat⟩ := hW3
  have hUeq : a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ)) = zHat ρ Z :=
    (LiftHyp.inf_normalizer_a1L hA l he he').1
  have hBeq : CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) ⊓
      Subgroup.normalizer ((a1L ρ Z A : Subgroup (VGL ρ)) : Set (VGL ρ)) = zHat ρ Z₁ :=
    (LiftHyp.inf_normalizer_a1L hA l he he').2
  refine ⟨?_, ?_⟩
  · rw [Subgroup.map_sup, w16l_map_rightHom_a1L, w16l_map_rightHom_conjSubgroup_a1L]
  · intro x hx
    constructor
    · intro hx1
      have hker_le : (a1L ρ Z A ⊔ CFSG.Quasithin.conjSubgroup (a1L ρ Z A)
            (SemidirectProduct.inr l⁻¹)) ⊓ (SemidirectProduct.rightHom : VGL ρ →* L).ker ≤
          pCoreOf 2 (a1L ρ Z A ⊔ CFSG.Quasithin.conjSubgroup (a1L ρ Z A)
            (SemidirectProduct.inr l⁻¹)) := by
        refine CFSG.LieType.BorelTits.le_pCoreOf (r := 2) inf_le_left ?_ ?_
        · rw [Subgroup.inf_subgroupOf_left]
          exact Subgroup.Normal.subgroupOf
            (MonoidHom.normal_ker (SemidirectProduct.rightHom : VGL ρ →* L)) _
        · refine IsPGroup.to_le ?_ inf_le_right
          rw [show (SemidirectProduct.rightHom : VGL ρ →* L).ker =
              SemidirectProduct.inl.range from
            SemidirectProduct.range_inl_eq_ker_rightHom.symm]
          exact w16l_isPGroup_range_inl
      exact hker_le ⟨hx, (MonoidHom.mem_ker).mpr hx1⟩
    · intro hxcore
      have hker : pCoreOf 2 (a1L ρ Z A ⊔ CFSG.Quasithin.conjSubgroup (a1L ρ Z A)
            (SemidirectProduct.inr l⁻¹)) ≤ (SemidirectProduct.rightHom : VGL ρ →* L).ker := by
        rw [hO2]
        refine sup_le ?_ ?_
        · rw [hUeq]; exact w16l_zHat_le_ker
        · rw [hBeq]; exact w16l_zHat_le_ker
      exact MonoidHom.mem_ker.mp (hker hxcore)

theorem LiftHyp.pair_shape [Finite L] [Finite W] (hA : LiftHyp ρ A Z) (l : L)
    (hnc : ∃ a ∈ A, ∃ b ∈ A.map (MulAut.conj l).toMonoidHom, a * b ≠ b * a)
    (he : ∀ a ∈ A, (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1)
    (he' : ∀ a ∈ A, (Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)).map
      ((ρ a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
        Z.map ((ρ l⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) → a = 1) :
    ∃ n : ℕ, Nat.card A = 2 ^ n ∧
      (IsL2 ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n ∨
        IsSz ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n ∨
        (n = 1 ∧ ∃ m : ℕ, Odd m ∧
          Nonempty (↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) ≃* DihedralGroup m))) := by
  classical
  set Z₁ : Submodule (ZMod 2) W :=
    Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) with hZ₁
  set A' : Subgroup L := A.map (MulAut.conj l).toMonoidHom with hA'
  have hcomm := w16l_comm_ne_bot hA l he
  have hg := w16l_conj_not_mem_normalizer hA l he
  have hW3 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.w3Lem71_holds (G := VGL ρ)
    (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) hA.hyp7_a1L hg
    (w16l_pair_inf_ne_bot hA l he he') (w16l_pair_inf_ne_self hA l he he') hcomm
  obtain ⟨hO2, hUB, hcommUB, hshape, hodd, hnat⟩ := hW3
  set X : Subgroup (VGL ρ) := a1L ρ Z A ⊔
    CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) with hX
  have hUeq : a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ)) = zHat ρ Z :=
    (LiftHyp.inf_normalizer_a1L hA l he he').1
  have hproj := LiftHyp.pair_projection hA l he he'
  rw [← hX] at hproj
  obtain ⟨Y, hYgrp, φ, hφsurj, hφker, hPY⟩ := hshape
  letI : Group Y := hYgrp
  have hφker' : φ.ker = (pCoreOf 2 X).subgroupOf X := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker k
  let eφ : ↥X ⧸ φ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
  have hψker : ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).ker =
      (pCoreOf 2 X).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hproj.2 x x.2
  have hψrange : ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).range = A ⊔ A' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hproj.1, ← hA']
  have hψrk : ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).rangeRestrict.ker =
      ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => Subtype.ext_iff.mp h, fun h => Subtype.ext h⟩
  let eψ : ↥X ⧸ ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).ker ≃*
      ↥(A ⊔ A') :=
    (QuotientGroup.quotientMulEquivOfEq hψrk.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective
        ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).rangeRestrict
        ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).rangeRestrict_surjective).trans
        (MulEquiv.subgroupCongr hψrange))
  have hkerEq : φ.ker = ((SemidirectProduct.rightHom : VGL ρ →* L).comp X.subtype).ker := by
    rw [hφker', hψker]
  let eZ : Y ≃* ↥(A ⊔ A') :=
    eφ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans eψ)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA.elemAbelian.isPGroup
  have hcardV : Nat.card (a1L ρ Z A) = Nat.card Z * Nat.card A := LiftHyp.card_a1L hA
  have hcardU : Nat.card ↥(a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ))) = Nat.card Z := by
    rw [hUeq]; exact w16l_card_zHat
  have hcardZ : Nat.card Z ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨Nonempty.intro ⟨0, Z.zero_mem⟩, inferInstance⟩
  have hrel : (a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ))).relIndex (a1L ρ Z A) = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ))) (K := a1L ρ Z A)
    rw [inf_eq_left.mpr inf_le_left] at h
    rw [hcardV, hcardU, mul_comm (Nat.card Z) (Nat.card A)] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hcardZ) h
  refine ⟨E3.mQuot (a1L ρ Z A) (a1L ρ Z A ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
        Subgroup (VGL ρ)) : Set (VGL ρ))), ?_, ?_⟩
  · have hn : E3.mQuot (a1L ρ Z A) (a1L ρ Z A ⊓ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) :
          Subgroup (VGL ρ)) : Set (VGL ρ))) = k := by
      rw [E3.mQuot, hrel, hk, padicValNat.prime_pow]
    rw [hk, hn]
  · rcases hPY with ⟨n', hL2, hn'⟩ | ⟨n', hSz, hn'⟩ | ⟨m, hm, hD, hn1⟩
    · left
      rw [hn']
      exact CFSG.Blueprint.LieModel.of_mulEquiv eZ hL2
    · right; left
      rw [hn']
      exact CFSG.Blueprint.LieModel.of_mulEquiv eZ hSz
    · right; right
      exact ⟨hn1, m, hm, ⟨eZ.symm.trans hD.some⟩⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
