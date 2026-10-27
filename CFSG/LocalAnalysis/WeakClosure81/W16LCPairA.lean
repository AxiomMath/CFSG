module

public import CFSG.LocalAnalysis.WeakClosure81.W16LCGrp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.LinearAlgebra CFSG.Open Subgroup
open SemidirectProduct

variable {L : Type} [Group L] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : L →* LGL 2 W} {A : Subgroup L} {Z : Submodule (ZMod 2) W}

theorem w16l_mem_zHat_iff {x : VGL ρ} :
    x ∈ zHat ρ Z ↔ ∃ z ∈ Z, x = SemidirectProduct.inl (Multiplicative.ofAdd z) := by
  rw [zHat, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨Multiplicative.toAdd y, ?_, hxy.symm⟩
    rw [Multiplicative.mem_toSubgroup] at hy
    simpa using hy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by rwa [Multiplicative.mem_toSubgroup], rfl⟩

theorem w16l_mem_aHatL_iff {x : VGL ρ} :
    x ∈ aHatL ρ A ↔ ∃ a ∈ A, x = SemidirectProduct.inr a := by
  rw [aHatL, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem w16l_conj_inl (l : L) (z : W) :
    MulAut.conj (SemidirectProduct.inr l : VGL ρ)
        (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) =
      (SemidirectProduct.inl (Multiplicative.ofAdd (ρ l z)) : VGL ρ) := by
  rw [MulAut.conj_apply, ← map_inv,
    ← SemidirectProduct.inl_aut (φ := glAct ρ) l (Multiplicative.ofAdd z), glAct_apply]

theorem w16l_conj_inr (l a : L) :
    MulAut.conj (SemidirectProduct.inr l : VGL ρ) (SemidirectProduct.inr a : VGL ρ) =
      SemidirectProduct.inr (MulAut.conj l a) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem w16l_conj_inl_mul_inr (l : L) (z : W) (a : L) :
    (SemidirectProduct.inr l : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a) *
        (SemidirectProduct.inr l : VGL ρ)⁻¹ =
      (SemidirectProduct.inl (Multiplicative.ofAdd (ρ l z)) : VGL ρ) *
        SemidirectProduct.inr (MulAut.conj l a) := by
  rw [show (SemidirectProduct.inr l : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a) *
        (SemidirectProduct.inr l : VGL ρ)⁻¹ =
      MulAut.conj (SemidirectProduct.inr l : VGL ρ)
          (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) *
        MulAut.conj (SemidirectProduct.inr l : VGL ρ)
          (SemidirectProduct.inr a : VGL ρ) by
    rw [MulAut.conj_apply, MulAut.conj_apply]; group,
    w16l_conj_inl, w16l_conj_inr]

theorem w16l_map_conj_zHat (l : L) :
    (zHat ρ Z).map (MulAut.conj (SemidirectProduct.inr l : VGL ρ)).toMonoidHom =
      zHat ρ (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) := by
  ext x
  simp only [Subgroup.mem_map, w16l_mem_zHat_iff]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
    exact ⟨ρ l z, Submodule.mem_map_of_mem hz, hxy.symm.trans (w16l_conj_inl l z)⟩
  · rintro ⟨z₁, hz₁, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hz₁
    exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd z), ⟨z, hz, rfl⟩, w16l_conj_inl l z⟩

theorem w16l_map_conj_aHatL (l : L) :
    (aHatL ρ A).map (MulAut.conj (SemidirectProduct.inr l : VGL ρ)).toMonoidHom =
      aHatL ρ (A.map (MulAut.conj l).toMonoidHom) := by
  ext x
  simp only [Subgroup.mem_map, w16l_mem_aHatL_iff]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hxy⟩
    exact ⟨MulAut.conj l a, Subgroup.mem_map_of_mem _ ha,
      hxy.symm.trans (w16l_conj_inr l a)⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨SemidirectProduct.inr a, ⟨a, ha, rfl⟩, w16l_conj_inr l a⟩

theorem w16l_conjSubgroup_a1L (l : L) :
    CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) =
      a1L ρ (Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W))
        (A.map (MulAut.conj l).toMonoidHom) := by
  unfold CFSG.Quasithin.conjSubgroup
  simp only [map_inv, inv_inv]
  rw [a1L, Subgroup.map_sup, w16l_map_conj_zHat, w16l_map_conj_aHatL, a1L]

theorem w16l_mem_conjSubgroup_a1L_iff (hA : LiftHyp ρ A Z) (l : L) {x : VGL ρ} :
    x ∈ CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) ↔
      ∃ z ∈ Z, ∃ a ∈ A,
        x = (SemidirectProduct.inl (Multiplicative.ofAdd (ρ l z)) : VGL ρ) *
            SemidirectProduct.inr (MulAut.conj l a) := by
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, LiftHyp.mem_a1L_iff hA]
  constructor
  · rintro ⟨z, hz, a, ha, h⟩
    refine ⟨z, hz, a, ha, ?_⟩
    have hx : x = (SemidirectProduct.inr l : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a) *
        (SemidirectProduct.inr l : VGL ρ)⁻¹ := by
      rw [← h]
      simp only [map_inv, inv_inv]
      group
    exact hx.trans (w16l_conj_inl_mul_inr l z a)
  · rintro ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, a, ha, ?_⟩
    have h := w16l_conj_inl_mul_inr (ρ := ρ) l z a
    have h' : (SemidirectProduct.inr l : VGL ρ)⁻¹ *
        ((SemidirectProduct.inl (Multiplicative.ofAdd (ρ l z)) : VGL ρ) *
          SemidirectProduct.inr (MulAut.conj l a)) *
        (SemidirectProduct.inr l : VGL ρ) =
        (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a := by
      rw [← h]; group
    simpa only [map_inv, inv_inv] using h'

theorem w16l_map_rightHom_zHat :
    (zHat ρ Z).map (SemidirectProduct.rightHom : VGL ρ →* L) = ⊥ := by
  rw [zHat, Subgroup.map_map, SemidirectProduct.rightHom_comp_inl]
  simp

theorem w16l_map_rightHom_aHatL :
    (aHatL ρ A).map (SemidirectProduct.rightHom : VGL ρ →* L) = A := by
  rw [aHatL, Subgroup.map_map, SemidirectProduct.rightHom_comp_inr, Subgroup.map_id]

theorem w16l_map_rightHom_a1L :
    (a1L ρ Z A).map (SemidirectProduct.rightHom : VGL ρ →* L) = A := by
  rw [a1L, Subgroup.map_sup, w16l_map_rightHom_zHat, w16l_map_rightHom_aHatL, bot_sup_eq]

theorem w16l_map_rightHom_conjSubgroup_a1L (l : L) :
    (CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹)).map
        (SemidirectProduct.rightHom : VGL ρ →* L) =
      A.map (MulAut.conj l).toMonoidHom := by
  unfold CFSG.Quasithin.conjSubgroup
  simp only [map_inv, inv_inv]
  rw [Subgroup.map_map]
  have hcomp : (SemidirectProduct.rightHom : VGL ρ →* L).comp
        (MulAut.conj (SemidirectProduct.inr l : VGL ρ)).toMonoidHom =
      (MulAut.conj l).toMonoidHom.comp (SemidirectProduct.rightHom : VGL ρ →* L) := by
    ext x
    simp [MulAut.conj_apply, map_mul]
  rw [hcomp, ← Subgroup.map_map, w16l_map_rightHom_a1L]

theorem w16l_inr_mul_inl (b : L) (m : Multiplicative W) :
    (SemidirectProduct.inr b : VGL ρ) * SemidirectProduct.inl m =
      SemidirectProduct.inl (glAct ρ b m) * SemidirectProduct.inr b := by
  rw [show (SemidirectProduct.inr b : VGL ρ) * SemidirectProduct.inl m =
      (SemidirectProduct.inr b * SemidirectProduct.inl m * (SemidirectProduct.inr b)⁻¹) *
        SemidirectProduct.inr b by group,
    ← map_inv, ← SemidirectProduct.inl_aut (φ := glAct ρ) b m]

theorem w16l_conj_inl_mul_inr' (z w : W) (b : L) :
    (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd w) : VGL ρ) * SemidirectProduct.inr b) *
        (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ)⁻¹ =
      (SemidirectProduct.inl (Multiplicative.ofAdd (w - (ρ b z - z))) : VGL ρ) *
        SemidirectProduct.inr b := by
  have hzinv : (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ)⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd (-z)) := by
    rw [← map_inv, ← ofAdd_neg]
  rw [show (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd w) : VGL ρ) * SemidirectProduct.inr b) *
        (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ)⁻¹ =
      (SemidirectProduct.inl (Multiplicative.ofAdd z) *
        SemidirectProduct.inl (Multiplicative.ofAdd w)) *
        (SemidirectProduct.inr b * (SemidirectProduct.inl (Multiplicative.ofAdd z))⁻¹) by group,
    hzinv, w16l_inr_mul_inl, glAct_apply,
    ← map_mul (f := (SemidirectProduct.inl : Multiplicative W →* VGL ρ)), ← mul_assoc,
    ← map_mul (f := (SemidirectProduct.inl : Multiplicative W →* VGL ρ))]
  refine congrArg (fun t : Multiplicative W =>
    (SemidirectProduct.inl t : VGL ρ) * SemidirectProduct.inr b) ?_
  rw [← ofAdd_add, ← ofAdd_add]
  congr 1
  simp only [map_neg]
  abel

theorem w16l_rho_conj_sub_mem (hA : LiftHyp ρ A Z) (l : L) {a : L} (ha : a ∈ A) (z : W) :
    ρ (MulAut.conj l a) z - z ∈ Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := by
  have h1 : ρ (MulAut.conj l a) z - z =
      ρ l (ρ a (ρ l⁻¹ z) - ρ l⁻¹ z) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    simp only [LinearEquiv.mul_apply, map_sub]
    simp
  rw [h1]
  exact Submodule.mem_map_of_mem (hA.comm_le a ha (ρ l⁻¹ z))

theorem w16l_submodule_map_eq_of_le_of_sq {f : W ≃ₗ[ZMod 2] W} (hf : f * f = 1)
    {p : Submodule (ZMod 2) W} (h : p.map (f : W →ₗ[ZMod 2] W) ≤ p) :
    p.map (f : W →ₗ[ZMod 2] W) = p := by
  refine le_antisymm h ?_
  have hff : p.map ((f * f : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = p := by
    rw [hf]; simp
  calc p = p.map ((f * f : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := hff.symm
    _ = (p.map (f : W →ₗ[ZMod 2] W)).map (f : W →ₗ[ZMod 2] W) := by
          change p.map ((f : W →ₗ[ZMod 2] W).comp (f : W →ₗ[ZMod 2] W)) =
            (p.map (f : W →ₗ[ZMod 2] W)).map (f : W →ₗ[ZMod 2] W)
          rw [Submodule.map_comp]
    _ ≤ p.map (f : W →ₗ[ZMod 2] W) := Submodule.map_mono h

theorem w16l_mem_conjSubgroup_a1L_iff' (hA : LiftHyp ρ A Z) (l : L) {x : VGL ρ} :
    x ∈ CFSG.Quasithin.conjSubgroup (a1L ρ Z A) (SemidirectProduct.inr l⁻¹) ↔
      ∃ z₁ ∈ Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W), ∃ a ∈ A,
        x = (SemidirectProduct.inl (Multiplicative.ofAdd z₁) : VGL ρ) *
            SemidirectProduct.inr (MulAut.conj l a) := by
  constructor
  · intro hx
    obtain ⟨z, hz, a, ha, rfl⟩ := (w16l_mem_conjSubgroup_a1L_iff hA l).mp hx
    exact ⟨ρ l z, Submodule.mem_map_of_mem hz, a, ha, rfl⟩
  · rintro ⟨z₁, hz₁, a, ha, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hz₁
    exact (w16l_mem_conjSubgroup_a1L_iff hA l).mpr ⟨z, hz, a, ha, rfl⟩

theorem w16l_conj_a1L_inl (z w : W) (a : L) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a) *
        (SemidirectProduct.inl (Multiplicative.ofAdd w) : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a)⁻¹ =
      (SemidirectProduct.inl (Multiplicative.ofAdd (ρ a w)) : VGL ρ) := by
  have hzinv : (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ)⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd (-z)) := by
    rw [← map_inv, ← ofAdd_neg]
  rw [show ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a) *
        (SemidirectProduct.inl (Multiplicative.ofAdd w) : VGL ρ) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ) * SemidirectProduct.inr a)⁻¹ =
      (SemidirectProduct.inl (Multiplicative.ofAdd z) *
        (SemidirectProduct.inr a * (SemidirectProduct.inl (Multiplicative.ofAdd w) : VGL ρ) *
          (SemidirectProduct.inr a)⁻¹)) *
        (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ)⁻¹ by group,
    ← map_inv, ← SemidirectProduct.inl_aut (φ := glAct ρ) a (Multiplicative.ofAdd w), glAct_apply,
    hzinv, ← map_mul (f := (SemidirectProduct.inl : Multiplicative W →* VGL ρ)),
    ← map_mul (f := (SemidirectProduct.inl : Multiplicative W →* VGL ρ))]
  refine congrArg (fun t : Multiplicative W => (SemidirectProduct.inl t : VGL ρ)) ?_
  rw [← ofAdd_add, ← ofAdd_add]
  congr 1
  abel

theorem w16l_le_normalizer_of_conj_mem {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ K, ∀ y ∈ H, x * y * x⁻¹ ∈ H) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h x hx y
  · intro hy
    have hx' : x⁻¹ ∈ K := K.inv_mem hx
    have hmem := h x⁻¹ hx' (x * y * x⁻¹) hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group] at hmem

theorem w16l_card_zHat : Nat.card (zHat ρ Z) = Nat.card Z := by
  rw [zHat]
  rw [Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  refine Nat.card_congr (α := Z) (β := Z.toAddSubgroup.toSubgroup) ?_
  refine
    { toFun := fun z => ⟨Multiplicative.ofAdd z.1, by
        rw [Multiplicative.mem_toSubgroup]; simpa using z.2⟩
      invFun := fun x => ⟨Multiplicative.toAdd x.1, by
        have hx := x.2
        rw [Multiplicative.mem_toSubgroup] at hx
        simpa using hx⟩
      left_inv := fun z => rfl
      right_inv := fun x => rfl }

theorem w16l_zHat_ne_bot (hZ : Z ≠ ⊥) : zHat ρ Z ≠ ⊥ := by
  intro hbot
  have h1 : (AddSubgroup.toSubgroup Z.toAddSubgroup : Subgroup (Multiplicative W)) = ⊥ := by
    rw [zHat] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective
      (AddSubgroup.toSubgroup Z.toAddSubgroup : Subgroup (Multiplicative W))
      (f := (SemidirectProduct.inl : Multiplicative W →* VGL ρ))
      SemidirectProduct.inl_injective).mp hbot
  have h2 : Z.toAddSubgroup = (⊥ : AddSubgroup W) := by
    apply AddSubgroup.toSubgroup.injective
    simpa using h1
  exact hZ (Submodule.toAddSubgroup_injective (by simpa using h2))

theorem w16l_zHat_le_ker :
    zHat ρ Z ≤ (SemidirectProduct.rightHom : VGL ρ →* L).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨z, hz, rfl⟩ := w16l_mem_zHat_iff.mp hx
  simp

theorem w16l_mul_self_eq_one (w : W) :
    (Multiplicative.ofAdd w : Multiplicative W) * Multiplicative.ofAdd w = 1 := by
  rw [← ofAdd_add, show w + w = 0 by
    have h : (1 + 1 : ZMod 2) • w = 0 := by
      rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]
    simpa [add_smul] using h]
  rfl

theorem w16l_isPGroup_top : IsPGroup 2 (⊤ : Subgroup (Multiplicative W)) := by
  intro y
  refine ⟨1, ?_⟩
  rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
  apply Subtype.ext
  show (y : Multiplicative W) ^ 2 = 1
  obtain ⟨w, hw⟩ := Multiplicative.ofAdd.surjective (y : Multiplicative W)
  rw [← hw, sq]
  exact w16l_mul_self_eq_one w

theorem w16l_isPGroup_range_inl :
    IsPGroup 2 (SemidirectProduct.inl.range : Subgroup (VGL ρ)) := by
  rw [MonoidHom.range_eq_map]
  exact IsPGroup.map (p := 2) w16l_isPGroup_top SemidirectProduct.inl

end CFSG.LocalAnalysis.WeakClosure81

end
