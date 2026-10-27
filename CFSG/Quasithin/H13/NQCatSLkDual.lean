module

public import CFSG.Quasithin.H13.NQCatSLkBlock
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.Quasithin.H13.NQCat.SLk

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L Module

variable {k : ℕ}

@[expose] noncomputable def coflag (k i : ℕ) : Submodule (ZMod 2) (Fin k → ZMod 2) :=
  (flagSpace k (ZMod 2) (k - i)).map
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Fin.revPerm (n := k)) :
      (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))

theorem mem_coflag {i : ℕ} (hi : i ≤ k) {v : Fin k → ZMod 2} :
    v ∈ coflag k i ↔ ∀ j : Fin k, (j : ℕ) < i → v j = 0 := by
  rw [coflag, Submodule.mem_map_equiv, mem_flagSpace]
  constructor
  · intro h j hj
    have := h (Fin.rev j) (by simp [Fin.val_rev]; omega)
    simpa [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, Fin.revPerm] using this
  · intro h j hj
    have := h (Fin.rev j) (by simp [Fin.val_rev]; omega)
    simpa [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, Fin.revPerm] using this

theorem finrank_coflag {i : ℕ} (hi : i ≤ k) : finrank (ZMod 2) (coflag k i) = k - i := by
  rw [coflag, LinearEquiv.finrank_map_eq, finrank_flagSpace (by omega)]

theorem transpose_inv_mulVec_mem {i : ℕ} (hi : i ≤ k) {g : SpecialLinearGroup (Fin k) (ZMod 2)}
    (hg : g ∈ stabilizer (flagSpace k (ZMod 2) i)) {v : Fin k → ZMod 2} (hv : v ∈ coflag k i) :
    (((g⁻¹ : SpecialLinearGroup (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2))ᵀ *ᵥ v) ∈
      coflag k i := by
  have hg' := inv_mem hg
  rw [mem_coflag hi] at hv ⊢
  intro l hl
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge (j : ℕ) i with hj | hj
  · rw [hv j hj, mul_zero]
  · rw [transpose_apply, stabilizer_entries hg' hl hj, zero_mul]

theorem inner_of_map_stabilizer (hk : 3 ≤ k) (α : MulAut (SpecialLinearGroup (Fin k) (ZMod 2)))
    {i : ℕ} (hi : 1 ≤ i) (hik : i < k) (hk2 : k ≠ 2 * i)
    (hα : (stabilizer (flagSpace k (ZMod 2) i)).map α.toMonoidHom =
      stabilizer (flagSpace k (ZMod 2) i)) :
    ∃ x : SpecialLinearGroup (Fin k) (ZMod 2), ∀ y, α y = x * y * x⁻¹ := by
  obtain ⟨A, σ, h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl hk α
  have hσ : ∀ c : ZMod 2, σ c = c := by
    intro c
    fin_cases c
    · exact map_zero σ
    · exact map_one σ
  have hmap : ∀ M : Matrix (Fin k) (Fin k) (ZMod 2), M.map σ = M := fun M => by
    ext r c
    simp [hσ]
  have hAA : (A : Matrix (Fin k) (Fin k) (ZMod 2)) * ((A⁻¹ : GL (Fin k) (ZMod 2)) :
      Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : (A : Matrix (Fin k) (Fin k) (ZMod 2)).det = 1 := det_eq_one_of_mul_eq_one hAA
  rcases h with h | h
  ·
    set x : SpecialLinearGroup (Fin k) (ZMod 2) := ⟨A, hdet⟩ with hxdef
    have hx : ((x⁻¹ : SpecialLinearGroup (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) =
        ((A⁻¹ : GL (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one,
        one_smul]
    refine ⟨x, fun y => Subtype.ext ?_⟩
    rw [h, hmap, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx]
  ·
    exfalso
    set eA := (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv with heA
    have heA_apply : ∀ v, eA v = (A : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ v := fun v => rfl
    set W := (coflag k i).map (eA : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) with hW
    have hWinv : ∀ g ∈ flagStabilizer k (ZMod 2) {i}, ∀ w ∈ W,
        (g : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ w ∈ W := by
      intro g hg w hw
      rw [flagStabilizer_singleton] at hg
      have hg' : g ∈ (stabilizer (flagSpace k (ZMod 2) i)).map α.toMonoidHom := hα.symm ▸ hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg'
      obtain ⟨v, hv, rfl⟩ := hw
      have key : ((α g₀ : SpecialLinearGroup (Fin k) (ZMod 2)) :
          Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ ((A : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ v) =
          (A : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ
            ((((g₀⁻¹ : SpecialLinearGroup (Fin k) (ZMod 2)) :
              Matrix (Fin k) (Fin k) (ZMod 2))ᵀ) *ᵥ v) := by
        rw [h, hmap, mulVec_mulVec, mulVec_mulVec, mul_assoc, mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, mul_one]
      refine ⟨_, transpose_inv_mulVec_mem hik.le hg₀ hv, ?_⟩
      rw [MulEquiv.coe_toMonoidHom]
      simp only [LinearEquiv.coe_coe, heA_apply]
      exact key.symm
    have hWr : finrank (ZMod 2) W = k - i := by
      rw [hW, LinearEquiv.finrank_map_eq, finrank_coflag hik.le]
    rcases ((subflag_stabilizer_generation (K := ZMod 2) (n := k) {i}).2.1 W).1 hWinv with
      h0 | htop | ⟨j, hj, hWj⟩
    · rw [h0, finrank_bot] at hWr
      omega
    · rw [htop, finrank_top, Module.finrank_fin_fun] at hWr
      omega
    · rw [Set.mem_singleton_iff] at hj
      subst hj
      rw [hWj, finrank_flagSpace hik.le] at hWr
      omega

end CFSG.Quasithin.H13.NQCat.SLk
