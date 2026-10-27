module

public import CFSG.Quasithin.Background.RonanG25BaseCore
public import CFSG.Quasithin.Background.RonanG25Mod

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model
open scoped MatrixGroups Matrix

section U

variable {F : Type} [Field F] [Finite F] [CharP F 2] {Γ : Type} [Group Γ]

theorem dualHom_entry (g : SL(3, F)) (i j : Fin 3) :
    (dualHom F 3 g).1 i j = (g⁻¹ : SL(3, F)).1 j i := by
  rw [dualHom_apply, slT_coe, Matrix.transpose_apply]

theorem actUg_apply (g : SL(3, F)) (v : Fin 2 → F) :
    actUg g v = g.1 0 0 • (ablk (dualHom F 3 g) *ᵥ v) := rfl

theorem ablk_mul_of_row {X Y : SL(3, F)} (hY1 : Y.1 0 1 = 0) (hY2 : Y.1 0 2 = 0) :
    ablk (X * Y) = ablk X * ablk Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ablk, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hY1, hY2]

theorem conj_tqv {g : SL(3, F)} (hg : g ∈ Pt (vE F 0)) (v : Fin 2 → F) :
    g * tqv v * g⁻¹ = tqv (actUg g v) := by
  obtain ⟨h, hh⟩ : ∃ h : SL(3, F), g⁻¹ = h := ⟨_, rfl⟩
  obtain ⟨h10, h20⟩ := Pt_entries hg
  have hhP : h ∈ Pt (vE F 0) := by
    rw [← hh]
    exact inv_mem hg
  obtain ⟨k10, k20⟩ := Pt_entries hhP
  have hmat : (h : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← hh, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have E11 : h.1 1 1 * g.1 1 1 + h.1 1 2 * g.1 2 1 = 1 := by
    have := congrFun (congrFun hmat 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, k10] at this
    linear_combination this
  have E12 : h.1 1 1 * g.1 1 2 + h.1 1 2 * g.1 2 2 = 0 := by
    have := congrFun (congrFun hmat 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, k10] at this
    linear_combination this
  have E21 : h.1 2 1 * g.1 1 1 + h.1 2 2 * g.1 2 1 = 0 := by
    have := congrFun (congrFun hmat 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, k20] at this
    linear_combination this
  have E22 : h.1 2 1 * g.1 1 2 + h.1 2 2 * g.1 2 2 = 1 := by
    have := congrFun (congrFun hmat 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, k20] at this
    linear_combination this
  have hD : ∀ i j : Fin 3, (dualHom F 3 g).1 i j = h.1 j i := fun i j => by
    rw [dualHom_entry, hh]
  have hb : actUg g v 0 = g.1 0 0 * (h.1 1 1 * v 0 + h.1 2 1 * v 1) := by
    rw [actUg_apply]
    simp [ablk, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD]
  have hc : actUg g v 1 = g.1 0 0 * (h.1 1 2 * v 0 + h.1 2 2 * v 1) := by
    rw [actUg_apply]
    simp [ablk, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD]
  have key : g * tqv v = tqv (actUg g v) * g := by
    apply Subtype.ext
    simp only [tqv, Matrix.SpecialLinearGroup.coe_mul, tq_coe, hb, hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20] <;>
      first
        | linear_combination (-(g.1 0 0 * v 0)) * E11 + (-(g.1 0 0 * v 1)) * E21
        | linear_combination (-(g.1 0 0 * v 0)) * E12 + (-(g.1 0 0 * v 1)) * E22
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def Umat (g : SL(3, F)) : Matrix (Fin 2) (Fin 2) F :=
  g.1 0 0 • ablk (dualHom F 3 g)

theorem Umat_mulVec (g : SL(3, F)) (v : Fin 2 → F) : Umat g *ᵥ v = actUg g v := by
  rw [Umat, Matrix.smul_mulVec, actUg_apply]

theorem Umat_one : Umat (1 : SL(3, F)) = 1 := by
  simp [Umat, ablk_one]

theorem Umat_mul {g k : SL(3, F)} (hk : k ∈ Pt (vE F 0)) :
    Umat (g * k) = Umat g * Umat k := by
  obtain ⟨k10, k20⟩ := Pt_entries hk
  have hgk : (g * k).1 0 0 = g.1 0 0 * k.1 0 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, k10, k20]
    ring
  have hab : ablk (dualHom F 3 (g * k)) = ablk (dualHom F 3 g) * ablk (dualHom F 3 k) := by
    rw [map_mul]
    exact ablk_mul_of_row (dual_entries hk).2.1 (dual_entries hk).2.2.1
  unfold Umat
  rw [hgk, hab, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

@[expose] noncomputable def UmatHom : Pt (vE F 0) →* Matrix.GeneralLinearGroup (Fin 2) F where
  toFun g :=
    { val := Umat g.1
      inv := Umat g.1⁻¹
      val_inv := by rw [← Umat_mul (inv_mem g.2), mul_inv_cancel, Umat_one]
      inv_val := by rw [← Umat_mul g.2, inv_mul_cancel, Umat_one] }
  map_one' := Units.ext Umat_one
  map_mul' g h := Units.ext (Umat_mul (g := g.1) h.2)

@[expose] noncomputable def betaU (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) :
    Γ →* Matrix.GeneralLinearGroup (Fin 2) F :=
  UmatHom.comp
    { toFun := fun x => ⟨ρ x, hρ.stab x⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun x y => Subtype.ext (map_mul ρ x y) }

theorem betaU_coe (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) (x : Γ) :
    ((betaU ρ hρ x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Umat (ρ x) :=
  rfl

private theorem ablk_dualHom_blk (K : SL(2, F)) :
    ablk (dualHom F 3 (CFSG.Quasithin.SL3Model.blk K)) =
      ((K⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  rw [dualHom_apply, ← map_inv CFSG.Quasithin.SL3Model.blk]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ablk, slT_coe, CFSG.Quasithin.SL3Model.blk_coe, Matrix.adjugate_fin_two]

theorem Umat_blk (K : SL(2, F)) :
    Umat (CFSG.Quasithin.SL3Model.blk K) = ((K⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  have h00 : (CFSG.Quasithin.SL3Model.blk K : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
    simp [CFSG.Quasithin.SL3Model.blk_coe]
  unfold Umat
  rw [h00, one_smul, ablk_dualHom_blk]

theorem dualHom_inv_coe (N : SL(2, F)) :
    (((dualHom F 2 N)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ = N.1 := by
  rw [dualHom_apply, ← slT_inv, inv_inv, slT_coe, Matrix.transpose_transpose]

theorem actUg_blk (K : SL(2, F)) (v : Fin 2 → F) :
    actUg (CFSG.Quasithin.SL3Model.blk K) v =
      ((K⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ v := by
  rw [← Umat_mulVec, Umat_blk]

theorem U_nat {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) :
    ModStep (actU ρ) ⊥ ⊤ ∧ ModNatural F (actU ρ) ⊥ ⊤ := by
  have hlt : (⊥ : AddSubgroup (Fin 2 → F)) < ⊤ := by
    refine lt_of_le_of_ne bot_le fun h => ?_
    have hmem : (Pi.single 0 1 : Fin 2 → F) ∈ (⊤ : AddSubgroup (Fin 2 → F)) :=
      AddSubgroup.mem_top _
    rw [← h, AddSubgroup.mem_bot] at hmem
    have := congrFun hmem 0
    simp at this
  have hinv1 : AInv (actU ρ) (⊥ : AddSubgroup (Fin 2 → F)) := by
    intro x e he
    rw [AddSubgroup.mem_bot] at he ⊢
    rw [he, map_zero]
  have hsimple : ∀ M : AddSubgroup (Fin 2 → F), ⊥ ≤ M → M ≤ ⊤ → AInv (actU ρ) M →
      M = ⊥ ∨ M = ⊤ := by
    intro M _ _ hM
    by_cases hbot : M = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨v, hvM, hv0⟩ : ∃ v ∈ M, v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hbot (eq_bot_iff.2 ?_)
      intro v hv
      exact AddSubgroup.mem_bot.2 (hcon v hv)
    refine eq_top_iff.2 ?_
    intro w _
    by_cases hw : w = 0
    · rw [hw]
      exact M.zero_mem
    obtain ⟨N, hN, hNw⟩ := exists_blk_transitive hv0 hw
    have hdual : Function.Surjective (dualHom F 2 : SL(2, F) →* SL(2, F)) :=
      fun K => ⟨dualHom F 2 K, dualHom_dualHom K⟩
    have hcomm : (commutator SL(2, F)).map (dualHom F 2) = commutator SL(2, F) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.2 hdual, commutator_def]
    have hN' : dualHom F 2 N ∈ commutator SL(2, F) := by
      rw [← hcomm]
      exact Subgroup.mem_map_of_mem _ hN
    obtain ⟨x, hx⟩ := hρ.blk _ hN'
    have hact : actU ρ x v = w := by
      show actUg (ρ x) v = w
      rw [hx, actUg_blk, dualHom_inv_coe, hNw]
    rw [← hact]
    exact hM x v hvM
  have hinv2 : AInv (actU ρ) (⊤ : AddSubgroup (Fin 2 → F)) := by
    intro _ _ _
    exact AddSubgroup.mem_top _
  refine ⟨⟨hlt, hinv1, hinv2, hsimple⟩, ?_⟩
  refine ⟨AddMonoidHom.id (Fin 2 → F), betaU ρ hρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact ⟨w, AddSubgroup.mem_top _, rfl⟩
  · intro e _
    simp
  · intro x e _
    rw [betaU_coe]
    exact (Umat_mulVec (ρ x) e).symm
  · intro _ hβ
    obtain ⟨x, hx⟩ := hρ.blk (c3 F) CFSG.Quasithin.SL3Model.c3_mem_commutator
    have h1 : betaU ρ hρ x = 1 := by
      rw [hβ, MonoidHom.one_apply]
    have h2 : ((betaU ρ hρ x : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [h1, Units.val_one]
    rw [betaU_coe, hx, Umat_blk] at h2
    have h4 : ((c3 F)⁻¹ : SL(2, F)).1 = 1 := by
      have := congrArg Matrix.transpose h2
      rwa [Matrix.transpose_transpose, Matrix.transpose_one] at this
    apply CFSG.Quasithin.SL2Model.c3_ne_one (F := F)
    rw [← inv_eq_one]
    apply Subtype.ext
    rw [h4, Matrix.SpecialLinearGroup.coe_one]
  · intro hF M
    have hM' : dualHom F 2 M ∈ commutator SL(2, F) := by
      rw [commutator_eq_top_of_two_lt hF]
      exact Subgroup.mem_top _
    obtain ⟨x, hx⟩ := hρ.blk _ hM'
    refine ⟨x, ?_⟩
    rw [betaU_coe, hx, Umat_blk, dualHom_inv_coe]

end U

end CFSG.Quasithin.RonanG25
