module

public import CFSG.Quasithin.Background.RonanG25BaseCore
public import CFSG.Quasithin.Background.RonanG25Mod

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model
open scoped MatrixGroups Matrix

section Vd

variable {F : Type} [Field F] [Finite F] [CharP F 2] {Γ : Type} [Group Γ]

theorem actVd_apply (ρ : Γ →* SL(3, F)) (x : Γ) (f : Fin 3 → F) :
    actVd ρ x f = (dualHom F 3 (ρ x) : Matrix (Fin 3) (Fin 3) F) *ᵥ f := rfl

theorem actVd_zero_coord {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) (x : Γ) (f : Fin 3 → F) :
    actVd ρ x f 0 = (dualHom F 3 (ρ x)).1 0 0 * f 0 := by
  obtain ⟨-, h01, h02, -⟩ := dual_entries (hρ.stab x)
  rw [actVd_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01, h02]

theorem entry00_of_smul {A : SL(3, F)} {c : F} (h : A • vE F 0 = c • vE F 0) :
    A.1 0 0 = c := by
  have h0 := congrFun h 0
  rw [smul_single_one] at h0
  simpa [vE] using h0

theorem dual_entry00_of_smul {g : SL(3, F)} (hg : g ∈ Pt (vE F 0)) {c : F}
    (h : g • vE F 0 = c • vE F 0) : (dualHom F 3 g).1 0 0 = c⁻¹ := by
  have hm := (dual_entries hg).2.2.2
  rw [entry00_of_smul h] at hm
  exact eq_inv_of_mul_eq_one_left hm

@[expose] def annCoord : (Fin 3 → F) →+ (Fin 2 → F) :=
  AddMonoidHom.mk' (fun f => ![f 1, f 2]) fun a b => by
    funext i
    fin_cases i <;> simp

theorem annCoord_apply (f : Fin 3 → F) : annCoord f = ![f 1, f 2] := rfl

theorem annCoord_eq_zero_iff {f : Fin 3 → F} (hf : f 0 = 0) : annCoord f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h1 : f 1 = 0 := by simpa [annCoord_apply] using congrFun h 0
    have h2 : f 2 = 0 := by simpa [annCoord_apply] using congrFun h 1
    funext i
    fin_cases i <;> simp [hf, h1, h2]
  · rintro rfl
    funext i
    fin_cases i <;> simp [annCoord_apply]

@[expose] noncomputable def vdPtHom (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) :
    Γ →* ↥(Pt (vE F 0)) where
  toFun x := ⟨ρ x, hρ.stab x⟩
  map_one' := Subtype.ext (map_one ρ)
  map_mul' x y := Subtype.ext (map_mul ρ x y)

@[expose] noncomputable def vdBeta (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) :
    Γ →* Matrix.GeneralLinearGroup (Fin 2) F :=
  glDual.comp (ablkHom.comp (vdPtHom ρ hρ))

theorem vdBeta_coe (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) (x : Γ) :
    ((vdBeta ρ hρ x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ablk (dualHom F 3 (ρ x)) := by
  have h := (dual_entries (hρ.stab x)).1
  change ((glDual (ablkHom ⟨ρ x, hρ.stab x⟩) : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = _
  rw [glDual_coe]
  exact h.symm

theorem annCoord_act {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) (x : Γ) {f : Fin 3 → F} (hf : f 0 = 0) :
    annCoord (actVd ρ x f) = (vdBeta ρ hρ x : Matrix (Fin 2) (Fin 2) F) *ᵥ annCoord f := by
  rw [vdBeta_coe]
  funext i
  fin_cases i <;>
    simp [annCoord_apply, actVd_apply, ablk, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two, hf]

theorem ablk_dualHom_blk (N : SL(2, F)) :
    ablk (dualHom F 3 (CFSG.Quasithin.SL3Model.blk N)) =
      ((N⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  rw [dualHom_apply, ← map_inv CFSG.Quasithin.SL3Model.blk N]
  generalize (N⁻¹ : SL(2, F)) = P
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ablk, slT_coe, blk_coe]

theorem dualHom_two_inv_transpose (M : SL(2, F)) :
    (((dualHom F 2 M)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ =
      (M : Matrix (Fin 2) (Fin 2) F) := by
  rw [dualHom_apply, ← slT_inv, inv_inv, slT_coe, Matrix.transpose_transpose]

theorem invT_mulVec (M : SL(2, F)) (v : Fin 2 → F) :
    ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ v =
      ![(M : Matrix (Fin 2) (Fin 2) F) 1 1 * v 0 + (M : Matrix (Fin 2) (Fin 2) F) 1 0 * v 1,
        (M : Matrix (Fin 2) (Fin 2) F) 0 1 * v 0 + (M : Matrix (Fin 2) (Fin 2) F) 0 0 * v 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, CharTwo.neg_eq]

theorem exists_vdBeta_transitive (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) {v w : Fin 2 → F}
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x : Γ, (vdBeta ρ hρ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v = w := by
  have hsw : ∀ u : Fin 2 → F, u ≠ 0 → (![u 1, u 0] : Fin 2 → F) ≠ 0 := by
    intro u hu h
    apply hu
    have h1 : u 1 = 0 := by simpa using congrFun h 0
    have h0 : u 0 = 0 := by simpa using congrFun h 1
    funext i
    fin_cases i <;> simp [h0, h1]
  obtain ⟨M, hM, hMv⟩ := exists_blk_transitive (hsw v hv) (hsw w hw)
  obtain ⟨x, hx⟩ := hρ.blk M hM
  refine ⟨x, ?_⟩
  rw [vdBeta_coe, hx, ablk_dualHom_blk, invT_mulVec]
  have h0 := congrFun hMv 0
  have h1 := congrFun hMv 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i
  · simp
    linear_combination h1
  · simp
    linear_combination h0

theorem vd_card_annSub : Nat.card (annSub F) = Nat.card F ^ 2 := by
  have hb : Function.Bijective (fun f : annSub F => annCoord (f : Fin 3 → F)) := by
    refine ⟨fun f g h => ?_, fun w => ?_⟩
    · apply Subtype.ext
      have hf : f.1 0 = 0 := f.2
      have hg : g.1 0 = 0 := g.2
      have h1 : f.1 1 = g.1 1 := by simpa [annCoord_apply] using congrFun h 0
      have h2 : f.1 2 = g.1 2 := by simpa [annCoord_apply] using congrFun h 1
      funext i
      fin_cases i <;> simp [hf, hg, h1, h2]
    · refine ⟨⟨![0, w 0, w 1], show (![0, w 0, w 1] : Fin 3 → F) 0 = 0 from rfl⟩, ?_⟩
      funext i
      fin_cases i <;> simp [annCoord_apply]
  rw [Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_fun]
  simp

theorem vd_card_top : Nat.card (⊤ : AddSubgroup (Fin 3 → F)) = Nat.card F ^ 3 := by
  rw [AddSubgroup.card_top, Nat.card_fun]
  simp

theorem vd_card_top_eq :
    Nat.card (⊤ : AddSubgroup (Fin 3 → F)) = Nat.card F * Nat.card (annSub F) := by
  rw [vd_card_top, vd_card_annSub]
  ring

theorem Vd_ann {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) :
    ModStep (actVd ρ) ⊥ (annSub F) ∧ ModNatural F (actVd ρ) ⊥ (annSub F) := by
  have hbot : AInv (actVd ρ) (⊥ : AddSubgroup (Fin 3 → F)) := fun x e he => by
    rw [AddSubgroup.mem_bot] at he ⊢
    rw [he, map_zero]
  have hann : AInv (actVd ρ) (annSub F) := fun x f hf => by
    show actVd ρ x f 0 = 0
    rw [actVd_zero_coord hρ x f, show f 0 = 0 from hf, mul_zero]
  have hlt : (⊥ : AddSubgroup (Fin 3 → F)) < annSub F := by
    refine lt_of_le_of_ne bot_le fun h => ?_
    have h1 : vE F 1 ∈ annSub F := by
      show (vE F 1) 0 = 0
      simp [vE, Pi.single_apply]
    rw [← h, AddSubgroup.mem_bot] at h1
    have h2 := congrFun h1 1
    simp [vE, Pi.single_apply] at h2
  refine ⟨⟨hlt, hbot, hann, fun M hM1 hM2 hMi => ?_⟩, ?_⟩
  ·
    by_cases hMb : M = ⊥
    · exact Or.inl hMb
    right
    refine le_antisymm hM2 ?_
    obtain ⟨f, hfM, hf0⟩ : ∃ f ∈ M, f ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hMb (eq_bot_iff.2 fun f hf => AddSubgroup.mem_bot.2 (hc f hf))
    have hfann : f 0 = 0 := hM2 hfM
    have hv : annCoord f ≠ 0 := fun h => hf0 ((annCoord_eq_zero_iff hfann).1 h)
    intro g hg
    have hg0 : g 0 = 0 := hg
    by_cases hw : annCoord g = 0
    · rw [(annCoord_eq_zero_iff hg0).1 hw]
      exact M.zero_mem
    · obtain ⟨x, hx⟩ := exists_vdBeta_transitive ρ hρ hv hw
      have hh0 : actVd ρ x f 0 = 0 := by
        rw [actVd_zero_coord hρ x f, hfann, mul_zero]
      have hdiff : g - actVd ρ x f = 0 := by
        apply (annCoord_eq_zero_iff (f := g - actVd ρ x f) (by simp [hg0, hh0])).1
        rw [map_sub, annCoord_act hρ x hfann, hx, sub_self]
      have hgeq : g = actVd ρ x f := sub_eq_zero.1 hdiff
      rw [hgeq]
      exact hMi x f hfM
  · refine ⟨annCoord, vdBeta ρ hρ, ?_, ?_, ?_, ?_, ?_⟩
    · intro w
      refine ⟨![0, w 0, w 1], show (![0, w 0, w 1] : Fin 3 → F) 0 = 0 from rfl, ?_⟩
      funext i
      fin_cases i <;> simp [annCoord_apply]
    · intro e he
      rw [AddSubgroup.mem_bot]
      exact annCoord_eq_zero_iff (f := e) he
    · intro x e he
      exact annCoord_act hρ x (f := e) he
    · intro h2 hβ
      obtain ⟨x, hx⟩ := hρ.blk (CFSG.Quasithin.SL2Model.c3 F)
        CFSG.Quasithin.SL3Model.c3_mem_commutator
      have hβx : vdBeta ρ hρ x = 1 := by simp [hβ]
      have h1 : ablk (dualHom F 3 (ρ x)) = 1 := by
        rw [← vdBeta_coe ρ hρ x, hβx, Units.val_one]
      rw [hx, ablk_dualHom_blk] at h1
      apply CFSG.Quasithin.SL2Model.c3_ne_one (F := F)
      have h2' := congrArg Matrix.transpose h1
      rw [Matrix.transpose_transpose, Matrix.transpose_one] at h2'
      exact inv_eq_one.1 (Subtype.ext h2')
    · intro h2 M
      have hN : dualHom F 2 M ∈ commutator SL(2, F) := by
        rw [commutator_eq_top_of_two_lt h2]
        exact Subgroup.mem_top _
      obtain ⟨x, hx⟩ := hρ.blk (dualHom F 2 M) hN
      refine ⟨x, ?_⟩
      rw [vdBeta_coe ρ hρ x, hx, ablk_dualHom_blk, dualHom_two_inv_transpose]

theorem Vd_quot {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) :
    ModStep (actVd ρ) (annSub F) ⊤ ∧ (Nat.card F = 2 → ModCentral (actVd ρ) (annSub F) ⊤) ∧
      (2 < Nat.card F → ModAdditional F (actVd ρ) (annSub F) ⊤) := by
  have hann : AInv (actVd ρ) (annSub F) := fun x f hf => by
    show actVd ρ x f 0 = 0
    rw [actVd_zero_coord hρ x f, show f 0 = 0 from hf, mul_zero]
  have hlt : annSub F < (⊤ : AddSubgroup (Fin 3 → F)) := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have h0 : vE F 0 ∈ annSub F := by
      rw [h]
      exact AddSubgroup.mem_top _
    have h00 : (vE F 0) 0 = 0 := h0
    simp [vE] at h00
  have htop : AInv (actVd ρ) (⊤ : AddSubgroup (Fin 3 → F)) :=
    fun _ _ _ => AddSubgroup.mem_top _
  refine ⟨⟨hlt, hann, htop, fun M hM1 hM2 hMi => ?_⟩, fun h2 => ?_, fun h2 => ?_⟩
  ·
    by_cases hMA : M = annSub F
    · exact Or.inl hMA
    right
    have hex : ∃ f ∈ M, f 0 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hMA (le_antisymm (fun f hf => hc f hf) hM1)
    obtain ⟨f, hfM, hf0⟩ := hex
    have hsurj : ∀ t : F, ∃ h ∈ M, h 0 = t := by
      intro t
      by_cases ht : t = 0
      · exact ⟨0, M.zero_mem, by simp [ht]⟩
      · obtain ⟨x, hx⟩ := hρ.torus (f 0 * t⁻¹) (mul_ne_zero hf0 (inv_ne_zero ht))
        refine ⟨actVd ρ x f, hMi x f hfM, ?_⟩
        rw [actVd_zero_coord hρ x f, dual_entry00_of_smul (hρ.stab x) hx]
        field_simp
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨h, hhM, hh0⟩ := hsurj (g 0)
    have hgh : g - h ∈ M := hM1 (show g - h ∈ annSub F from by
      show (g - h) 0 = 0
      simp [hh0])
    have := M.add_mem hgh hhM
    rwa [sub_add_cancel] at this
  ·
    refine ⟨fun x e _ => ?_, Nat.card F, ?_, vd_card_top_eq⟩
    · have hD1 : (dualHom F 3 (ρ x)).1 0 0 = 1 :=
        (eq_zero_or_one_of_card_two h2 ((dualHom F 3 (ρ x)).1 0 0)).resolve_left fun h0 => by
          have hm := (dual_entries (hρ.stab x)).2.2.2
          rw [h0, zero_mul] at hm
          exact zero_ne_one hm
      show (actVd ρ x e - e) 0 = 0
      rw [Pi.sub_apply, actVd_zero_coord hρ x e, hD1, one_mul, sub_self]
    · rw [h2]
      exact Nat.prime_two
  ·
    obtain ⟨a, ha0, ha1⟩ := (card_two_or_exists_sq_ne_one (F := F)).resolve_left (by omega)
    obtain ⟨x, hx⟩ := hρ.torus a ha0
    have hD := dual_entry00_of_smul (hρ.stab x) hx
    refine ⟨vd_card_top_eq, x, vE F 0, AddSubgroup.mem_top _, fun hmem => ?_⟩
    have h0 : (actVd ρ x (vE F 0) - vE F 0) 0 = 0 := hmem
    rw [Pi.sub_apply, actVd_zero_coord hρ x (vE F 0), hD] at h0
    have e1 : (vE F 0) 0 = 1 := by simp [vE]
    rw [e1, mul_one, sub_eq_zero] at h0
    exact ha1 (by rw [inv_eq_one.1 h0, one_pow])

end Vd

end CFSG.Quasithin.RonanG25
