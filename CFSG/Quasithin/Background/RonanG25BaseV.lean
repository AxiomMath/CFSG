module

public import CFSG.Quasithin.Background.RonanG25BaseCore
public import CFSG.Quasithin.Background.RonanG25Mod

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model
open scoped MatrixGroups Matrix

section V

variable {F : Type} [Field F] [Finite F] [CharP F 2] {Γ : Type} [Group Γ]

theorem actV_apply {ρ : Γ →* SL(3, F)} (x : Γ) (e : Fin 3 → F) :
    actV ρ x e = (ρ x : Matrix (Fin 3) (Fin 3) F) *ᵥ e := rfl

theorem actV_eq_smul {ρ : Γ →* SL(3, F)} (x : Γ) (e : Fin 3 → F) :
    actV ρ x e = ρ x • e := rfl

theorem actV_smul {ρ : Γ →* SL(3, F)} (x : Γ) (c : F) (e : Fin 3 → F) :
    actV ρ x (c • e) = c • actV ρ x e := by
  rw [actV_apply, actV_apply, Matrix.mulVec_smul]

theorem vE_zero_ne : vE F 0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

theorem mem_lineSub {e : Fin 3 → F} : e ∈ lineSub F ↔ ∃ c : F, c • vE F 0 = e := by
  unfold lineSub
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]

theorem mem_lineSub_coords {e : Fin 3 → F} : e ∈ lineSub F ↔ e 1 = 0 ∧ e 2 = 0 := by
  constructor
  · intro he
    obtain ⟨c, rfl⟩ := mem_lineSub.1 he
    simp [vE]
  · rintro ⟨h1, h2⟩
    rw [mem_lineSub]
    refine ⟨e 0, ?_⟩
    ext i
    fin_cases i <;> simp [vE, h1, h2]

theorem lineSub_inv {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) : AInv (actV ρ) (lineSub F) := by
  intro x e he
  obtain ⟨c, rfl⟩ := mem_lineSub.1 he
  obtain ⟨c', hc'⟩ := mem_Pt.1 (hρ.stab x)
  refine mem_lineSub.2 ⟨c * c', ?_⟩
  rw [actV_smul, actV_eq_smul, hc', smul_smul]

theorem bot_inv {ρ : Γ →* SL(3, F)} : AInv (actV ρ) (⊥ : AddSubgroup (Fin 3 → F)) := by
  intro x e he
  rw [AddSubgroup.mem_bot.1 he, map_zero]
  exact AddSubgroup.zero_mem _

theorem top_inv {ρ : Γ →* SL(3, F)} : AInv (actV ρ) (⊤ : AddSubgroup (Fin 3 → F)) :=
  fun _ _ _ => AddSubgroup.mem_top _

theorem scalar_ne_zero_of_stab {ρ : Γ →* SL(3, F)} (x : Γ) {c' : F}
    (hc' : ρ x • vE F 0 = c' • vE F 0) : c' ≠ 0 := by
  rintro rfl
  apply vE_zero_ne (F := F)
  calc vE F 0 = (ρ x)⁻¹ • ρ x • vE F 0 := (inv_smul_smul _ _).symm
    _ = (ρ x)⁻¹ • (0 : F) • vE F 0 := by rw [hc']
    _ = 0 := by rw [zero_smul, smul_zero]

theorem bot_lt_lineSub : (⊥ : AddSubgroup (Fin 3 → F)) < lineSub F := by
  refine lt_of_le_of_ne bot_le fun h => ?_
  have h0 : vE F 0 ∈ (⊥ : AddSubgroup (Fin 3 → F)) := by
    rw [h]
    exact mem_lineSub.2 ⟨1, one_smul _ _⟩
  exact vE_zero_ne (AddSubgroup.mem_bot.1 h0)

theorem lineSub_lt_top : lineSub F < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => ?_
  have h1 : vE F 1 ∈ lineSub F := by
    rw [h]
    exact AddSubgroup.mem_top _
  obtain ⟨c, hc⟩ := mem_lineSub.1 h1
  have h2 := congrFun hc 1
  simp [vE] at h2

theorem card_lineSub : Nat.card (lineSub F) = Nat.card F := by
  let f : F → lineSub F := fun c => ⟨c • vE F 0, mem_lineSub.2 ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun e => ?_⟩
    · have h' := congrArg (fun v : lineSub F => (v : Fin 3 → F) 0) h
      simpa [f, vE] using h'
    · obtain ⟨c, hc⟩ := mem_lineSub.1 e.2
      exact ⟨c, Subtype.ext hc⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem line_simple {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) (M : AddSubgroup (Fin 3 → F))
    (h2 : M ≤ lineSub F) (hM : AInv (actV ρ) M) : M = ⊥ ∨ M = lineSub F := by
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨m, hmM, hm0⟩ : ∃ m ∈ M, m ≠ 0 := by
    by_contra hcon
    apply hbot
    refine eq_bot_iff.2 fun m hm => AddSubgroup.mem_bot.2 ?_
    exact Classical.byContradiction fun h => hcon ⟨m, hm, h⟩
  obtain ⟨c₀, hc₀m⟩ := mem_lineSub.1 (h2 hmM)
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hm0
    rw [← hc₀m, zero_smul]
  refine le_antisymm h2 fun e he => ?_
  obtain ⟨c, rfl⟩ := mem_lineSub.1 he
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact M.zero_mem
  obtain ⟨x, hx⟩ := hρ.torus (c / c₀) (div_ne_zero hc hc₀)
  have h3 : actV ρ x m ∈ M := hM x m hmM
  have hcc : c₀ * (c / c₀) = c := by field_simp
  rw [← hc₀m, actV_smul, actV_eq_smul, hx, smul_smul, hcc] at h3
  exact h3

theorem blk_mulVec_one (N : SL(2, F)) (e : Fin 3 → F) :
    ((CFSG.Quasithin.SL3Model.blk N : Matrix (Fin 3) (Fin 3) F) *ᵥ e) 1 =
      (N.1 *ᵥ ![e 1, e 2]) 0 := by
  simp [CFSG.Quasithin.SL3Model.blk_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_two]

theorem blk_mulVec_two (N : SL(2, F)) (e : Fin 3 → F) :
    ((CFSG.Quasithin.SL3Model.blk N : Matrix (Fin 3) (Fin 3) F) *ᵥ e) 2 =
      (N.1 *ᵥ ![e 1, e 2]) 1 := by
  simp [CFSG.Quasithin.SL3Model.blk_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_two]

theorem quot_simple {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) (M : AddSubgroup (Fin 3 → F))
    (h1 : lineSub F ≤ M) (hM : AInv (actV ρ) M) : M = lineSub F ∨ M = ⊤ := by
  by_cases hML : M ≤ lineSub F
  · exact Or.inl (le_antisymm hML h1)
  right
  obtain ⟨e, heM, heL⟩ : ∃ e ∈ M, e ∉ lineSub F := by
    by_contra hcon
    apply hML
    intro e he
    exact Classical.byContradiction fun h => hcon ⟨e, he, h⟩
  have hv : (![e 1, e 2] : Fin 2 → F) ≠ 0 := by
    intro h
    apply heL
    rw [mem_lineSub_coords]
    constructor
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  have key : ∀ w : Fin 3 → F, ∃ m ∈ M, m 1 = w 1 ∧ m 2 = w 2 := by
    intro w
    by_cases hu : (![w 1, w 2] : Fin 2 → F) = 0
    · refine ⟨0, M.zero_mem, ?_, ?_⟩
      · simpa using (congrFun hu 0).symm
      · simpa using (congrFun hu 1).symm
    · obtain ⟨N, hN, hNv⟩ := exists_blk_transitive hv hu
      obtain ⟨x, hx⟩ := hρ.blk N hN
      refine ⟨actV ρ x e, hM x e heM, ?_, ?_⟩
      · rw [actV_apply, hx, blk_mulVec_one, hNv]
        simp
      · rw [actV_apply, hx, blk_mulVec_two, hNv]
        simp
  apply eq_top_iff.2
  intro w _
  obtain ⟨m, hmM, hm1, hm2⟩ := key w
  have hdiff : w - m ∈ lineSub F := by
    rw [mem_lineSub_coords]
    constructor
    · simp [hm1]
    · simp [hm2]
  have hsum := M.add_mem hmM (h1 hdiff)
  simpa using hsum

@[expose] def planeCoord (F : Type) [Field F] : (Fin 3 → F) →+ (Fin 2 → F) where
  toFun e := ![e 1, e 2]
  map_zero' := by
    ext i
    fin_cases i <;> simp
  map_add' a b := by
    ext i
    fin_cases i <;> simp

theorem planeCoord_apply (e : Fin 3 → F) : planeCoord F e = ![e 1, e 2] := rfl

@[expose] noncomputable def betaV (ρ : Γ →* SL(3, F)) (hρ : L1Rep ρ) :
    Γ →* Matrix.GeneralLinearGroup (Fin 2) F :=
  ablkHom.comp (ρ.codRestrict (Pt (vE F 0)) hρ.stab)

theorem betaV_coe {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) (x : Γ) :
    ((betaV ρ hρ x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ablk (ρ x) :=
  ablkHom_coe ⟨ρ x, hρ.stab x⟩

theorem V_line {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) :
    ModStep (actV ρ) ⊥ (lineSub F) ∧ (Nat.card F = 2 → ModCentral (actV ρ) ⊥ (lineSub F)) ∧
      (2 < Nat.card F → ModAdditional F (actV ρ) ⊥ (lineSub F)) := by
  refine ⟨⟨bot_lt_lineSub, bot_inv, lineSub_inv hρ, fun M _ h2 hM => line_simple hρ M h2 hM⟩,
    fun h2 => ?_, fun h2 => ?_⟩
  · unfold ModCentral
    refine ⟨fun x e he => ?_, 2, Nat.prime_two, ?_⟩
    · obtain ⟨c, rfl⟩ := mem_lineSub.1 he
      obtain ⟨c', hc'⟩ := mem_Pt.1 (hρ.stab x)
      have hc'1 : c' = 1 :=
        (eq_zero_or_one_of_card_two h2 c').resolve_left (scalar_ne_zero_of_stab x hc')
      rw [actV_smul, actV_eq_smul, hc', hc'1, one_smul, sub_self]
      exact AddSubgroup.zero_mem _
    · rw [card_lineSub, h2, AddSubgroup.card_bot, mul_one]
  · unfold ModAdditional
    refine ⟨by rw [card_lineSub, AddSubgroup.card_bot, mul_one], ?_⟩
    obtain ⟨a, ha0, ha2⟩ : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 :=
      (card_two_or_exists_sq_ne_one (F := F)).resolve_left (by omega)
    have ha1 : a ≠ 1 := fun h => ha2 (by rw [h, one_pow])
    obtain ⟨x, hx⟩ := hρ.torus a ha0
    refine ⟨x, vE F 0, mem_lineSub.2 ⟨1, one_smul _ _⟩, ?_⟩
    rw [AddSubgroup.mem_bot, actV_eq_smul, hx]
    intro h
    have h' : (a - 1) • vE F 0 = 0 := by
      rw [sub_smul, one_smul]
      exact h
    rcases smul_eq_zero.1 h' with h'' | h''
    · exact ha1 (sub_eq_zero.1 h'')
    · exact vE_zero_ne h''

theorem V_quot {ρ : Γ →* SL(3, F)} (hρ : L1Rep ρ) :
    ModStep (actV ρ) (lineSub F) ⊤ ∧ ModNatural F (actV ρ) (lineSub F) ⊤ := by
  refine ⟨⟨lineSub_lt_top, lineSub_inv hρ, top_inv, fun M h1 _ hM => quot_simple hρ M h1 hM⟩, ?_⟩
  unfold ModNatural
  refine ⟨planeCoord F, betaV ρ hρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    refine ⟨![0, w 0, w 1], AddSubgroup.mem_top _, ?_⟩
    ext i
    fin_cases i <;> simp [planeCoord_apply]
  · intro e _
    rw [planeCoord_apply, mem_lineSub_coords]
    constructor
    · intro h
      exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩
      ext i
      fin_cases i <;> simp [h1, h2]
  · intro x e _
    rw [planeCoord_apply, planeCoord_apply, betaV_coe hρ x, actV_apply]
    obtain ⟨h10, h20⟩ := Pt_entries (hρ.stab x)
    ext i
    fin_cases i <;>
      simp [ablk, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, h10, h20]
  · intro h2 hβ
    obtain ⟨x, hx⟩ := hρ.blk (CFSG.Quasithin.SL2Model.c3 F)
      CFSG.Quasithin.SL3Model.c3_mem_commutator
    apply CFSG.Quasithin.SL2Model.c3_ne_one (F := F)
    apply Subtype.ext
    have h1 : ((betaV ρ hρ x : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [hβ, MonoidHom.one_apply, Units.val_one]
    have h3 : ((betaV ρ hρ x : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = (CFSG.Quasithin.SL2Model.c3 F).1 := by
      rw [betaV_coe hρ x, hx, ablk_blk]
    exact h3.symm.trans (h1.trans rfl)
  · intro h2 M
    have hM : M ∈ commutator SL(2, F) := by
      rw [commutator_eq_top_of_two_lt h2]
      exact Subgroup.mem_top M
    obtain ⟨x, hx⟩ := hρ.blk M hM
    exact ⟨x, by rw [betaV_coe hρ x, hx, ablk_blk]⟩

end V

end CFSG.Quasithin.RonanG25
