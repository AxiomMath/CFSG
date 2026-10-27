module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups Matrix

section FixDef

variable {F : Type*} [Field F] {V : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(2, F) V)

@[expose] def sl2Fix (S : Set SL(2, F)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ g ∈ S, ρ g v = v}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg]

theorem mem_sl2Fix {S : Set SL(2, F)} {v : V} : v ∈ sl2Fix ρ S ↔ ∀ g ∈ S, ρ g v = v :=
  Iff.rfl

@[expose] def sl2OddFix : Submodule (ZMod 2) V := sl2Fix ρ {g | Odd (orderOf g)}

theorem mem_sl2OddFix {v : V} :
    v ∈ sl2OddFix ρ ↔ ∀ g : SL(2, F), Odd (orderOf g) → ρ g v = v :=
  Iff.rfl

end FixDef

section Fix

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(2, F) V)

theorem apply_mem_sl2OddFix (h : SL(2, F)) {v : V} (hv : v ∈ sl2OddFix ρ) :
    ρ h v ∈ sl2OddFix ρ := by
  intro g hg
  have hodd : Odd (orderOf (h⁻¹ * g * h)) := by
    have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) g
    rw [MulAut.conj_apply, inv_inv] at this
    rwa [this]
  have e : g * h = h * (h⁻¹ * g * h) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv _ hodd]

theorem eq_of_odd_of_fix_sub {g : SL(2, F)} (hg : Odd (orderOf g)) {v : V}
    (hw : ρ g (ρ g v - v) = ρ g v - v) : ρ g v = v := by
  set w := ρ g v - v with hwdef
  have hv : ρ g v = v + w := by rw [hwdef]; abel
  have hpow : ∀ k : ℕ, ρ (g ^ k) v = v + k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_add, map_nsmul, hw, hv, succ_nsmul]
      abel
  have h2 : ∀ j : ℕ, (2 * j) • w = 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, add_nsmul, ih, zero_add, two_nsmul, add_self_eq_zero_of_charTwo (ZMod 2)]
  obtain ⟨j, hj⟩ := hg
  have h := hpow (orderOf g)
  rw [pow_orderOf_eq_one, map_one, Module.End.one_apply, hj, succ_nsmul, h2, zero_add] at h
  have hw0 : w = 0 := by
    have := congrArg (fun u => u - v) h
    simpa using this.symm
  rw [hv, hw0, add_zero]

theorem sl2Fix_conj_le_map (x : SL(2, F)) (S : Set SL(2, F)) :
    sl2Fix ρ ((fun g => x * g * x⁻¹) '' S) ≤ (sl2Fix ρ S).map (ρ x) := by
  intro v hv
  refine ⟨ρ x⁻¹ v, fun g hg => ?_, ?_⟩
  · have h1 := hv (x * g * x⁻¹) ⟨g, hg, rfl⟩
    have e : g * x⁻¹ = x⁻¹ * (x * g * x⁻¹) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h1]
  · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem finrank_sl2Fix_conj [Module.Finite (ZMod 2) V] (x : SL(2, F)) (S : Set SL(2, F)) :
    Module.finrank (ZMod 2) (sl2Fix ρ ((fun g => x * g * x⁻¹) '' S)) =
      Module.finrank (ZMod 2) (sl2Fix ρ S) := by
  have key : ∀ (y : SL(2, F)) (T : Set SL(2, F)),
      Module.finrank (ZMod 2) (sl2Fix ρ ((fun g => y * g * y⁻¹) '' T)) ≤
        Module.finrank (ZMod 2) (sl2Fix ρ T) := fun y T =>
    (Submodule.finrank_mono (sl2Fix_conj_le_map ρ y T)).trans (Submodule.finrank_map_le _ _)
  refine le_antisymm (key x S) ?_
  have hS : (fun g => x⁻¹ * g * x⁻¹⁻¹) '' ((fun g => x * g * x⁻¹) '' S) = S := by
    rw [Set.image_image]
    have : (fun g => x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹) = id := funext fun g => by
      simp only [id_eq]; group
    rw [this, Set.image_id]
  calc Module.finrank (ZMod 2) (sl2Fix ρ S) = Module.finrank (ZMod 2) (sl2Fix ρ
        ((fun g => x⁻¹ * g * x⁻¹⁻¹) '' ((fun g => x * g * x⁻¹) '' S))) := by rw [hS]
    _ ≤ _ := key x⁻¹ _

end Fix

section Gen

variable {F : Type*} [Field F]

theorem sl2_eq_uElt_lElt_uElt (m : SL(2, F)) (hc : (m : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    m = uElt (((m : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (m : Matrix (Fin 2) (Fin 2) F) 1 0) *
      lElt ((m : Matrix (Fin 2) (Fin 2) F) 1 0) *
      uElt (((m : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (m : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [uElt, lElt, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : F) * hdet

theorem lElt_neg_one_mul_lElt_one : lElt (-1 : F) * lElt 1 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [lElt, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def weylNegSL2 : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem lElt_eq_conj (t : F) : lElt t = weylNegSL2 * uElt (-t) * weylNegSL2⁻¹ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [weylNegSL2, uElt, lElt, Matrix.mul_apply, Fin.sum_univ_two]

theorem range_lElt_eq : Set.range (lElt (F := F)) =
    (fun g => weylNegSL2 * g * weylNegSL2⁻¹) '' Set.range (uElt (F := F)) := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨uElt (-t), ⟨-t, rfl⟩, (lElt_eq_conj t).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨-t, by rw [lElt_eq_conj, neg_neg]⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) SL(2, F) V)

theorem fix_of_fix_uElt_lElt {v : V} (hu : ∀ t : F, ρ (uElt t) v = v)
    (hl : ∀ t : F, ρ (lElt t) v = v) (g : SL(2, F)) : ρ g v = v := by
  have key : ∀ m : SL(2, F), (m : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → ρ m v = v := by
    intro m hm
    rw [sl2_eq_uElt_lElt_uElt m hm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hu, hl, hu]
  by_cases hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      have hdet := g.2
      rw [Matrix.det_fin_two, h0, hg] at hdet
      simp at hdet
    have hm : ((lElt 1 * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simpa [lElt, Matrix.mul_apply, Fin.sum_univ_two, hg] using h00
    have e : g = lElt (-1) * (lElt 1 * g) := by
      rw [← mul_assoc, lElt_neg_one_mul_lElt_one, one_mul]
    rw [e, map_mul, Module.End.mul_apply, key _ hm, hl]
  · exact key g hg

end Gen

section Main

private theorem natCard_eq_two_pow {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

variable {F : Type*} [Field F] [Fintype F]

theorem exists_eq_conj_uElt [CharP F 2] (X : Subgroup SL(2, F)) (hX : IsPGroup 2 X)
    (hXc : Nat.card X = Nat.card F) :
    ∃ x : SL(2, F), ∀ g, g ∈ X ↔ ∃ t : F, g = x * uElt t * x⁻¹ := by
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent X hX
  have hmapeq : X.map (MulAut.conj x⁻¹).toMonoidHom = (upperUnipotent (F := F)).range := by
    apply Subgroup.eq_of_le_of_card_ge hx
    rw [upperUnipotent_card, ← hXc]
    exact (Nat.card_congr (X.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv).le
  refine ⟨x, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · have hmem : (MulAut.conj x⁻¹).toMonoidHom g ∈ (upperUnipotent (F := F)).range :=
      hmapeq ▸ ⟨g, hg, rfl⟩
    obtain ⟨t, ht⟩ := (mem_rootGroup_iff _).mp hmem
    refine ⟨t, ?_⟩
    rw [← ht, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨t, rfl⟩
    have hmem : uElt t ∈ (upperUnipotent (F := F)).range := (mem_rootGroup_iff _).mpr ⟨t, rfl⟩
    rw [← hmapeq] at hmem
    obtain ⟨h, hh, hht⟩ := hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hht
    have : h = x * uElt t * x⁻¹ := by rw [← hht]; group
    rwa [← this]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) SL(2, F) V)

theorem natural_of_sl2Fix {n : ℕ} (hF : Fintype.card F = 2 ^ n) (X : Subgroup SL(2, F))
    (hX : IsPGroup 2 X) (hXc : Nat.card X = Nat.card F)
    (hoff : Nat.card V ≤ Nat.card F * Nat.card (sl2Fix ρ (X : Set SL(2, F)))) :
    sl2OddFix ρ = ⊤ ∨ ∃ φ : V →+ (Fin 2 → F), Function.Surjective φ ∧
      (∀ g v, φ (ρ g v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v) ∧
      ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ := by
  classical
  have : CharP F 2 := charP_two_of_card_eq hF
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have := Fintype.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact h
  have hcardF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  set W := sl2OddFix ρ with hWdef
  by_cases hW : W = ⊤
  · exact Or.inl hW
  right
  obtain ⟨x, hxX⟩ := exists_eq_conj_uElt X hX hXc
  have hXset : (X : Set SL(2, F)) = (fun g => x * g * x⁻¹) '' Set.range (uElt (F := F)) := by
    ext g
    rw [SetLike.mem_coe, hxX]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨uElt t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  set C := sl2Fix ρ (X : Set SL(2, F)) with hCdef
  set C' := sl2Fix ρ ((fun g => x * g * x⁻¹) '' Set.range (lElt (F := F))) with hC'def
  have hCC : Module.finrank (ZMod 2) C' = Module.finrank (ZMod 2) C := by
    rw [hC'def, finrank_sl2Fix_conj, range_lElt_eq, finrank_sl2Fix_conj, hCdef, hXset,
      finrank_sl2Fix_conj]
  have hCW : C ⊓ C' ≤ W := by
    intro v hv
    have hv1 := (Submodule.mem_inf.mp hv).1
    have hv2 := (Submodule.mem_inf.mp hv).2
    have hv' : ∀ g, ρ g (ρ x⁻¹ v) = ρ x⁻¹ v := by
      refine fix_of_fix_uElt_lElt ρ (fun t => ?_) (fun t => ?_)
      · have h1 := hv1 (x * uElt t * x⁻¹) (by rw [hXset]; exact ⟨uElt t, ⟨t, rfl⟩, rfl⟩)
        have e : uElt t * x⁻¹ = x⁻¹ * (x * uElt t * x⁻¹) := by group
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h1]
      · have h1 := hv2 (x * lElt t * x⁻¹) ⟨lElt t, ⟨t, rfl⟩, rfl⟩
        have e : lElt t * x⁻¹ = x⁻¹ * (x * lElt t * x⁻¹) := by group
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h1]
    refine (mem_sl2OddFix ρ).mpr fun g _ => ?_
    have e : v = ρ x (ρ x⁻¹ v) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : g * x = x * (x⁻¹ * g * x) := by group
    rw [e, ← Module.End.mul_apply, ← map_mul, e2, map_mul, Module.End.mul_apply, hv']
  have hdimC : Module.finrank (ZMod 2) V ≤ n + Module.finrank (ZMod 2) C := by
    have h1 : Nat.card V ≤ 2 ^ (n + Module.finrank (ZMod 2) C) := by
      rw [pow_add, ← hcardF, ← natCard_eq_two_pow]
      exact hoff
    rw [natCard_eq_two_pow] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq C C'
  have hsup : Module.finrank (ZMod 2) ↥(C ⊔ C') ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  have hinfW : Module.finrank (ZMod 2) ↥(C ⊓ C') ≤ Module.finrank (ZMod 2) W :=
    Submodule.finrank_mono hCW
  have hquot := Submodule.finrank_quotient_add_finrank W
  have hdimQ : Module.finrank (ZMod 2) (V ⧸ W) ≤ 2 * n := by omega
  have hWinv : ∀ g, W ≤ W.comap (ρ g) := fun g v hv => apply_mem_sl2OddFix ρ g hv
  set σ := ρ.quotient W hWinv with hσdef
  have hσ : ∀ g v, σ g (W.mkQ v) = W.mkQ (ρ g v) := fun g v => rfl
  have hA : ∀ q : V ⧸ W, (∀ g : SL(2, F), Odd (orderOf g) → σ g q = q) → q = 0 := by
    intro q hq
    obtain ⟨v, rfl⟩ := W.mkQ_surjective q
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (mem_sl2OddFix ρ).mpr fun g hg => ?_
    have h1 := hq g hg
    rw [hσ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
    exact eq_of_odd_of_fix_sub ρ hg ((mem_sl2OddFix ρ).mp h1 g hg)
  set CQ := sl2Fix σ (X : Set SL(2, F)) with hCQdef
  have hdimCQ : Module.finrank (ZMod 2) (V ⧸ W) ≤ n + Module.finrank (ZMod 2) CQ := by
    let f : C →ₗ[ZMod 2] V ⧸ W := W.mkQ.comp C.subtype
    have hrange : LinearMap.range f ≤ CQ := by
      rintro _ ⟨c, rfl⟩ a ha
      show σ a (W.mkQ c) = W.mkQ c
      rw [hσ, c.2 a ha]
    have hker : (LinearMap.ker f).map C.subtype ≤ W := by
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hc
      simpa [f] using hc
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := Submodule.finrank_mono hrange
    have h3 := Submodule.finrank_mono hker
    rw [Submodule.finrank_map_subtype_eq] at h3
    omega
  have hQnt : Nontrivial (V ⧸ W) := by
    obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
      by_contra h
      push Not at h
      exact hW (eq_top_iff.mpr fun v _ => h v)
    exact ⟨⟨W.mkQ v, 0, by rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hv⟩⟩
  have : Finite (V ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  have hbt : (⊥ : Subrepresentation σ) ≠ ⊤ := by
    intro h
    have h' : (⊥ : Submodule (ZMod 2) (V ⧸ W)) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  have hex : ∃ d, ∃ S : Subrepresentation σ, S ≠ ⊥ ∧
      Module.finrank (ZMod 2) S.toSubmodule = d := ⟨_, ⊤, hbt.symm, rfl⟩
  obtain ⟨S, hSne, hSd⟩ := Nat.find_spec hex
  have hSmin : ∀ T : Subrepresentation σ, T ≠ ⊥ →
      Nat.find hex ≤ Module.finrank (ZMod 2) T.toSubmodule :=
    fun T hT => Nat.find_min' hex ⟨T, hT, rfl⟩
  have hSbot : S.toSubmodule ≠ ⊥ := fun h => hSne (Subrepresentation.toSubmodule_injective h)
  have hirr : S.toRepresentation.IsIrreducible := by
    have : Nontrivial (Subrepresentation S.toRepresentation) := by
      refine ⟨⊥, ⊤, fun h => ?_⟩
      have h' : (⊥ : Submodule (ZMod 2) S.toSubmodule) = ⊤ :=
        congrArg Subrepresentation.toSubmodule h
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSbot
      have hmem : (⟨s, hs⟩ : S.toSubmodule) ∈ (⊥ : Submodule (ZMod 2) S.toSubmodule) :=
        h' ▸ Submodule.mem_top
      exact hs0 (by simpa using hmem)
    refine { eq_bot_or_eq_top := fun T => ?_ }
    by_cases hT : T = ⊥
    · exact Or.inl hT
    right
    have hTbot : T.toSubmodule ≠ ⊥ := fun h => hT (Subrepresentation.toSubmodule_injective h)
    let T' : Subrepresentation σ :=
      { toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
        apply_mem_toSubmodule := by
          rintro g _ ⟨t, ht, rfl⟩
          exact ⟨S.toRepresentation g t, T.apply_mem_toSubmodule g ht, rfl⟩ }
    have hT' : T' ≠ ⊥ := by
      intro h
      obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTbot
      have hmem : (t : V ⧸ W) ∈ T'.toSubmodule := ⟨t, ht, rfl⟩
      rw [h] at hmem
      exact ht0 (Subtype.ext ((Submodule.mem_bot _).mp hmem))
    have h1 := hSmin T' hT'
    have h2 : Module.finrank (ZMod 2) T'.toSubmodule = Module.finrank (ZMod 2) T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hnt : ∃ g, S.toRepresentation g ≠ 1 := by
    by_contra h
    push Not at h
    apply hSbot
    rw [eq_bot_iff]
    intro s hs
    rw [Submodule.mem_bot]
    refine hA s fun g _ => ?_
    exact congrArg Subtype.val (LinearMap.congr_fun (h g) ⟨s, hs⟩)
  have hX2 : ∀ a ∈ X, a * a = 1 := by
    intro a ha
    obtain ⟨t, rfl⟩ := (hxX a).mp ha
    have : uElt t * uElt t = 1 := by rw [← uElt_add, CharTwo.add_self_eq_zero, uElt_zero]
    calc x * uElt t * x⁻¹ * (x * uElt t * x⁻¹) = x * (uElt t * uElt t) * x⁻¹ := by group
      _ = 1 := by rw [this, mul_one, mul_inv_cancel]
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, rfl⟩ := (hxX a).mp ha
    obtain ⟨t, rfl⟩ := (hxX b).mp hb
    have : uElt s * uElt t = uElt t * uElt s := by rw [← uElt_add, ← uElt_add, add_comm]
    calc x * uElt s * x⁻¹ * (x * uElt t * x⁻¹) = x * (uElt s * uElt t) * x⁻¹ := by group
      _ = x * (uElt t * uElt s) * x⁻¹ := by rw [this]
      _ = x * uElt t * x⁻¹ * (x * uElt s * x⁻¹) := by group
  have : CFSG.IsElementaryAbelian 2 X :=
    { is_comm := ⟨fun a b => Subtype.ext (hXcomm _ a.2 _ b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa [pow_two] using hX2 _ a.2) }
  have hX1 : X ≠ ⊥ := by
    intro h
    have h1 : Nat.card X = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hXc, hcardF] at h1
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hoffS : Nat.card S.toSubmodule ≤ Nat.card X *
      Nat.card {s : S.toSubmodule // ∀ a ∈ X, S.toRepresentation a s = s} := by
    set CS := sl2Fix S.toRepresentation (X : Set SL(2, F)) with hCSdef
    have hCSmap : CS.map S.toSubmodule.subtype = S.toSubmodule ⊓ CQ := by
      ext q
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s.2, fun a ha => congrArg Subtype.val (hs a ha)⟩
      · rintro ⟨hqS, hqC⟩
        exact ⟨⟨q, hqS⟩, fun a ha => Subtype.ext (hqC a ha), rfl⟩
    have hdimCS : Module.finrank (ZMod 2) CS =
        Module.finrank (ZMod 2) ↥(S.toSubmodule ⊓ CQ) := by
      rw [← hCSmap, Submodule.finrank_map_subtype_eq]
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq S.toSubmodule CQ
    have hsle : Module.finrank (ZMod 2) ↥(S.toSubmodule ⊔ CQ) ≤
        Module.finrank (ZMod 2) (V ⧸ W) := Submodule.finrank_le _
    have hcard1 : Nat.card {s : S.toSubmodule // ∀ a ∈ X, S.toRepresentation a s = s} =
        Nat.card CS := Nat.card_congr (Equiv.subtypeEquivRight fun s => Iff.rfl)
    rw [hcard1, hXc, hcardF, natCard_eq_two_pow, natCard_eq_two_pow, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨φS, hφS, hdimS, -⟩ := binary_SL2_internal_offender_natural_module hn hF
    S.toRepresentation hirr hnt X hX1 hoffS
  have hStop : S.toSubmodule = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hmemS : ∀ q : V ⧸ W, q ∈ S.toSubmodule := fun q => hStop ▸ Submodule.mem_top
  let φ : V →+ (Fin 2 → F) :=
    { toFun := fun v => φS ⟨W.mkQ v, hmemS _⟩
      map_zero' := by
        have : (⟨W.mkQ 0, hmemS _⟩ : S.toSubmodule) = 0 := Subtype.ext (map_zero _)
        show φS ⟨W.mkQ 0, hmemS _⟩ = 0
        rw [this, map_zero]
      map_add' := fun v v' => by
        have : (⟨W.mkQ (v + v'), hmemS _⟩ : S.toSubmodule) =
            ⟨W.mkQ v, hmemS _⟩ + ⟨W.mkQ v', hmemS _⟩ := Subtype.ext (map_add _ _ _)
        show φS ⟨W.mkQ (v + v'), hmemS _⟩ = φS ⟨W.mkQ v, hmemS _⟩ + φS ⟨W.mkQ v', hmemS _⟩
        rw [this, map_add] }
  have hφ : ∀ v, φ v = φS ⟨W.mkQ v, hmemS _⟩ := fun v => rfl
  refine ⟨φ, fun y => ?_, fun g v => ?_, fun v => ?_⟩
  · obtain ⟨s, rfl⟩ := φS.surjective y
    obtain ⟨v, hv⟩ := W.mkQ_surjective s
    exact ⟨v, by rw [hφ]; exact congrArg φS (Subtype.ext hv)⟩
  · rw [hφ, hφ, ← hφS]
    exact congrArg φS (Subtype.ext rfl)
  · rw [hφ, AddEquiv.map_eq_zero_iff, Submodule.mk_eq_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]

end Main

end CFSG.Quasithin.MS93.S46
