module

public import CFSG.Quasithin.Background.A3Structure316

public section

open Matrix

namespace CFSG.Quasithin.SBc5SL2

abbrev SL2 (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 2) F

section Defs

variable {F : Type} [Field F]

@[expose] def xm (t : F) : SL2 F := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def dm (c : Fˣ) : SL2 F :=
  ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

@[expose] def wm : SL2 F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

private theorem coe_xm (t : F) : (xm t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

private theorem coe_dm (c : Fˣ) :
    (dm c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] := rfl

private theorem coe_wm : ((wm : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

private theorem det_entries (g : SL2 F) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

variable (F)

@[expose] def Uplus : Subgroup (SL2 F) where
  carrier := {g | ∃ t : F, g = xm t}
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        add_comm]
  one_mem' := by
    refine ⟨0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_xm]
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_xm, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[expose] def Tplus : Subgroup (SL2 F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    have hg' : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
    have hh' : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hh
    show ((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg', hh']
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    have hg' : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
    show ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg']

end Defs

section Lemmas

variable {F : Type} [Field F]

theorem xm_mul (s t : F) : xm s * xm t = xm (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem xm_mem_Uplus (t : F) : xm t ∈ Uplus F := ⟨t, rfl⟩

theorem mem_Uplus_iff {g : SL2 F} : g ∈ Uplus F ↔ ∃ t : F, g = xm t := Iff.rfl

theorem mem_Tplus_iff {g : SL2 F} : g ∈ Tplus F ↔ ∃ (t : F) (c : Fˣ), g = xm t * dm c := by
  constructor
  · intro hg
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
    have hdet := det_entries g
    rw [h10, mul_zero, sub_zero] at hdet
    have hne : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    refine ⟨g 0 1 * g 0 0, Units.mk0 (g 0 0) hne, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_xm, coe_dm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, h10, hd, hne]
  · rintro ⟨t, c, rfl⟩
    show ((xm t * dm c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [coe_xm, coe_dm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem Uplus_le_Tplus : Uplus F ≤ Tplus F := by
  rintro _ ⟨t, rfl⟩
  show ((xm t : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp [coe_xm]

theorem dm_mem_Tplus (c : Fˣ) : dm c ∈ Tplus F := by
  show ((dm c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp [coe_dm]

theorem closure_gen [CharP F 2] :
    Subgroup.closure (Set.range (xm (F := F)) ∪ Set.range (dm (F := F)) ∪ {wm}) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set H := Subgroup.closure (Set.range (xm (F := F)) ∪ Set.range (dm (F := F)) ∪ {wm})
  have hx : ∀ t : F, xm t ∈ H := fun t => Subgroup.subset_closure (Or.inl (Or.inl ⟨t, rfl⟩))
  have hd : ∀ c : Fˣ, dm c ∈ H := fun c => Subgroup.subset_closure (Or.inl (Or.inr ⟨c, rfl⟩))
  have hw : (wm : SL2 F) ∈ H := Subgroup.subset_closure (Or.inr rfl)
  by_cases hc : g 1 0 = 0
  · obtain ⟨t, c, rfl⟩ := mem_Tplus_iff.1 hc
    exact H.mul_mem (hx t) (hd c)
  · have hdet := det_entries g
    have hc' : g 1 0 ≠ 0 := hc
    have hg : g = xm (g 0 0 / g 1 0) * wm * dm (Units.mk0 (-(g 1 0)) (neg_ne_zero.2 hc)) *
        xm (g 1 1 / g 1 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coe_xm, coe_dm, coe_wm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
          Fin.sum_univ_two]
      all_goals first | done | (field_simp; done) | (field_simp; linear_combination -hdet)
    rw [hg]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hx _) hw) (hd _)) (hx _)

private theorem conj_xm_entry10 (g : SL2 F) (s : F) :
    ((g * xm s * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = -(s * (g 1 0) ^ 2) := by
  simp [coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem conj_xm_of_mem_Tplus {g : SL2 F} (hg : g ∈ Tplus F) (s : F) :
    g * xm s * g⁻¹ = xm ((g 0 0) ^ 2 * s) := by
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
  have hdet := det_entries g
  rw [h10, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h10]
  all_goals first | exact hdet | ring1 | linear_combination hdet

theorem normalizer_Uplus : Subgroup.normalizer (Uplus F : Set (SL2 F)) = Tplus F := by
  ext g
  rw [Subgroup.mem_set_normalizer_iff]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (h (xm 1)).1 (xm_mem_Uplus 1)
    have h10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) ht
    simp only [conj_xm_entry10, coe_xm] at h10
    show (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simpa using h10
  · intro hg h
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, conj_xm_of_mem_Tplus hg s⟩
    · rintro ⟨s, hs⟩
      refine ⟨((g⁻¹ : SL2 F) 0 0) ^ 2 * s, ?_⟩
      rw [← conj_xm_of_mem_Tplus (inv_mem hg) s, ← hs]
      group

private theorem card_Uplus : Nat.card (Uplus F) = Nat.card F := by
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun t : F => (⟨xm t, xm_mem_Uplus t⟩ : Uplus F)) ⟨?_, ?_⟩))
  · intro s t hst
    have h := congrArg (fun x : Uplus F => ((x : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1) hst
    simpa [coe_xm] using h
  · rintro ⟨_, t, rfl⟩
    exact ⟨t, rfl⟩

private theorem card_SL2 [Finite F] : Nat.card (SL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have := Fintype.ofFinite F
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, ← Nat.card_eq_fintype_card] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hq1 : 0 < Nat.card F - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hq1
  rw [h, show Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) by
    rw [Nat.mul_sub_one, sq]]
  ring

theorem isSylowTwoOf_Uplus [Finite F] {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Uplus F) ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := m) (by rw [card_Uplus, hF]), ?_⟩
  show ¬ 2 ∣ (Uplus F).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := (Uplus F).index_mul_card
  rw [card_Uplus, card_SL2] at h
  have hq : 0 < Nat.card F := Nat.card_pos
  have hidx : (Uplus F).index = Nat.card F ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_right hq (by rw [h, mul_comm])
  rw [hidx, hF, ← pow_mul]
  have h2 : 2 ∣ 2 ^ (m * 2) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (m * 2) := Nat.one_le_two_pow
  generalize 2 ^ (m * 2) = x at h1 h2
  omega

theorem eq_zero_of_fixed_dm {a : Fˣ} (ha : a ≠ 1) (v : Fin 2 → F)
    (hv : (dm a : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [coe_dm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have ha' : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have hv0 : v 0 = 0 := by
    by_contra hne
    exact ha' (mul_right_cancel₀ hne (by rw [one_mul]; exact h0))
  have hv1 : v 1 = 0 := by
    by_contra hne
    exact ha' (inv_eq_one.1 (mul_right_cancel₀ hne (by rw [one_mul]; exact h1)))
  ext i
  fin_cases i <;> simp [hv0, hv1]

private theorem xm_zero : xm (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_xm]

private theorem dm_one : dm (1 : Fˣ) = (1 : SL2 F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dm]

private theorem xm_inv (t : F) : (xm t)⁻¹ = xm (-t) := by
  rw [inv_eq_iff_mul_eq_one, xm_mul, add_neg_cancel, xm_zero]

private theorem xm_mul_dm_apply00 (t : F) (a : Fˣ) :
    ((xm t * dm a : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by
  simp [coe_xm, coe_dm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem commutator_xm {g : SL2 F} (hg : g ∈ Tplus F) (s : F) :
    xm s * g * (xm s)⁻¹ * g⁻¹ = xm (s * (1 - (g 0 0) ^ 2)) := by
  calc xm s * g * (xm s)⁻¹ * g⁻¹ = xm s * (g * xm (-s) * g⁻¹) := by rw [xm_inv]; group
    _ = xm s * xm ((g 0 0) ^ 2 * (-s)) := by rw [conj_xm_of_mem_Tplus hg]
    _ = xm (s * (1 - (g 0 0) ^ 2)) := by rw [xm_mul]; congr 1; ring

private theorem eq_one_of_sq_eq_one [CharP F 2] {x : F} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h : (x - 1) ^ 2 = 0 := by linear_combination hx + (1 - x) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)

private theorem one_sub_sq_ne_zero [CharP F 2] {a : Fˣ} (ha : a ≠ 1) : 1 - (a : F) ^ 2 ≠ 0 :=
  fun h => ha (Units.ext (eq_one_of_sq_eq_one (sub_eq_zero.1 h).symm))

theorem o3_Tplus [Finite F] [CharP F 2] (h : CFSG.Quasithin.oPrimeResidualOf 3 (Tplus F) ≠ ⊥) :
    Uplus F ≤ CFSG.Quasithin.oPrimeResidualOf 3 (Tplus F) ∧
      ∃ a : Fˣ, a ≠ 1 ∧ dm a ∈ CFSG.Quasithin.oPrimeResidualOf 3 (Tplus F) := by
  set R := CFSG.Quasithin.oPrimeResidualOf 3 (Tplus F)
  have hex : ∃ g : SL2 F, g ∈ Tplus F ∧ (∃ k : ℕ, orderOf g = 3 ^ k) ∧ g ≠ 1 := by
    by_contra hne
    refine h (le_bot_iff.1 ((Subgroup.closure_le ⊥).2 ?_))
    rintro x ⟨hxT, hk⟩
    by_contra hx
    exact hne ⟨x, hxT, hk, fun h1 => hx (h1 ▸ (⊥ : Subgroup (SL2 F)).one_mem)⟩
  obtain ⟨g, hgT, ⟨k, hk⟩, hg1⟩ := hex
  have hgR : g ∈ R := Subgroup.subset_closure ⟨hgT, k, hk⟩
  obtain ⟨t, a, rfl⟩ := mem_Tplus_iff.1 hgT
  have hchar2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have ha : a ≠ 1 := by
    rintro rfl
    have h2 : (xm t * dm (1 : Fˣ) : SL2 F) ^ 2 = 1 := by
      rw [dm_one, mul_one, pow_two, xm_mul, ← two_mul, hchar2, zero_mul, xm_zero]
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h3 : 3 ∣ 2 := (dvd_pow_self 3 hk0).trans hdvd
      omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hg1 hk
  have hcomm : ∀ s : F, xm (s * (1 - (a : F) ^ 2)) ∈ R := by
    intro s
    have hu : xm s ∈ Tplus F := Uplus_le_Tplus (xm_mem_Uplus s)
    have hconj : xm s * (xm t * dm a) * (xm s)⁻¹ ∈ R := by
      refine Subgroup.subset_closure ⟨(Tplus F).mul_mem ((Tplus F).mul_mem hu hgT)
        ((Tplus F).inv_mem hu), k, ?_⟩
      rw [← hk]
      exact (SemiconjBy.orderOf_eq (xm s) (by simp [SemiconjBy])).symm
    have := R.mul_mem hconj (R.inv_mem hgR)
    rwa [commutator_xm hgT, xm_mul_dm_apply00] at this
  have hU : Uplus F ≤ R := by
    rintro _ ⟨u, rfl⟩
    have := hcomm (u / (1 - (a : F) ^ 2))
    rwa [div_mul_cancel₀ _ (one_sub_sq_ne_zero ha)] at this
  refine ⟨hU, a, ha, ?_⟩
  have := R.mul_mem (R.inv_mem (hU (xm_mem_Uplus t))) hgR
  rwa [inv_mul_cancel_left] at this

private theorem dm_mul_xm (c : Fˣ) (t : F) : dm c * xm t = xm ((c : F) ^ 2 * t) * dm c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_xm, coe_dm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  field_simp

private theorem wm_mul_dm (c : Fˣ) : wm * dm c = dm c⁻¹ * wm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_wm, coe_dm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem wm_mul_xm_mul_wm : wm * xm (-1 : F) * wm = xm 1 * wm * xm 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_wm, coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem dm_mul_comm (c c' : Fˣ) : dm c * dm c' = dm c' * dm c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem inv_mulVec_mulVec (g : SL2 F) (v : Fin 2 → F) :
    ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec
      ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

private theorem hom_dm_eq [CharP F 2] (σ : SL2 F →* SL2 F) (hx : ∀ t : F, σ (xm t) = xm t)
    {a : Fˣ} (ha : a ≠ 1) (hd : σ (dm a) = dm a) (c : Fˣ) : σ (dm c) = dm c := by
  have ha2 : 1 - (a : F) ^ 2 ≠ 0 := one_sub_sq_ne_zero ha
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have hcomm : σ (dm c) * dm a = dm a * σ (dm c) := by
    have := congrArg σ (dm_mul_comm c a)
    rwa [map_mul, map_mul, hd] at this
  have hconj : σ (dm c) * xm 1 = xm ((c : F) ^ 2 * 1) * σ (dm c) := by
    have := congrArg σ (dm_mul_xm c 1)
    rwa [map_mul, map_mul, hx, hx] at this
  generalize σ (dm c) = N at hcomm hconj
  have e01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hcomm
  have e10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) hcomm
  have f01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hconj
  have hdet := det_entries N
  simp [coe_dm, coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] at e01 e10 f01
  field_simp at e01 e10
  have h01 : N 0 1 = 0 :=
    (mul_eq_zero.1 (show N 0 1 * (1 - (a : F) ^ 2) = 0 by linear_combination e01)).resolve_right
      ha2
  have h10 : N 1 0 = 0 :=
    (mul_eq_zero.1 (show N 1 0 * (1 - (a : F) ^ 2) = 0 by linear_combination -e10)).resolve_right
      ha2
  have h00 : N 0 0 = (c : F) ^ 2 * N 1 1 := by linear_combination f01
  have hsq : ((c : F) * N 1 1) ^ 2 = 1 := by
    linear_combination hdet - N 1 1 * h00 + N 1 0 * h01
  have hc1 : (c : F) * N 1 1 = 1 := eq_one_of_sq_eq_one hsq
  have h11 : N 1 1 = ((c⁻¹ : Fˣ) : F) := Units.eq_inv_of_mul_eq_one_left hc1
  have h00' : N 0 0 = c := by linear_combination h00 + (c : F) * hc1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dm, h00', h01, h10, h11]

private theorem hom_wm_eq [CharP F 2] (σ : SL2 F →* SL2 F) (hx : ∀ t : F, σ (xm t) = xm t)
    {a : Fˣ} (ha : a ≠ 1) (hdc : ∀ c : Fˣ, σ (dm c) = dm c) : σ wm = wm := by
  have ha2 : 1 - (a : F) ^ 2 ≠ 0 := one_sub_sq_ne_zero ha
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have h1 : σ wm * dm a = dm a⁻¹ * σ wm := by
    have := congrArg σ (wm_mul_dm a)
    rwa [map_mul, map_mul, hdc, hdc] at this
  have h2 : σ wm * xm (-1) * σ wm = xm 1 * σ wm * xm 1 := by
    have := congrArg σ (wm_mul_xm_mul_wm (F := F))
    simpa only [map_mul, hx] using this
  generalize σ wm = M at h1 h2
  have e00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  have e11 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 1) h1
  have g00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h2
  have hdet := det_entries M
  simp [coe_dm, coe_xm, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e00 e11 g00
  field_simp at e00 e11
  have hM00 : M 0 0 = 0 :=
    (mul_eq_zero.1 (show M 0 0 * (1 - (a : F) ^ 2) = 0 by linear_combination -e00)).resolve_right
      ha2
  have hM11 : M 1 1 = 0 :=
    (mul_eq_zero.1 (show M 1 1 * (1 - (a : F) ^ 2) = 0 by linear_combination e11)).resolve_right
      ha2
  have hM10 : M 1 0 = -1 := by
    linear_combination -g00 - hdet + (M 0 0 - M 1 0 - 1 + M 1 1) * hM00
  have hM01 : M 0 1 = 1 := by linear_combination hdet - M 1 1 * hM00 + M 0 1 * hM10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_wm, hM00, hM11, hM01, hM10]

theorem hom_eq_id [CharP F 2] (σ : SL2 F →* SL2 F) (hx : ∀ t : F, σ (xm t) = xm t) {a : Fˣ}
    (ha : a ≠ 1) (hd : σ (dm a) = dm a) : ∀ g : SL2 F, σ g = g := by
  have hdc : ∀ c : Fˣ, σ (dm c) = dm c := hom_dm_eq σ hx ha hd
  have hw : σ wm = wm := hom_wm_eq σ hx ha hdc
  have hK : Subgroup.closure (Set.range (xm (F := F)) ∪ Set.range (dm (F := F)) ∪ {wm}) ≤
      MonoidHom.eqLocus σ (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro _ ((⟨t, rfl⟩ | ⟨c, rfl⟩) | rfl)
    · exact hx t
    · exact hdc c
    · exact hw
  rw [closure_gen] at hK
  exact fun g => hK (Subgroup.mem_top g)

theorem cocycle_eq_zero [CharP F 2] (ζ : SL2 F → (Fin 2 → F))
    (hζ : ∀ g h : SL2 F, ζ (g * h) = ζ g + (g : Matrix (Fin 2) (Fin 2) F).mulVec (ζ h))
    (hx : ∀ t : F, ζ (xm t) = 0) {a : Fˣ} (ha : a ≠ 1) (hd : ζ (dm a) = 0) :
    ∀ g : SL2 F, ζ g = 0 := by
  have hdc : ∀ c : Fˣ, ζ (dm c) = 0 := by
    intro c
    have h1 := hζ (dm c) (dm a)
    have h2 := hζ (dm a) (dm c)
    rw [dm_mul_comm, hd, Matrix.mulVec_zero, add_zero] at h1
    rw [h1, hd, zero_add] at h2
    exact eq_zero_of_fixed_dm ha _ h2.symm
  have hw : ζ wm = 0 := by
    have h1 := hζ wm (dm a⁻¹)
    have h2 := hζ (dm a) wm
    rw [wm_mul_dm, inv_inv, hdc a⁻¹, Matrix.mulVec_zero, add_zero] at h1
    rw [h1, hd, zero_add] at h2
    exact eq_zero_of_fixed_dm ha _ h2.symm
  have hone : ζ 1 = 0 := by simpa [xm_zero] using hx 0
  let K : Subgroup (SL2 F) :=
    { carrier := {g | ζ g = 0}
      mul_mem' := fun {g h} hg hh => by
        have hg' : ζ g = 0 := hg
        have hh' : ζ h = 0 := hh
        show ζ (g * h) = 0
        rw [hζ, hg', hh', Matrix.mulVec_zero, add_zero]
      one_mem' := hone
      inv_mem' := fun {g} hg => by
        have hg' : ζ g = 0 := hg
        have h1 := hζ g g⁻¹
        rw [mul_inv_cancel, hone, hg', zero_add] at h1
        show ζ g⁻¹ = 0
        have h2 := congrArg ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec h1
        rw [Matrix.mulVec_zero, inv_mulVec_mulVec] at h2
        exact h2.symm }
  have hK : Subgroup.closure
      (Set.range (xm (F := F)) ∪ Set.range (dm (F := F)) ∪ {wm}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ((⟨t, rfl⟩ | ⟨c, rfl⟩) | rfl)
    · exact hx t
    · exact hdc c
    · exact hw
  rw [closure_gen] at hK
  exact fun g => hK (Subgroup.mem_top g)

end Lemmas

end CFSG.Quasithin.SBc5SL2
