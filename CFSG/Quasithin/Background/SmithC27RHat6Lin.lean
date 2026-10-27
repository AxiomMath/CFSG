module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Quasithin

section Alt6

theorem card_of_isHat_alt6 {Γ : Type} [Group Γ] (hΓ : IsHat Γ ↥(alternatingGroup (Fin 6))) :
    Nat.card Γ = 1080 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hΓ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Γ),
    Nat.card_congr e.toEquiv, CFSG.QuasithinUnique.Setup.X3.card_alt6, hZ]

theorem index_cases_of_alt6 {Γ : Type*} [Group Γ] (e : Γ ≃* ↥(alternatingGroup (Fin 6)))
    (P : Subgroup Γ) : P.index = 1 ∨ (6 ≤ P.index ∧ P.index ≠ 9) := by
  have h := CFSG.QuasithinUnique.Setup.X3.orbit_card_cases (X := Γ ⧸ P) e ((1 : Γ) : Γ ⧸ P)
  rw [← MulAction.index_stabilizer, MulAction.stabilizer_quotient] at h
  rcases h with h | ⟨h6, -, -, h9, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h6, h9⟩

theorem index_cases_of_isHat {Γ : Type} [Group Γ] (hΓ : IsHat Γ ↥(alternatingGroup (Fin 6)))
    {P : Subgroup Γ} (hZ : Subgroup.center Γ ≤ P) :
    P.index = 1 ∨ (6 ≤ P.index ∧ P.index ≠ 9) := by
  obtain ⟨-, -, ⟨e⟩⟩ := hΓ
  have hP : (P.map (QuotientGroup.mk' (Subgroup.center Γ))).index = P.index := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
      Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])]
  rw [← hP]
  exact index_cases_of_alt6 e _

end Alt6

section Arith

theorem index_cases_1080 {p i : ℕ} (h : p * i = 1080) (h24 : 24 ∣ p) :
    i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 9 ∨ i = 15 ∨ i = 45 := by
  obtain ⟨m, rfl⟩ := h24
  have hmi : m * i = 45 := by
    have : 24 * (m * i) = 24 * 45 := by rw [← mul_assoc, h]
    omega
  have hi : i ∣ 45 := ⟨m, by rw [← hmi, mul_comm]⟩
  have hi45 : i ≤ 45 := Nat.le_of_dvd (by norm_num) hi
  interval_cases i <;> omega

theorem two_pow_le_eight_of_dvd {a : ℕ} (h : 2 ^ a ∣ 1080) : 2 ^ a ≤ 8 := by
  by_contra hlt
  have ha : 4 ≤ a := by
    by_contra ha
    have : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16 : 2 ^ 4 ∣ 1080 := (Nat.pow_dvd_pow 2 ha).trans h
  omega

theorem two_pow_eq_eight_of_mul_odd {a m : ℕ} (h : 2 ^ a * m = 1080) (hm : ¬ 2 ∣ m) :
    2 ^ a = 8 := by
  have hle := two_pow_le_eight_of_dvd ⟨m, h.symm⟩
  have ha : a ≤ 3 := by
    by_contra ha
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases a <;> omega

end Arith

section Lin

variable {F Γ : Type*} [Field F] [Group Γ]

@[expose] def fixSub (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F) (T : Set Γ) :
    Submodule F (Fin 3 → F) where
  carrier := {x | ∀ t ∈ T,
    ((ρ t : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x}
  add_mem' := fun {x y} hx hy t ht => by rw [Matrix.mulVec_add, hx t ht, hy t ht]
  zero_mem' := fun t _ => Matrix.mulVec_zero _
  smul_mem' := fun c x hx t ht => by rw [Matrix.mulVec_smul, hx t ht]

theorem eq_one_of_fixSub_eq_top {ρ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F} {T : Set Γ}
    (h : fixSub ρ T = ⊤) {t : Γ} (ht : t ∈ T) : ρ t = 1 := by
  have hx : ∀ x : Fin 3 → F,
      ((ρ t : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x :=
    fun x => (h ▸ Submodule.mem_top : x ∈ fixSub ρ T) t ht
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_))
  rw [Matrix.toLin'_apply, hx, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]

@[expose] def stabGL (W : Submodule F (Fin 3 → F)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) where
  carrier := {g | ∀ w ∈ W,
    ((g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W ∧
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W}
  mul_mem' := fun {g h} hg hh w hw => by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hg _ (hh w hw).1).1
    · rw [mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hh _ (hg w hw).2).2
  one_mem' := fun w hw => by simpa using hw
  inv_mem' := fun {g} hg w hw => by
    rw [inv_inv]
    exact ⟨(hg w hw).2, (hg w hw).1⟩

theorem mem_stabGL_iff [Finite F] {W : Submodule F (Fin 3 → F)}
    {g : Matrix.GeneralLinearGroup (Fin 3) F} : g ∈ stabGL W ↔ ∀ w ∈ W,
      ((g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W := by
  refine ⟨fun hg w hw => (hg w hw).1, fun hW w hw => ⟨hW w hw, ?_⟩⟩
  have hinv : ∀ v : Fin 3 → F,
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (((g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  let f : ↥W → ↥W := fun v => ⟨_, hW v v.2⟩
  have hf : Function.Injective f := fun v v' hvv' => by
    have h1 := congrArg (fun x : ↥W => ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec (x : Fin 3 → F)) hvv'
    simp only [f, hinv] at h1
    exact Subtype.ext h1
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 hf) ⟨w, hw⟩
  have hv' : ((g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = w :=
    congrArg Subtype.val hv
  rw [← hv', hinv]
  exact v.2

end Lin

end CFSG.Quasithin.SmithC27
