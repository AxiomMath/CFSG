module

public import CFSG.Quasithin.H13.L32A764c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.RuType
open scoped MatrixGroups Pointwise

theorem f4_upper_mul : ∀ a b : F4,
    (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F4) * !![1, b; 0, 1] = !![1, a + b; 0, 1] := by
  decide

theorem f4_upper_sq : ∀ a : F4,
    (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F4) * !![1, a; 0, 1] = 1 := by
  decide

theorem f4_upper_conj : ∀ g : SL(2, F4), (g : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 → ∀ a : F4,
    ∃ a' : F4, (g : Matrix (Fin 2) (Fin 2) F4) * !![1, a; 0, 1] *
      ((g⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) = !![1, a'; 0, 1] := by
  decide +kernel

theorem f4_inv_upper : ∀ g : SL(2, F4), (g : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 →
    ((g⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 := by
  decide

theorem f4_lower_gen : ∀ g : SL(2, F4), (g : Matrix (Fin 2) (Fin 2) F4) 1 0 ≠ 0 → ∀ b : F4,
    ∃ x y w : F4, (!![1, 0; b, 1] : Matrix (Fin 2) (Fin 2) F4) = !![1, x; 0, 1] *
      ((g : Matrix (Fin 2) (Fin 2) F4) * !![1, y; 0, 1] *
        ((g⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4)) * !![1, w; 0, 1] := by
  decide +kernel

theorem f4_lower_conj_ne : ∀ a : F4, (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F4) *
    !![1, 1; 0, 1] * !![1, 0; 1, 1] ≠ !![1, a; 0, 1] := by
  decide

theorem f4_upper_lower_ne : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F4) * !![1, 0; 1, 1] ≠
    !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
  decide

theorem f4_sq_eq_one : ∀ r : F4, r ^ 2 = 1 → r = 1 := by
  decide

theorem sl24_exists_fpf : ∃ A : SL(2, F4), ∀ v : Fin 2 → F4,
    (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = v → v = 0 := by
  decide

theorem sl24_fix_all : ∀ v : Fin 2 → F4,
    (∀ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = v) → v = 0 := by
  decide

@[expose] def lower24 (b : F4) : SL(2, F4) :=
  ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_lower24 (b : F4) :
    ((lower24 b : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) = !![1, 0; b, 1] := rfl

theorem upper24_mul (a b : F4) : upper24 a * upper24 b = upper24 (a + b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, coe_upper24, coe_upper24, f4_upper_mul]

theorem upper24_inv (a : F4) : (upper24 a)⁻¹ = upper24 a := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, f4_upper_sq]
  rfl

theorem upper24_zero : upper24 0 = 1 := by
  ext i j
  rw [coe_upper24]
  fin_cases i <;> fin_cases j <;> rfl

theorem upper24_lower24_ne : upper24 1 * lower24 1 ≠ lower24 1 * upper24 1 := fun h =>
  f4_upper_lower_ne (by
    have := congrArg (fun A : SL(2, F4) => (A : Matrix (Fin 2) (Fin 2) F4)) h
    simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, coe_lower24] using this)

@[expose] def upperSub : Subgroup SL(2, F4) where
  carrier := Set.range upper24
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (upper24_mul a b).symm⟩
  one_mem' := ⟨0, upper24_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (upper24_inv a).symm⟩

theorem mem_upperSub {A : SL(2, F4)} : A ∈ upperSub ↔ ∃ a, upper24 a = A := Iff.rfl

theorem card_upperSub : Nat.card upperSub = 4 := by
  have hinj : Function.Injective upper24 := fun a b h => by
    have := congrArg (fun A : SL(2, F4) => (A : Matrix (Fin 2) (Fin 2) F4) 0 1) h
    simpa [coe_upper24] using this
  calc Nat.card upperSub = Nat.card (Set.range upper24) := rfl
    _ = Nat.card F4 := Nat.card_range_of_injective hinj
    _ = 4 := by rw [Nat.card_eq_fintype_card, F4.card]

theorem card_sl24 : Nat.card SL(2, F4) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem index_upperSub : upperSub.index = 15 := by
  have := Subgroup.index_mul_card upperSub
  rw [card_upperSub, card_sl24] at this
  omega

theorem isPGroup_upperSub : IsPGroup 2 upperSub :=
  IsPGroup.of_card (n := 2) (by rw [card_upperSub]; norm_num)

theorem mem_normalizer_upperSub_of {g : SL(2, F4)}
    (h0 : (g : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0) :
    g ∈ Subgroup.normalizer (upperSub : Set SL(2, F4)) := by
  have key : ∀ k : SL(2, F4), (k : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 →
      ∀ A ∈ upperSub, k * A * k⁻¹ ∈ upperSub := by
    intro k hk A hA
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨a', e⟩ := f4_upper_conj k hk a
    refine ⟨a', ?_⟩
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upper24]
    rw [e]
  rw [Subgroup.mem_normalizer_iff]
  intro A
  refine ⟨key g h0 A, fun hA => ?_⟩
  have := key g⁻¹ (f4_inv_upper g h0) _ hA
  rwa [show g⁻¹ * (g * A * g⁻¹) * g⁻¹⁻¹ = A by group] at this

theorem lower24_not_mem_normalizer :
    lower24 1 ∉ Subgroup.normalizer (upperSub : Set SL(2, F4)) := by
  intro h
  obtain ⟨a, ha⟩ := (Subgroup.mem_normalizer_iff.mp h (upper24 1)).mp ⟨1, rfl⟩
  have hl : (lower24 1)⁻¹ = lower24 1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_lower24]
    fin_cases i <;> fin_cases j <;> decide
  rw [hl] at ha
  have e := congrArg (fun A : SL(2, F4) => (A : Matrix (Fin 2) (Fin 2) F4)) ha
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, coe_lower24] at e
  exact f4_lower_conj_ne a e.symm

theorem eq_top_or_le_normalizer_upperSub {M : Subgroup SL(2, F4)} (hM : upperSub ≤ M) :
    M = ⊤ ∨ M ≤ Subgroup.normalizer (upperSub : Set SL(2, F4)) := by
  by_cases hN : M ≤ Subgroup.normalizer (upperSub : Set SL(2, F4))
  · exact Or.inr hN
  left
  obtain ⟨g, hgM, hgN⟩ := Set.not_subset.mp hN
  have hg : (g : Matrix (Fin 2) (Fin 2) F4) 1 0 ≠ 0 := fun h0 =>
    hgN (mem_normalizer_upperSub_of h0)
  have hlow : ∀ b : F4, lower24 b ∈ M := by
    intro b
    obtain ⟨x, y, w, e⟩ := f4_lower_gen g hg b
    have e' : lower24 b = upper24 x * (g * upper24 y * g⁻¹) * upper24 w := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, coe_lower24]
      rw [e]
    rw [e']
    exact mul_mem (mul_mem (hM ⟨x, rfl⟩) (mul_mem (mul_mem hgM (hM ⟨y, rfl⟩)) (inv_mem hgM)))
      (hM ⟨w, rfl⟩)
  refine eq_top_iff.mpr fun A _ => ?_
  obtain ⟨a, b, c, d, e⟩ := sl24_prod A
  have e' : A = upper24 a * lower24 b * upper24 c * lower24 d := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, coe_lower24]
    rw [e]
  rw [e']
  exact mul_mem (mul_mem (mul_mem (hM ⟨a, rfl⟩) (hlow b)) (hM ⟨c, rfl⟩)) (hlow d)

theorem exists_conj_eq_upperSub {P : Subgroup SL(2, F4)} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) : ∃ g : SL(2, F4), ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ upperSub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUi : ¬ 2 ∣ upperSub.index := by rw [index_upperSub]; decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F4) (isPGroup_upperSub.toSylow hUi)
    (hP.toSylow hPi)
  refine ⟨g, fun x => ?_⟩
  have e : x ∈ P ↔ x ∈ ((hP.toSylow hPi : Sylow 2 SL(2, F4)) : Subgroup SL(2, F4)) := by
    rw [IsPGroup.toSylow_coe]
  rw [e, ← hg, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

theorem eq_top_or_le_normalizer_of_isPGroup {P M : Subgroup SL(2, F4)} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) (hPM : P ≤ M) :
    M = ⊤ ∨ M ≤ Subgroup.normalizer (P : Set SL(2, F4)) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_upperSub hP hPi
  set M' : Subgroup SL(2, F4) := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'def
  have hmem : ∀ y, y ∈ M' ↔ g * y * g⁻¹ ∈ M := by
    intro y
    rw [hM'def, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hm
    · intro hy
      exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩
  have hM' : upperSub ≤ M' := by
    intro A hA
    rw [hmem]
    refine hPM ((hg _).mpr ?_)
    rwa [show g⁻¹ * (g * A * g⁻¹) * g = A by group]
  rcases eq_top_or_le_normalizer_upperSub hM' with h | h
  · left
    refine eq_top_iff.mpr fun x _ => ?_
    have := (hmem (g⁻¹ * x * g)).mp (h ▸ Subgroup.mem_top _)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  · right
    intro m hm
    have hm' : g⁻¹ * m * g ∈ Subgroup.normalizer (upperSub : Set SL(2, F4)) :=
      h ((hmem _).mpr (by rwa [show g * (g⁻¹ * m * g) * g⁻¹ = m by group]))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hg x, hg (m * x * m⁻¹), Subgroup.mem_normalizer_iff.mp hm' (g⁻¹ * x * g)]
    rw [show g⁻¹ * m * g * (g⁻¹ * x * g) * (g⁻¹ * m * g)⁻¹ = g⁻¹ * (m * x * m⁻¹) * g by group]

theorem not_top_le_normalizer_of_isPGroup {P : Subgroup SL(2, F4)} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) :
    ¬ (⊤ : Subgroup SL(2, F4)) ≤ Subgroup.normalizer (P : Set SL(2, F4)) := by
  intro htop
  obtain ⟨g, hg⟩ := exists_conj_eq_upperSub hP hPi
  apply lower24_not_mem_normalizer
  have hm := htop (Subgroup.mem_top (g * lower24 1 * g⁻¹))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e := Subgroup.mem_normalizer_iff.mp hm (g * x * g⁻¹)
  rw [hg, hg] at e
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group,
    show g⁻¹ * (g * lower24 1 * g⁻¹ * (g * x * g⁻¹) * (g * lower24 1 * g⁻¹)⁻¹) * g =
      lower24 1 * x * (lower24 1)⁻¹ by group] at e

theorem isSimpleGroup_sl24 : IsSimpleGroup SL(2, F4) := by
  have hZ : Subgroup.center SL(2, F4) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Fintype.card_fin] at hr
    rw [Subgroup.mem_bot]
    ext i j
    rw [← hA', f4_sq_eq_one r hr]
    simp [Matrix.one_apply]
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4 ≃* SL(2, F4) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hc : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  exact ePSL.symm.isSimpleGroup

end CFSG.Quasithin.H13.L32A
