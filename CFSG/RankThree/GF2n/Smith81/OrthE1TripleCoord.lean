module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

variable {K : Type} [Field K]

abbrev T3E (K : Type) [Field K] := Tensor3 K ≃ₗ[K] Tensor3 K

theorem tensor3Act0_add (A : Matrix (Fin 2) (Fin 2) K) (T T' : Tensor3 K) :
    tensor3Act0 A (T + T') = tensor3Act0 A T + tensor3Act0 A T' := by
  funext a b c
  simp [tensor3Act0, mul_add, Finset.sum_add_distrib]

theorem tensor3Act0_smul (A : Matrix (Fin 2) (Fin 2) K) (r : K) (T : Tensor3 K) :
    tensor3Act0 A (r • T) = r • tensor3Act0 A T := by
  funext a b c
  simp [tensor3Act0, Finset.mul_sum, mul_left_comm, mul_add]

theorem tensor3Act0_mul (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act0 (A * B) T = tensor3Act0 A (tensor3Act0 B T) := by
  funext a b c
  simp only [tensor3Act0, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensor3Act0_one (T : Tensor3 K) : tensor3Act0 (1 : Matrix (Fin 2) (Fin 2) K) T = T := by
  funext a b c
  simp [tensor3Act0, Matrix.one_apply, Fin.sum_univ_two]

theorem tensor3Act1_add (A : Matrix (Fin 2) (Fin 2) K) (T T' : Tensor3 K) :
    tensor3Act1 A (T + T') = tensor3Act1 A T + tensor3Act1 A T' := by
  funext a b c
  simp [tensor3Act1, mul_add, Finset.sum_add_distrib]

theorem tensor3Act1_smul (A : Matrix (Fin 2) (Fin 2) K) (r : K) (T : Tensor3 K) :
    tensor3Act1 A (r • T) = r • tensor3Act1 A T := by
  funext a b c
  simp [tensor3Act1, Finset.mul_sum, mul_left_comm, mul_add]

theorem tensor3Act1_mul (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act1 (A * B) T = tensor3Act1 A (tensor3Act1 B T) := by
  funext a b c
  simp only [tensor3Act1, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensor3Act1_one (T : Tensor3 K) : tensor3Act1 (1 : Matrix (Fin 2) (Fin 2) K) T = T := by
  funext a b c
  simp [tensor3Act1, Matrix.one_apply, Fin.sum_univ_two]

theorem tensor3Act2_add (A : Matrix (Fin 2) (Fin 2) K) (T T' : Tensor3 K) :
    tensor3Act2 A (T + T') = tensor3Act2 A T + tensor3Act2 A T' := by
  funext a b c
  simp [tensor3Act2, mul_add, Finset.sum_add_distrib]

theorem tensor3Act2_smul (A : Matrix (Fin 2) (Fin 2) K) (r : K) (T : Tensor3 K) :
    tensor3Act2 A (r • T) = r • tensor3Act2 A T := by
  funext a b c
  simp [tensor3Act2, Finset.mul_sum, mul_left_comm, mul_add]

theorem tensor3Act2_mul (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act2 (A * B) T = tensor3Act2 A (tensor3Act2 B T) := by
  funext a b c
  simp only [tensor3Act2, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensor3Act2_one (T : Tensor3 K) : tensor3Act2 (1 : Matrix (Fin 2) (Fin 2) K) T = T := by
  funext a b c
  simp [tensor3Act2, Matrix.one_apply, Fin.sum_univ_two]

section ActHom

@[expose] def actHom (act : Matrix (Fin 2) (Fin 2) K → Tensor3 K → Tensor3 K)
    (hadd : ∀ A T T', act A (T + T') = act A T + act A T')
    (hsmul : ∀ A (r : K) T, act A (r • T) = r • act A T)
    (hmul : ∀ A B T, act (A * B) T = act A (act B T)) (hone : ∀ T, act 1 T = T) :
    Matrix.SpecialLinearGroup (Fin 2) K →* T3E K where
  toFun A := LinearEquiv.ofLinear
    { toFun := act (A : Matrix (Fin 2) (Fin 2) K)
      map_add' := hadd _
      map_smul' := fun r T => hsmul _ r T }
    { toFun := act ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      map_add' := hadd _
      map_smul' := fun r T => hsmul _ r T }
    (LinearMap.ext fun T => by
      change act _ (act _ T) = T
      rw [← hmul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, hone])
    (LinearMap.ext fun T => by
      change act _ (act _ T) = T
      rw [← hmul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, hone])
  map_one' := by
    ext T : 1
    change act ((1 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) T = T
    rw [Matrix.SpecialLinearGroup.coe_one, hone]
  map_mul' A B := by
    ext T : 1
    change act ((A * B : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) T =
      act (A : Matrix (Fin 2) (Fin 2) K) (act (B : Matrix (Fin 2) (Fin 2) K) T)
    rw [Matrix.SpecialLinearGroup.coe_mul, hmul]

@[expose] def act0E : Matrix.SpecialLinearGroup (Fin 2) K →* T3E K :=
  actHom tensor3Act0 tensor3Act0_add tensor3Act0_smul tensor3Act0_mul tensor3Act0_one

@[expose] def act1E : Matrix.SpecialLinearGroup (Fin 2) K →* T3E K :=
  actHom tensor3Act1 tensor3Act1_add tensor3Act1_smul tensor3Act1_mul tensor3Act1_one

@[expose] def act2E : Matrix.SpecialLinearGroup (Fin 2) K →* T3E K :=
  actHom tensor3Act2 tensor3Act2_add tensor3Act2_smul tensor3Act2_mul tensor3Act2_one

theorem act0E_apply (A : Matrix.SpecialLinearGroup (Fin 2) K) (T : Tensor3 K) :
    act0E A T = tensor3Act0 (A : Matrix (Fin 2) (Fin 2) K) T := rfl

theorem act1E_apply (A : Matrix.SpecialLinearGroup (Fin 2) K) (T : Tensor3 K) :
    act1E A T = tensor3Act1 (A : Matrix (Fin 2) (Fin 2) K) T := rfl

theorem act2E_apply (A : Matrix.SpecialLinearGroup (Fin 2) K) (T : Tensor3 K) :
    act2E A T = tensor3Act2 (A : Matrix (Fin 2) (Fin 2) K) T := rfl

end ActHom

section Groups

@[expose] def slotG : Subgroup (T3E K) := (act0E (K := K)).range

@[expose] def rowG : Subgroup (T3E K) := (act1E (K := K)).range

@[expose] def colG : Subgroup (T3E K) := (act2E (K := K)).range

theorem act0E_injective : Function.Injective (act0E (K := K)) := by
  intro A B hAB
  ext i j
  have h := LinearEquiv.congr_fun hAB (fun a _ _ => if a = j then (1 : K) else 0)
  have h' := congrFun (congrFun (congrFun h i) 0) 0
  simpa [act0E_apply, tensor3Act0, Fin.sum_univ_two] using h'

theorem act1E_injective : Function.Injective (act1E (K := K)) := by
  intro A B hAB
  ext i j
  have h := LinearEquiv.congr_fun hAB (fun _ b _ => if b = j then (1 : K) else 0)
  have h' := congrFun (congrFun (congrFun h 0) i) 0
  simpa [act1E_apply, tensor3Act1, Fin.sum_univ_two] using h'

theorem act2E_injective : Function.Injective (act2E (K := K)) := by
  intro A B hAB
  ext i j
  have h := LinearEquiv.congr_fun hAB (fun _ _ c => if c = j then (1 : K) else 0)
  have h' := congrFun (congrFun (congrFun h 0) 0) i
  simpa [act2E_apply, tensor3Act2, Fin.sum_univ_two] using h'

theorem card_slotG : Nat.card (slotG (K := K)) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Nat.card_congr (MonoidHom.ofInjective act0E_injective).toEquiv.symm

theorem card_rowG : Nat.card (rowG (K := K)) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Nat.card_congr (MonoidHom.ofInjective act1E_injective).toEquiv.symm

theorem tensor3Act0_comm_act1 (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act0 A (tensor3Act1 B T) = tensor3Act1 B (tensor3Act0 A T) := by
  funext a b c
  simp only [tensor3Act0, tensor3Act1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensor3Act0_comm_act2 (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act0 A (tensor3Act2 B T) = tensor3Act2 B (tensor3Act0 A T) := by
  funext a b c
  simp only [tensor3Act0, tensor3Act2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensor3Act1_comm_act2 (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act1 A (tensor3Act2 B T) = tensor3Act2 B (tensor3Act1 A T) := by
  funext a b c
  simp only [tensor3Act1, tensor3Act2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem act0E_comm_act1E (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    act0E A * act1E B = act1E B * act0E A := by
  ext T : 1
  exact tensor3Act0_comm_act1 _ _ T

theorem act0E_comm_act2E (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    act0E A * act2E B = act2E B * act0E A := by
  ext T : 1
  exact tensor3Act0_comm_act2 _ _ T

theorem act1E_comm_act2E (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    act1E A * act2E B = act2E B * act1E A := by
  ext T : 1
  exact tensor3Act1_comm_act2 _ _ T

end Groups

section Forms

@[expose] def detW (T : Tensor3 K) : K := T 1 0 0 * T 1 1 1 - T 1 0 1 * T 1 1 0

@[expose] def Qk (κ : K) (T : Tensor3 K) : K := tensor3Form T + κ * detW T

@[expose] def Ok (κ : K) : Subgroup (T3E K) where
  carrier := {g | ∀ T, Qk κ (g T) = Qk κ T}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb T => by
    rw [LinearEquiv.mul_apply, ha, hb]
  inv_mem' := fun {a} ha T => by
    have h := ha (a.symm T)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_Ok {κ : K} {g : T3E K} : g ∈ Ok κ ↔ ∀ T, Qk κ (g T) = Qk κ T := Iff.rfl

theorem act1E_mem_Ok [CharP K 2] (κ : K) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    act1E A ∈ Ok κ := by
  intro T
  have h := A.2
  rw [Matrix.det_fin_two] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [act1E_apply, Qk, tensor3Form, detW, tensor3Act1, Fin.sum_univ_two]
  linear_combination
    (T 0 0 0 * T 1 1 1 + T 0 0 1 * T 1 1 0 + T 0 1 0 * T 1 0 1 + T 0 1 1 * T 1 0 0) *
      (h) + κ * (T 1 0 0 * T 1 1 1 - T 1 0 1 * T 1 1 0) * h +
    (A 0 0 * T 0 0 0 * A 1 0 * T 1 0 1 + A 0 0 * A 1 0 * T 0 0 1 * T 1 0 0 +
      T 0 0 0 * A 0 1 * A 1 0 * T 1 1 1 + A 0 1 * T 0 1 0 * A 1 0 * T 1 0 1 +
      A 0 1 * T 0 1 0 * A 1 1 * T 1 1 1 + A 0 1 * A 1 0 * T 0 0 1 * T 1 1 0 +
      A 0 1 * A 1 0 * T 0 1 1 * T 1 0 0 + A 0 1 * A 1 1 * T 0 1 1 * T 1 1 0) * h2

theorem rowG_le_Ok [CharP K 2] (κ : K) : rowG ≤ Ok κ := by
  rintro _ ⟨A, rfl⟩
  exact act1E_mem_Ok κ A

end Forms

section Line

@[expose] def unipSL (c : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem unipSL_apply (c : K) : (unipSL c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

theorem unipSL_mul (a b : K) : unipSL a * unipSL b = unipSL (a + b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, unipSL_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem unipSL_zero : unipSL (0 : K) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipSL_apply]

theorem unipSL_injective : Function.Injective (unipSL (K := K)) := by
  intro a b h
  have := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [unipSL_apply] using this

@[expose] def unipHom : Multiplicative K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun c := unipSL (Multiplicative.toAdd c)
  map_one' := unipSL_zero
  map_mul' a b := (unipSL_mul _ _).symm

@[expose] def lineG : Subgroup (T3E K) := ((act0E (K := K)).comp unipHom).range

theorem mem_lineG_iff {g : T3E K} : g ∈ lineG ↔ ∃ c : K, g = act0E (unipSL c) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem lineG_le_slotG : lineG ≤ (slotG : Subgroup (T3E K)) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨unipHom c, rfl⟩

theorem card_lineG : Nat.card (lineG (K := K)) = Nat.card K := by
  have hinj : Function.Injective ((act0E (K := K)).comp unipHom) :=
    act0E_injective.comp (fun a b h => Multiplicative.toAdd.injective (unipSL_injective h))
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm).trans
    (Nat.card_congr Multiplicative.toAdd)

theorem lineG_le_Ok [CharP K 2] (κ : K) : lineG ≤ Ok κ := by
  rintro _ ⟨c, rfl⟩ T
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [MonoidHom.comp_apply, unipHom, MonoidHom.coe_mk, OneHom.coe_mk, act0E_apply, Qk,
    tensor3Form, detW, tensor3Act0, Fin.sum_univ_two, unipSL_apply, toAdd_ofAdd]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  simp
  linear_combination (Multiplicative.toAdd c * (T 1 0 0 * T 1 1 1 + T 1 0 1 * T 1 1 0)) * h2

end Line

section Flip

@[expose] def flipL : Tensor3 K →ₗ[K] Tensor3 K where
  toFun T a b c := T a c b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def flipE : T3E K := LinearEquiv.ofLinear flipL flipL (by ext; rfl) (by ext; rfl)

theorem flipE_apply (T : Tensor3 K) (a b c : Fin 2) : flipE T a b c = T a c b := rfl

theorem flipE_mul_self : flipE * flipE = (1 : T3E K) := by
  ext T a b c
  rfl

theorem flipE_inv : (flipE : T3E K)⁻¹ = flipE := by
  rw [inv_eq_iff_mul_eq_one, flipE_mul_self]

@[expose] def conjFlip : T3E K ≃* T3E K := MulAut.conj (flipE : T3E K)

theorem conjFlip_apply (g : T3E K) : conjFlip g = flipE * g * flipE := by
  simp [conjFlip, flipE_inv]

theorem conjFlip_act0E (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjFlip (act0E A) = act0E A := by
  rw [conjFlip_apply]
  ext T a b c
  simp [act0E_apply, flipE_apply, tensor3Act0, LinearEquiv.mul_apply]

theorem conjFlip_act1E (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjFlip (act1E A) = act2E A := by
  rw [conjFlip_apply]
  ext T a b c
  simp [act1E_apply, act2E_apply, flipE_apply, tensor3Act1, tensor3Act2, LinearEquiv.mul_apply]

theorem conjFlip_act2E (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjFlip (act2E A) = act1E A := by
  rw [conjFlip_apply]
  ext T a b c
  simp [act1E_apply, act2E_apply, flipE_apply, tensor3Act1, tensor3Act2, LinearEquiv.mul_apply]

theorem flipE_mem_Ok (κ : K) : (flipE : T3E K) ∈ Ok κ := by
  intro T
  simp only [flipE_apply, Qk, tensor3Form, detW]
  ring

theorem conjFlip_mem_Ok (κ : K) (g : T3E K) : conjFlip g ∈ Ok κ ↔ g ∈ Ok κ := by
  have hf := flipE_mem_Ok (K := K) κ
  rw [conjFlip_apply]
  constructor
  · intro h
    have h' := (Ok κ).mul_mem ((Ok κ).mul_mem hf h) hf
    have e : (flipE : T3E K) * (flipE * g * flipE) * flipE = g := by
      calc (flipE : T3E K) * (flipE * g * flipE) * flipE
          = (flipE * flipE) * g * (flipE * flipE) := by simp only [mul_assoc]
        _ = g := by rw [flipE_mul_self, one_mul, mul_one]
    rwa [e] at h'
  · intro h
    exact (Ok κ).mul_mem ((Ok κ).mul_mem hf h) hf

end Flip

section Misc

@[expose] def NotTwoPow {G : Type*} [Monoid G] (y : G) : Prop := ∀ k : ℕ, y ^ 2 ^ k ≠ 1

variable [CharP K 2]

theorem SL2_eq_one_of_scalar {A : Matrix.SpecialLinearGroup (Fin 2) K} {s : K}
    (h : (A : Matrix (Fin 2) (Fin 2) K) = s • (1 : Matrix (Fin 2) (Fin 2) K)) : A = 1 := by
  have hd := A.2
  rw [h, Matrix.det_smul] at hd
  simp at hd
  have hs : s = 1 := by
    rcases hd with hs | hs
    · exact hs
    · rw [hs, CharTwo.neg_eq]
  apply Subtype.ext
  rw [h, hs]
  simp

@[expose] def indT (x₀ y₀ z₀ : Fin 2) : Tensor3 K :=
  fun x y z => if x = x₀ ∧ y = y₀ ∧ z = z₀ then 1 else 0

theorem eq_one_of_cross {A B : Matrix.SpecialLinearGroup (Fin 2) K}
    (ev : ∀ a x b y : Fin 2, (A : Matrix (Fin 2) (Fin 2) K) a x * (if b = y then 1 else 0) =
      (B : Matrix (Fin 2) (Fin 2) K) b y * (if a = x then 1 else 0)) : A = 1 ∧ B = 1 := by
  have a10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simpa using ev 1 0 0 0
  have a01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simpa using ev 0 1 0 0
  have b10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simpa using (ev 0 0 1 0).symm
  have b01 : (B : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simpa using (ev 0 0 0 1).symm
  have e00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    simpa using ev 0 0 0 0
  have e11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    simpa using ev 1 1 0 0
  have f11 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (B : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simpa using ev 0 0 1 1
  have hA : (A : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a10, a01, e00, e11]
  have hB : (B : Matrix (Fin 2) (Fin 2) K) = (B : Matrix (Fin 2) (Fin 2) K) 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [b10, b01, ← f11, e00]
  exact ⟨SL2_eq_one_of_scalar hA, SL2_eq_one_of_scalar hB⟩

theorem act0E_eq_act1E {A B : Matrix.SpecialLinearGroup (Fin 2) K} (h : act0E A = act1E B) :
    A = 1 ∧ B = 1 := by
  refine eq_one_of_cross fun a x b y => ?_
  have h1 := congrFun (congrFun (congrFun (LinearEquiv.congr_fun h (indT x y 0)) a) b) 0
  simp only [act0E_apply, act1E_apply, tensor3Act0, tensor3Act1, Fin.sum_univ_two, indT] at h1
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;> simp at h1 ⊢ <;>
    first | exact h1 | exact h1.symm | (rw [← h1]; simp) | skip

theorem act1E_eq_act2E {A B : Matrix.SpecialLinearGroup (Fin 2) K} (h : act1E A = act2E B) :
    A = 1 ∧ B = 1 := by
  refine eq_one_of_cross fun a x b y => ?_
  have h1 := congrFun (congrFun (congrFun (LinearEquiv.congr_fun h (indT 0 x y)) 0) a) b
  simp only [act1E_apply, act2E_apply, tensor3Act1, tensor3Act2, Fin.sum_univ_two, indT] at h1
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;> simp at h1 ⊢ <;>
    first | exact h1 | exact h1.symm | (rw [← h1]; simp) | skip

theorem slotG_inf_rowG : (slotG : Subgroup (T3E K)) ⊓ rowG = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
  obtain ⟨rfl, -⟩ := act0E_eq_act1E hB.symm
  simp

theorem rowG_inf_colG : (rowG : Subgroup (T3E K)) ⊓ colG = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
  obtain ⟨rfl, -⟩ := act1E_eq_act2E hB.symm
  simp

end Misc

section Conj

variable {E : Type} [AddCommGroup E] [Module K E]

@[expose] def conjE {F : Type} [AddCommGroup F] [Module K F] (θ : E ≃ₗ[K] F) :
    (E ≃ₗ[K] E) ≃* (F ≃ₗ[K] F) where
  toFun g := θ.symm.trans (g.trans θ)
  invFun h := θ.trans (h.trans θ.symm)
  left_inv g := by ext e; simp
  right_inv h := by ext T; simp
  map_mul' g h := by ext T; simp

theorem conjE_apply {F : Type} [AddCommGroup F] [Module K F] (θ : E ≃ₗ[K] F) (g : E ≃ₗ[K] E)
    (x : F) : conjE θ g x = θ (g (θ.symm x)) := rfl

end Conj

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
