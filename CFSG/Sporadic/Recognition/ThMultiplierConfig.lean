module

public import CFSG.GroupTheory.GLnTwoSplitting.OfConj
public import CFSG.LocalAnalysis.SteinbergCCDempwolffBasic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open CFSG.GroupTheory.GLnTwoSplitting CFSG.LocalAnalysis.DempwolffFive Matrix
open scoped commutatorElement

theorem pow_val_add_of_mul_self {G : Type*} [Group G] {v : G} (hv : v * v = 1) (x y : ZMod 2) :
    v ^ (x + y).val = v ^ x.val * v ^ y.val := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  rw [ZMod.val_add]
  generalize x.val = a at *
  generalize y.val = b at *
  interval_cases a <;> interval_cases b <;> simp [hv]

theorem prod_ofFn_add {G : Type*} [Group G] : ∀ (n : ℕ) (v : Fin n → G),
    (∀ i j, v i * v j = v j * v i) → (∀ j, v j ^ 2 = 1) → ∀ a b : Fin n → ZMod 2,
    (List.ofFn fun j => v j ^ (a j + b j).val).prod =
      (List.ofFn fun j => v j ^ (a j).val).prod * (List.ofFn fun j => v j ^ (b j).val).prod
  | 0, _, _, _, _, _ => by simp
  | n + 1, v, hc, hs, a, b => by
    simp only [List.ofFn_succ, List.prod_cons]
    have ih := prod_ofFn_add n (fun i => v i.succ) (fun i j => hc _ _) (fun j => hs _)
      (fun i => a i.succ) (fun i => b i.succ)
    have h0 : v 0 * v 0 = 1 := by rw [← pow_two]; exact hs 0
    have hv := pow_val_add_of_mul_self h0 (a 0) (b 0)
    have hcomm : Commute (List.ofFn fun j : Fin n => v j.succ ^ (a j.succ).val).prod
        (v 0 ^ (b 0).val) := by
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact ((show Commute (v 0) (v j.succ) from hc 0 j.succ).symm.pow_left _).pow_right _
    rw [hv, ih]
    calc v 0 ^ (a 0).val * v 0 ^ (b 0).val *
          ((List.ofFn fun j : Fin n => v j.succ ^ (a j.succ).val).prod *
            (List.ofFn fun j : Fin n => v j.succ ^ (b j.succ).val).prod)
        = v 0 ^ (a 0).val * ((v 0 ^ (b 0).val *
          (List.ofFn fun j : Fin n => v j.succ ^ (a j.succ).val).prod) *
            (List.ofFn fun j : Fin n => v j.succ ^ (b j.succ).val).prod) := by
          simp only [mul_assoc]
      _ = _ := by rw [← hcomm.eq]; simp only [mul_assoc]

@[expose] def iotaG {Γ : Type*} [Group Γ] (v : Fin 5 → Γ) (c : Fin 5 → ZMod 2) : Γ :=
  (List.ofFn fun j => v j ^ (c j).val).prod

structure Config (Γ : Type*) [Group Γ] where
  v : Fin 5 → Γ
  v_sq : ∀ j, v j * v j = 1
  v_comm : ∀ i j, v i * v j = v j * v i
  v_indep : ∀ c : Fin 5 → ZMod 2, c ≠ 0 → iotaG v c ≠ 1
  a : Fin 3 → Γ
  atom : Fin 3 → GL (Fin 5) (ZMod 2)
  a_conj : ∀ k j, a k * v j * (a k)⁻¹ =
    iotaG v (fun i => ((atom k : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j)
  word : Fin 5 → Fin 5 → List (Fin 3 × Bool)
  word_spec : ∀ i j : Fin 5, i ≠ j →
    xg (i, j, 1) = ((word i j).map fun l => if l.2 then (atom l.1)⁻¹ else atom l.1).prod
  Q : Subgroup Γ
  M : Subgroup Γ
  Q_le_M : Q ≤ M
  v_mem_Q : ∀ j, v j ∈ Q
  M_conj_Q : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q
  Q_comm : ∀ q ∈ Q, ∀ g ∈ Q, ⁅q, g⁆ ∈ Subgroup.zpowers (v 0)
  card_Q : Nat.card Q = 512
  cent_M : ∀ g : Γ, g * v 0 = v 0 * g → g ∈ M
  cent_Q : ∀ g ∈ M, (∀ q ∈ Q, q * g = g * q) → g ∈ Subgroup.zpowers (v 0)

namespace Config

variable {Γ : Type*} [Group Γ] (X : Config Γ)

@[expose] def iota (c : Fin 5 → ZMod 2) : Γ := iotaG X.v c

theorem iota_add (a b : Fin 5 → ZMod 2) : X.iota (a + b) = X.iota a * X.iota b :=
  prod_ofFn_add 5 X.v X.v_comm (fun j => by rw [pow_two]; exact X.v_sq j) a b

theorem iota_zero : X.iota 0 = 1 := by
  simp [iota, iotaG]

theorem iota_mul_self (a : Fin 5 → ZMod 2) : X.iota a * X.iota a = 1 := by
  rw [← X.iota_add]
  have : a + a = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  rw [this, X.iota_zero]

theorem iota_inv (a : Fin 5 → ZMod 2) : (X.iota a)⁻¹ = X.iota a :=
  inv_eq_of_mul_eq_one_right (X.iota_mul_self a)

theorem iota_comm (a b : Fin 5 → ZMod 2) : X.iota a * X.iota b = X.iota b * X.iota a := by
  rw [← X.iota_add, ← X.iota_add, add_comm]

theorem iota_injective : Function.Injective X.iota := by
  intro a b hab
  have h1 : X.iota (a + b) = 1 := by
    rw [X.iota_add, hab, X.iota_mul_self]
  by_contra hne
  have h2 : a + b ≠ 0 := by
    intro h
    apply hne
    funext i
    have := congrFun h i
    exact CharTwo.add_eq_zero.1 this
  exact X.v_indep _ h2 h1

theorem iota_single (j : Fin 5) : X.iota (Pi.single j 1) = X.v j := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  have h0 : (0 : ZMod 2).val = 0 := rfl
  fin_cases j <;> simp [iota, iotaG, List.ofFn_succ, Pi.single_apply, h1, h0]

@[expose] def Vsub : Subgroup Γ where
  carrier := Set.range X.iota
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, X.iota_add a b⟩
  one_mem' := ⟨0, X.iota_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (X.iota_inv a).symm⟩

theorem iota_mem_Vsub (c : Fin 5 → ZMod 2) : X.iota c ∈ X.Vsub := ⟨c, rfl⟩

theorem v_mem_Vsub (j : Fin 5) : X.v j ∈ X.Vsub := by
  rw [← X.iota_single]
  exact X.iota_mem_Vsub _

instance : Finite X.Vsub := (Set.finite_range X.iota).to_subtype

theorem card_Vsub : Nat.card X.Vsub = 32 := by
  have h1 : Nat.card X.Vsub = Nat.card (Fin 5 → ZMod 2) :=
    Nat.card_range_of_injective X.iota_injective
  rw [h1]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem conj_mem_Vsub {A : Γ} (hA : ∀ j, A * X.v j * A⁻¹ ∈ X.Vsub) {g : Γ} (hg : g ∈ X.Vsub) :
    A * g * A⁻¹ ∈ X.Vsub := by
  obtain ⟨c, rfl⟩ := hg
  have h := map_list_prod (MulAut.conj A) (List.ofFn fun j => X.v j ^ (c j).val)
  simp only [MulAut.conj_apply] at h
  unfold iota iotaG
  rw [h]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
  have := Subgroup.pow_mem X.Vsub (hA j) (c j).val
  simpa [MulAut.conj_apply, map_pow] using this

theorem mem_normalizer_of_conj {A : Γ} (hA : ∀ j, A * X.v j * A⁻¹ ∈ X.Vsub) :
    A ∈ Subgroup.normalizer (X.Vsub : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => X.conj_mem_Vsub hA hh, fun hh => ?_⟩
  let f : X.Vsub → X.Vsub := fun v => ⟨A * v * A⁻¹, X.conj_mem_Vsub hA v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have := congrArg Subtype.val hvw
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 hf) ⟨A * h * A⁻¹, hh⟩
  have := congrArg Subtype.val hv
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact v.2

@[expose] def Hsub : Subgroup Γ := Subgroup.normalizer (X.Vsub : Set Γ)

theorem Vsub_le_Hsub : X.Vsub ≤ X.Hsub := Subgroup.le_normalizer

@[expose] def iotaH (c : Fin 5 → ZMod 2) : X.Hsub :=
  ⟨X.iota c, X.Vsub_le_Hsub (X.iota_mem_Vsub c)⟩

theorem iotaH_add (a b : Fin 5 → ZMod 2) : X.iotaH (a + b) = X.iotaH a * X.iotaH b :=
  Subtype.ext (X.iota_add a b)

theorem iotaH_injective : Function.Injective X.iotaH := fun _ _ h =>
  X.iota_injective (congrArg Subtype.val h)

theorem iotaH_norm (g : X.Hsub) (c : Fin 5 → ZMod 2) :
    ∃ c', g * X.iotaH c * g⁻¹ = X.iotaH c' := by
  have h := (Subgroup.mem_normalizer_iff.1 g.2 (X.iota c)).1 (X.iota_mem_Vsub c)
  obtain ⟨c', hc'⟩ := h
  exact ⟨c', Subtype.ext hc'.symm⟩

@[expose] noncomputable def actV :
    X.Hsub →* ((Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2)) :=
  embConjHom X.iotaH X.iotaH_add X.iotaH_injective X.iotaH_norm

theorem actV_spec (g : X.Hsub) (c : Fin 5 → ZMod 2) :
    g * X.iotaH c * g⁻¹ = X.iotaH (X.actV g c) :=
  conj_embConjHom X.iotaH X.iotaH_add X.iotaH_injective X.iotaH_norm g c

end Config

end CFSG.Sporadic.Recognition.ThMultiplier
