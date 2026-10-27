module

public import CFSG.Quasithin.Background.G2SL2
public import CFSG.Quasithin.Background.G2Omega4PlusModel
public import Mathlib.GroupTheory.Nilpotent

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

theorem sl2_conj_ne_aux : ∀ τ γ : SL(2, ZMod 2),
    τ * τ ≠ 1 ∨ τ = 1 ∨ γ ^ 3 ≠ 1 ∨ γ = 1 ∨ γ * τ * γ⁻¹ ≠ τ := by
  decide +kernel

theorem sl2_cube_aux : ∀ γ : SL(2, ZMod 2),
    γ ^ 3 ≠ 1 ∨ γ = 1 ∨ γ = c3 (ZMod 2) ∨ γ = c3 (ZMod 2) * c3 (ZMod 2) := by
  decide +kernel

theorem sl2_two_invol_words_aux : ∀ τ τ' C : SL(2, ZMod 2),
    τ * τ ≠ 1 ∨ τ' * τ' ≠ 1 ∨ τ = 1 ∨ τ' = 1 ∨ τ = τ' ∨
      C ∈ [1, τ, τ', τ * τ', τ' * τ, τ * τ' * τ] := by
  decide +kernel

theorem sl2_gen_c3_e12 : ∀ C : SL(2, ZMod 2),
    C ∈ [1, c3 (ZMod 2), c3 (ZMod 2) * c3 (ZMod 2), e12 (1 : ZMod 2),
      c3 (ZMod 2) * e12 (1 : ZMod 2), c3 (ZMod 2) * c3 (ZMod 2) * e12 (1 : ZMod 2)] := by
  decide +kernel

theorem sl2_e12_c3 : e12 (1 : ZMod 2) * c3 (ZMod 2) = c3 (ZMod 2) * c3 (ZMod 2) * e12 (1 : ZMod 2) := by
  decide +kernel

theorem sl2_exists_invol_fix : ∀ a : Fin 2 → ZMod 2, a = 0 ∨
    ∃ τ : SL(2, ZMod 2), τ * τ = 1 ∧ τ ≠ 1 ∧ τ • a = a := by
  decide +kernel

theorem rep_mul_apply {Γ X : Type*} [Group Γ] [AddCommGroup X] (ρ : Γ →* AddMonoid.End X)
    (g h : Γ) (x : X) : ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul]
  rfl

theorem rep_one_apply {Γ X : Type*} [Group Γ] [AddCommGroup X] (ρ : Γ →* AddMonoid.End X)
    (x : X) : ρ 1 x = x := by
  rw [map_one]
  rfl

theorem rep_inv_apply {Γ X : Type*} [Group Γ] [AddCommGroup X] (ρ : Γ →* AddMonoid.End X)
    (g : Γ) (x : X) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rep_mul_apply, inv_mul_cancel, rep_one_apply]

@[expose] noncomputable def restrictHom {Γ X : Type*} [Group Γ] [AddCommGroup X]
    (ρ : Γ →* AddMonoid.End X) (Y : AddSubgroup X) (hY : ∀ g : Γ, ∀ x ∈ Y, ρ g x ∈ Y) :
    Γ →* AddMonoid.End ↥Y where
  toFun g :=
    { toFun := fun y => ⟨ρ g y, hY g y y.2⟩
      map_zero' := Subtype.ext (map_zero (ρ g))
      map_add' := fun a b => Subtype.ext (map_add (ρ g) (a : X) (b : X)) }
  map_one' := by
    apply AddMonoidHom.ext
    intro y
    apply Subtype.ext
    exact rep_one_apply ρ y
  map_mul' := fun g h => by
    apply AddMonoidHom.ext
    intro y
    apply Subtype.ext
    exact rep_mul_apply ρ g h y

theorem natural_sum_of_fpf {Y : Type*} [AddCommGroup Y] [Finite Y] (h2 : ∀ y : Y, y + y = 0)
    (ρ : SL(2, ZMod 2) →* AddMonoid.End Y) (hfpf : ∀ y : Y, ρ (c3 (ZMod 2)) y = y → y = 0) :
    ∃ (s : ℕ) (e : Y ≃+ (Fin s → Fin 2 → ZMod 2)), ∀ (A : SL(2, ZMod 2)) (y : Y),
      e (ρ A y) = fun j => A • e y j := by
  set c := ρ (c3 (ZMod 2)) with hc
  set u := ρ (e12 (1 : ZMod 2)) with hu
  have hc3 : ∀ y, c (c (c y)) = y := by
    intro y
    have h : ρ (c3 (ZMod 2) * c3 (ZMod 2) * c3 (ZMod 2)) y = y := by
      have : c3 (ZMod 2) * c3 (ZMod 2) * c3 (ZMod 2) = 1 := by
        simpa [pow_succ] using c3_pow_three (F := ZMod 2)
      rw [this, rep_one_apply]
    rwa [rep_mul_apply, rep_mul_apply] at h
  have hu2 : ∀ y, u (u y) = y := by
    intro y
    have h : ρ (e12 (1 : ZMod 2) * e12 1) y = y := by
      rw [e12_mul_self, rep_one_apply]
    rwa [rep_mul_apply] at h
  have huc : ∀ y, u (c y) = c (c (u y)) := by
    intro y
    have h := congrArg (fun A => ρ A y) sl2_e12_c3
    simp only [rep_mul_apply] at h
    exact h
  have hN : ∀ y, y + c y + c (c y) = 0 := by
    intro y
    apply hfpf
    rw [map_add, map_add, hc3 y]
    abel
  have hcb : ∀ y, c y + c (c y) = y := by
    intro y
    linear_combination (norm := abel1) (hN y) - (h2 y)
  let C : AddSubgroup Y :=
    { carrier := {y | u y = y}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_neg, ha] }
  have hb : ∀ y, u (y + u y) = y + u y := by
    intro y
    rw [map_add, hu2]
    abel
  have ha : ∀ y, u (y + c (y + u y)) = y + c (y + u y) := by
    intro y
    have h1 : u (c (y + u y)) = c (c (y + u y)) := by rw [huc, hb]
    rw [map_add, h1]
    linear_combination (norm := abel1) -(hcb (y + u y)) + (h2 (c (c (y + u y)))) - (h2 y)
  have hbc : ∀ y, c y + u (c y) = (y + c (y + u y)) + (y + u y) := by
    intro y
    simp only [map_add, huc]
    linear_combination (norm := abel1) (hN (u y)) - (h2 (u y)) - (h2 (c (u y))) - (h2 y)
  have hac : ∀ y, c y + c (c y + u (c y)) = y + u y := by
    intro y
    simp only [map_add, huc, hc3]
    linear_combination (norm := abel1) (hcb y)
  have hau : ∀ y, u y + c (u y + u (u y)) = (y + c (y + u y)) + (y + u y) := by
    intro y
    simp only [map_add, hu2]
    linear_combination (norm := abel1) -(h2 y)
  let Φ : Y ≃+ C × C :=
    { toFun := fun y => (⟨y + c (y + u y), ha y⟩, ⟨y + u y, hb y⟩)
      invFun := fun p => (p.1 : Y) + c (p.2 : Y)
      left_inv := fun y => by
        show y + c (y + u y) + c (y + u y) = y
        linear_combination (norm := abel1) (h2 (c (y + u y)))
      right_inv := by
        rintro ⟨⟨a, haC⟩, ⟨b, hbC⟩⟩
        have hua : u a = a := haC
        have hub : u b = b := hbC
        have huy : u (a + c b) = a + c (c b) := by rw [map_add, hua, huc, hub]
        have hyb : (a + c b) + u (a + c b) = b := by
          rw [huy]
          linear_combination (norm := abel1) (h2 a) + (hcb b)
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show (a + c b) + c ((a + c b) + u (a + c b)) = a
          rw [hyb]
          linear_combination (norm := abel1) (h2 (c b))
        · exact hyb
      map_add' := fun y y' => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show (y + y') + c ((y + y') + u (y + y')) = (y + c (y + u y)) + (y' + c (y' + u y'))
          simp only [map_add]
          abel
        · show (y + y') + u (y + y') = (y + u y) + (y' + u y')
          simp only [map_add]
          abel }
  have h2C : ∀ x : C, 2 • x = 0 := by
    intro x
    apply Subtype.ext
    simpa [two_nsmul] using h2 (x : Y)
  let _inst : Module (ZMod 2) C := AddCommGroup.zmodModule h2C
  have _inst2 : Module.Finite (ZMod 2) C := Module.Finite.of_finite
  let ι : C ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) C) → ZMod 2) :=
    (Module.finBasis (ZMod 2) C).equivFun
  let pairEquiv : (Fin (Module.finrank (ZMod 2) C) → ZMod 2) × (Fin (Module.finrank (ZMod 2) C) → ZMod 2) ≃+
      (Fin (Module.finrank (ZMod 2) C) → Fin 2 → ZMod 2) :=
    { toFun := fun p j => ![p.1 j, p.2 j]
      invFun := fun f => (fun j => f j 0, fun j => f j 1)
      left_inv := fun p => by ext j <;> simp
      right_inv := fun f => by
        funext j i
        fin_cases i <;> rfl
      map_add' := fun p q => by
        funext j i
        fin_cases i <;> simp }
  let e : Y ≃+ (Fin (Module.finrank (ZMod 2) C) → Fin 2 → ZMod 2) :=
    Φ.trans ((ι.toAddEquiv.prodCongr ι.toAddEquiv).trans pairEquiv)
  have he : ∀ y j, e y j = ![ι ⟨y + c (y + u y), ha y⟩ j, ι ⟨y + u y, hb y⟩ j] := fun y j => rfl
  refine ⟨_, e, ?_⟩
  have hec : ∀ y, e (c y) = fun j => c3 (ZMod 2) • e y j := by
    intro y
    funext j
    rw [he, he, c3_smul]
    have h1 : (⟨c y + c (c y + u (c y)), ha (c y)⟩ : C) = ⟨y + u y, hb y⟩ := Subtype.ext (hac y)
    have h2' : (⟨c y + u (c y), hb (c y)⟩ : C) =
        ⟨y + c (y + u y), ha y⟩ + ⟨y + u y, hb y⟩ := Subtype.ext (hbc y)
    rw [h1, h2', map_add]
    ext i
    fin_cases i <;> simp
  have heu : ∀ y, e (u y) = fun j => e12 (1 : ZMod 2) • e y j := by
    intro y
    funext j
    rw [he, he, e12_smul]
    have h1 : (⟨u y + c (u y + u (u y)), ha (u y)⟩ : C) =
        ⟨y + c (y + u y), ha y⟩ + ⟨y + u y, hb y⟩ := Subtype.ext (hau y)
    have h2' : (⟨u y + u (u y), hb (u y)⟩ : C) = ⟨y + u y, hb y⟩ :=
      Subtype.ext (by simp only [hu2]; abel)
    rw [h1, h2', map_add]
    ext i
    fin_cases i <;> simp
  let J : Subgroup SL(2, ZMod 2) :=
    { carrier := {A | ∀ y, e (ρ A y) = fun j => A • e y j}
      mul_mem' := fun {A B} hA hB y => by
        have hA' : ∀ y, e (ρ A y) = fun j => A • e y j := hA
        have hB' : ∀ y, e (ρ B y) = fun j => B • e y j := hB
        show e (ρ (A * B) y) = fun j => (A * B) • e y j
        rw [rep_mul_apply, hA', hB']
        funext j
        exact (mul_smul A B _).symm
      one_mem' := fun y => by
        show e (ρ 1 y) = fun j => (1 : SL(2, ZMod 2)) • e y j
        rw [rep_one_apply]
        funext j
        exact (one_smul _ _).symm
      inv_mem' := fun {A} hA y => by
        have hA' : ∀ y, e (ρ A y) = fun j => A • e y j := hA
        show e (ρ A⁻¹ y) = fun j => A⁻¹ • e y j
        have h1 := hA' (ρ A⁻¹ y)
        rw [← rep_mul_apply, mul_inv_cancel, rep_one_apply] at h1
        funext j
        have h2 := congrFun h1 j
        rw [h2, inv_smul_smul] }
  have hcJ : c3 (ZMod 2) ∈ J := fun y => hec y
  have heJ : e12 (1 : ZMod 2) ∈ J := fun y => heu y
  intro A y
  have hAJ : A ∈ J := by
    have hw := sl2_gen_c3_e12 A
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact J.one_mem
    · exact hcJ
    · exact J.mul_mem hcJ hcJ
    · exact heJ
    · exact J.mul_mem hcJ heJ
    · exact J.mul_mem (J.mul_mem hcJ hcJ) heJ
  exact hAJ y

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

theorem OmG_comm_cc : ∀ g : OmG,
    (g * ((c3 (ZMod 2), 1) : OmG) = (c3 (ZMod 2), 1) * g ∧
      g * ((c3 (ZMod 2), 1) * (c3 (ZMod 2), 1) : OmG) = (c3 (ZMod 2), 1) * (c3 (ZMod 2), 1) * g) ∨
    (g * ((c3 (ZMod 2), 1) : OmG) = (c3 (ZMod 2), 1) * (c3 (ZMod 2), 1) * g ∧
      g * ((c3 (ZMod 2), 1) * (c3 (ZMod 2), 1) : OmG) = (c3 (ZMod 2), 1) * g) := by
  decide +kernel

theorem OmG_comm_dd : ∀ g : OmG,
    (g * ((1, c3 (ZMod 2)) : OmG) = (1, c3 (ZMod 2)) * g ∧
      g * ((1, c3 (ZMod 2)) * (1, c3 (ZMod 2)) : OmG) = (1, c3 (ZMod 2)) * (1, c3 (ZMod 2)) * g) ∨
    (g * ((1, c3 (ZMod 2)) : OmG) = (1, c3 (ZMod 2)) * (1, c3 (ZMod 2)) * g ∧
      g * ((1, c3 (ZMod 2)) * (1, c3 (ZMod 2)) : OmG) = (1, c3 (ZMod 2)) * g) := by
  decide +kernel

theorem OmG_cc_cube : ((c3 (ZMod 2), 1) : OmG) * (c3 (ZMod 2), 1) * (c3 (ZMod 2), 1) = 1 := by
  decide +kernel

theorem OmG_invol_cc_aux : ∀ τ : SL(2, ZMod 2), τ * τ ≠ 1 ∨ τ = 1 ∨
    ((τ, 1) : OmG) * (c3 (ZMod 2), 1) = (c3 (ZMod 2), 1) * (c3 (ZMod 2), 1) * (τ, 1) := by
  decide +kernel

theorem left_mem_of_two_invol {J : Subgroup OmG} {τ τ' : SL(2, ZMod 2)} (h1 : τ * τ = 1)
    (h1' : τ' * τ' = 1) (h2 : τ ≠ 1) (h2' : τ' ≠ 1) (h3 : τ ≠ τ') (hJ : (τ, 1) ∈ J)
    (hJ' : (τ', 1) ∈ J) (C : SL(2, ZMod 2)) : (C, 1) ∈ J := by
  have hw := sl2_two_invol_words_aux τ τ' C
  have hm : ∀ x y : SL(2, ZMod 2), (x * y, (1 : SL(2, ZMod 2))) = (x, 1) * (y, 1) := by
    intro x y; simp
  rcases hw with h | h | h | h | h | hC
  · exact absurd h1 h
  · exact absurd h1' h
  · exact absurd h h2
  · exact absurd h h2'
  · exact absurd h h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · exact J.one_mem
  · exact hJ
  · exact hJ'
  · rw [hm]; exact J.mul_mem hJ hJ'
  · rw [hm]; exact J.mul_mem hJ' hJ
  · rw [hm, hm]; exact J.mul_mem (J.mul_mem hJ hJ') hJ

theorem right_mem_of_two_invol {J : Subgroup OmG} {τ τ' : SL(2, ZMod 2)} (h1 : τ * τ = 1)
    (h1' : τ' * τ' = 1) (h2 : τ ≠ 1) (h2' : τ' ≠ 1) (h3 : τ ≠ τ') (hJ : (1, τ) ∈ J)
    (hJ' : (1, τ') ∈ J) (C : SL(2, ZMod 2)) : (1, C) ∈ J := by
  have hw := sl2_two_invol_words_aux τ τ' C
  have hm : ∀ x y : SL(2, ZMod 2), ((1 : SL(2, ZMod 2)), x * y) = (1, x) * (1, y) := by
    intro x y; simp
  rcases hw with h | h | h | h | h | hC
  · exact absurd h1 h
  · exact absurd h1' h
  · exact absurd h h2
  · exact absurd h h2'
  · exact absurd h h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · exact J.one_mem
  · exact hJ
  · exact hJ'
  · rw [hm]; exact J.mul_mem hJ hJ'
  · rw [hm]; exact J.mul_mem hJ' hJ
  · rw [hm, hm]; exact J.mul_mem (J.mul_mem hJ hJ') hJ

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

abbrev cc : OmG := (c3 (ZMod 2), 1)

abbrev dd : OmG := (1, c3 (ZMod 2))

section ModuleAlgebra

variable {X : Type*} [AddCommGroup X]

@[expose] def Nc (ρ : OmG →* AddMonoid.End X) (x : X) : X := x + ρ cc x + ρ (cc * cc) x

variable (ρ : OmG →* AddMonoid.End X)

theorem cc_cube_apply (x : X) : ρ cc (ρ cc (ρ cc x)) = x := by
  have h := congrArg (fun g => ρ g x) OmG_cc_cube
  simp only [rep_mul_apply, rep_one_apply] at h
  exact h

theorem Nc_add (x y : X) : Nc ρ (x + y) = Nc ρ x + Nc ρ y := by
  simp only [Nc, map_add]
  abel

theorem Nc_fixed (x : X) : ρ cc (Nc ρ x) = Nc ρ x := by
  simp only [Nc, map_add, rep_mul_apply, cc_cube_apply]
  abel

theorem Nc_comm (g : OmG) (x : X) : Nc ρ (ρ g x) = ρ g (Nc ρ x) := by
  rcases OmG_comm_cc g with ⟨h, h'⟩ | ⟨h, h'⟩
  · have h1 : ρ g (ρ cc x) = ρ cc (ρ g x) := by
      rw [← rep_mul_apply, ← rep_mul_apply, h]
    have h2 : ρ g (ρ (cc * cc) x) = ρ (cc * cc) (ρ g x) := by
      rw [← rep_mul_apply, ← rep_mul_apply, h']
    simp only [Nc, map_add, h1, h2]
  · have h1 : ρ g (ρ cc x) = ρ (cc * cc) (ρ g x) := by
      rw [← rep_mul_apply, ← rep_mul_apply, h]
    have h2 : ρ g (ρ (cc * cc) x) = ρ cc (ρ g x) := by
      rw [← rep_mul_apply, ← rep_mul_apply, h']
    simp only [Nc, map_add, h1, h2]
    abel

theorem fixed_inv {z : X} (hc : ρ cc z = z) (hd : ρ dd z = z) (g : OmG) :
    ρ cc (ρ g z) = ρ g z ∧ ρ dd (ρ g z) = ρ g z := by
  constructor
  · rcases OmG_comm_cc g with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [← rep_mul_apply, ← h, rep_mul_apply, hc]
    · rw [← rep_mul_apply, ← h', rep_mul_apply, rep_mul_apply, hc, hc]
  · rcases OmG_comm_dd g with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [← rep_mul_apply, ← h, rep_mul_apply, hd]
    · rw [← rep_mul_apply, ← h', rep_mul_apply, rep_mul_apply, hd, hd]

end ModuleAlgebra

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section ModuleDecomp

variable {X : Type*} [AddCommGroup X]

structure ModHyp (ρ : OmG →* AddMonoid.End X) (τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2))
    (W₀ : AddSubgroup X) : Prop where
  h2 : ∀ x : X, x + x = 0
  τ₁_sq : τ₁ * τ₁ = 1
  τ₁_ne : τ₁ ≠ 1
  τ₂_sq : τ₂ * τ₂ = 1
  τ₂_ne : τ₂ ≠ 1
  γ₁_cube : γ₁ ^ 3 = 1
  γ₁_ne : γ₁ ≠ 1
  γ₂_cube : γ₂ ^ 3 = 1
  γ₂_ne : γ₂ ≠ 1
  q₁ : ∀ x, ρ (τ₁, 1) x + x ∈ W₀
  q₂ : ∀ x, ρ (1, τ₂) x + x ∈ W₀
  f₁ : ∀ w ∈ W₀, ρ (τ₁, 1) w = w
  f₂ : ∀ w ∈ W₀, ρ (1, τ₂) w = w
  sum : ∀ x, ∃ w₀ ∈ W₀, ∃ w₁ ∈ W₀, x = w₀ + ρ (γ₁, γ₂)⁻¹ w₁
  cap : ∀ w₁ ∈ W₀, ρ (γ₁, γ₂)⁻¹ w₁ ∈ W₀ → ρ (γ₁, γ₂)⁻¹ w₁ = 0

namespace ModHyp

variable {ρ : OmG →* AddMonoid.End X} {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {W₀ : AddSubgroup X}
  (H : ModHyp ρ τ₁ τ₂ γ₁ γ₂ W₀)

include H

theorem eq_of_add_eq_zero {a b : X} (h : a + b = 0) : a = b := by
  linear_combination (norm := abel1) h - (H.h2 b)

theorem fixed_gamma {z : X} (hc : ρ cc z = z) (hd : ρ dd z = z) : ρ (γ₁, γ₂) z = z := by
  have e : ((γ₁, γ₂) : OmG) = ((γ₁, 1) : OmG) * (1, γ₂) := by simp
  have h1 : ρ ((γ₁, 1) : OmG) z = z := by
    rcases sl2_cube_aux γ₁ with h | h | h | h
    · exact absurd H.γ₁_cube h
    · exact absurd h H.γ₁_ne
    · rw [h]; exact hc
    · rw [h]
      have : ((c3 (ZMod 2) * c3 (ZMod 2), 1) : OmG) = cc * cc := by simp
      rw [this, rep_mul_apply, hc, hc]
  have h2 : ρ ((1, γ₂) : OmG) z = z := by
    rcases sl2_cube_aux γ₂ with h | h | h | h
    · exact absurd H.γ₂_cube h
    · exact absurd h H.γ₂_ne
    · rw [h]; exact hd
    · rw [h]
      have : ((1, c3 (ZMod 2) * c3 (ZMod 2)) : OmG) = dd * dd := by simp
      rw [this, rep_mul_apply, hd, hd]
  rw [e, rep_mul_apply, h2, h1]

theorem cap_fixed {w : X} (hw : w ∈ W₀) (hf : ρ (γ₁, γ₂) w = w) : w = 0 := by
  have h1 : ρ (γ₁, γ₂)⁻¹ w = w := by
    have := rep_inv_apply ρ (γ₁, γ₂) w
    rwa [hf] at this
  have := H.cap w hw
  rw [h1] at this
  exact this hw

end ModHyp

end ModuleDecomp

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section ModuleDecomp2

variable {X : Type*} [AddCommGroup X]

theorem rep_apply_inv (ρ : OmG →* AddMonoid.End X) (g : OmG) (x : X) : ρ g (ρ g⁻¹ x) = x := by
  have := rep_inv_apply ρ g⁻¹ x
  rwa [inv_inv] at this

@[expose] def stabSub (ρ : OmG →* AddMonoid.End X) (w : X) : Subgroup OmG where
  carrier := {g | ρ g w = w}
  mul_mem' := fun {g h} hg hh => by
    show ρ (g * h) w = w
    rw [rep_mul_apply, show ρ h w = w from hh]
    exact hg
  one_mem' := rep_one_apply ρ w
  inv_mem' := fun {g} hg => by
    show ρ g⁻¹ w = w
    have := rep_inv_apply ρ g w
    rwa [show ρ g w = w from hg] at this

omit [AddCommGroup X] in
theorem conj_invol_ne (τ γ : SL(2, ZMod 2)) (hτ : τ * τ = 1) (hτ' : τ ≠ 1) (hγ : γ ^ 3 = 1)
    (hγ' : γ ≠ 1) : γ * τ * γ⁻¹ ≠ τ := by
  rcases sl2_conj_ne_aux τ γ with h | h | h | h | h
  · exact absurd hτ h
  · exact absurd h hτ'
  · exact absurd hγ h
  · exact absurd h hγ'
  · exact h

omit [AddCommGroup X] in
theorem conj_invol_sq (τ γ : SL(2, ZMod 2)) (hτ : τ * τ = 1) :
    (γ * τ * γ⁻¹) * (γ * τ * γ⁻¹) = 1 := by
  rw [show γ * τ * γ⁻¹ * (γ * τ * γ⁻¹) = γ * (τ * τ) * γ⁻¹ by group, hτ]
  simp

omit [AddCommGroup X] in
theorem conj_invol_ne_one (τ γ : SL(2, ZMod 2)) (hτ' : τ ≠ 1) : γ * τ * γ⁻¹ ≠ 1 := by
  intro h
  apply hτ'
  have : τ = γ⁻¹ * (γ * τ * γ⁻¹) * γ := by group
  rw [this, h]
  group

namespace ModHyp

variable {ρ : OmG →* AddMonoid.End X} {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {W₀ : AddSubgroup X}
  (H : ModHyp ρ τ₁ τ₂ γ₁ γ₂ W₀)

include H

theorem fixed_E {z : X} (hc : ρ cc z = z) (hd : ρ dd z = z) :
    ρ (τ₁, 1) z = z ∧ ρ (1, τ₂) z = z := by
  have key : ∀ g : OmG, (ρ g z + z ∈ W₀) → ρ g z = z := by
    intro g hg
    have hfix := fixed_inv ρ hc hd g
    have h1 : ρ cc (ρ g z + z) = ρ g z + z := by rw [map_add, hfix.1, hc]
    have h2 : ρ dd (ρ g z + z) = ρ g z + z := by rw [map_add, hfix.2, hd]
    have h3 := H.cap_fixed hg (H.fixed_gamma h1 h2)
    exact H.eq_of_add_eq_zero h3
  exact ⟨key _ (H.q₁ z), key _ (H.q₂ z)⟩

theorem fixed_E_part {w : X} (hw : w ∈ W₀) (hb1 : ρ (τ₁, 1) (ρ (γ₁, γ₂)⁻¹ w) = ρ (γ₁, γ₂)⁻¹ w)
    (hb2 : ρ (1, τ₂) (ρ (γ₁, γ₂)⁻¹ w) = ρ (γ₁, γ₂)⁻¹ w) : ρ (γ₁, γ₂)⁻¹ w = 0 := by
  have hJ1 : ((τ₁, 1) : OmG) ∈ stabSub ρ w := H.f₁ w hw
  have hJ2 : ((1, τ₂) : OmG) ∈ stabSub ρ w := H.f₂ w hw
  have hJ1' : ((γ₁ * τ₁ * γ₁⁻¹, 1) : OmG) ∈ stabSub ρ w := by
    show ρ _ w = w
    have e : ((γ₁ * τ₁ * γ₁⁻¹, 1) : OmG) = (γ₁, γ₂) * (τ₁, 1) * (γ₁, γ₂)⁻¹ := by simp
    rw [e, rep_mul_apply, rep_mul_apply, hb1, rep_apply_inv]
  have hJ2' : ((1, γ₂ * τ₂ * γ₂⁻¹) : OmG) ∈ stabSub ρ w := by
    show ρ _ w = w
    have e : ((1, γ₂ * τ₂ * γ₂⁻¹) : OmG) = (γ₁, γ₂) * (1, τ₂) * (γ₁, γ₂)⁻¹ := by simp
    rw [e, rep_mul_apply, rep_mul_apply, hb2, rep_apply_inv]
  have hall1 := left_mem_of_two_invol H.τ₁_sq (conj_invol_sq τ₁ γ₁ H.τ₁_sq) H.τ₁_ne
    (conj_invol_ne_one τ₁ γ₁ H.τ₁_ne)
    (fun h => conj_invol_ne τ₁ γ₁ H.τ₁_sq H.τ₁_ne H.γ₁_cube H.γ₁_ne h.symm) hJ1 hJ1'
  have hall2 := right_mem_of_two_invol H.τ₂_sq (conj_invol_sq τ₂ γ₂ H.τ₂_sq) H.τ₂_ne
    (conj_invol_ne_one τ₂ γ₂ H.τ₂_ne)
    (fun h => conj_invol_ne τ₂ γ₂ H.τ₂_sq H.τ₂_ne H.γ₂_cube H.γ₂_ne h.symm) hJ2 hJ2'
  have hc : ρ cc w = w := hall1 (c3 (ZMod 2))
  have hd : ρ dd w = w := hall2 (c3 (ZMod 2))
  have h0 := H.cap_fixed hw (H.fixed_gamma hc hd)
  rw [h0, map_zero]

theorem fixed_Lambda_zero {z : X} (hc : ρ cc z = z) (hd : ρ dd z = z) : z = 0 := by
  obtain ⟨hu1, hu2⟩ := H.fixed_E hc hd
  obtain ⟨w₀, hw₀, w₁, hw₁, hz⟩ := H.sum z
  have hbz : ρ (γ₁, γ₂)⁻¹ w₁ = z + w₀ := by
    linear_combination (norm := abel1) -hz - (H.h2 w₀)
  have hb1 : ρ (τ₁, 1) (ρ (γ₁, γ₂)⁻¹ w₁) = ρ (γ₁, γ₂)⁻¹ w₁ := by
    rw [hbz, map_add, hu1, H.f₁ w₀ hw₀]
  have hb2 : ρ (1, τ₂) (ρ (γ₁, γ₂)⁻¹ w₁) = ρ (γ₁, γ₂)⁻¹ w₁ := by
    rw [hbz, map_add, hu2, H.f₂ w₀ hw₀]
  have h0 := H.fixed_E_part hw₁ hb1 hb2
  have hzw : z = w₀ := by rw [hz, h0, add_zero]
  exact H.cap_fixed (hzw ▸ hw₀) (H.fixed_gamma hc hd)

end ModHyp

end ModuleDecomp2

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section ModuleDecomp3

variable {X : Type*} [AddCommGroup X]

@[expose] def NcHom (ρ : OmG →* AddMonoid.End X) : X →+ X where
  toFun := Nc ρ
  map_zero' := by simp [Nc]
  map_add' := Nc_add ρ

@[expose] def X₁ (ρ : OmG →* AddMonoid.End X) : AddSubgroup X := AddMonoidHom.ker (NcHom ρ)

theorem mem_X₁ {ρ : OmG →* AddMonoid.End X} {x : X} : x ∈ X₁ ρ ↔ Nc ρ x = 0 := Iff.rfl

variable (ρ : OmG →* AddMonoid.End X)

theorem X₁_inv {x : X} (hx : x ∈ X₁ ρ) (g : OmG) : ρ g x ∈ X₁ ρ := by
  rw [mem_X₁] at hx ⊢
  rw [Nc_comm, hx, map_zero]

theorem X₁_fixed_zero (h2 : ∀ x : X, x + x = 0) {x : X} (hx : x ∈ X₁ ρ) (hf : ρ cc x = x) :
    x = 0 := by
  have h1 : ρ (cc * cc) x = x := by rw [rep_mul_apply, hf, hf]
  have h := mem_X₁.1 hx
  simp only [Nc] at h
  rw [hf, h1, h2 x, zero_add] at h
  exact h

theorem Nc_decomp (h2 : ∀ x : X, x + x = 0) (x : X) :
    x = Nc ρ x + (ρ cc x + ρ (cc * cc) x) := by
  simp only [Nc]
  linear_combination (norm := abel1) -(h2 (ρ cc x)) - (h2 (ρ (cc * cc) x))

theorem Nc_comp_mem (h2 : ∀ x : X, x + x = 0) (x : X) :
    ρ cc x + ρ (cc * cc) x ∈ X₁ ρ := by
  rw [mem_X₁, Nc_add, Nc_comm, Nc_comm, Nc_fixed ρ, rep_mul_apply, Nc_fixed ρ, Nc_fixed ρ]
  exact h2 _

theorem X₁_cc_cc (h2 : ∀ x : X, x + x = 0) {x : X} (hx : x ∈ X₁ ρ) :
    ρ cc (ρ cc x) + ρ cc x = x := by
  have h := mem_X₁.1 hx
  simp only [Nc, rep_mul_apply] at h
  linear_combination (norm := abel1) h - (h2 x)

end ModuleDecomp3

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section ModuleDecomp4

variable {X : Type*} [AddCommGroup X]

@[expose] def swapHom : OmG →* OmG := (MulEquiv.prodComm (M := SL(2, ZMod 2)) (N := SL(2, ZMod 2))).toMonoidHom

namespace ModHyp

theorem swap {ρ : OmG →* AddMonoid.End X} {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {W₀ : AddSubgroup X}
    (H : ModHyp ρ τ₁ τ₂ γ₁ γ₂ W₀) : ModHyp (ρ.comp swapHom) τ₂ τ₁ γ₂ γ₁ W₀ where
  h2 := H.h2
  τ₁_sq := H.τ₂_sq
  τ₁_ne := H.τ₂_ne
  τ₂_sq := H.τ₁_sq
  τ₂_ne := H.τ₁_ne
  γ₁_cube := H.γ₂_cube
  γ₁_ne := H.γ₂_ne
  γ₂_cube := H.γ₁_cube
  γ₂_ne := H.γ₁_ne
  q₁ := H.q₂
  q₂ := H.q₁
  f₁ := H.f₂
  f₂ := H.f₁
  sum := fun x => by
    obtain ⟨w₀, hw₀, w₁, hw₁, hx⟩ := H.sum x
    exact ⟨w₀, hw₀, w₁, hw₁, hx⟩
  cap := fun w₁ hw₁ => H.cap w₁ hw₁

variable {ρ : OmG →* AddMonoid.End X} {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {W₀ : AddSubgroup X}
  (H : ModHyp ρ τ₁ τ₂ γ₁ γ₂ W₀)

include H

theorem u₂_fixed {x : X} (hx : x ∈ X₁ ρ) : ρ (1, τ₂) x = x := by
  have hNx := mem_X₁.1 hx
  have hu2' : ∀ y, ρ (τ₁, 1) (ρ (τ₁, 1) y) = y := by
    intro y
    have h := congrArg (fun g => ρ g y) (show ((τ₁, 1) : OmG) * (τ₁, 1) = 1 by simp [H.τ₁_sq])
    simp only [rep_mul_apply, rep_one_apply] at h
    exact h
  have huc : ∀ y, ρ (τ₁, 1) (ρ cc y) = ρ cc (ρ cc (ρ (τ₁, 1) y)) := by
    intro y
    rcases OmG_invol_cc_aux τ₁ with h | h | h
    · exact absurd H.τ₁_sq h
    · exact absurd h H.τ₁_ne
    · have := congrArg (fun g => ρ g y) h
      simp only [rep_mul_apply] at this
      exact this
  have hu₂cc : ∀ y, ρ (1, τ₂) (ρ cc y) = ρ cc (ρ (1, τ₂) y) := by
    intro y
    have h : ((1, τ₂) : OmG) * cc = cc * (1, τ₂) := by simp [cc]
    have := congrArg (fun g => ρ g y) h
    simp only [rep_mul_apply] at this
    exact this
  set b := x + ρ (τ₁, 1) x with hb
  have hbW : b ∈ W₀ := by rw [hb, add_comm]; exact H.q₁ x
  have hNb : Nc ρ b = 0 := by rw [hb, Nc_add, hNx, zero_add, Nc_comm, hNx, map_zero]
  have hub : ρ (τ₁, 1) b = b := by rw [hb, map_add, hu2', add_comm]
  set a := x + ρ cc b with ha
  have hNa : Nc ρ a = 0 := by rw [ha, Nc_add, hNx, zero_add, Nc_comm, hNb, map_zero]
  have hua : ρ (τ₁, 1) a = a := by
    rw [ha, map_add, huc, hub]
    have hNb' : b + ρ cc b + ρ cc (ρ cc b) = 0 := by
      have h := hNb
      simp only [Nc, rep_mul_apply] at h
      exact h
    linear_combination (norm := abel1) hNb' - hb - (H.h2 x) - (H.h2 (ρ cc b))
  have haW : a ∈ W₀ := by
    have h1 : ρ (τ₁, 1) (ρ cc a) + ρ cc a = a := by
      rw [huc, hua]
      exact X₁_cc_cc ρ H.h2 (mem_X₁.2 hNa)
    have := H.q₁ (ρ cc a)
    rwa [h1] at this
  have hxab : x = a + ρ cc b := by
    rw [ha]
    linear_combination (norm := abel1) -(H.h2 (ρ cc b))
  calc ρ (1, τ₂) x = ρ (1, τ₂) (a + ρ cc b) := by rw [← hxab]
    _ = ρ (1, τ₂) a + ρ (1, τ₂) (ρ cc b) := map_add _ _ _
    _ = a + ρ cc b := by rw [H.f₂ a haW, hu₂cc, H.f₂ b hbW]
    _ = x := hxab.symm

theorem M₂_fixed {x : X} (hx : x ∈ X₁ ρ) (B : SL(2, ZMod 2)) : ρ (1, B) x = x := by
  have hJ : ((1, τ₂) : OmG) ∈ stabSub ρ x := H.u₂_fixed hx
  have hJ' : ((1, c3 (ZMod 2) * τ₂ * (c3 (ZMod 2))⁻¹) : OmG) ∈ stabSub ρ x := by
    show ρ _ x = x
    have e : ((1, c3 (ZMod 2) * τ₂ * (c3 (ZMod 2))⁻¹) : OmG) = dd * (1, τ₂) * dd⁻¹ := by simp [dd]
    rw [e, rep_mul_apply, rep_mul_apply, H.u₂_fixed (X₁_inv ρ hx dd⁻¹), rep_apply_inv]
  exact right_mem_of_two_invol H.τ₂_sq (conj_invol_sq τ₂ (c3 (ZMod 2)) H.τ₂_sq) H.τ₂_ne
    (conj_invol_ne_one τ₂ (c3 (ZMod 2)) H.τ₂_ne)
    (fun h => conj_invol_ne τ₂ (c3 (ZMod 2)) H.τ₂_sq H.τ₂_ne c3_pow_three c3_ne_one h.symm)
    hJ hJ' B

end ModHyp

end ModuleDecomp4

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section ModuleDecomp5

variable {X : Type*} [AddCommGroup X]

@[expose] def X₂ (ρ : OmG →* AddMonoid.End X) : AddSubgroup X := X₁ (ρ.comp swapHom)

theorem X₂_inv (ρ : OmG →* AddMonoid.End X) {x : X} (hx : x ∈ X₂ ρ) (g : OmG) :
    ρ g x ∈ X₂ ρ := by
  have := X₁_inv (ρ.comp swapHom) hx (swapHom g)
  have e : (ρ.comp swapHom) (swapHom g) x = ρ g x := rfl
  rwa [e] at this

namespace ModHyp

variable {ρ : OmG →* AddMonoid.End X} {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {W₀ : AddSubgroup X}
  (H : ModHyp ρ τ₁ τ₂ γ₁ γ₂ W₀)

include H

theorem X₁_inf_X₂ {x : X} (h1 : x ∈ X₁ ρ) (h2 : x ∈ X₂ ρ) : x = 0 := by
  have hf : ρ cc x = x := H.swap.M₂_fixed h2 (c3 (ZMod 2))
  exact X₁_fixed_zero ρ H.h2 h1 hf

theorem decomp (x : X) : ∃ x₁ ∈ X₁ ρ, ∃ x₂ ∈ X₂ ρ, x = x₁ + x₂ := by
  set ρ' := ρ.comp swapHom with hρ'
  set y := Nc ρ x with hy
  have hyc : ρ cc y = y := Nc_fixed ρ x
  have hz : Nc ρ' y = 0 := by
    apply H.fixed_Lambda_zero
    · have h1 : ρ cc (Nc ρ' y) = Nc ρ' (ρ cc y) := Nc_comm ρ' dd y |>.symm
      rw [h1, hyc]
    · exact Nc_fixed ρ' y
  refine ⟨ρ cc x + ρ (cc * cc) x, Nc_comp_mem ρ H.h2 x, ρ' cc y + ρ' (cc * cc) y,
    Nc_comp_mem ρ' H.h2 y, ?_⟩
  have h1 := Nc_decomp ρ H.h2 x
  have h2 := Nc_decomp ρ' H.h2 y
  rw [hz, zero_add] at h2
  rw [← hy] at h1
  calc x = y + (ρ cc x + ρ (cc * cc) x) := h1
    _ = (ρ' cc y + ρ' (cc * cc) y) + (ρ cc x + ρ (cc * cc) x) := by rw [← h2]
    _ = (ρ cc x + ρ (cc * cc) x) + (ρ' cc y + ρ' (cc * cc) y) := add_comm _ _

theorem X₁_iff {x : X} : x ∈ X₁ ρ ↔ ∀ B : SL(2, ZMod 2), ρ (1, B) x = x := by
  constructor
  · intro hx B
    exact H.M₂_fixed hx B
  · intro hfix
    obtain ⟨x₁, hx₁, x₂, hx₂, hxx⟩ := H.decomp x
    have hx₂eq : x₂ = x + x₁ := by
      linear_combination (norm := abel1) -hxx - (H.h2 x₁)
    have hx₂fix : ρ dd x₂ = x₂ := by
      rw [hx₂eq, map_add, show ρ dd x = x from hfix (c3 (ZMod 2)),
        show ρ dd x₁ = x₁ from H.M₂_fixed hx₁ (c3 (ZMod 2))]
    have hx₂zero : x₂ = 0 := X₁_fixed_zero (ρ.comp swapHom) H.h2 hx₂ hx₂fix
    rw [hxx, hx₂zero, add_zero]
    exact hx₁

theorem X₂_iff {x : X} : x ∈ X₂ ρ ↔ ∀ A : SL(2, ZMod 2), ρ (A, 1) x = x :=
  H.swap.X₁_iff

theorem X₁_eq_closure :
    X₁ ρ = AddSubgroup.closure {z | ∃ (A : SL(2, ZMod 2)) (y : X), z = ρ (A, 1) y + y} := by
  apply le_antisymm
  · intro x hx
    apply AddSubgroup.subset_closure
    refine ⟨c3 (ZMod 2), ρ cc x, ?_⟩
    exact (X₁_cc_cc ρ H.h2 hx).symm
  · rw [AddSubgroup.closure_le]
    rintro z ⟨A, y, rfl⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, hyy⟩ := H.decomp y
    have h2fix : ρ (A, 1) y₂ = y₂ := H.swap.M₂_fixed hy₂ A
    have : ρ (A, 1) y + y = ρ (A, 1) y₁ + y₁ := by
      rw [hyy, map_add, h2fix]
      linear_combination (norm := abel1) (H.h2 y₂)
    rw [SetLike.mem_coe, this]
    exact (X₁ ρ).add_mem (X₁_inv ρ hy₁ _) hy₁

theorem X₂_eq_closure :
    X₂ ρ = AddSubgroup.closure {z | ∃ (B : SL(2, ZMod 2)) (y : X), z = ρ (1, B) y + y} :=
  H.swap.X₁_eq_closure

theorem X₁_natural [Finite X] :
    ∃ (s : ℕ) (e : ↥(X₁ ρ) ≃+ (Fin s → Fin 2 → ZMod 2)),
      ∀ (A : SL(2, ZMod 2)) (x y : ↥(X₁ ρ)), (y : X) = ρ (A, 1) (x : X) →
        e y = fun j => A • e x j := by
  let ρ₁ : SL(2, ZMod 2) →* AddMonoid.End X :=
    ρ.comp (MonoidHom.inl SL(2, ZMod 2) SL(2, ZMod 2))
  let ρ₂ := restrictHom ρ₁ (X₁ ρ) (fun A x hx => X₁_inv ρ hx (A, 1))
  have : Finite (X₁ ρ) := inferInstance
  obtain ⟨s, e, he⟩ := natural_sum_of_fpf (Y := ↥(X₁ ρ))
    (fun y => Subtype.ext (by simpa using H.h2 (y : X))) ρ₂
    (fun y hy => Subtype.ext (X₁_fixed_zero ρ H.h2 y.2 (congrArg Subtype.val hy)))
  refine ⟨s, e, fun A x y hy => ?_⟩
  have : y = ρ₂ A x := Subtype.ext hy
  rw [this]
  exact he A x

theorem X₂_natural [Finite X] :
    ∃ (s : ℕ) (e : ↥(X₂ ρ) ≃+ (Fin s → Fin 2 → ZMod 2)),
      ∀ (A : SL(2, ZMod 2)) (x y : ↥(X₂ ρ)), (y : X) = ρ (1, A) (x : X) →
        e y = fun j => A • e x j :=
  H.swap.X₁_natural

end ModHyp

end ModuleDecomp5

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section MulWrapper

variable {Y : Type*} [CommGroup Y]

@[expose] def addEndHom (ρ : OmG →* MulAut Y) : OmG →* AddMonoid.End (Additive Y) where
  toFun g := (MulEquiv.toAdditive (ρ g)).toAddMonoidHom
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    show Additive.ofMul (ρ 1 (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' := fun g h => by
    apply AddMonoidHom.ext
    intro x
    show Additive.ofMul (ρ (g * h) (Additive.toMul x)) =
      Additive.ofMul (ρ g (ρ h (Additive.toMul x)))
    rw [map_mul]
    rfl

theorem inv_eq_self_of_sq (h2 : ∀ y : Y, y * y = 1) (y : Y) : y⁻¹ = y :=
  inv_eq_of_mul_eq_one_right (h2 y)

@[expose] def subgroupEquivOfAdd (S : AddSubgroup (Additive Y)) {M : Type*} [AddCommGroup M]
    (e : ↥S ≃+ M) : ↥(AddSubgroup.toSubgroup' S) ≃* Multiplicative M where
  toFun y := Multiplicative.ofAdd (e ⟨Additive.ofMul (y : Y), (AddSubgroup.mem_toSubgroup' _ _).1 y.2⟩)
  invFun v := ⟨Additive.toMul ((e.symm (Multiplicative.toAdd v) : ↥S) : Additive Y),
    (AddSubgroup.mem_toSubgroup' _ _).2 (by simp)⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv v := by
    simp
  map_mul' a b := by
    show Multiplicative.ofAdd (e _) = Multiplicative.ofAdd (e _) * Multiplicative.ofAdd (e _)
    rw [← ofAdd_add, ← map_add]
    rfl

theorem mul_module_decomposition [Finite Y] (h2 : ∀ y : Y, y * y = 1)
    (ρ : OmG →* MulAut Y) {τ₁ τ₂ γ₁ γ₂ : SL(2, ZMod 2)} {W₀ : Subgroup Y}
    (hτ₁ : τ₁ * τ₁ = 1) (hτ₁' : τ₁ ≠ 1) (hτ₂ : τ₂ * τ₂ = 1) (hτ₂' : τ₂ ≠ 1)
    (hγ₁ : γ₁ ^ 3 = 1) (hγ₁' : γ₁ ≠ 1) (hγ₂ : γ₂ ^ 3 = 1) (hγ₂' : γ₂ ≠ 1)
    (hq₁ : ∀ y, ρ (τ₁, 1) y * y ∈ W₀) (hq₂ : ∀ y, ρ (1, τ₂) y * y ∈ W₀)
    (hf₁ : ∀ w ∈ W₀, ρ (τ₁, 1) w = w) (hf₂ : ∀ w ∈ W₀, ρ (1, τ₂) w = w)
    (hsum : ∀ y, ∃ w₀ ∈ W₀, ∃ w₁ ∈ W₀, y = w₀ * ρ (γ₁, γ₂)⁻¹ w₁)
    (hcap : ∀ w₁ ∈ W₀, ρ (γ₁, γ₂)⁻¹ w₁ ∈ W₀ → ρ (γ₁, γ₂)⁻¹ w₁ = 1) :
    ∃ Y₁ Y₂ : Subgroup Y,
      (∀ y, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, y = y₁ * y₂) ∧ (∀ y ∈ Y₁, y ∈ Y₂ → y = 1) ∧
      (∀ g : OmG, ∀ y ∈ Y₁, ρ g y ∈ Y₁) ∧ (∀ g : OmG, ∀ y ∈ Y₂, ρ g y ∈ Y₂) ∧
      (∀ y, y ∈ Y₁ ↔ ∀ B : SL(2, ZMod 2), ρ (1, B) y = y) ∧
      (∀ y, y ∈ Y₂ ↔ ∀ A : SL(2, ZMod 2), ρ (A, 1) y = y) ∧
      (Y₁ = Subgroup.closure {z | ∃ (A : SL(2, ZMod 2)) (y : Y), z = ρ (A, 1) y * y⁻¹}) ∧
      (Y₂ = Subgroup.closure {z | ∃ (B : SL(2, ZMod 2)) (y : Y), z = ρ (1, B) y * y⁻¹}) ∧
      (∃ (s : ℕ) (e : ↥Y₁ ≃* Multiplicative (Fin s → Fin 2 → ZMod 2)),
        ∀ (A : SL(2, ZMod 2)) (x y : ↥Y₁), (y : Y) = ρ (A, 1) (x : Y) →
          e y = Multiplicative.ofAdd (fun j => A • Multiplicative.toAdd (e x) j)) ∧
      (∃ (s : ℕ) (e : ↥Y₂ ≃* Multiplicative (Fin s → Fin 2 → ZMod 2)),
        ∀ (A : SL(2, ZMod 2)) (x y : ↥Y₂), (y : Y) = ρ (1, A) (x : Y) →
          e y = Multiplicative.ofAdd (fun j => A • Multiplicative.toAdd (e x) j)) := by
  classical
  have hH : ModHyp (addEndHom ρ) τ₁ τ₂ γ₁ γ₂ (W₀.toAddSubgroup) :=
    { h2 := fun x => congrArg Additive.ofMul (h2 (Additive.toMul x))
      τ₁_sq := hτ₁
      τ₁_ne := hτ₁'
      τ₂_sq := hτ₂
      τ₂_ne := hτ₂'
      γ₁_cube := hγ₁
      γ₁_ne := hγ₁'
      γ₂_cube := hγ₂
      γ₂_ne := hγ₂'
      q₁ := fun x => (Additive.mem_toAddSubgroup _ _).2 (hq₁ (Additive.toMul x))
      q₂ := fun x => (Additive.mem_toAddSubgroup _ _).2 (hq₂ (Additive.toMul x))
      f₁ := fun w hw => congrArg Additive.ofMul (hf₁ (Additive.toMul w) hw)
      f₂ := fun w hw => congrArg Additive.ofMul (hf₂ (Additive.toMul w) hw)
      sum := fun x => by
        obtain ⟨w₀, hw₀, w₁, hw₁, hx⟩ := hsum (Additive.toMul x)
        exact ⟨Additive.ofMul w₀, hw₀, Additive.ofMul w₁, hw₁, congrArg Additive.ofMul hx⟩
      cap := fun w hw hmem => by
        have := hcap (Additive.toMul w) hw hmem
        exact congrArg Additive.ofMul this }
  refine ⟨AddSubgroup.toSubgroup' (X₁ (addEndHom ρ)), AddSubgroup.toSubgroup' (X₂ (addEndHom ρ)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x₁, hx₁, x₂, hx₂, hxx⟩ := hH.decomp (Additive.ofMul y)
    exact ⟨Additive.toMul x₁, (AddSubgroup.mem_toSubgroup' _ _).2 hx₁, Additive.toMul x₂,
      (AddSubgroup.mem_toSubgroup' _ _).2 hx₂, congrArg Additive.toMul hxx⟩
  · intro y hy1 hy2
    exact congrArg Additive.toMul (hH.X₁_inf_X₂ ((AddSubgroup.mem_toSubgroup' _ _).1 hy1)
      ((AddSubgroup.mem_toSubgroup' _ _).1 hy2))
  · intro g y hy
    exact (AddSubgroup.mem_toSubgroup' _ _).2
      (X₁_inv (addEndHom ρ) ((AddSubgroup.mem_toSubgroup' _ _).1 hy) g)
  · intro g y hy
    exact (AddSubgroup.mem_toSubgroup' _ _).2
      (X₂_inv (addEndHom ρ) ((AddSubgroup.mem_toSubgroup' _ _).1 hy) g)
  · intro y
    rw [AddSubgroup.mem_toSubgroup', hH.X₁_iff]
    exact ⟨fun h B => congrArg Additive.toMul (h B), fun h B => congrArg Additive.ofMul (h B)⟩
  · intro y
    rw [AddSubgroup.mem_toSubgroup', hH.X₂_iff]
    exact ⟨fun h A => congrArg Additive.toMul (h A), fun h A => congrArg Additive.ofMul (h A)⟩
  · rw [hH.X₁_eq_closure, AddSubgroup.toSubgroup'_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨A, y, hz⟩
      refine ⟨A, Additive.toMul y, ?_⟩
      have := congrArg Additive.toMul hz
      rw [inv_eq_self_of_sq h2]
      exact this
    · rintro ⟨A, y, hz⟩
      refine ⟨A, Additive.ofMul y, ?_⟩
      rw [inv_eq_self_of_sq h2] at hz
      exact congrArg Additive.ofMul hz
  · rw [hH.X₂_eq_closure, AddSubgroup.toSubgroup'_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨B, y, hz⟩
      refine ⟨B, Additive.toMul y, ?_⟩
      have := congrArg Additive.toMul hz
      rw [inv_eq_self_of_sq h2]
      exact this
    · rintro ⟨B, y, hz⟩
      refine ⟨B, Additive.ofMul y, ?_⟩
      rw [inv_eq_self_of_sq h2] at hz
      exact congrArg Additive.ofMul hz
  · obtain ⟨s, e, he⟩ := hH.X₁_natural
    refine ⟨s, subgroupEquivOfAdd (X₁ (addEndHom ρ)) e, fun A x y hy => ?_⟩
    have hy' : (Additive.ofMul (y : Y) : Additive Y) =
        addEndHom ρ (A, 1) (Additive.ofMul (x : Y)) := congrArg Additive.ofMul hy
    have := he A ⟨Additive.ofMul (x : Y), (AddSubgroup.mem_toSubgroup' _ _).1 x.2⟩
      ⟨Additive.ofMul (y : Y), (AddSubgroup.mem_toSubgroup' _ _).1 y.2⟩ hy'
    apply Multiplicative.toAdd.injective
    exact this
  · obtain ⟨s, e, he⟩ := hH.X₂_natural
    refine ⟨s, subgroupEquivOfAdd (X₂ (addEndHom ρ)) e, fun A x y hy => ?_⟩
    have hy' : (Additive.ofMul (y : Y) : Additive Y) =
        addEndHom ρ (1, A) (Additive.ofMul (x : Y)) := congrArg Additive.ofMul hy
    have := he A ⟨Additive.ofMul (x : Y), (AddSubgroup.mem_toSubgroup' _ _).1 x.2⟩
      ⟨Additive.ofMul (y : Y), (AddSubgroup.mem_toSubgroup' _ _).1 y.2⟩ hy'
    apply Multiplicative.toAdd.injective
    exact this

end MulWrapper

end CFSG.Quasithin.Om4Model
