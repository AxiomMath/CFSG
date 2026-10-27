module

public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.Quasithin.H13.U3

open Matrix

local notation "𝔽₉" => GaloisField 3 (2 * 1)

noncomputable abbrev f9ι : ZMod 3 →+* 𝔽₉ := algebraMap (ZMod 3) 𝔽₉

theorem f9_three_eq_zero : (3 : 𝔽₉) = 0 := by
  have := CharP.cast_eq_zero 𝔽₉ 3
  exact_mod_cast this

theorem f9ι_pow_three (a : ZMod 3) : (f9ι a) ^ 3 = f9ι a := by
  rw [← map_pow]
  congr 1
  revert a
  decide

theorem f9ι_injective : Function.Injective f9ι := f9ι.injective

theorem f9_exists_sq_eq_neg_one : ∃ τ : 𝔽₉, τ * τ = -1 := by
  classical
  have : Fintype 𝔽₉ := Fintype.ofFinite 𝔽₉
  have h : IsSquare (-1 : 𝔽₉) := by
    rw [FiniteField.isSquare_neg_one_iff]
    have hc : Fintype.card 𝔽₉ = 9 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 1) (by norm_num)]
      norm_num
    rw [hc]
    decide
  obtain ⟨τ, hτ⟩ := h
  exact ⟨τ, hτ.symm⟩

@[expose] noncomputable def uMat (τ : 𝔽₉) (a b : ZMod 3) : Matrix (Fin 3) (Fin 3) 𝔽₉ :=
  !![1, -(f9ι a), f9ι a ^ 2 + f9ι b * τ; 0, 1, f9ι a; 0, 0, 1]

theorem uMat_mul (τ : 𝔽₉) (a b a' b' : ZMod 3) :
    uMat τ a b * uMat τ a' b' = uMat τ (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, map_add]
  · linear_combination (-(f9ι a * f9ι a')) * f9_three_eq_zero
  · ring

theorem uMat_zero (τ : 𝔽₉) : uMat τ 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_mul_neg (τ : 𝔽₉) (a b : ZMod 3) : uMat τ a b * uMat τ (-a) (-b) = 1 := by
  rw [uMat_mul, show a + -a = 0 from add_neg_cancel a, show b + -b = 0 from add_neg_cancel b,
    uMat_zero]

theorem uMat_neg_mul (τ : 𝔽₉) (a b : ZMod 3) : uMat τ (-a) (-b) * uMat τ a b = 1 := by
  rw [uMat_mul, show -a + a = 0 from neg_add_cancel a, show -b + b = 0 from neg_add_cancel b,
    uMat_zero]

theorem uMat_unitary {τ : 𝔽₉} (hτ : τ * τ = -1) (a b : ZMod 3) :
    (Matrix.of fun i j => (uMat τ a b) j i ^ (3 ^ 1)) * !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
      uMat τ a b = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  have hτ3 : τ ^ 3 = -τ := by
    rw [pow_succ, pow_two, hτ]
    ring
  have hfrob : ∀ x y : 𝔽₉, (x + y) ^ 3 = x ^ 3 + y ^ 3 := fun x y => add_pow_char x y 3
  have hneg : ∀ x : 𝔽₉, (-x) ^ 3 = -x ^ 3 := fun x => Odd.neg_pow (by decide) x
  have ha3 := f9ι_pow_three a
  have hb3 := f9ι_pow_three b
  have hι2 : (f9ι a ^ 2) ^ 3 = f9ι a ^ 2 := by
    rw [show (f9ι a ^ 2) ^ 3 = (f9ι a ^ 3) ^ 2 by ring, ha3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, hfrob, mul_pow, hτ3, hι2, hneg, ha3, hb3]
  linear_combination (f9ι a ^ 2) * f9_three_eq_zero

theorem uMat_det (τ : 𝔽₉) (a b : ZMod 3) : (uMat τ a b).det = 1 := by
  simp [uMat, Matrix.det_fin_three]

@[expose] noncomputable def uGL (τ : 𝔽₉) : Multiplicative (ZMod 3 × ZMod 3) →* GL (Fin 3) 𝔽₉ where
  toFun x := ⟨uMat τ x.toAdd.1 x.toAdd.2, uMat τ (-x.toAdd.1) (-x.toAdd.2),
    uMat_mul_neg τ _ _, uMat_neg_mul τ _ _⟩
  map_one' := Units.ext (uMat_zero τ)
  map_mul' x y := Units.ext (by
    change uMat τ (x * y).toAdd.1 (x * y).toAdd.2 =
      uMat τ x.toAdd.1 x.toAdd.2 * uMat τ y.toAdd.1 y.toAdd.2
    rw [uMat_mul, toAdd_mul, Prod.fst_add, Prod.snd_add])

theorem coe_uGL (τ : 𝔽₉) (x : Multiplicative (ZMod 3 × ZMod 3)) :
    ((uGL τ x : GL (Fin 3) 𝔽₉) : Matrix (Fin 3) (Fin 3) 𝔽₉) = uMat τ x.toAdd.1 x.toAdd.2 := rfl

theorem uPGL_injective {τ : 𝔽₉} (hτ : τ ≠ 0) :
    Function.Injective (ProjGenLinGroup.mk.comp (uGL τ)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar] at hx
  obtain ⟨c, hc⟩ := hx
  have h01 := congrArg (fun g : GL (Fin 3) 𝔽₉ => (g : Matrix (Fin 3) (Fin 3) 𝔽₉) 0 1) hc
  have h02 := congrArg (fun g : GL (Fin 3) 𝔽₉ => (g : Matrix (Fin 3) (Fin 3) 𝔽₉) 0 2) hc
  simp only [coe_uGL, uMat] at h01 h02
  simp [GeneralLinearGroup.scalar] at h01 h02
  have ha : x.toAdd.1 = 0 := h01
  rw [ha, map_zero] at h02
  have hb : x.toAdd.2 = 0 := by
    refine f9ι_injective ?_
    rw [map_zero]
    have h1 : f9ι x.toAdd.2 * τ = 0 := by simpa using h02.symm
    exact (mul_eq_zero.mp h1).resolve_right hτ
  apply Multiplicative.toAdd.injective
  exact Prod.ext ha hb

theorem uPGL_mem_PSU3 {τ : 𝔽₉} (hτ : τ * τ = -1) (x : Multiplicative (ZMod 3 × ZMod 3)) :
    ProjGenLinGroup.mk.comp (uGL τ) x ∈ CFSG.Open.PSU3 3 1 := by
  refine Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ?_)
  refine ⟨?_, ?_⟩
  · rw [coe_uGL]
    exact uMat_unitary hτ _ _
  · refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, coe_uGL]
    exact uMat_det τ _ _

instance isElementaryAbelian_top_F3sq :
    IsElementaryAbelian 3 (⊤ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      change 3 • Multiplicative.toAdd (x : Multiplicative (ZMod 3 × ZMod 3)) = 0
      generalize Multiplicative.toAdd (x : Multiplicative (ZMod 3 × ZMod 3)) = y
      exact Prod.ext (by revert y; decide) (by revert y; decide) }

theorem unitary_three_field_three_elementary_nine_subgroup {H : Type} [Group H] [Finite H]
    (hH : CFSG.Blueprint.LieModel H .PSU 3 3 1) :
    (∃ E : Subgroup H, IsElementaryAbelian 3 E ∧ Nat.card E = 9) ∧ 2 ≤ CFSG.pRank 3 H := by
  obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hH
  obtain ⟨τ, hτ⟩ := f9_exists_sq_eq_neg_one
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set φ := ProjGenLinGroup.mk.comp (uGL τ) with hφ
  let ψ : Multiplicative (ZMod 3 × ZMod 3) →* H :=
    e.symm.toMonoidHom.comp (φ.codRestrict (CFSG.Open.PSU3 3 1) (uPGL_mem_PSU3 hτ))
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 := e.symm.injective hxy
    exact uPGL_injective hτ0 (congrArg Subtype.val h1)
  have hE : IsElementaryAbelian 3 ((⊤ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))).map ψ) :=
    IsElementaryAbelian.map ψ
  have hcard : Nat.card ((⊤ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))).map ψ) = 9 := by
    rw [Subgroup.card_map_of_injective hψ, Subgroup.card_top, Nat.card_congr
      Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
  refine ⟨⟨_, hE, hcard⟩, ?_⟩
  exact le_csSup (SteinbergBM.bddAbove_pRank_set (X := H) (by norm_num))
    ⟨_, hE, by rw [hcard]; norm_num⟩

end CFSG.Quasithin.H13.U3
