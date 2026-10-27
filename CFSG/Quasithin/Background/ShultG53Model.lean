module

public import CFSG.Quasithin.Background.RonanG51Lines
public import CFSG.Quasithin.Background.ShultG53Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

abbrev V4 : Type := Fin 4 → ZMod 2

@[expose] def Rm (k : Fin 2) (σ : Perm (Fin 6)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  if k = 0 then heartHom σ else heartHom (totalPermHom σ)

@[expose] noncomputable def ρk :
    Fin 2 → Representation (ZMod 2) ↥(alternatingGroup (Fin 6)) V4
  | 0 => a6BinaryRep 1
  | 1 => a6BinaryRep 2

theorem ρk_apply (k : Fin 2)
    (g : ↥(alternatingGroup (Fin 6))) (x : V4) :
    ρk k g x = Matrix.mulVec (Rm k (g : Perm (Fin 6))) x := by
  fin_cases k
  · exact a6BinaryRep_one_apply g x
  · exact a6BinaryRep_two_apply g x

noncomputable abbrev Mk (k : Fin 2) :
    Md ↥(alternatingGroup (Fin 6)) := ⟨V4, ρk k⟩

@[expose] def B0 (x y : V4) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 1 * y 2 + x 2 * y 1 + x 2 * y 3 + x 3 * y 2

@[expose] def B0form : LinearMap.BilinForm (ZMod 2) V4 :=
  LinearMap.mk₂ (ZMod 2) B0
    (fun x x' y => by simp only [B0, Pi.add_apply]; ring)
    (fun c x y => by simp only [B0, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [B0, Pi.add_apply]; ring)
    (fun c x y => by simp only [B0, Pi.smul_apply, smul_eq_mul]; ring)

theorem B0form_apply (x y : V4) : B0form x y = B0 x y := rfl

@[expose] def Qf (x : V4) : ZMod 2 := x 0 * x 1 + x 1 * x 2 + x 2 * x 3

theorem Qf_polar : ∀ x y : V4, Qf (x + y) = Qf x + Qf y + B0 x y := by decide +kernel

theorem a6_ind {P : Perm (Fin 6) → Prop} (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (h3 : ∀ σ : Perm (Fin 6), σ.support.card = 3 → P σ) :
    ∀ σ ∈ alternatingGroup (Fin 6), P σ := by
  intro σ hσ
  rw [← Perm.closure_three_cycles_eq_alternating] at hσ
  induction hσ using Subgroup.closure_induction'' with
  | mem x hx => exact h3 x hx.card_support
  | inv_mem x hx => exact h3 x⁻¹ (by rw [Perm.support_inv]; exact hx.card_support)
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem B0_inv_three : ∀ k : Fin 2, ∀ σ : Perm (Fin 6), σ.support.card = 3 →
    ∀ x y : V4, B0 (Matrix.mulVec (Rm k σ) x) (Matrix.mulVec (Rm k σ) y) = B0 x y := by
  decide +kernel

theorem Rm_mul (k : Fin 2) (a b : Perm (Fin 6)) : Rm k (a * b) = Rm k a * Rm k b := by
  fin_cases k <;> simp [Rm, map_mul]

theorem Rm_one (k : Fin 2) : Rm k 1 = 1 := by
  fin_cases k <;> simp [Rm]

theorem B0_inv_perm (k : Fin 2) : ∀ σ ∈ alternatingGroup (Fin 6), ∀ x y : V4,
    B0 (Matrix.mulVec (Rm k σ) x) (Matrix.mulVec (Rm k σ) y) = B0 x y := by
  refine a6_ind (P := fun σ => ∀ x y : V4,
    B0 (Matrix.mulVec (Rm k σ) x) (Matrix.mulVec (Rm k σ) y) = B0 x y) ?_ ?_ ?_
  · intro x y
    simp [Rm_one]
  · intro a b ha hb x y
    rw [Rm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [ha, hb]
  · intro σ hσ
    exact B0_inv_three k σ hσ

theorem B0_inv (k : Fin 2) (g : ↥(alternatingGroup (Fin 6)))
    (x y : V4) : B0 (ρk k g x) (ρk k g y) = B0 x y := by
  rw [ρk_apply, ρk_apply]
  exact B0_inv_perm k g g.2 x y

theorem additive_eq_B0 : ∀ a : Fin 4 → ZMod 2, ∃ m : V4, ∀ y : V4,
    (∑ i, y i * a i) = B0 y m := by decide +kernel

theorem add_fun_eq (d : V4 → ZMod 2) (hd : ∀ x y, d (x + y) = d x + d y) :
    ∃ m : V4, ∀ y, d y = B0 y m := by
  let f : V4 →+ ZMod 2 := AddMonoidHom.mk' d hd
  let fl : V4 →ₗ[ZMod 2] ZMod 2 := f.toZModLinearMap 2
  obtain ⟨m, hm⟩ := additive_eq_B0 (fun i => d (Pi.single i 1))
  refine ⟨m, fun y => ?_⟩
  have h1 : y = ∑ i, y i • (Pi.single i 1 : V4) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : d y = ∑ i, y i * d (Pi.single i 1) := by
    have : d y = fl y := rfl
    rw [this]
    conv_lhs => rw [h1]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [h2, hm y]

theorem qlaw (R : V4 →ₗ[ZMod 2] V4) (hR : ∀ x y, B0 (R x) (R y) = B0 x y) :
    ∃ m : V4, ∀ y, Qf (R y) = Qf y + B0 y m := by
  have hadd : ∀ x y, (Qf (R (x + y)) + Qf (x + y)) =
      (Qf (R x) + Qf x) + (Qf (R y) + Qf y) := by
    intro x y
    rw [map_add, Qf_polar, Qf_polar, hR]
    generalize Qf (R x) = a
    generalize Qf (R y) = b
    generalize Qf x = c
    generalize Qf y = d
    generalize B0 x y = e
    revert a b c d e
    decide
  obtain ⟨m, hm⟩ := add_fun_eq (fun y => Qf (R y) + Qf y) hadd
  refine ⟨m, fun y => ?_⟩
  have key : ∀ a b e : ZMod 2, a + b = e → a = b + e := by decide
  exact key _ _ _ (hm y)

end CFSG.Quasithin.ShultG53
