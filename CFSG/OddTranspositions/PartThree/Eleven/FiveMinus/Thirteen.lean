module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import TauCeti.LinearAlgebra.Eigenspace.Separation

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

private lemma five_pow_modEq_thirteen {j k : ℕ} (hj : j ≤ k) (hk : k ≤ 3)
    (h : 5 ^ k ≡ 5 ^ j [MOD 13]) : j = k := by
  interval_cases k <;> interval_cases j <;> first | rfl | exact absurd h (by decide)

private lemma le_eigenspace_one_of_finrank_le_three {V : Type*} [AddCommGroup V]
    [Module (ZMod 5) V] [Fintype V] [Fact (Nat.Prime 5)] {C : Module.End (ZMod 5) V}
    (hC13 : C ^ 13 = 1)
    {W : Submodule (ZMod 5) V} (hCW : ∀ x ∈ W, C x ∈ W)
    (hk : Module.finrank (ZMod 5) W ≤ 3) : W ≤ C.eigenspace 1 := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  haveI : Finite W := Finite.of_injective (Subtype.val : W → V) Subtype.val_injective
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype ↥(W ⊓ C.eigenspace 1) := Fintype.ofFinite ↥(W ⊓ C.eigenspace 1)
  let g : W → W := fun y => ⟨C y.1, hCW y.1 y.2⟩
  let gE : Function.End W := g
  have hgpow : ∀ n (y : W), ((g^[n]) y : V) = (C ^ n) y.1 := by
    intro n
    induction n with
    | zero => intro y; rw [Function.iterate_zero_apply, pow_zero]; rfl
    | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ']
        show C (((g^[n]) y : W) : V) = C ((C ^ n) y.1)
        rw [ih y]
  have hg13 : gE ^ 13 = 1 := by
    funext y
    apply Subtype.ext
    show ((g^[13]) y : V) = y.1
    rw [hgpow 13 y, hC13]
    rfl
  let e : {y : W // g y = y} ≃ ↥(W ⊓ C.eigenspace 1) :=
    { toFun := fun y => ⟨y.1.1, y.1.2, by
        simpa [Module.End.mem_eigenspace_iff, g] using congrArg Subtype.val y.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        apply Subtype.ext
        show C x.1 = x.1
        simpa using (Module.End.mem_eigenspace_iff.mp x.2.2)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  have hcardW : Fintype.card W = 5 ^ Module.finrank (ZMod 5) W := by
    have h := Module.card_eq_pow_finrank (K := ZMod 5) (V := W)
    simpa using h
  have hcardFix : Fintype.card (Function.fixedPoints gE) =
      5 ^ Module.finrank (ZMod 5) ↥(W ⊓ C.eigenspace 1) := by
    change Fintype.card {y : W // g y = y} =
      5 ^ Module.finrank (ZMod 5) ↥(W ⊓ C.eigenspace 1)
    rw [Fintype.card_congr e]
    have h := Module.card_eq_pow_finrank (K := ZMod 5) (V := ↥(W ⊓ C.eigenspace 1))
    simpa using h
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := W) (f := gE) (p := 13) (n := 1)
    (by simpa using hg13)
  rw [hcardW, hcardFix] at hmod
  have hle : Module.finrank (ZMod 5) ↥(W ⊓ C.eigenspace 1) ≤
      Module.finrank (ZMod 5) W :=
    Submodule.finrank_mono inf_le_left
  have heq := five_pow_modEq_thirteen hle hk hmod
  have hWeq : W ⊓ C.eigenspace 1 = W :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left heq
  exact inf_eq_left.mp hWeq

theorem eq_one_or_eq_neg_one_or_exists_eigenline_of_commute {t c : GL (Fin 5) (ZMod 5)}
    (ht : t * t = 1) (hc : c ^ 13 = 1) (hc1 : c ≠ 1) (htc : t * c = c * t) :
    t = 1 ∨ t = -1 ∨
      (∃ w : Fin 5 → ZMod 5, w ≠ 0 ∧
        ∀ x, (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = -x ↔ ∃ a : ZMod 5, x = a • w) ∨
      ∃ w : Fin 5 → ZMod 5, w ≠ 0 ∧
        ∀ x, (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = x ↔ ∃ a : ZMod 5, x = a • w := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let V : Type := Fin 5 → ZMod 5
  let E : V ≃ₗ[ZMod 5] V := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
    (Matrix.GeneralLinearGroup.toLin t)
  let D : V ≃ₗ[ZMod 5] V := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
    (Matrix.GeneralLinearGroup.toLin c)
  let T : Module.End (ZMod 5) V := (E : V →ₗ[ZMod 5] V)
  let C : Module.End (ZMod 5) V := (D : V →ₗ[ZMod 5] V)
  have hE2 : E * E = 1 := by
    change LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin t) *
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin t) = 1
    rw [← map_mul, ← map_mul, ht, map_one, map_one]
  have hD13 : D ^ 13 = 1 := by
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin c)) ^ 13 = 1
    rw [← map_pow, ← map_pow, hc, map_one, map_one]
  have hED : E * D = D * E := by
    change LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin t) *
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin c) =
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin c) *
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin t)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, htc]
  have hT2 : T * T = 1 := by
    change (E : V →ₗ[ZMod 5] V) * (E : V →ₗ[ZMod 5] V) = 1
    rw [← LinearEquiv.coe_toLinearMap_mul, hE2, LinearEquiv.coe_toLinearMap_one]
    rfl
  have hC13 : C ^ 13 = 1 := by
    change (D : V →ₗ[ZMod 5] V) ^ 13 = 1
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ZMod 5) (M := V)) D 13
    rw [hD13, map_one] at h
    exact h.symm
  have hCT : C * T = T * C := by
    change (D : V →ₗ[ZMod 5] V) * (E : V →ₗ[ZMod 5] V) =
      (E : V →ₗ[ZMod 5] V) * (D : V →ₗ[ZMod 5] V)
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hED]
  have hT : Function.Involutive T := fun x => by
    have h := congrArg (fun f : Module.End (ZMod 5) V => f x) hT2
    simpa [Module.End.mul_apply] using h
  have h2unit : IsUnit (2 : ZMod 5) := by
    rw [isUnit_iff_ne_zero]
    have h : ((2 : ℕ) : ZMod 5) ≠ 0 := by
      intro hzero
      have hdvd : (5 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 5).mp hzero
      norm_num at hdvd
    simpa using h
  let Wp : Submodule (ZMod 5) V := T.eigenspace 1
  let Wm : Submodule (ZMod 5) V := T.eigenspace (-1)
  have hcompl : IsCompl Wp Wm := TauCeti.isCompl_eigenspace_one_neg_one h2unit hT
  have hTapply : ∀ x : V, T x = (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x := by
    intro x
    change (E : V →ₗ[ZMod 5] V) x = (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x
    rw [show E = LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin t) from rfl,
      LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hCapply : ∀ x : V, C x = (c : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x := by
    intro x
    change (D : V →ₗ[ZMod 5] V) x = (c : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x
    rw [show D = LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
        (Matrix.GeneralLinearGroup.toLin c) from rfl,
      LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hmem_pos : ∀ x : V, x ∈ Wp ↔ (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = x := by
    intro x
    rw [show Wp = T.eigenspace 1 from rfl, Module.End.mem_eigenspace_iff, one_smul, hTapply x]
  have hmem_neg : ∀ x : V, x ∈ Wm ↔ (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = -x := by
    intro x
    rw [show Wm = T.eigenspace (-1) from rfl, Module.End.mem_eigenspace_iff, neg_one_smul,
      hTapply x]
  have hpres : ∀ μ : ZMod 5, ∀ x, x ∈ T.eigenspace μ → C x ∈ T.eigenspace μ := by
    intro μ x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    calc T (C x) = (T * C) x := rfl
      _ = (C * T) x := by rw [← hCT]
      _ = C (T x) := rfl
      _ = C (μ • x) := by rw [hx]
      _ = μ • C x := map_smul C μ x
  have hCWp : ∀ x ∈ Wp, C x ∈ Wp := fun x hx => hpres 1 x hx
  have hCWm : ∀ x ∈ Wm, C x ∈ Wm := fun x hx => hpres (-1) x hx
  have hfinV : Module.finrank (ZMod 5) V = 5 := by
    change Module.finrank (ZMod 5) (Fin 5 → ZMod 5) = 5
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  set kp : ℕ := Module.finrank (ZMod 5) Wp
  set km : ℕ := Module.finrank (ZMod 5) Wm
  have hsum : kp + km = 5 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hfinV] at h
    simpa [kp, km] using h
  have hnotboth : ¬ (kp ≤ 3 ∧ km ≤ 3) := by
    rintro ⟨hkp3, hkm3⟩
    have hp_le : Wp ≤ C.eigenspace 1 :=
      le_eigenspace_one_of_finrank_le_three hC13 hCWp (by simpa [kp] using hkp3)
    have hm_le : Wm ≤ C.eigenspace 1 :=
      le_eigenspace_one_of_finrank_le_three hC13 hCWm (by simpa [km] using hkm3)
    have htop : (⊤ : Submodule (ZMod 5) V) ≤ C.eigenspace 1 := by
      rw [← hcompl.sup_eq_top]
      exact sup_le hp_le hm_le
    have hC1 : C = 1 := by
      have htop' : C.eigenspace 1 = ⊤ := le_antisymm le_top htop
      apply LinearMap.ext; intro x
      have hx : x ∈ C.eigenspace 1 := by rw [htop']; trivial
      rwa [Module.End.mem_eigenspace_iff, one_smul] at hx
    have hmat : (c : Matrix (Fin 5) (Fin 5) (ZMod 5)) = 1 := by
      ext i j
      have hx : (c : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single j (1 : ZMod 5) =
          Pi.single j (1 : ZMod 5) := by
        rw [← hCapply (Pi.single j (1 : ZMod 5))]
        exact congrArg (fun f : Module.End (ZMod 5) V => f (Pi.single j (1 : ZMod 5))) hC1
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using congrFun hx i
    exact hc1 (Units.ext hmat)
  have hmax : 4 ≤ kp ∨ 4 ≤ km := by omega
  rcases hmax with hkp4 | hkm4
  · have hkm01 : km = 0 ∨ km = 1 := by omega
    rcases hkm01 with hkm0 | hkm1
    · left
      have hWm_bot : Wm = ⊥ := by
        rw [← Submodule.finrank_eq_zero]
        simpa [km] using hkm0
      have hWp_top : Wp = ⊤ := by
        have h := hcompl.sup_eq_top
        rwa [hWm_bot, sup_bot_eq] at h
      have hT1 : T = 1 := by
        apply LinearMap.ext; intro x
        have hx : x ∈ T.eigenspace 1 := by
          change x ∈ Wp
          rw [hWp_top]
          exact Submodule.mem_top
        rwa [Module.End.mem_eigenspace_iff, one_smul] at hx
      have hmat : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) = 1 := by
        ext i j
        have hx : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single j (1 : ZMod 5) =
            Pi.single j (1 : ZMod 5) := by
          rw [← hTapply (Pi.single j (1 : ZMod 5))]
          exact congrArg (fun f : Module.End (ZMod 5) V => f (Pi.single j (1 : ZMod 5))) hT1
        simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using congrFun hx i
      exact Units.ext hmat
    · right; right; left
      have hne : Wm ≠ ⊥ := by
        intro hbot
        have h0 : km = 0 := by
          rw [show km = Module.finrank (ZMod 5) Wm from rfl, hbot, finrank_bot]
        omega
      obtain ⟨w, hwmem, hwnz⟩ : ∃ w, w ∈ Wm ∧ w ≠ 0 :=
        Submodule.exists_mem_ne_zero_of_ne_bot hne
      refine ⟨w, hwnz, ?_⟩
      intro x
      constructor
      · intro hx
        have hxmem : x ∈ Wm := (hmem_neg x).mpr hx
        have hspan := (finrank_eq_one_iff_of_nonzero' (⟨w, hwmem⟩ : Wm)
          (by intro h; exact hwnz (by simpa using congrArg Subtype.val h))).mp
          (by simpa [km] using hkm1)
        obtain ⟨a, ha⟩ := hspan ⟨x, hxmem⟩
        exact ⟨a, (congrArg Subtype.val ha).symm⟩
      · rintro ⟨a, rfl⟩
        exact (hmem_neg (a • w)).mp (Wm.smul_mem a hwmem)
  · have hkp01 : kp = 0 ∨ kp = 1 := by omega
    rcases hkp01 with hkp0 | hkp1
    · right; left
      have hWp_bot : Wp = ⊥ := by
        rw [← Submodule.finrank_eq_zero]
        simpa [kp] using hkp0
      have hWm_top : Wm = ⊤ := by
        have h := hcompl.sup_eq_top
        rwa [hWp_bot, bot_sup_eq] at h
      have hTneg : T = -1 := by
        apply LinearMap.ext; intro x
        have hx : x ∈ T.eigenspace (-1) := by
          change x ∈ Wm
          rw [hWm_top]
          exact Submodule.mem_top
        rwa [Module.End.mem_eigenspace_iff, neg_one_smul] at hx
      have hmat : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) = -1 := by
        ext i j
        have hx : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single j (1 : ZMod 5) =
            -Pi.single j (1 : ZMod 5) := by
          rw [← hTapply (Pi.single j (1 : ZMod 5))]
          simpa using congrArg (fun f : Module.End (ZMod 5) V =>
            f (Pi.single j (1 : ZMod 5))) hTneg
        simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using congrFun hx i
      exact Units.ext (by simpa using hmat)
    · right; right; right
      have hne : Wp ≠ ⊥ := by
        intro hbot
        have h0 : kp = 0 := by
          rw [show kp = Module.finrank (ZMod 5) Wp from rfl, hbot, finrank_bot]
        omega
      obtain ⟨w, hwmem, hwnz⟩ : ∃ w, w ∈ Wp ∧ w ≠ 0 :=
        Submodule.exists_mem_ne_zero_of_ne_bot hne
      refine ⟨w, hwnz, ?_⟩
      intro x
      constructor
      · intro hx
        have hxmem : x ∈ Wp := (hmem_pos x).mpr hx
        have hspan := (finrank_eq_one_iff_of_nonzero' (⟨w, hwmem⟩ : Wp)
          (by intro h; exact hwnz (by simpa using congrArg Subtype.val h))).mp
          (by simpa [kp] using hkp1)
        obtain ⟨a, ha⟩ := hspan ⟨x, hxmem⟩
        exact ⟨a, (congrArg Subtype.val ha).symm⟩
      · rintro ⟨a, rfl⟩
        exact (hmem_pos (a • w)).mp (Wp.smul_mem a hwmem)

end CFSG.OddTranspositions.PartThree
