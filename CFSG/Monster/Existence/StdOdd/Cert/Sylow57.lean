module

public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.Monster.Existence.StdOdd.Cert.Base
public import CFSG.Monster.Existence.StdOdd.Cert.Reps
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
public meta import CFSG.Monster.Existence.StdOdd.Cert.Reps
public meta import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Inputs
public import Certificates.Certificate6037
public import Certificates.Certificate6036
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate10004
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

@[expose] noncomputable def rgrpMat :
    Rgrp →* Matrix (Fin 78) (Fin 78) K :=
  glMat.comp stdGroup.subtype

theorem rgrpMat_injective :
    Function.Injective rgrpMat := fun _ _ h =>
  Subtype.ext (glMat_injective h)

private theorem coe_stdA :
    (stdA : ModGL Tag.E6 K) = genA := by
  simpa [img2] using congrFun img2_stdA_stdB 0

private theorem coe_stdB :
    (stdB : ModGL Tag.E6 K) = genB := by
  simpa [img2] using congrFun img2_stdA_stdB 1

theorem rgrpMat_stdA :
    rgrpMat stdA = toMat nativeAB.1 :=
  (congrArg glMat coe_stdA).trans glMat_genA

theorem rgrpMat_stdB :
    rgrpMat stdB = toMat nativeAB.2 :=
  (congrArg glMat coe_stdB).trans glMat_genB

theorem rgrpMat_repOf
    (v : List (ℕ × Bool)) :
    rgrpMat (repOf v) = toMat (Native.wordMat nativeAB.1 nativeAB.2 v) := by
  have hA : genA * genA = 1 := by rw [← pow_two, ← orderOf_genA, pow_orderOf_eq_one]
  have hB : genB * genB * genB = 1 := by rw [← pow_three', ← orderOf_genB, pow_orderOf_eq_one]
  show glMat ((repOf v : Rgrp) : ModGL Tag.E6 K) = _
  rw [coe_repOf, glMat_wordProd hA hB]

noncomputable def rgrpSlp
    (prog : List (List ℕ)) : Array Rgrp :=
  slpRunG #[stdA, stdB] prog

theorem rgrpMat_rgrpSlp
    (prog : List (List ℕ)) (i : ℕ) :
    rgrpMat ((rgrpSlp prog).getD i 1) =
      toMat ((Native.slpRun #[nativeAB.1, nativeAB.2] prog).getD i Native.one) := by
  have hAB : (#[stdA, stdB] : Array Rgrp).map rgrpMat =
      (#[nativeAB.1, nativeAB.2] : Array Native.Mat).map toMat := by
    simp only [List.map_toArray, List.map_cons, List.map_nil, rgrpMat_stdA, rgrpMat_stdB]
  have h : (rgrpSlp prog).map rgrpMat =
      (Native.slpRun #[nativeAB.1, nativeAB.2] prog).map toMat := by
    rw [rgrpSlp, map_slpRunG, hAB, toMat_slpRun]
  have e1 := getD_map rgrpMat (rgrpSlp prog) i 1
  have e2 := getD_map toMat (Native.slpRun #[nativeAB.1, nativeAB.2] prog) i Native.one
  rw [← e1, map_one, h, ← toMat_one, e2]

theorem rgrpMat_pow
    (g : Rgrp) (P : Native.Mat) (h : rgrpMat g = toMat P) (n : ℕ) :
    rgrpMat (g ^ n) = toMat (Native.pow P n) := by
  rw [map_pow, h, toMat_pow]

theorem rgrpMat_mul
    (a b : Rgrp) (P Q : Native.Mat) (ha : rgrpMat a = toMat P)
    (hb : rgrpMat b = toMat Q) : rgrpMat (a * b) = toMat (Native.mul P Q) := by
  rw [map_mul, ha, hb, toMat_mul]

theorem sylowFusionCheck_sound
    {p : ℕ} [Fact p.Prime] [Finite Rgrp] {x y : Rgrp}
    {X Y : Native.Mat} {C r : ℕ → Native.Mat}
    (hx : rgrpMat x = toMat X) (hy : rgrpMat y = toMat Y)
    (hxp : orderOf x = p) (h : sylowFusionCheck p X Y C r = true) :
    orderOf y = p ∧ Commute x y ∧ y ∉ Subgroup.zpowers x ∧
      ∀ i < p, ∀ c ρ : Rgrp, rgrpMat c = toMat (C i) → rgrpMat ρ = toMat (r i) →
        IsConj ρ (x ^ i * y) := by
  simp only [sylowFusionCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_of_ordP (g := (y : ModGL Tag.E6 K)) hy h1
  · apply rgrpMat_injective
    rw [map_mul, map_mul, hx, hy, ← toMat_mul, ← toMat_mul]
    exact toMat_eq_of_eqM h2
  · refine not_mem_zpowers_of_forall_ne hxp fun k hk hkx => ?_
    have e : rgrpMat (x ^ k) = toMat (Native.pow X k) := rgrpMat_pow x X hx k
    rw [hkx, hy] at e
    have := eqM_of_toMat_eq e.symm
    rw [h3 k hk] at this
    exact Bool.false_ne_true this
  · intro i hi c ρ hc hρ
    rw [isConj_iff]
    refine ⟨c, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply rgrpMat_injective
    rw [rgrpMat_mul c ρ _ _ hc hρ,
      rgrpMat_mul _ c _ _ (rgrpMat_mul _ y _ _ (rgrpMat_pow x X hx i) hy) hc]
    exact toMat_eq_of_eqM (h4 i hi)

theorem rgrp_finite :
    Finite Rgrp :=
  Nat.finite_of_card_ne_zero (by rw [C2E6Std.card_stdGroup]; norm_num)

theorem sylow5Check_eq_true : sylow5Check = true :=
  Certificates.certificate6037.1

theorem sylow_five_fusion :
    ∃ y₀ : Rgrp, orderOf y₀ = 5 ∧ Commute rep5 y₀ ∧
    y₀ ∉ Subgroup.zpowers rep5 ∧ ∀ i < 5, IsConj rep5 (rep5 ^ i * y₀) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite Rgrp := rgrp_finite
  have hx : rgrpMat rep5 = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord5) :=
    rgrpMat_repOf repWord5
  have hy := rgrpMat_rgrpSlp sylow5Prog sylow5Y
  have h := sylowFusionCheck_sound (p := 5) (x := rep5) (y := (rgrpSlp sylow5Prog).getD sylow5Y 1)
    hx hy orderOf_rep5 sylow5Check_eq_true
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨_, h1, h2, h3, fun i hi => h4 i hi _ rep5 (rgrpMat_rgrpSlp _ _) hx⟩

theorem sylow7Check_eq_true : sylow7Check = true :=
  Certificates.certificate6037.2

theorem sylow_seven_fusion :
    ∃ x₀ y₀ : Rgrp, orderOf x₀ = 7 ∧ orderOf y₀ = 7 ∧ Commute x₀ y₀ ∧
    y₀ ∉ Subgroup.zpowers x₀ ∧ (IsConj rep7A x₀ ∨ IsConj rep7B x₀) ∧
    ∀ i < 7, IsConj rep7A (x₀ ^ i * y₀) ∨ IsConj rep7B (x₀ ^ i * y₀) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite Rgrp := rgrp_finite
  have hx : rgrpMat rep7B = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7B) :=
    rgrpMat_repOf repWord7B
  have hxA : rgrpMat rep7A = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7A) :=
    rgrpMat_repOf repWord7A
  have hy := rgrpMat_rgrpSlp sylow7Prog sylow7Z
  obtain ⟨h1, h2, h3, h4⟩ := sylowFusionCheck_sound (p := 7) (x := rep7B)
    (y := (rgrpSlp sylow7Prog).getD sylow7Z 1) hx hy orderOf_rep7B sylow7Check_eq_true
  refine ⟨rep7B, _, orderOf_rep7B, h1, h2, h3, Or.inr (IsConj.refl _), fun i hi => ?_⟩
  by_cases hA : sylow7IsA.getD i false = true
  · exact Or.inl (h4 i hi _ rep7A (rgrpMat_rgrpSlp _ _) (by simp only [hA]; exact hxA))
  · exact Or.inr (h4 i hi _ rep7B (rgrpMat_rgrpSlp _ _) (by simp only [hA]; exact hx))

end CFSG.Monster.Existence.StdOdd.Cert
