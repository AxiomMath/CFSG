module

public import CFSG.RepresentationTheory.SzMartineau.Relations
public import CFSG.RepresentationTheory.SzMartineau.Cocycle
public import CFSG.RepresentationTheory.SzMartineau.SzTwo
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

private noncomputable def torusHom (a : ℕ) : (F a)ˣ →* ↥(Sz a) :=
  MonoidHom.mk' (torusSz a) fun x y => (torusSz_mul_torusSz a x y).symm

@[simp] private theorem torusHom_apply (a : ℕ) (x : (F a)ˣ) : torusHom a x = torusSz a x := rfl

theorem rootMat_one_zero_eq_szX₀ (a : ℕ) :
    rootMat a 1 0 = (szX₀ : Matrix (Fin 4) (Fin 4) (F a)) := by
  rw [rootMat_one_zero, szX₀]

theorem wMat_eq_szJ (a : ℕ) : wMat a = (szJ : Matrix (Fin 4) (Fin 4) (F a)) := by
  rw [wMat, szJ]

theorem coboundary_add {G R : Type*} [Group G] [Ring R] (φ ψ : G →* R) (X X' : R) (g : G) :
    coboundary φ ψ (X + X') g = coboundary φ ψ X g + coboundary φ ψ X' g := by
  simp only [coboundary_apply]
  noncomm_ring

variable {a c : ℕ} {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}

private lemma exists_coboundary_torus (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    ∃ X₁ : Matrix (Fin 4) (Fin 4) (F a),
      ∀ x : (F a)ˣ, Y (torusSz a x) =
        coboundary (natHom a) (twHom a c) X₁ (torusSz a x) := by
  classical
  haveI : Fintype (F a) := Fintype.ofFinite _
  have hH : IsUnit (Fintype.card (F a)ˣ : Matrix (Fin 4) (Fin 4) (F a)) := by
    have hcard : Fintype.card (F a)ˣ = 2 ^ (2 * a + 1) - 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card,
        GaloisField.card 2 (2 * a + 1) (by omega)]
    have h1 : ((2 ^ (2 * a + 1) - 1 : ℕ) : Matrix (Fin 4) (Fin 4) (F a)) = 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow (n := 2 * a + 1))]
      rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      have h2 : (2 : Matrix (Fin 4) (Fin 4) (F a)) = 0 := CharTwo.two_eq_zero
      rw [h2, zero_pow (by omega), zero_sub, CharTwo.neg_eq]
    rw [hcard, h1]
    exact isUnit_one
  obtain ⟨X₁, hX₁⟩ := hY.exists_eq_coboundary_comp (torusHom a) hH
  exact ⟨X₁, fun x => by simpa using hX₁ x⟩

private noncomputable def szP (a : ℕ) : Matrix (Fin 4) (Fin 4) (F a) :=
  !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]

private lemma szP_mul_torus (x : (F a)ˣ) : szP a * torusMat a x = torusMat a x * szP a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szP, torusMat, Matrix.mul_apply, Fin.sum_univ_four]

private lemma wMat_mul_szP : wMat a * szP a = (1 - szP a) * wMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szP, wMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply]

private lemma weyl_commute (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    wMat a * Y (w a) = Y (w a) * wMat a := by
  have h := hY (w a) (w a)
  rw [w_mul_self, hY.map_one, natHom_w, twHom_w] at h
  have h' : wMat a * Y (w a) + Y (w a) * wMat a = 0 := h.symm
  have h'' : wMat a * Y (w a) = -(Y (w a) * wMat a) := by
    rw [eq_neg_iff_add_eq_zero]
    exact h'
  calc wMat a * Y (w a) = -(Y (w a) * wMat a) := h''
    _ = Y (w a) * wMat a := CharTwo.neg_eq _

private lemma weyl_torus (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) (x : (F a)ˣ) :
    Y (w a) * torusMat a (x ^ 2 ^ c) = torusMat a x⁻¹ * Y (w a) := by
  have h1 := hY (w a) (torusSz a x)
  have h2 := hY (torusSz a x⁻¹) (w a)
  rw [hT x, natHom_w, twHom_torusSz, mul_zero, zero_add] at h1
  rw [hT x⁻¹, natHom_torusSz, twHom_w, zero_mul, add_zero] at h2
  rw [w_mul_torusSz] at h1
  rw [h1] at h2
  exact h2

private lemma weyl_Ztorus (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) (x : (F a)ˣ) :
    torusMat a x * (Y (w a) * wMat a) =
      (Y (w a) * wMat a) * torusMat a (x ^ 2 ^ c) := by
  have hb := weyl_torus hY hT x⁻¹
  rw [inv_inv] at hb
  have hw := wMat_mul_torusMat a (((x⁻¹) ^ 2 ^ c)⁻¹)
  rw [inv_inv] at hw
  calc torusMat a x * (Y (w a) * wMat a)
      = (torusMat a x * Y (w a)) * wMat a := by rw [mul_assoc]
    _ = (Y (w a) * torusMat a ((x⁻¹) ^ 2 ^ c)) * wMat a := by rw [← hb]
    _ = Y (w a) * (torusMat a ((x⁻¹) ^ 2 ^ c) * wMat a) := by rw [mul_assoc]
    _ = Y (w a) * (wMat a * torusMat a (((x⁻¹) ^ 2 ^ c)⁻¹)) := by rw [← hw]
    _ = (Y (w a) * wMat a) * torusMat a (((x⁻¹) ^ 2 ^ c)⁻¹) := by rw [mul_assoc]
    _ = (Y (w a) * wMat a) * torusMat a (x ^ 2 ^ c) := by congr 1

private lemma weyl_coboundary_torus (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) (x : (F a)ˣ) :
    coboundary (natHom a) (twHom a c) (szP a * (Y (w a) * wMat a)) (torusSz a x) = 0 := by
  rw [coboundary_apply, natHom_torusSz, twHom_torusSz]
  change torusMat a x * (szP a * (Y (w a) * wMat a)) -
    (szP a * (Y (w a) * wMat a)) * torusMat a (x ^ 2 ^ c) = 0
  have h1 : torusMat a x * (szP a * (Y (w a) * wMat a)) =
      szP a * (torusMat a x * (Y (w a) * wMat a)) := by
    calc torusMat a x * (szP a * (Y (w a) * wMat a))
        = (torusMat a x * szP a) * (Y (w a) * wMat a) := by rw [← mul_assoc]
      _ = (szP a * torusMat a x) * (Y (w a) * wMat a) := by rw [← szP_mul_torus x]
      _ = szP a * (torusMat a x * (Y (w a) * wMat a)) := by rw [mul_assoc]
  have h2 : (szP a * (Y (w a) * wMat a)) * torusMat a (x ^ 2 ^ c) =
      szP a * ((Y (w a) * wMat a) * torusMat a (x ^ 2 ^ c)) := by rw [mul_assoc]
  rw [h1, h2, ← mul_sub, weyl_Ztorus hY hT x, sub_self, mul_zero]

private lemma weyl_coboundary_w (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    coboundary (natHom a) (twHom a c) (szP a * (Y (w a) * wMat a)) (w a) = Y (w a) := by
  rw [coboundary_apply, natHom_w, twHom_w]
  change wMat a * (szP a * (Y (w a) * wMat a)) -
    (szP a * (Y (w a) * wMat a)) * wMat a = Y (w a)
  have hwB : wMat a * Y (w a) = Y (w a) * wMat a := weyl_commute hY
  have hPP : szP a + szP a = 0 := CharTwo.add_self_eq_zero (szP a)
  have h1 : (szP a * (Y (w a) * wMat a)) * wMat a = szP a * Y (w a) := by
    rw [mul_assoc, mul_assoc, wMat_mul_self, mul_one]
  have h2 : wMat a * (szP a * (Y (w a) * wMat a)) = (1 - szP a) * Y (w a) := by
    calc wMat a * (szP a * (Y (w a) * wMat a))
        = (wMat a * szP a) * (Y (w a) * wMat a) := by rw [← mul_assoc]
      _ = ((1 - szP a) * wMat a) * (Y (w a) * wMat a) := by rw [wMat_mul_szP]
      _ = (1 - szP a) * (wMat a * (Y (w a) * wMat a)) := by rw [mul_assoc]
      _ = (1 - szP a) * ((wMat a * Y (w a)) * wMat a) := by
            congr 1
            rw [← mul_assoc]
      _ = (1 - szP a) * ((Y (w a) * wMat a) * wMat a) := by rw [hwB]
      _ = (1 - szP a) * (Y (w a) * (wMat a * wMat a)) := by rw [mul_assoc]
      _ = (1 - szP a) * (Y (w a) * 1) := by rw [wMat_mul_self]
      _ = (1 - szP a) * Y (w a) := by rw [mul_one]
  have h3 : (1 - szP a) * Y (w a) - szP a * Y (w a) = Y (w a) := by
    rw [← sub_mul, sub_sub, hPP, sub_zero, one_mul]
  rw [h2, h1, h3]

private lemma exists_coboundary_weyl (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) :
    ∃ D : Matrix (Fin 4) (Fin 4) (F a),
      (∀ x, coboundary (natHom a) (twHom a c) D (torusSz a x) = 0) ∧
        coboundary (natHom a) (twHom a c) D (w a) = Y (w a) :=
  ⟨szP a * (Y (w a) * wMat a), weyl_coboundary_torus hY hT, weyl_coboundary_w hY⟩

theorem IsTwistedCocycle.exists_normalized (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    ∃ X : Matrix (Fin 4) (Fin 4) (F a),
      (∀ x, Y (torusSz a x) = coboundary (natHom a) (twHom a c) X (torusSz a x)) ∧
        Y (w a) = coboundary (natHom a) (twHom a c) X (w a) := by
  obtain ⟨X₁, hX₁⟩ := exists_coboundary_torus hY
  set Y₁ : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a) :=
    Y - coboundary (natHom a) (twHom a c) X₁ with hY₁
  have hY₁c : IsTwistedCocycle (natHom a) (twHom a c) Y₁ := by
    rw [hY₁]
    exact hY.sub (isTwistedCocycle_coboundary _ _ X₁)
  have hY₁T : ∀ x, Y₁ (torusSz a x) = 0 := by
    intro x
    rw [hY₁]
    simp only [Pi.sub_apply, hX₁ x, sub_self]
  obtain ⟨D, hDtorus, hDw⟩ := exists_coboundary_weyl hY₁c hY₁T
  have hY₁w : Y₁ (w a) = Y (w a) - coboundary (natHom a) (twHom a c) X₁ (w a) := by
    rw [hY₁]
    rfl
  refine ⟨X₁ + D, ?_, ?_⟩
  · intro x
    rw [coboundary_add, hDtorus x, add_zero]
    exact hX₁ x
  · have hYw : Y (w a) = coboundary (natHom a) (twHom a c) X₁ (w a) + Y₁ (w a) := by
      have h' : Y (w a) = Y₁ (w a) + coboundary (natHom a) (twHom a c) X₁ (w a) :=
        eq_add_of_sub_eq hY₁w.symm
      rw [h', add_comm]
    rw [coboundary_add, hDw]
    exact hYw

private lemma szTwo_sq (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    Y (rootSz a 1 0 ^ 2) =
      rootMat a 1 0 * Y (rootSz a 1 0) + Y (rootSz a 1 0) * rootMat a 1 0 := by
  rw [pow_two, hY (rootSz a 1 0) (rootSz a 1 0)]
  simp only [natHom_rootSz, twHom_rootSz_one_zero]

private lemma szTwo_relation_four (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    Y (rootSz a 1 0) * rootMat a 1 0 ^ 3 +
        rootMat a 1 0 * Y (rootSz a 1 0) * rootMat a 1 0 ^ 2 +
        rootMat a 1 0 ^ 2 * Y (rootSz a 1 0) * rootMat a 1 0 +
        rootMat a 1 0 ^ 3 * Y (rootSz a 1 0) = 0 := by
  set A : Matrix (Fin 4) (Fin 4) (F a) := Y (rootSz a 1 0) with hA
  have hg2 := szTwo_sq hY
  rw [← hA] at hg2
  have h := hY (rootSz a 1 0 ^ 2) (rootSz a 1 0 ^ 2)
  rw [← pow_add, show 2 + 2 = 4 by norm_num, rootSz_one_zero_pow_four, hY.map_one] at h
  rw [map_pow (natHom a) (rootSz a 1 0) 2, map_pow (twHom a c) (rootSz a 1 0) 2] at h
  rw [hg2, natHom_rootSz, twHom_rootSz_one_zero] at h
  have h' : rootMat a 1 0 ^ 2 * (rootMat a 1 0 * A + A * rootMat a 1 0) +
      (rootMat a 1 0 * A + A * rootMat a 1 0) * rootMat a 1 0 ^ 2 = 0 := h.symm
  calc A * rootMat a 1 0 ^ 3 + rootMat a 1 0 * A * rootMat a 1 0 ^ 2 +
        rootMat a 1 0 ^ 2 * A * rootMat a 1 0 + rootMat a 1 0 ^ 3 * A
      = rootMat a 1 0 ^ 2 * (rootMat a 1 0 * A + A * rootMat a 1 0) +
        (rootMat a 1 0 * A + A * rootMat a 1 0) * rootMat a 1 0 ^ 2 := by
        noncomm_ring
    _ = 0 := h'

private lemma szTwo_relation_weyl (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hw : Y (w a) = 0) :
    wMat a * Y (rootSz a 1 0) * wMat a =
      rootMat a 1 0 * wMat a * rootMat a 1 0 * Y (rootSz a 1 0) +
        rootMat a 1 0 * wMat a * Y (rootSz a 1 0) * rootMat a 1 0 +
        Y (rootSz a 1 0) * wMat a * rootMat a 1 0 ^ 2 := by
  set A : Matrix (Fin 4) (Fin 4) (F a) := Y (rootSz a 1 0) with hA
  have hg2 := szTwo_sq hY
  rw [← hA] at hg2
  have hgw : Y (rootSz a 1 0 * w a) = A * wMat a := by
    have h := hY (rootSz a 1 0) (w a)
    rw [hw, natHom_rootSz, twHom_w, mul_zero, zero_add, ← hA] at h
    exact h
  have hwg : Y (w a * rootSz a 1 0) = wMat a * A := by
    have h := hY (w a) (rootSz a 1 0)
    rw [hw, twHom_rootSz_one_zero, zero_mul, add_zero, natHom_w, ← hA] at h
    exact h
  have hwgw : Y (w a * rootSz a 1 0 * w a) = wMat a * A * wMat a := by
    have h := hY (w a * rootSz a 1 0) (w a)
    rw [hw, hwg, twHom_w, mul_zero, zero_add] at h
    exact h
  have hgwg2 : Y (rootSz a 1 0 * w a * rootSz a 1 0 ^ 2) =
      rootMat a 1 0 * wMat a * rootMat a 1 0 * A +
        rootMat a 1 0 * wMat a * A * rootMat a 1 0 +
        A * wMat a * rootMat a 1 0 ^ 2 := by
    have h := hY (rootSz a 1 0 * w a) (rootSz a 1 0 ^ 2)
    rw [hgw, map_pow (twHom a c) (rootSz a 1 0) 2] at h
    rw [hg2, twHom_rootSz_one_zero] at h
    rw [map_mul (natHom a) (rootSz a 1 0) (w a), natHom_rootSz, natHom_w] at h
    have h' : (rootMat a 1 0 * wMat a) * (rootMat a 1 0 * A + A * rootMat a 1 0) +
        (A * wMat a) * rootMat a 1 0 ^ 2 =
        rootMat a 1 0 * wMat a * rootMat a 1 0 * A +
          rootMat a 1 0 * wMat a * A * rootMat a 1 0 +
          A * wMat a * rootMat a 1 0 ^ 2 := by noncomm_ring
    rw [h'] at h
    exact h
  rw [w_mul_rootSz_one_zero_mul_w a] at hwgw
  rw [hgwg2] at hwgw
  exact hwgw.symm

theorem IsTwistedCocycle.exists_szTwo (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hw : Y (w a) = 0) :
    ∃ X : Matrix (Fin 4) (Fin 4) (F a), wMat a * X = X * wMat a ∧
      Y (rootSz a 1 0) = rootMat a 1 0 * X + X * rootMat a 1 0 := by
  have h4 := szTwo_relation_four hY
  have hC := szTwo_relation_weyl hY hw
  have h4' : Y (rootSz a 1 0) * szX₀ ^ 3 + szX₀ * Y (rootSz a 1 0) * szX₀ ^ 2 +
      szX₀ ^ 2 * Y (rootSz a 1 0) * szX₀ + szX₀ ^ 3 * Y (rootSz a 1 0) = 0 := by
    rw [rootMat_one_zero_eq_szX₀ a] at h4
    exact h4
  have hC' : szJ * Y (rootSz a 1 0) * szJ =
      szX₀ * szJ * szX₀ * Y (rootSz a 1 0) +
        szX₀ * szJ * Y (rootSz a 1 0) * szX₀ +
        Y (rootSz a 1 0) * szJ * szX₀ ^ 2 := by
    rw [wMat_eq_szJ a, rootMat_one_zero_eq_szX₀ a] at hC
    exact hC
  obtain ⟨X, hXJ, hXA⟩ := exists_szTwo_coboundary (Y (rootSz a 1 0)) h4' hC'
  refine ⟨X, ?_, ?_⟩
  · rw [wMat_eq_szJ a]
    exact hXJ
  · rw [rootMat_one_zero_eq_szX₀ a]
    exact hXA

end CFSG.RepresentationTheory.SzMartineau
