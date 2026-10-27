module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainGroups
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4cAux

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def coordRoot (t : ℕ) (e : V t) (i : Fin t) : Dual F (V t) :=
  e i • LinearMap.proj i

@[expose] def coordCoroot (t : ℕ) (e : V t) (i : Fin t) : V t :=
  Pi.single i (e i)

theorem coordRoot_apply (t : ℕ) (e : V t) (i : Fin t) (v : V t) :
    coordRoot t e i v = e i * v i := by
  simp [coordRoot]

theorem coordCoroot_apply (t : ℕ) (e : V t) (i k : Fin t) :
    coordCoroot t e i k = if k = i then e i else 0 := by
  rw [coordCoroot, Pi.single_apply]

private theorem pcd_sq_all : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

private theorem pcd_sq {x : ZMod 3} (hx : x ≠ 0) : x * x = 1 := pcd_sq_all x hx

private theorem pcd_pairing_coord {t : ℕ} {e : V t} {i j : Fin t} (hi : e i ≠ 0) :
    coordRoot t e i (coordCoroot t e j) = if i = j then 1 else 0 := by
  rw [coordRoot_apply, coordCoroot_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    exact pcd_sq hi
  · rw [if_neg h, if_neg h, mul_zero]

private theorem pcd_pairA {t : ℕ} {e : V t} {a b p q : Fin t}
    (ha : e a ≠ 0) (hb : e b ≠ 0) :
    (coordRoot t e a - coordRoot t e b) (coordCoroot t e p - coordCoroot t e q) =
      (if a = p then 1 else 0) - (if a = q then 1 else 0) -
        ((if b = p then 1 else 0) - (if b = q then 1 else 0)) := by
  simp only [LinearMap.sub_apply, map_sub]
  rw [pcd_pairing_coord (j := p) ha, pcd_pairing_coord (j := q) ha,
    pcd_pairing_coord (j := p) hb, pcd_pairing_coord (j := q) hb]
  ring

private theorem pcd_pairB_last {t : ℕ} {e : V t} {a b l : Fin t}
    (ha : e a ≠ 0) (hb : e b ≠ 0) :
    (coordRoot t e a - coordRoot t e b) (2 • coordCoroot t e l) =
      (2 : F) * (if a = l then 1 else 0) - (2 : F) * (if b = l then 1 else 0) := by
  rw [two_nsmul]
  simp only [map_add, LinearMap.sub_apply, pcd_pairing_coord (j := l) ha,
    pcd_pairing_coord (j := l) hb]
  ring

private theorem pcd_pairB_coord {t : ℕ} {e : V t} {i l : Fin t} (hi : e i ≠ 0) :
    coordRoot t e i (2 • coordCoroot t e l) = (2 : F) * (if i = l then 1 else 0) := by
  rw [two_nsmul]
  simp only [map_add, pcd_pairing_coord (j := l) hi]
  ring

@[expose] def chainRootA (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 1) → Fin t) (κ : Fin m) :
    Dual F (V t) :=
  coordRoot t e (c κ.castSucc) - coordRoot t e (c κ.succ)

@[expose] def chainCorootA (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 1) → Fin t) (κ : Fin m) :
    V t :=
  coordCoroot t e (c κ.castSucc) - coordCoroot t e (c κ.succ)

@[expose] def chainRootB (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 1) → Fin t) :
    Fin (m + 1) → Dual F (V t) :=
  Fin.lastCases (coordRoot t e (c (Fin.last m))) (chainRootA t e c)

@[expose] def chainCorootB (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 1) → Fin t) :
    Fin (m + 1) → V t :=
  Fin.lastCases (2 • coordCoroot t e (c (Fin.last m))) (chainCorootA t e c)

@[expose] def chainRootD (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 2) → Fin t) :
    Fin (m + 2) → Dual F (V t) :=
  Fin.lastCases (coordRoot t e (c (Fin.last m).castSucc) + coordRoot t e (c (Fin.last (m + 1))))
    (chainRootA t e c)

@[expose] def chainCorootD (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 2) → Fin t) :
    Fin (m + 2) → V t :=
  Fin.lastCases
    (coordCoroot t e (c (Fin.last m).castSucc) + coordCoroot t e (c (Fin.last (m + 1))))
    (chainCorootA t e c)

@[expose] def chainReflB (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 1) → Fin t) :
    Fin (m + 1) → (V t ≃ₗ[F] V t) :=
  Fin.lastCases (negEquiv t (c (Fin.last m))) fun κ => swapTwist t e (c κ.castSucc) (c κ.succ)

@[expose] def chainReflD (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 2) → Fin t) :
    Fin (m + 2) → (V t ≃ₗ[F] V t) :=
  Fin.lastCases (forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1))))
    fun κ => swapTwist t e (c κ.castSucc) (c κ.succ)

theorem chainRootA_apply (t : ℕ) (e : V t) {m : ℕ} (c : Fin (m + 1) → Fin t) (κ : Fin m)
    (v : V t) :
    chainRootA t e c κ v = e (c κ.castSucc) * v (c κ.castSucc) - e (c κ.succ) * v (c κ.succ) := by
  simp [chainRootA, coordRoot_apply]

private theorem pcd_cartanA_int {m : ℕ} (κ μ : Fin m) :
    (if κ = μ then (1 : ℤ) else 0) - (if κ.castSucc = μ.succ then 1 else 0) -
        ((if κ.succ = μ.castSucc then 1 else 0) - (if κ = μ then 1 else 0)) =
      CartanMatrix.A m κ μ := by
  have h1 : (κ = μ) ↔ (κ.val = μ.val) := Fin.ext_iff
  have h2 : (κ.castSucc = μ.succ) ↔ (κ.val = μ.val + 1) := by
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  have h3 : (κ.succ = μ.castSucc) ↔ (κ.val + 1 = μ.val) := by
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  simp only [CartanMatrix.A, Matrix.of_apply, h1, h2, h3]
  split_ifs <;> omega

private theorem pcd_cartanA_entry {m : ℕ} (κ μ : Fin m) :
    ((if κ = μ then 1 else 0) - (if κ.castSucc = μ.succ then 1 else 0) -
        ((if κ.succ = μ.castSucc then 1 else 0) - (if κ = μ then 1 else 0)) : F) =
      (CartanMatrix.A m κ μ : F) := by
  rw [← pcd_cartanA_int κ μ]
  push_cast
  ring

theorem chainA_pairing {t m : ℕ} {e : V t} {c : Fin (m + 1) → Fin t} (hc : Function.Injective c)
    (he : ∀ κ, e (c κ) ≠ 0) (κ μ : Fin m) :
    chainRootA t e c κ (chainCorootA t e c μ) = (CartanMatrix.A m κ μ : F) := by
  simp only [chainRootA, chainCorootA]
  rw [pcd_pairA (he κ.castSucc) (he κ.succ)]
  simp only [hc.eq_iff, Fin.castSucc_inj, Fin.succ_inj]
  exact pcd_cartanA_entry κ μ

private theorem pcd_cartanB_castSucc {m : ℕ} (κ μ : Fin m) :
    CartanMatrix.B (m + 1) κ.castSucc μ.castSucc = CartanMatrix.A m κ μ := by
  have hκ : κ.val < m := κ.isLt
  have hμ : μ.val < m := μ.isLt
  simp only [CartanMatrix.B, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc]
  push_cast
  by_cases h1 : κ.val = μ.val
  · simp only [if_pos h1]
  · simp only [if_neg h1]
    by_cases h2 : κ.val + 1 = μ.val
    · have h3 : ¬ (μ.val + 1 = κ.val) := by omega
      have h4 : ¬ (μ.val = m) := by omega
      simp only [if_pos h2, if_neg h4, if_pos (Or.inl h2)]
    · simp only [if_neg h2]
      by_cases h3 : μ.val + 1 = κ.val
      · have h4 : ¬ (μ.val = m) := by omega
        simp only [if_pos h3, if_pos (Or.inr h3)]
      · simp only [if_neg h3, if_neg (not_or.mpr ⟨h2, h3⟩)]

private theorem pcd_cartanB_castSucc_last {m : ℕ} (κ : Fin m) :
    (CartanMatrix.B (m + 1) κ.castSucc (Fin.last m) : F) =
      if κ.val + 1 = m then -2 else 0 := by
  have hκ : κ.val < m := κ.isLt
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
  push_cast
  rw [if_pos rfl]
  by_cases h : κ.val + 1 = m
  · have h1 : ¬ (κ.val = m) := by omega
    simp only [if_neg h1, if_pos h]
  · have h1 : ¬ (κ.val = m) := by omega
    have h2 : ¬ (m + 1 = κ.val) := by omega
    simp only [if_neg h1, if_neg h, if_neg h2]

private theorem pcd_cartanB_last_castSucc {m : ℕ} (κ : Fin m) :
    (CartanMatrix.B (m + 1) (Fin.last m) κ.castSucc : F) =
      if κ.val + 1 = m then -1 else 0 := by
  have hκ : κ.val < m := κ.isLt
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
  push_cast
  by_cases h : κ.val + 1 = m
  · have h1 : ¬ (m = κ.val) := by omega
    have h2 : ¬ (m + 1 = κ.val) := by omega
    simp only [if_neg h1, if_neg h2, if_pos h]
  · have h1 : ¬ (m = κ.val) := by omega
    have h2 : ¬ (m + 1 = κ.val) := by omega
    simp only [if_neg h1, if_neg h2, if_neg h]

theorem chainB_pairing {t m : ℕ} {e : V t} {c : Fin (m + 1) → Fin t} (hc : Function.Injective c)
    (he : ∀ κ, e (c κ) ≠ 0) (κ μ : Fin (m + 1)) :
    chainRootB t e c κ (chainCorootB t e c μ) = (CartanMatrix.B (m + 1) κ μ : F) := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last μ with ⟨μ', rfl⟩ | rfl
    · simp only [chainRootB, chainCorootB, Fin.lastCases_castSucc]
      rw [chainA_pairing hc he κ' μ']
      exact congrArg (fun x : ℤ => (x : F)) (pcd_cartanB_castSucc κ' μ').symm
    · simp only [chainRootB, chainCorootB, Fin.lastCases_castSucc, Fin.lastCases_last, chainRootA]
      rw [pcd_pairB_last (he κ'.castSucc) (he κ'.succ), pcd_cartanB_castSucc_last]
      have hκ : κ'.val < m := κ'.isLt
      simp only [hc.eq_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
      by_cases h : κ'.val + 1 = m
      · have h1 : ¬ (κ'.val = m) := by omega
        simp only [if_pos h, if_neg h1]; norm_num
      · have h1 : ¬ (κ'.val = m) := by omega
        simp only [if_neg h, if_neg h1]; norm_num
  · rcases Fin.eq_castSucc_or_eq_last μ with ⟨μ', rfl⟩ | rfl
    · simp only [chainRootB, chainCorootB, Fin.lastCases_last, Fin.lastCases_castSucc]
      simp only [chainCorootA, map_sub]
      rw [pcd_pairing_coord (j := c μ'.castSucc) (he (Fin.last m)),
        pcd_pairing_coord (j := c μ'.succ) (he (Fin.last m)), pcd_cartanB_last_castSucc]
      have hκ : μ'.val < m := μ'.isLt
      simp only [hc.eq_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
      by_cases h : μ'.val + 1 = m
      · have h1 : ¬ (m = μ'.val) := by omega
        simp only [if_pos h.symm, if_pos h, if_neg h1]; norm_num
      · have h1 : ¬ (m = μ'.val) := by omega
        have h' : ¬ (m = μ'.val + 1) := fun hh => h hh.symm
        simp only [if_neg h', if_neg h, if_neg h1]; norm_num
    · simp only [chainRootB, chainCorootB, Fin.lastCases_last]
      rw [pcd_pairB_coord (he (Fin.last m)), CartanMatrix.B_diag]
      norm_num

private theorem pcd_cartanD_castSucc {m : ℕ} (κ μ : Fin (m + 1)) :
    CartanMatrix.D (m + 2) κ.castSucc μ.castSucc = CartanMatrix.A (m + 1) κ μ := by
  have hκ := κ.isLt
  have hμ := μ.isLt
  simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc]
  split_ifs <;> omega

private theorem pcd_cartanD_castSucc_last {m : ℕ} (κ : Fin (m + 1)) :
    CartanMatrix.D (m + 2) κ.castSucc (Fin.last (m + 1)) =
      if κ.val + 1 = m then -1 else 0 := by
  have hκ := κ.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_last,
    or_true, and_true]
  split_ifs <;> omega

private theorem pcd_cartanD_last_castSucc {m : ℕ} (κ : Fin (m + 1)) :
    CartanMatrix.D (m + 2) (Fin.last (m + 1)) κ.castSucc =
      if κ.val + 1 = m then -1 else 0 := by
  have hκ := κ.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_last,
    or_true, and_true]
  split_ifs <;> omega

private theorem pcd_cartanD_castSucc_last_F {m : ℕ} (κ : Fin (m + 1)) :
    (CartanMatrix.D (m + 2) κ.castSucc (Fin.last (m + 1)) : F) =
      if κ.val + 1 = m then -1 else 0 := by
  rw [pcd_cartanD_castSucc_last]
  push_cast
  ring

private theorem pcd_cartanD_last_castSucc_F {m : ℕ} (κ : Fin (m + 1)) :
    (CartanMatrix.D (m + 2) (Fin.last (m + 1)) κ.castSucc : F) =
      if κ.val + 1 = m then -1 else 0 := by
  rw [pcd_cartanD_last_castSucc]
  push_cast
  ring

theorem chainD_pairing {t m : ℕ} {e : V t} {c : Fin (m + 2) → Fin t} (hc : Function.Injective c)
    (he : ∀ κ, e (c κ) ≠ 0) (κ μ : Fin (m + 2)) :
    chainRootD t e c κ (chainCorootD t e c μ) = (CartanMatrix.D (m + 2) κ μ : F) := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last μ with ⟨μ', rfl⟩ | rfl
    · simp only [chainRootD, chainCorootD, Fin.lastCases_castSucc]
      rw [chainA_pairing hc he κ' μ']
      exact congrArg (fun x : ℤ => (x : F)) (pcd_cartanD_castSucc κ' μ').symm
    · simp only [chainRootD, chainCorootD, Fin.lastCases_castSucc, Fin.lastCases_last,
        chainRootA, LinearMap.sub_apply, map_add]
      rw [pcd_pairing_coord (j := c ((Fin.last m).castSucc)) (he κ'.castSucc),
        pcd_pairing_coord (j := c (Fin.last (m + 1))) (he κ'.castSucc),
        pcd_pairing_coord (j := c ((Fin.last m).castSucc)) (he κ'.succ),
        pcd_pairing_coord (j := c (Fin.last (m + 1))) (he κ'.succ),
        pcd_cartanD_castSucc_last_F]
      have hκ : κ'.val < m + 1 := κ'.isLt
      simp only [hc.eq_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
      by_cases h : κ'.val + 1 = m
      · have h1 : ¬ (κ'.val = m) := by omega
        have h2 : ¬ (κ'.val = m + 1) := by omega
        have h3 : ¬ (κ'.val + 1 = m + 1) := by omega
        simp only [if_pos h, if_neg h1, if_neg h2, if_neg h3]; norm_num
      · by_cases hq : κ'.val = m
        · have h1 : ¬ (κ'.val = m + 1) := by omega
          have h3 : κ'.val + 1 = m + 1 := by omega
          simp only [if_neg h, if_pos hq, if_neg h1, if_pos h3]; norm_num
        · have h1 : ¬ (κ'.val = m + 1) := by omega
          have h3 : ¬ (κ'.val + 1 = m + 1) := by omega
          simp only [if_neg h, if_neg hq, if_neg h1, if_neg h3]; norm_num
  · rcases Fin.eq_castSucc_or_eq_last μ with ⟨μ', rfl⟩ | rfl
    · simp only [chainRootD, chainCorootD, Fin.lastCases_last, Fin.lastCases_castSucc,
        chainCorootA, LinearMap.add_apply, map_sub]
      rw [pcd_pairing_coord (j := c μ'.castSucc) (he (Fin.last m).castSucc),
        pcd_pairing_coord (j := c μ'.succ) (he (Fin.last m).castSucc),
        pcd_pairing_coord (j := c μ'.castSucc) (he (Fin.last (m + 1))),
        pcd_pairing_coord (j := c μ'.succ) (he (Fin.last (m + 1))),
        pcd_cartanD_last_castSucc_F]
      have hκ : μ'.val < m + 1 := μ'.isLt
      simp only [hc.eq_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
      by_cases h : μ'.val + 1 = m
      · have h1 : ¬ (m = μ'.val) := by omega
        have h2 : ¬ (m + 1 = μ'.val) := by omega
        have h4 : ¬ (m + 1 = μ'.val + 1) := by omega
        rw [if_pos h, if_pos h.symm, if_neg h1, if_neg h2, if_neg h4]
        norm_num
      · by_cases hq : μ'.val = m
        · have h1 : ¬ (m + 1 = μ'.val) := by omega
          have h3 : ¬ (m = μ'.val + 1) := by omega
          have h4 : m + 1 = μ'.val + 1 := by omega
          rw [if_neg h, if_pos hq.symm, if_neg h1, if_neg h3, if_pos h4]
          norm_num
        · have h1 : ¬ (m + 1 = μ'.val) := by omega
          have h3 : ¬ (m = μ'.val + 1) := by omega
          have h4 : ¬ (m + 1 = μ'.val + 1) := by omega
          rw [if_neg h, if_neg (fun hh : m = μ'.val => hq hh.symm), if_neg h1, if_neg h3,
            if_neg h4]
          norm_num
    · simp only [chainRootD, chainCorootD, Fin.lastCases_last, LinearMap.add_apply, map_add,
        pcd_pairing_coord (j := c ((Fin.last m).castSucc)) (he (Fin.last m).castSucc),
        pcd_pairing_coord (j := c (Fin.last (m + 1))) (he (Fin.last m).castSucc),
        pcd_pairing_coord (j := c ((Fin.last m).castSucc)) (he (Fin.last (m + 1))),
        pcd_pairing_coord (j := c (Fin.last (m + 1))) (he (Fin.last (m + 1))),
        CartanMatrix.D_diag]
      have hpl : ((Fin.last m).castSucc : Fin (m + 2)) ≠ Fin.last (m + 1) := by
        simp [Fin.ext_iff]
      simp only [hc.eq_iff, if_neg (fun hh : ((Fin.last m).castSucc : Fin (m + 2)) =
        Fin.last (m + 1) => hpl hh), if_neg (fun hh : Fin.last (m + 1) =
        ((Fin.last m).castSucc : Fin (m + 2)) => hpl hh.symm)]; norm_num

private theorem pcd_reflection_swapTwist {t : ℕ} {e : V t} {a b : Fin t} (ha : e a ≠ 0)
    (hb : e b ≠ 0)
    (h : (coordRoot t e a - coordRoot t e b) (coordCoroot t e a - coordCoroot t e b) = 2) :
    Module.reflection h = swapTwist t e a b := by
  have hne : a ≠ b := by
    intro hab
    subst hab
    simp only [sub_self, LinearMap.zero_apply] at h
    exact absurd h (by decide)
  have hs : e a * e a = 1 := pcd_sq ha
  have ht : e b * e b = 1 := pcd_sq hb
  apply LinearEquiv.ext
  intro v
  funext k
  rw [Module.reflection_apply, swapTwist_apply ha hb v k]
  by_cases hka : k = a
  · rw [hka]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
      coordRoot_apply, coordCoroot_apply, if_true, if_neg hne, sub_zero]
    calc v a - (e a * v a - e b * v b) * e a
        = v a - (e a * v a * e a - e b * v b * e a) := by ring
      _ = e a * e b * v b := by
        rw [show e a * v a * e a = v a by
          rw [mul_assoc, mul_comm (v a) (e a), ← mul_assoc, hs, one_mul]]
        ring
  · by_cases hkb : k = b
    · rw [hkb]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
        coordRoot_apply, coordCoroot_apply, if_neg (Ne.symm hne), if_true, zero_sub]
      calc v b - (e a * v a - e b * v b) * (-e b)
          = v b - (-(e a * v a * e b) + e b * v b * e b) := by ring
        _ = e a * e b * v a := by
          rw [show e b * v b * e b = v b by
            rw [mul_assoc, mul_comm (v b) (e b), ← mul_assoc, ht, one_mul]]
          ring
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
        coordRoot_apply, coordCoroot_apply, if_neg hka, if_neg hkb, sub_zero, sub_self, mul_zero]

private theorem pcd_reflection_neg {t : ℕ} {e : V t} {l : Fin t} (hl : e l ≠ 0)
    (h : coordRoot t e l (2 • coordCoroot t e l) = 2) :
    Module.reflection h = negEquiv t l := by
  have hs : e l * e l = 1 := pcd_sq hl
  apply LinearEquiv.ext
  intro v
  funext k
  rw [Module.reflection_apply, negEquiv_apply]
  by_cases hk : k = l
  · rw [hk]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coordRoot_apply, two_nsmul,
      Pi.add_apply, coordCoroot_apply, if_true]
    calc v l - e l * v l * (e l + e l) = v l - 2 * (e l * e l) * v l := by ring
      _ = - v l := by rw [hs]; ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coordRoot_apply, two_nsmul,
      Pi.add_apply, coordCoroot_apply, if_neg hk, sub_zero, add_zero, mul_zero]

private theorem pcd_reflection_fork {t : ℕ} {e : V t} {p l : Fin t} (hp : e p ≠ 0)
    (hl : e l ≠ 0) (hpl : p ≠ l)
    (h : (coordRoot t e p + coordRoot t e l) (coordCoroot t e p + coordCoroot t e l) = 2) :
    Module.reflection h = forkTwist t e p l := by
  have hs : e p * e p = 1 := pcd_sq hp
  have ht : e l * e l = 1 := pcd_sq hl
  apply LinearEquiv.ext
  intro v
  funext k
  rw [Module.reflection_apply, forkTwist_apply hp hl hpl v k]
  by_cases hkp : k = p
  · rw [hkp]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.add_apply,
      coordRoot_apply, Pi.add_apply, coordCoroot_apply, if_true, if_neg hpl]
    ring_nf
    rw [show e p ^ 2 = 1 by rw [pow_two]; exact hs]
    ring
  · by_cases hkl : k = l
    · rw [hkl]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.add_apply,
        coordRoot_apply, Pi.add_apply, coordCoroot_apply, if_neg (Ne.symm hpl), if_true]
      ring_nf
      rw [show e l ^ 2 = 1 by rw [pow_two]; exact ht]
      ring
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.add_apply,
        coordRoot_apply, Pi.add_apply, coordCoroot_apply, if_neg hkp, if_neg hkl, sub_zero,
        add_zero, mul_zero]

private theorem pcd_reflection_swapTwist_of_eq {t : ℕ} {e : V t} {a b : Fin t} (ha : e a ≠ 0)
    (hb : e b ≠ 0) {A : Dual F (V t)} {B : V t}
    (hA : A = coordRoot t e a - coordRoot t e b)
    (hB : B = coordCoroot t e a - coordCoroot t e b) (h : A B = 2) :
    Module.reflection h = swapTwist t e a b := by
  subst hA
  subst hB
  exact pcd_reflection_swapTwist ha hb h

private theorem pcd_reflection_neg_of_eq {t : ℕ} {e : V t} {l : Fin t} (hl : e l ≠ 0)
    {A : Dual F (V t)} {B : V t} (hA : A = coordRoot t e l)
    (hB : B = 2 • coordCoroot t e l) (h : A B = 2) :
    Module.reflection h = negEquiv t l := by
  subst hA
  subst hB
  exact pcd_reflection_neg hl h

private theorem pcd_reflection_fork_of_eq {t : ℕ} {e : V t} {p l : Fin t} (hp : e p ≠ 0)
    (hl : e l ≠ 0) (hpl : p ≠ l) {A : Dual F (V t)} {B : V t}
    (hA : A = coordRoot t e p + coordRoot t e l)
    (hB : B = coordCoroot t e p + coordCoroot t e l) (h : A B = 2) :
    Module.reflection h = forkTwist t e p l := by
  subst hA
  subst hB
  exact pcd_reflection_fork hp hl hpl h

theorem reflection_chainB {t m : ℕ} {e : V t} {c : Fin (m + 1) → Fin t}
    (he : ∀ κ, e (c κ) ≠ 0) (κ : Fin (m + 1))
    (h : chainRootB t e c κ (chainCorootB t e c κ) = 2) :
    Module.reflection h = chainReflB t e c κ := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · have hA : chainRootB t e c κ'.castSucc =
        coordRoot t e (c κ'.castSucc) - coordRoot t e (c κ'.succ) := by
      simp only [chainRootB, Fin.lastCases_castSucc, chainRootA]
    have hB : chainCorootB t e c κ'.castSucc =
        coordCoroot t e (c κ'.castSucc) - coordCoroot t e (c κ'.succ) := by
      simp only [chainCorootB, Fin.lastCases_castSucc, chainCorootA]
    calc Module.reflection h = swapTwist t e (c κ'.castSucc) (c κ'.succ) :=
          pcd_reflection_swapTwist_of_eq (he κ'.castSucc) (he κ'.succ) hA hB h
      _ = chainReflB t e c κ'.castSucc := by
          simp only [chainReflB, Fin.lastCases_castSucc]
  · have hA : chainRootB t e c (Fin.last m) = coordRoot t e (c (Fin.last m)) := by
      simp only [chainRootB, Fin.lastCases_last]
    have hB : chainCorootB t e c (Fin.last m) = 2 • coordCoroot t e (c (Fin.last m)) := by
      simp only [chainCorootB, Fin.lastCases_last]
    calc Module.reflection h = negEquiv t (c (Fin.last m)) :=
          pcd_reflection_neg_of_eq (he (Fin.last m)) hA hB h
      _ = chainReflB t e c (Fin.last m) := by simp only [chainReflB, Fin.lastCases_last]

theorem reflection_chainD {t m : ℕ} {e : V t} {c : Fin (m + 2) → Fin t}
    (he : ∀ κ, e (c κ) ≠ 0) (κ : Fin (m + 2))
    (h : chainRootD t e c κ (chainCorootD t e c κ) = 2) :
    Module.reflection h = chainReflD t e c κ := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · have hA : chainRootD t e c κ'.castSucc =
        coordRoot t e (c κ'.castSucc) - coordRoot t e (c κ'.succ) := by
      simp only [chainRootD, Fin.lastCases_castSucc, chainRootA]
    have hB : chainCorootD t e c κ'.castSucc =
        coordCoroot t e (c κ'.castSucc) - coordCoroot t e (c κ'.succ) := by
      simp only [chainCorootD, Fin.lastCases_castSucc, chainCorootA]
    calc Module.reflection h = swapTwist t e (c κ'.castSucc) (c κ'.succ) :=
          pcd_reflection_swapTwist_of_eq (he κ'.castSucc) (he κ'.succ) hA hB h
      _ = chainReflD t e c κ'.castSucc := by
          simp only [chainReflD, Fin.lastCases_castSucc]
  · have hfork : c ((Fin.last m).castSucc) ≠ c (Fin.last (m + 1)) := by
      intro heq
      have h1 : (coordRoot t e (c ((Fin.last m).castSucc)) + coordRoot t e (c (Fin.last (m + 1))))
          (coordCoroot t e (c ((Fin.last m).castSucc)) +
            coordCoroot t e (c (Fin.last (m + 1)))) = 1 := by
        rw [heq]
        simp only [LinearMap.add_apply, map_add, pcd_pairing_coord (j := c (Fin.last (m + 1)))
          (he (Fin.last (m + 1)))]
        decide
      have hu : chainRootD t e c (Fin.last (m + 1)) =
          coordRoot t e (c ((Fin.last m).castSucc)) + coordRoot t e (c (Fin.last (m + 1))) := by
        simp only [chainRootD, Fin.lastCases_last]
      have hv : chainCorootD t e c (Fin.last (m + 1)) =
          coordCoroot t e (c ((Fin.last m).castSucc)) +
            coordCoroot t e (c (Fin.last (m + 1))) := by
        simp only [chainCorootD, Fin.lastCases_last]
      rw [← hu, ← hv] at h1
      rw [h1] at h
      exact absurd h (by decide)
    have hA : chainRootD t e c (Fin.last (m + 1)) =
        coordRoot t e (c ((Fin.last m).castSucc)) + coordRoot t e (c (Fin.last (m + 1))) := by
      simp only [chainRootD, Fin.lastCases_last]
    have hB : chainCorootD t e c (Fin.last (m + 1)) =
        coordCoroot t e (c ((Fin.last m).castSucc)) +
          coordCoroot t e (c (Fin.last (m + 1))) := by
      simp only [chainCorootD, Fin.lastCases_last]
    calc Module.reflection h =
          forkTwist t e (c ((Fin.last m).castSucc)) (c (Fin.last (m + 1))) :=
          pcd_reflection_fork_of_eq (he ((Fin.last m).castSucc)) (he (Fin.last (m + 1))) hfork
            hA hB h
      _ = chainReflD t e c (Fin.last (m + 1)) := by
          simp only [chainReflD, Fin.lastCases_last]

theorem range_chainReflB {t m : ℕ} (e : V t) (c : Fin (m + 1) → Fin t) :
    Set.range (chainReflB t e c) =
      Set.range (fun κ : Fin m => swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
        {negEquiv t (c (Fin.last m))} := by
  ext T
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨κ, rfl⟩ | rfl
    · exact Or.inl ⟨κ, by simp only [chainReflB, Fin.lastCases_castSucc]⟩
    · exact Or.inr (by simp only [chainReflB, Fin.lastCases_last])
  · rintro (⟨κ, rfl⟩ | rfl)
    · exact ⟨κ.castSucc, by simp only [chainReflB, Fin.lastCases_castSucc]⟩
    · exact ⟨Fin.last m, by simp only [chainReflB, Fin.lastCases_last]⟩

theorem range_chainReflD {t m : ℕ} (e : V t) (c : Fin (m + 2) → Fin t) :
    Set.range (chainReflD t e c) =
      Set.range (fun κ : Fin (m + 1) => swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
        {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))} := by
  ext T
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨κ, rfl⟩ | rfl
    · exact Or.inl ⟨κ, by simp only [chainReflD, Fin.lastCases_castSucc]⟩
    · exact Or.inr (by simp only [chainReflD, Fin.lastCases_last])
  · rintro (⟨κ, rfl⟩ | rfl)
    · exact ⟨κ.castSucc, by simp only [chainReflD, Fin.lastCases_castSucc]⟩
    · exact ⟨Fin.last (m + 1), by simp only [chainReflD, Fin.lastCases_last]⟩

theorem chainRootA_succ {t m : ℕ} (e : V t) (c : Fin (m + 2) → Fin t) (κ : Fin m) :
    chainRootA t e c κ.succ = chainRootA t e (c ∘ Fin.succ) κ := by
  simp only [chainRootA, Function.comp_apply, Fin.succ_castSucc]

theorem chainRootB_succ {t m : ℕ} (e : V t) (c : Fin (m + 2) → Fin t) (κ : Fin (m + 1)) :
    chainRootB t e c κ.succ = chainRootB t e (c ∘ Fin.succ) κ := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · simp only [chainRootB, Fin.lastCases_castSucc, Fin.succ_castSucc]
    exact chainRootA_succ e c κ'
  · simp only [chainRootB, Fin.lastCases_last, Fin.succ_last, Function.comp_apply]

theorem chainReflB_succ {t m : ℕ} (e : V t) (c : Fin (m + 2) → Fin t) (κ : Fin (m + 1)) :
    chainReflB t e c κ.succ = chainReflB t e (c ∘ Fin.succ) κ := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · simp only [chainReflB, Fin.lastCases_castSucc, Fin.succ_castSucc, Function.comp_apply]
  · simp only [chainReflB, Fin.lastCases_last, Fin.succ_last, Function.comp_apply]

theorem chainRootD_succ {t m : ℕ} (e : V t) (c : Fin (m + 3) → Fin t) (κ : Fin (m + 2)) :
    chainRootD t e c κ.succ = chainRootD t e (c ∘ Fin.succ) κ := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · simp only [chainRootD, Fin.lastCases_castSucc, Fin.succ_castSucc]
    exact chainRootA_succ e c κ'
  · simp only [chainRootD, Fin.lastCases_last, Fin.succ_last,
      Fin.succ_castSucc, Function.comp_apply]

theorem chainReflD_succ {t m : ℕ} (e : V t) (c : Fin (m + 3) → Fin t) (κ : Fin (m + 2)) :
    chainReflD t e c κ.succ = chainReflD t e (c ∘ Fin.succ) κ := by
  rcases Fin.eq_castSucc_or_eq_last κ with ⟨κ', rfl⟩ | rfl
  · simp only [chainReflD, Fin.lastCases_castSucc, Fin.succ_castSucc, Function.comp_apply]
  · simp only [chainReflD, Fin.lastCases_last, Fin.succ_last,
      Fin.succ_castSucc, Function.comp_apply]

theorem cartanB_zero_leaf (m : ℕ) : ∃! x, x ≠ 0 ∧ CartanMatrix.B (m + 2) 0 x ≠ 0 := by
  refine ⟨1, ⟨?_, ?_⟩, ?_⟩
  · simp
  · simp only [CartanMatrix.B, Matrix.of_apply, Fin.val_zero, Fin.val_one,
      if_true]
    split_ifs <;> omega
  · rintro y ⟨hy0, hyA⟩
    simp only [Fin.ext_iff, Fin.val_one]
    have hy0' : y.val ≠ 0 := by simpa only [ne_eq, Fin.ext_iff, Fin.val_zero] using hy0
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_zero] at hyA
    split_ifs at hyA <;> simp_all

theorem cartanB_last_leaf (m : ℕ) :
    ∃! x, x ≠ Fin.last (m + 1) ∧ CartanMatrix.B (m + 2) (Fin.last (m + 1)) x ≠ 0 := by
  refine ⟨⟨m, by omega⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  · simp only [CartanMatrix.B, Matrix.of_apply, Fin.val_last,
      if_true]
    split_ifs <;> omega
  · rintro y ⟨hy, hyA⟩
    simp only [Fin.ext_iff]
    have hy' : y.val ≠ m + 1 := by
      simpa only [ne_eq, Fin.ext_iff, Fin.val_last] using hy
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last] at hyA
    split_ifs at hyA <;> omega

theorem cartanD_zero_leaf (m : ℕ) : ∃! x, x ≠ 0 ∧ CartanMatrix.D (m + 4) 0 x ≠ 0 := by
  refine ⟨1, ⟨?_, ?_⟩, ?_⟩
  · simp
  · simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_zero, Fin.val_one]
    split_ifs <;> simp_all
  · rintro y ⟨hy0, hyA⟩
    simp only [Fin.ext_iff, Fin.val_one]
    have hy0' : y.val ≠ 0 := by simpa only [ne_eq, Fin.ext_iff, Fin.val_zero] using hy0
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_zero] at hyA
    split_ifs at hyA <;> simp_all

theorem cartanD_last_leaf (m : ℕ) :
    ∃! x, x ≠ Fin.last (m + 2) ∧ CartanMatrix.D (m + 3) (Fin.last (m + 2)) x ≠ 0 := by
  refine ⟨⟨m, by omega⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  · simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_last, or_true]
    split_ifs <;> simp_all
  · rintro y ⟨hy, hyA⟩
    simp only [Fin.ext_iff]
    have hy' : y.val ≠ m + 2 := by
      simpa only [ne_eq, Fin.ext_iff, Fin.val_last] using hy
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_last, or_true] at hyA
    split_ifs at hyA <;> omega

theorem cartanD_penult_leaf (m : ℕ) :
    ∃! x, x ≠ (Fin.last (m + 1)).castSucc ∧
      CartanMatrix.D (m + 3) (Fin.last (m + 1)).castSucc x ≠ 0 := by
  refine ⟨⟨m, by omega⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
    omega
  · simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_castSucc, Fin.val_last,
      true_or]
    split_ifs <;> simp_all
  · rintro y ⟨hy, hyA⟩
    simp only [Fin.ext_iff]
    have hy' : y.val ≠ m + 1 := by
      simpa only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] using hy
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_last,
      true_or] at hyA
    split_ifs at hyA <;> omega

theorem chainB_linearIndependent {t m : ℕ} {e : V t} {c : Fin (m + 1) → Fin t}
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0) :
    LinearIndependent F (chainCorootB t e c) := by
  refine linearIndependent_of_det_ne_zero (chainCorootB t e c) (chainRootB t e c) ?_
  have hmat : (Matrix.of fun i j => chainRootB t e c i (chainCorootB t e c j)) =
      (CartanMatrix.B (m + 1)).map (Int.castRingHom F) := by
    ext i j
    rw [Matrix.of_apply, Matrix.map_apply, chainB_pairing hc he]
    rfl
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    CFSG.StandardType.LevTwo.levTwoS4c_det_B (Nat.succ_pos m)]
  decide

theorem chainD_linearIndependent {t m : ℕ} {e : V t} {c : Fin (m + 2) → Fin t}
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0) :
    LinearIndependent F (chainCorootD t e c) := by
  refine linearIndependent_of_det_ne_zero (chainCorootD t e c) (chainRootD t e c) ?_
  have hmat : (Matrix.of fun i j => chainRootD t e c i (chainCorootD t e c j)) =
      (CartanMatrix.D (m + 2)).map (Int.castRingHom F) := by
    ext i j
    rw [Matrix.of_apply, Matrix.map_apply, chainD_pairing hc he]
    rfl
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    CFSG.StandardType.LevTwo.levTwoS4c_det_D (by omega : 2 ≤ m + 2)]
  decide

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw

end
