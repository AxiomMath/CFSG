module

public import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

@[expose] def PMdata : List (List (Fin 4)) :=
  [[3, 2, 1, 2, 3, 1, 2, 1, 0],
   [0, 1, 2, 3, 1, 0],
   [0, 1, 2, 1, 0],
   [],
   [],
   [],
   [],
   [3, 2, 1, 2, 3],
   [],
   [1, 2, 1],
   [],
   [2, 1, 2, 0, 1, 2, 1, 0],
   [2, 1, 2, 0, 1, 2, 3, 1, 0],
   [],
   [],
   [],
   [],
   [],
   [3, 2, 1, 2, 3, 0],
   [],
   [],
   [2, 1, 2],
   [],
   [3, 2, 1, 2, 3, 1, 2, 1]]

@[expose] def PSdata : List (List (Fin 4)) :=
  [[3, 0, 1, 2, 1, 0],
   [0],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [3, 2, 0, 1, 2, 3],
   [],
   [],
   [],
   [],
   [],
   [3],
   [],
   [],
   [],
   [],
   []]

@[expose] def PM (y : Nat) : List (Fin 4) := PMdata.getD y []

@[expose] def PS (y : Nat) : List (Fin 4) := PSdata.getD y []

theorem pairMixed : ∀ y, y < 24 →
    (T1 y = 2 → commb (Rm y) (Sm 1) = true →
      conjW (PM y) (Sm 1) = Sm 1 ∧ conjW (PM y) (Rm y) = Sm 3) ∧
    (T1 y = 1 → commb (Rm y) (Sm 2) = true →
      conjW (PM y) (Sm 2) = Sm 2 ∧ conjW (PM y) (Rm y) = Sm 0) := by
  decide +kernel

theorem pairSameLong : ∀ y, y < 24 → T1 y = 1 → commb (Rm y) (Sm 1) = true → Rm y ≠ Sm 1 →
    conjW (PS y) (Sm 1) = Sm 1 ∧ conjW (PS y) (Rm y) = (Sm 2).mul ((Sm 1).mul (Sm 2)) := by
  decide +kernel

theorem pairSameShort : ∀ y, y < 24 → T1 y = 2 → commb (Rm y) (Sm 2) = true → Rm y ≠ Sm 2 →
    conjW (PS y) (Sm 2) = Sm 2 ∧ conjW (PS y) (Rm y) = (Sm 1).mul ((Sm 2).mul (Sm 1)) := by
  decide +kernel

theorem swap_s1s3 : conjW [3, 2, 1, 0] (Sm 1) = Sm 0 ∧ conjW [3, 2, 1, 0] (Sm 3) = Sm 2 := by
  decide +kernel

theorem swap_s2s0 : conjW [0, 1, 2, 3] (Sm 2) = Sm 3 ∧ conjW [0, 1, 2, 3] (Sm 0) = Sm 1 := by
  decide +kernel

theorem Sm_cls : ∀ j : Fin 4, ∃ x, x < 24 ∧ Sm j = Rm x ∧ T1 x = if j.val < 2 then 1 else 2 := by
  decide +kernel

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

private theorem commb_of_commute_pair {u v : W} {x y : M4} (hu : R.ρ u = x.toMat)
    (hv : R.ρ v = y.toMat) (h : Commute u v) : commb x y = true := by
  rw [commb_iff x y]
  apply M4.toMat_injective
  rw [M4.toMat_mul, M4.toMat_mul, ← hu, ← hv, ← map_mul, ← map_mul, h.eq]

theorem cls_s (i : Fin 4) : R.cls (R.s i) = if i.val < 2 then 1 else 2 := by
  obtain ⟨x, hx, hSx, hTx⟩ := Sm_cls i
  rw [R.cls_eq (t := R.s i) hx (by rw [R.hs, hSx]), hTx]

private theorem pair_stage1 {t₁ t₂ : W} (h₁ : R.IsRefl t₁) (h₂ : R.IsRefl t₂)
    (hc : Commute t₁ t₂) :
    ∃ (g₁ : W) (T : Fin 4) (y : ℕ), (T = 1 ∨ T = 2) ∧ R.cls t₁ = T ∧ g₁ * t₁ * g₁⁻¹ = R.s T ∧
      y < 24 ∧ R.ρ (g₁ * t₂ * g₁⁻¹) = (Rm y).toMat ∧ R.cls t₂ = T1 y ∧
      commb (Rm y) (Sm T) = true := by
  obtain ⟨x, hx, ρx⟩ := R.refl_rep h₁
  obtain ⟨hT, hcx⟩ := stage1 x hx
  have e₁ : R.wd (W1 x) * t₁ * (R.wd (W1 x))⁻¹ = R.s (T1 x) :=
    R.conj_wd_eq ρx (R.hs (T1 x)) hcx
  obtain ⟨y, hy, ρy⟩ := R.refl_rep (h₂.conj (R.wd (W1 x)))
  refine ⟨R.wd (W1 x), T1 x, y, hT, R.cls_eq hx ρx, e₁, hy, ρy, ?_, ?_⟩
  · rw [← R.cls_eq hy ρy, R.cls_conj h₂]
  · refine R.commb_of_commute_pair ρy (R.hs (T1 x)) ?_
    rw [← e₁]
    exact hc.symm.conj _

theorem exists_conj_pair_mixed {t₁ t₂ : W} (h₁ : R.IsRefl t₁) (h₂ : R.IsRefl t₂)
    (hc : Commute t₁ t₂) (hcls : R.cls t₁ ≠ R.cls t₂) :
    ∃ g : W, (g * t₁ * g⁻¹ = R.s 1 ∧ g * t₂ * g⁻¹ = R.s 3) ∨
      (g * t₁ * g⁻¹ = R.s 2 ∧ g * t₂ * g⁻¹ = R.s 0) := by
  obtain ⟨g₁, T, y, hT, hc₁, e₁, hy, ρy, hc₂, hcm⟩ := R.pair_stage1 h₁ h₂ hc
  have hTy : T ≠ T1 y := by rw [← hc₁, ← hc₂]; exact hcls
  have hy12 := (stage1 y hy).1
  have key : ∀ (l : List (Fin 4)) (a b : Fin 4), conjW l (Sm T) = Sm a → conjW l (Rm y) = Sm b →
      R.wd l * g₁ * t₁ * (R.wd l * g₁)⁻¹ = R.s a ∧ R.wd l * g₁ * t₂ * (R.wd l * g₁)⁻¹ = R.s b := by
    intro l a b ha hb
    constructor
    · rw [show R.wd l * g₁ * t₁ * (R.wd l * g₁)⁻¹ = R.wd l * (g₁ * t₁ * g₁⁻¹) * (R.wd l)⁻¹ by
        group, e₁]
      exact R.conj_wd_eq (R.hs T) (R.hs a) ha
    · rw [show R.wd l * g₁ * t₂ * (R.wd l * g₁)⁻¹ = R.wd l * (g₁ * t₂ * g₁⁻¹) * (R.wd l)⁻¹ by
        group]
      exact R.conj_wd_eq ρy (R.hs b) hb
  rcases hT with rfl | rfl
  · have hy2 : T1 y = 2 := hy12.resolve_left (fun h => hTy h.symm)
    obtain ⟨c₁, c₂⟩ := (pairMixed y hy).1 hy2 hcm
    exact ⟨_, Or.inl (key (PM y) 1 3 c₁ c₂)⟩
  · have hy1 : T1 y = 1 := hy12.resolve_right (fun h => hTy h.symm)
    obtain ⟨c₁, c₂⟩ := (pairMixed y hy).2 hy1 hcm
    exact ⟨_, Or.inr (key (PM y) 2 0 c₁ c₂)⟩

theorem exists_conj_pair_same {t₁ t₂ : W} (h₁ : R.IsRefl t₁) (h₂ : R.IsRefl t₂)
    (hc : Commute t₁ t₂) (hne : t₁ ≠ t₂) (hcls : R.cls t₁ = R.cls t₂) :
    ∃ g : W, (g * t₁ * g⁻¹ = R.s 1 ∧ g * t₂ * g⁻¹ = R.s 2 * R.s 1 * R.s 2) ∨
      (g * t₁ * g⁻¹ = R.s 2 ∧ g * t₂ * g⁻¹ = R.s 1 * R.s 2 * R.s 1) := by
  obtain ⟨g₁, T, y, hT, hc₁, e₁, hy, ρy, hc₂, hcm⟩ := R.pair_stage1 h₁ h₂ hc
  have hTy : T1 y = T := by rw [← hc₁, ← hc₂, hcls]
  have hne' : Rm y ≠ Sm T := by
    intro h
    apply hne
    have h' : g₁ * t₂ * g₁⁻¹ = g₁ * t₁ * g₁⁻¹ := by
      apply R.inj
      rw [ρy, h, e₁, R.hs]
    have h'' := congrArg (fun z => g₁⁻¹ * z * g₁) h'
    simpa [mul_assoc] using h''.symm
  have key : ∀ (l : List (Fin 4)) (a b c : Fin 4), conjW l (Sm T) = Sm a →
      conjW l (Rm y) = (Sm b).mul ((Sm c).mul (Sm b)) →
      R.wd l * g₁ * t₁ * (R.wd l * g₁)⁻¹ = R.s a ∧
        R.wd l * g₁ * t₂ * (R.wd l * g₁)⁻¹ = R.s b * R.s c * R.s b := by
    intro l a b c ha hb
    constructor
    · rw [show R.wd l * g₁ * t₁ * (R.wd l * g₁)⁻¹ = R.wd l * (g₁ * t₁ * g₁⁻¹) * (R.wd l)⁻¹ by
        group, e₁]
      exact R.conj_wd_eq (R.hs T) (R.hs a) ha
    · rw [show R.wd l * g₁ * t₂ * (R.wd l * g₁)⁻¹ = R.wd l * (g₁ * t₂ * g₁⁻¹) * (R.wd l)⁻¹ by
        group]
      exact R.conj_wd_eq ρy (R.rho_mul3 (R.hs b) (R.hs c) (R.hs b)) hb
  rcases hT with rfl | rfl
  · obtain ⟨c₁, c₂⟩ := pairSameLong y hy hTy hcm hne'
    exact ⟨_, Or.inl (key (PS y) 1 2 1 c₁ c₂)⟩
  · obtain ⟨c₁, c₂⟩ := pairSameShort y hy hTy hcm hne'
    exact ⟨_, Or.inr (key (PS y) 2 1 2 c₁ c₂)⟩

theorem conj_s1s3 : R.wd [3, 2, 1, 0] * R.s 1 * (R.wd [3, 2, 1, 0])⁻¹ = R.s 0 ∧
    R.wd [3, 2, 1, 0] * R.s 3 * (R.wd [3, 2, 1, 0])⁻¹ = R.s 2 :=
  ⟨R.conj_wd_eq (R.hs 1) (R.hs 0) swap_s1s3.1, R.conj_wd_eq (R.hs 3) (R.hs 2) swap_s1s3.2⟩

theorem conj_s2s0 : R.wd [0, 1, 2, 3] * R.s 2 * (R.wd [0, 1, 2, 3])⁻¹ = R.s 3 ∧
    R.wd [0, 1, 2, 3] * R.s 0 * (R.wd [0, 1, 2, 3])⁻¹ = R.s 1 :=
  ⟨R.conj_wd_eq (R.hs 2) (R.hs 3) swap_s2s0.1, R.conj_wd_eq (R.hs 0) (R.hs 1) swap_s2s0.2⟩

end F4Rep

end CFSG.StandardType.F4Model
