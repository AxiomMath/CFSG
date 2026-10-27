module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Iface

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Perp

variable {b c : K} (F : OmegaFrame Q b c)

@[expose] def OmegaFrame.PerpH (v : V) : Prop :=
  polar Q v (F.e 0) = 0 ∧ polar Q v (F.e 1) = 0 ∧ polar Q v (F.f 0) = 0 ∧ polar Q v (F.f 1) = 0

variable {F}

theorem OmegaFrame.PerpH.add {x y : V} (hx : F.PerpH x) (hy : F.PerpH y) : F.PerpH (x + y) := by
  obtain ⟨a, b, c, d⟩ := hx
  obtain ⟨a', b', c', d'⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [polar_add_left, *]

theorem OmegaFrame.perpH_e2 : F.PerpH (F.e 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [F.polar_ee, F.polar_ef]

theorem OmegaFrame.perpH_f2 : F.PerpH (F.f 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [F.polar_ff, F.polar_fe]

theorem OmegaFrame.perpH_t (s : Fin 2) : F.PerpH (F.t s) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [F.polar_te, F.polar_tf]

end Perp

section Triple

variable {F : OmegaFrame Q 1 1}

@[expose] def OmegaFrame.stdTriple (F : OmegaFrame Q 1 1) (x₂ y₂ : V) (hx : Q x₂ = 0)
    (hy : Q y₂ = 0) (hx' : F.PerpH x₂) (hy' : F.PerpH y₂) (hxy : polar Q x₂ y₂ = 1) :
    F2Triple Q where
  x := ![F.e 0, F.e 1, x₂]
  y := ![F.f 0, F.f 1, y₂]
  Q_x i := by fin_cases i <;> simp [F.Q_e, hx]
  Q_y i := by fin_cases i <;> simp [F.Q_f, hy]
  polar_xx i j := by
    obtain ⟨a, b, c, d⟩ := hx'
    have a' : polar Q (F.e 0) x₂ = 0 := by rw [polar_comm]; exact a
    have b' : polar Q (F.e 1) x₂ = 0 := by rw [polar_comm]; exact b
    fin_cases i <;> fin_cases j <;> simp [F.polar_ee, polar_self_eq_zero hx, a, b, a', b']
  polar_xy i j := by
    obtain ⟨a, b, c, d⟩ := hx'
    obtain ⟨a₂, b₂, c₂, d₂⟩ := hy'
    have a' : polar Q (F.e 0) y₂ = 0 := by rw [polar_comm]; exact a₂
    have b' : polar Q (F.e 1) y₂ = 0 := by rw [polar_comm]; exact b₂
    fin_cases i <;> fin_cases j <;> simp [F.polar_ef, c, d, hxy, a', b']

theorem OmegaFrame.perpH_etau (s : Fin 2) : F.PerpH (F.e 2 + F.f 2 + F.t s) :=
  (F.perpH_e2.add F.perpH_f2).add (F.perpH_t s)

@[expose] def F2Triple.IsRat {b c : K} (T : F2Triple Q) (F : OmegaFrame Q b c) (k : Subfield K) :
    Prop :=
  ∀ i, F.IsRat k (T.x i) ∧ F.IsRat k (T.y i)

@[expose] def OmegaFrame.BadAt (F : OmegaFrame Q 1 1) (k : Subfield K) (u w v : V) : Prop :=
  ∃ l₀ l₁ : K, l₀ ∈ k ∧ l₁ ∈ k ∧ polar Q (v + l₀ • F.e 0 + l₁ • F.e 1) u = 0 ∧
    polar Q (v + l₀ • F.e 0 + l₁ • F.e 1) w = 0

theorem OmegaFrame.BadAt.sub {k : Subfield K} {u w v v' : V} (h : F.BadAt k u w v)
    (h' : F.BadAt k u w v') : F.BadAt k u w (v - v') := by
  obtain ⟨a, b, ha, hb, h1, h2⟩ := h
  obtain ⟨a', b', ha', hb', h1', h2'⟩ := h'
  have key : v - v' + (a - a') • F.e 0 + (b - b') • F.e 1 =
      (v + a • F.e 0 + b • F.e 1) - (v' + a' • F.e 0 + b' • F.e 1) := by module
  exact ⟨a - a', b - b', k.sub_mem ha ha', k.sub_mem hb hb', by rw [key, polar_sub_left, h1, h1',
    sub_zero], by rw [key, polar_sub_left, h2, h2', sub_zero]⟩

theorem OmegaFrame.badAt_of_not_generic {k : Subfield K} (hk : ∀ x : K, x ∈ k ↔ x = 0 ∨ x = 1)
    {u w x₂ y₂ : V} (hx hy hx' hy' hxy) (hδ : Phi Q u w (F.e 0) (F.e 1) ≠ 0)
    (hng : ¬ (F.stdTriple x₂ y₂ hx hy hx' hy' hxy).Generic u w) : F.BadAt k u w x₂ := by
  by_contra hbad
  exact hng ⟨hδ, fun l₀ l₁ h₀ h₁ ⟨h1, h2⟩ =>
    hbad ⟨l₀, l₁, (hk _).2 h₀, (hk _).2 h₁, h1, h2⟩⟩

theorem OmegaFrame.stdTriple_isRat [CharP K 2] {k : Subfield K} {x₂ y₂ : V} (hx hy hx' hy' hxy)
    (hx₂ : F.IsRat k x₂) (hy₂ : F.IsRat k y₂) :
    (F.stdTriple x₂ y₂ hx hy hx' hy' hxy).IsRat F k := by
  intro i
  fin_cases i <;> simp [OmegaFrame.stdTriple, F.isRat_e, F.isRat_f, hx₂, hy₂]

section Char

variable [CharP K 2]

theorem OmegaFrame.Q_etau (s : Fin 2) : Q (F.e 2 + F.f 2 + F.t s) = 0 := by
  have hQt : Q (F.t s) = 1 := by fin_cases s <;> simp [F.Q_t₀, F.Q_t₁]
  rw [map_add₃, F.Q_e, F.Q_f, hQt]
  simp [F.polar_ef, F.polar_et, F.polar_ft, CharTwo.add_self_eq_zero]

@[expose] def OmegaFrame.triple₁ (F : OmegaFrame Q 1 1) : F2Triple Q :=
  F.stdTriple (F.e 2) (F.f 2) (F.Q_e 2) (F.Q_f 2) F.perpH_e2 F.perpH_f2 (by simp [F.polar_ef])

@[expose] def OmegaFrame.triple₂ (F : OmegaFrame Q 1 1) : F2Triple Q :=
  F.stdTriple (F.f 2) (F.e 2) (F.Q_f 2) (F.Q_e 2) F.perpH_f2 F.perpH_e2 (by simp [F.polar_fe])

@[expose] def OmegaFrame.triple₃ (F : OmegaFrame Q 1 1) (s : Fin 2) : F2Triple Q :=
  F.stdTriple (F.e 2 + F.f 2 + F.t s) (F.e 2) (F.Q_etau s) (F.Q_e 2) (F.perpH_etau s) F.perpH_e2
    (by simp [polar_add_left, F.polar_ee, F.polar_fe, F.polar_te])

theorem OmegaFrame.isRat_etau {k : Subfield K} (s : Fin 2) : F.IsRat k (F.e 2 + F.f 2 + F.t s) :=
  ((F.isRat_e 2).add (F.isRat_f 2)).add (F.isRat_t s)

theorem OmegaFrame.triple₁_isRat {k : Subfield K} : F.triple₁.IsRat F k :=
  F.stdTriple_isRat _ _ _ _ _ (F.isRat_e 2) (F.isRat_f 2)

theorem OmegaFrame.triple₂_isRat {k : Subfield K} : F.triple₂.IsRat F k :=
  F.stdTriple_isRat _ _ _ _ _ (F.isRat_f 2) (F.isRat_e 2)

theorem OmegaFrame.triple₃_isRat {k : Subfield K} (s : Fin 2) : (F.triple₃ s).IsRat F k :=
  F.stdTriple_isRat _ _ _ _ _ (F.isRat_etau s) (F.isRat_e 2)

end Char

end Triple

end CFSG.RankThree.PartOne.SEITZ2
