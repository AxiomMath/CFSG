module

public import CFSG.RepresentationTheory.SzMartineau.Normalize
public import CFSG.RepresentationTheory.SzMartineau.Devissage
public import CFSG.RepresentationTheory.SzMartineau.EightCase

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

private lemma exists_eq_coboundary_of_normalized {a c : ℕ} (ha : 1 ≤ a)
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x : (F a)ˣ, Y (torusSz a x) = 0) (hw : Y (w a) = 0) :
    ∃ X, ∀ g, Y g = coboundary (natHom a) (twHom a c) X g := by
  obtain ⟨X₂, hX₂J, hX₂A⟩ := hY.exists_szTwo hw
  obtain ⟨D, hDtorus, hDw, hDroot⟩ : ∃ D : Matrix (Fin 4) (Fin 4) (F a),
      (∀ x : (F a)ˣ, torusMat a x * D = D * torusMat a (x ^ 2 ^ c)) ∧
        wMat a * D = D * wMat a ∧
          Y (rootSz a 1 0) = rootMat a 1 0 * D + D * rootMat a 1 0 := by
    rcases eq_or_lt_of_le ha with h1 | ha2
    · have ha1 : a = 1 := h1.symm
      subst ha1
      exact hY.exists_diag_one hT hX₂J hX₂A
    · exact hY.exists_diag_of_two_le ha2 hT hX₂J hX₂A
  set Y₂ : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a) :=
    Y - coboundary (natHom a) (twHom a c) D with hY₂
  have hY₂c : IsTwistedCocycle (natHom a) (twHom a c) Y₂ := by
    rw [hY₂]
    exact hY.sub (isTwistedCocycle_coboundary _ _ D)
  have hY₂T : ∀ x : (F a)ˣ, Y₂ (torusSz a x) = 0 := by
    intro x
    have h : coboundary (natHom a) (twHom a c) D (torusSz a x) = 0 := by
      rw [coboundary_apply, natHom_torusSz, twHom_torusSz]
      exact sub_eq_zero.mpr (hDtorus x)
    rw [hY₂, Pi.sub_apply, hT x, h, sub_zero]
  have hY₂w : Y₂ (w a) = 0 := by
    have h : coboundary (natHom a) (twHom a c) D (w a) = 0 := by
      rw [coboundary_apply, natHom_w, twHom_w]
      exact sub_eq_zero.mpr hDw
    rw [hY₂, Pi.sub_apply, hw, h, sub_zero]
  have hY₂root : Y₂ (rootSz a 1 0) = 0 := by
    have hcob : coboundary (natHom a) (twHom a c) D (rootSz a 1 0) =
        rootMat a 1 0 * D - D * rootMat a 1 0 := by
      rw [coboundary_apply, natHom_rootSz, twHom_rootSz_one_zero]
    have hc : rootMat a 1 0 * D - D * rootMat a 1 0 =
        rootMat a 1 0 * D + D * rootMat a 1 0 := by
      rw [sub_eq_add_neg, CharTwo.neg_eq]
    rw [hY₂, Pi.sub_apply, hDroot, hcob, hc, sub_self]
  have hzero : ∀ g, Y₂ g = 0 :=
    hY₂c.eq_zero_of_normalized hY₂T hY₂w hY₂root
  refine ⟨D, fun g => ?_⟩
  have hY₂g : Y₂ g = 0 := hzero g
  rw [hY₂, Pi.sub_apply] at hY₂g
  exact sub_eq_zero.mp hY₂g

theorem isTwistedCocycle_eq_coboundary {a : ℕ} (ha : 1 ≤ a) (c : ℕ)
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    ∃ X, ∀ g, Y g = coboundary (natHom a) (twHom a c) X g := by
  obtain ⟨X₁, hX₁T, hX₁w⟩ := hY.exists_normalized
  set Y₁ : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a) :=
    Y - coboundary (natHom a) (twHom a c) X₁ with hY₁
  have hY₁c : IsTwistedCocycle (natHom a) (twHom a c) Y₁ := by
    rw [hY₁]
    exact hY.sub (isTwistedCocycle_coboundary _ _ X₁)
  have hY₁T : ∀ x : (F a)ˣ, Y₁ (torusSz a x) = 0 := by
    intro x
    rw [hY₁, Pi.sub_apply, hX₁T x, sub_self]
  have hY₁w : Y₁ (w a) = 0 := by
    rw [hY₁, Pi.sub_apply, hX₁w, sub_self]
  obtain ⟨X₂, hX₂⟩ := exists_eq_coboundary_of_normalized ha hY₁c hY₁T hY₁w
  refine ⟨X₁ + X₂, fun g => ?_⟩
  have hYg : Y g = Y₁ g + coboundary (natHom a) (twHom a c) X₁ g := by
    rw [hY₁, Pi.sub_apply, sub_add_cancel]
  rw [coboundary_add, hYg, hX₂ g, add_comm]

end CFSG.RepresentationTheory.SzMartineau
