module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section C1Neg

theorem tcrAllowedC1_neg_one_three (dJ dx : TcrCData) : tcrAllowedC1 (-1) 3 dJ dx = false := by
  simp [tcrAllowedC1]

private theorem tcrKindOfK_inj {a b : TwistKind} (h : tcrKindOfK a = tcrKindOfK b) : a = b := by
  cases a <;> cases b <;> simp_all [tcrKindOfK]

variable {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}

theorem tcC1_row_of_allowed_negOne {ΨJ Ψx : Set (Fin Tag.E6.rank → ℤ)} {dJ dx : TcrCData}
    (hJ : TcDataOK ρ ΨJ dJ) (hx : TcDataOK ρ Ψx dx) (h : tcrAllowedC1 (-1) 1 dJ dx = true) :
    TcC1RowNegOne ρ ΨJ Ψx := by
  obtain ⟨hJe, hJr, hJN, hJk⟩ := hJ
  obtain ⟨hXe, hXr, hXN, hXk⟩ := hx
  unfold tcrAllowedC1 at h
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.true_and, Int.reduceBEq, Nat.reduceBEq] at h
  have key : ∀ (Ψ : Set (Fin Tag.E6.rank → ℤ)) (d : TcrCData) (a : TwistKind) (k : TcrKind),
      tcrKindOfK a = k → tcrKindOfK (twistKindOf ρ Ψ) ∈ d.ks → d.ks = [k] →
      twistKindOf ρ Ψ = a := by
    intro Ψ d a k hak h1 h2
    rw [h2, List.mem_singleton] at h1
    exact tcrKindOfK_inj (h1.trans hak.symm)
  obtain ⟨⟨⟨⟨ar, aN⟩, ae⟩, aks⟩, hx'⟩ := h
  refine ⟨by omega, by omega, by omega, key _ _ .inner .inner rfl hJk aks, ?_⟩
  rcases hx' with (⟨⟨⟨br, bN⟩, be⟩, bks⟩ | ⟨⟨⟨br, bN⟩, be⟩, bks⟩) | ⟨⟨⟨br, bN⟩, be⟩, bks⟩
  · exact Or.inl ⟨by omega, by omega, by omega, key _ _ .suN .suN rfl hXk bks⟩
  · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, key _ _ .exc .exc rfl hXk bks⟩)
  · exact Or.inr (Or.inr ⟨by omega, by omega, by omega, key _ _ .suN .suN rfl hXk bks⟩)

theorem tcC1_row_of_allowed_negTwo {ΨJ Ψx : Set (Fin Tag.E6.rank → ℤ)} {dJ dx : TcrCData}
    (hJ : TcDataOK ρ ΨJ dJ) (hx : TcDataOK ρ Ψx dx) (h : tcrAllowedC1 (-1) 2 dJ dx = true) :
    TcC1RowNegTwo ρ ΨJ Ψx := by
  obtain ⟨hJe, hJr, hJN, hJk⟩ := hJ
  obtain ⟨hXe, hXr, hXN, hXk⟩ := hx
  unfold tcrAllowedC1 at h
  simp only [Bool.false_eq_true, and_false, ↓reduceIte, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, Bool.true_and, Int.reduceBEq, Nat.reduceBEq] at h
  have key : ∀ (Ψ : Set (Fin Tag.E6.rank → ℤ)) (d : TcrCData) (a : TwistKind) (k : TcrKind),
      tcrKindOfK a = k → tcrKindOfK (twistKindOf ρ Ψ) ∈ d.ks → d.ks = [k] →
      twistKindOf ρ Ψ = a := by
    intro Ψ d a k hak h1 h2
    rw [h2, List.mem_singleton] at h1
    exact tcrKindOfK_inj (h1.trans hak.symm)
  obtain ⟨⟨⟨⟨ar, aN⟩, ae⟩, aks⟩, hx'⟩ := h
  refine ⟨by omega, by omega, by omega, key _ _ .inner .inner rfl hJk aks, ?_⟩
  rcases hx' with ⟨⟨⟨br, bN⟩, be⟩, bks⟩ | ⟨⟨⟨br, bN⟩, be⟩, bks⟩
  · exact Or.inl ⟨by omega, by omega, by omega, key _ _ .inner .inner rfl hXk bks⟩
  · exact Or.inr ⟨by omega, by omega, by omega, key _ _ .twoD .twoD rfl hXk bks⟩

end C1Neg

end CFSG.StandardType.TableCRes

end
