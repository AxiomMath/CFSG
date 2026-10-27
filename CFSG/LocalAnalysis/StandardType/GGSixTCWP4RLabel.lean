module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenLieTag LargeEvenSplit LargeEvenHalfSplit
  LargeEvenUntwisted LargeEvenInLambda2)
open CFSG.StandardType (GGLabelIso)

section Labels

@[expose] def tcrTagOf : LargeEvenLieTag → TcrTg
  | .A => .A | .twA => .twA | .D => .D | .twD => .twD | .E6 => .E6 | .E7 => .E7
  | .E8 => .E8 | .twE6 => .twE6 | .triD4 => .triD4 | _ => .A

@[expose] def tcrLabOf (l : LargeEvenLabel) : TcrLab := ⟨tcrTagOf l.tag, l.rank, l.n⟩

@[expose] def TcrTagOK (t : LargeEvenLieTag) : Prop :=
  t = .A ∨ t = .twA ∨ t = .D ∨ t = .twD ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twE6 ∨ t = .triD4

theorem tcrLabOf_componentLabel (r N : ℕ) (k : TwistKind) (n : ℕ) :
    tcrLabOf (componentLabel r N k n) = tcrComponentLabel r N (tcrKindOfK k) n := by
  cases k <;> simp only [componentLabel, tcrComponentLabel, tcrLabOf, tcrKindOfK] <;>
    (try split_ifs) <;> simp [tcrTagOf]

theorem tcrTagOK_componentLabel (r N : ℕ) (k : TwistKind) (n : ℕ) :
    TcrTagOK (componentLabel r N k n).tag := by
  cases k <;> simp only [componentLabel] <;> (try split_ifs) <;> simp [TcrTagOK]

theorem tcrSplitT_of {p : ℕ} {lab : LargeEvenLabel} (hlab : TcrTagOK lab.tag)
    (h : LargeEvenSplit p lab) : tcrSplitT p (tcrLabOf lab) = true := by
  obtain ⟨t, r, m⟩ := lab
  cases t <;> simp_all [TcrTagOK, LargeEvenSplit, LargeEvenUntwisted, tcrSplitT, tcrLabOf,
    tcrTagOf, tcrUntw, Nat.dvd_iff_mod_eq_zero]
  tauto

theorem tcrHalfSplitT_of {p : ℕ} {lab : LargeEvenLabel} {c : Prop} (hlab : TcrTagOK lab.tag)
    (h : LargeEvenHalfSplit p lab c) : tcrHalfSplitT p (tcrLabOf lab) = true := by
  obtain ⟨t, r, m⟩ := lab
  cases t <;> simp_all [TcrTagOK, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted,
    tcrHalfSplitT, tcrSplitT, tcrLabOf, tcrTagOf, tcrUntw, Nat.dvd_iff_mod_eq_zero] <;> tauto

theorem tcrLabelClass_of_iso {lab lab' : LargeEvenLabel} (hlab : TcrTagOK lab.tag)
    (h : GGLabelIso lab lab') :
    TcrTagOK lab'.tag ∧ tcrLabOf lab' ∈ tcrLabelClass (tcrLabOf lab) := by
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨t', r', m'⟩ := lab'
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · cases h
    exact ⟨hlab, List.mem_cons_self⟩
  · obtain ⟨h1 | h1, -⟩ := h <;> dsimp only at h1 hlab <;> subst h1 <;> simp [TcrTagOK] at hlab
  · obtain ⟨h1, h2⟩ := h
    cases h1
    cases h2
    simp [TcrTagOK, tcrLabelClass, tcrLabOf, tcrTagOf]
  · obtain ⟨h1, h2⟩ := h
    cases h1
    cases h2
    simp [TcrTagOK, tcrLabelClass, tcrLabOf, tcrTagOf]
  · obtain ⟨h1, h2⟩ := h
    cases h1
    cases h2
    simp [TcrTagOK, tcrLabelClass, tcrLabOf, tcrTagOf]
  · obtain ⟨h1, h2⟩ := h
    cases h1
    cases h2
    simp [TcrTagOK, tcrLabelClass, tcrLabOf, tcrTagOf]
  · obtain ⟨h1, h2⟩ := h
    cases h1
    cases h2
    simp [TcrTagOK, tcrLabelClass, tcrLabOf, tcrTagOf]
  · obtain ⟨h1, h2⟩ := h
    cases h1
    cases h2
    simp [TcrTagOK, tcrLabelClass, tcrLabOf, tcrTagOf]

end Labels

end CFSG.StandardType.TableCRes

end
