module

public import Certificates.Kernel.AxisPlane.Letters
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import CFSG.Monster.AxisCount.BabyBasic
public import Mathlib.Data.Set.Card

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby CFSG.Monster.AxisCount.Native
  CertificateChecks.KernelAP CFSG.KC.AxisPlane

@[expose] def rowsB (o : BabyOrbit) : Array (Array ℕ) := (o.U.map Cover.wordRows).toArray

@[expose] def wordsB (o : BabyOrbit) : Bool :=
  o.U.all (fun w => w.all Gen.isVis) && o.h.toList.all (fun w => w.all Gen.isVis) &&
    o.h.size == o.lam.size && o.lam.size == o.size.size &&
    (o.h.toList.zip o.lam.toList).all (fun x => Cover.l2Word x.1 x.2 == 63) &&
    o.size.toList.sum == 46575

@[expose] def BabyStmt (o : BabyOrbit) : Prop :=
  wordsB o = true ∧ ∀ r < o.lam.size,
    natOrbit (rowsB o) o.lam[r]! ⊆ Set.Iio (2 ^ 24) ∧
    (natOrbit (rowsB o) o.lam[r]!).ncard = o.size[r]! ∧
    ∀ r' < o.lam.size, r ≠ r' →
      Disjoint (natOrbit (rowsB o) o.lam[r]!) (natOrbit (rowsB o) o.lam[r']!)

theorem forall₂_rows {ws : List (List Gen)} {mss : List (List (Array Nat))}
    (h : List.Forall₂ WordM ws mss) : ws.map Cover.wordRows = mss.map rowsOf := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, wordRows_eq hab.1, ih]

theorem forall₂_vis {ws : List (List Gen)} {mss : List (List (Array Nat))}
    (h : List.Forall₂ WordM ws mss) : ws.all (fun w => w.all Gen.isVis) = true := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.all_cons, hab.2, ih]; rfl

theorem forall₂_zip {ws : List (List Gen)} {mss : List (List (Array Nat))}
    (h : List.Forall₂ WordM ws mss) : ∀ ls : List Nat,
      (mss.zip ls).all (fun x => foldRows x.1 x.2 == 63) = true →
      (ws.zip ls).all (fun x => Cover.l2Word x.1 x.2 == 63) = true := by
  induction h with
  | nil => intro ls _; rfl
  | cons hab _ ih =>
    intro ls hl
    cases ls with
    | nil => rfl
    | cons l ls =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hl ⊢
      exact ⟨by rw [l2Word_eq hab.1]; exact hl.1, ih ls hl.2⟩

theorem words_of {o : BabyOrbit} {rs : List (List Nat)} {msU msH : List (List (Array Nat))}
    (hU : List.Forall₂ WordM o.U msU) (hH : List.Forall₂ WordM o.h.toList msH)
    (hk : (msU.map rowsOf == rs.map List.toArray && o.h.size == o.lam.size &&
      o.lam.size == o.size.size &&
      (msH.zip o.lam.toList).all (fun x => foldRows x.1 x.2 == 63) &&
      o.size.toList.sum == 46575) = true) :
    rowsB o = (rs.map List.toArray).toArray ∧ wordsB o = true := by
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨hr, h1⟩, h2⟩, h3⟩, h4⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [rowsB, forall₂_rows hU, eq_of_beq hr]
  · simp only [wordsB, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨forall₂_vis hU, forall₂_vis hH⟩, h1⟩, h2⟩, forall₂_zip hH _ h3⟩, h4⟩

end CertificateChecks.KernelAP.Baby

end
