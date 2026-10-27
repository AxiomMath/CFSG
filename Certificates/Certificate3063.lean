module

public import CFSG.Monster.B.TwoA.Unitary.Planes
public import Certificates.Certificate3124
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Fischer.F4

public section

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CertificateChecks.Orb14 CertificateChecks.Batch3124

namespace CertificateChecks.Batch3063

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CertificateChecks.Orb14 CertificateChecks.Batch3124

@[expose] noncomputable def X2 : Nat := Nat.lor (pw2 (nat_lit 1386)) (pw2 (nat_lit 2773))

@[expose] noncomputable def ok3063 (X PL : Nat) : Bool :=
  allN 891 fun p => (fun D => andB
    (orB (orB (bit D 0) (bit D 1)) (orB (Nat.beq p 0) (orB (Nat.beq p 1) (Nat.beq p 4))))
    (orB (notB (bit D 1)) (anyN 3 fun a => Nat.blt 0 (fget (rowP PL p a) 5 2))))
    (planeD X (rowP PL p))

theorem k3063 : ok3063 X2 PLP = true := by quickRfl

theorem neg3063 : notB (ok3063 (pw2 (nat_lit 2773)) PLP) = true := by quickRfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem anyN_iff (n : ℕ) (f : ℕ → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [anyN]
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem e1_eq : (Pi.single 1 1 : V6) = vec6 4 := by
  funext t
  fin_cases t <;> rfl

theorem e2_eq : (Pi.single 2 1 : V6) = vec6 16 := by
  funext t
  fin_cases t <;> rfl

theorem planes_e1 : PlanesAt X2 0 (vec6 4) := by
  intro t s hs
  rw [fb_vec6 _ _ hs]
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> fin_cases t <;> rfl

theorem planes_e2 : PlanesAt X2 1 (vec6 16) := by
  intro t s hs
  rw [fb_vec6 _ _ hs]
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> fin_cases t <;> rfl

theorem fixed_iff {X i : ℕ} {v : V6} (hX : PlanesAt X i v) {p : ℕ} (hp : p < 891) :
    expand ⟨p, hp⟩ v = v ↔ bit (planeD X (rowP PLP p)) i = false := by
  rw [bit_eq, Bool.eq_false_iff, ne_eq, planeD_bit hX, expand_eq hp, not_not]

theorem rowP_coord {p : ℕ} (hp : p < 891) (a : Fin 3) :
    planeRow ⟨p, hp⟩ a 5 ≠ 0 ↔ Nat.blt 0 (fget (rowP PLP p a) 5 2) = true := by
  have e : planeRow ⟨p, hp⟩ a = vec6 (rowP PLP p a) := by
    unfold planeRow rowP
    rw [(pl_spec.2 p hp a a.2).2]
  rw [e, vec6_ne_zero, Nat.blt_eq]
  rfl

theorem spec {p : ℕ} (hp : p < 891) :
    ((bit (planeD X2 (rowP PLP p)) 0 || bit (planeD X2 (rowP PLP p)) 1) ||
      (Nat.beq p 0 || (Nat.beq p 1 || Nat.beq p 4))) = true ∧
    (!bit (planeD X2 (rowP PLP p)) 1 || anyN 3 fun a => Nat.blt 0 (fget (rowP PLP p a) 5 2)) =
      true := by
  have h := k3063
  unfold ok3063 at h
  rw [allN_iff] at h
  have h' := h p hp
  simp only [andB_eq, orB_eq, notB_eq, Bool.and_eq_true] at h'
  exact h'

theorem planes_through_H :
    ∀ j : Fin 891, expand j (Pi.single 1 1) = Pi.single 1 1 →
    expand j (Pi.single 2 1) = Pi.single 2 1 → j = 0 ∨ j = 1 ∨ j = 4 := by
  rintro ⟨p, hp⟩ h1 h2
  rw [e1_eq, fixed_iff planes_e1 hp] at h1
  rw [e2_eq, fixed_iff planes_e2 hp] at h2
  have h := (spec hp).1
  rw [h1, h2] at h
  simp only [Bool.or_false, Bool.false_or, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem planes_e2_or_row :
    ∀ j : Fin 891,
    expand j (Pi.single 2 1) = Pi.single 2 1 ∨ ∃ a : Fin 3, planeRow j a 5 ≠ 0 := by
  rintro ⟨p, hp⟩
  rw [e2_eq, fixed_iff planes_e2 hp]
  have h := (spec hp).2
  rw [Bool.or_eq_true, anyN_iff] at h
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨⟨a, ha⟩, (rowP_coord hp ⟨a, ha⟩).2 h⟩

end CertificateChecks.Batch3063

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary in
theorem certificate3063 : (∀ j : Fin 891, expand j (Pi.single 1 1) = Pi.single 1 1 →
       expand j (Pi.single 2 1) = Pi.single 2 1 → j = 0 ∨ j = 1 ∨ j = 4)
    ∧ (∀ j : Fin 891,
       expand j (Pi.single 2 1) = Pi.single 2 1 ∨ ∃ a : Fin 3, planeRow j a 5 ≠ 0) := by
  exact ⟨CertificateChecks.Batch3063.planes_through_H, CertificateChecks.Batch3063.planes_e2_or_row⟩

end Certificates
