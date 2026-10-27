module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public import CFSG.Monster.B.TwoA.Unitary.Action
public import Certificates.Kernel.MonsterB.Co2Mem
public import Certificates.Kernel.MonsterB.Fix3081Data
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import CFSG.Certificates.Kernel.MonsterB.Co2CountSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.KC.Co2Mem CFSG.KC.U6Orb CFSG.KLie.CT
  CertificateChecks.KernelMonB CertificateChecks.Fix3081

namespace CertificateChecks.Batch3081

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.KC.Co2Mem CFSG.KC.U6Orb CFSG.KLie.CT
  CertificateChecks.KernelMonB CertificateChecks.Fix3081

set_option maxRecDepth 100000

theorem kRow : shapeL 22 (pw2 22) [n6RowArr[6]!] = true := by quickRfl

theorem kM : Nat.beq (packL 22 (n6RowArr[6]!).toList) M6 = true := by quickRfl

theorem kV : andB (boundL (pw2 22) n6VecArr.toList) (Nat.beq (packL 22 n6VecArr.toList) V891) =
    true := by
  quickRfl

theorem kO : andB (boundL (pw2 22) o14VecArr.toList) (Nat.beq (packL 22 o14VecArr.toList) V1408) =
    true := by
  quickRfl

theorem kSizes : n6VecArr.size = 891 ∧ o14VecArr.size = 1408 := by decide +kernel

theorem kWb : allN 2300 (fun j => Nat.blt (actK M6 (vecF j)) (pw2 22)) = true := by quickRfl

theorem kWc : Nat.beq (cntK 2300 (fun j => Nat.beq (actK M6 (vecF j)) (vecF j))) 284 = true := by
  quickRfl

theorem kVb : allN 891 (fun j => Nat.blt (actK M6 (Nat.xor 6144 (fget V891 j 22))) (pw2 22)) =
    true := by
  quickRfl

theorem kVc : Nat.beq (cntK 891 (fun j =>
    Nat.beq (actK M6 (Nat.xor 6144 (fget V891 j 22))) (Nat.xor 6144 (fget V891 j 22)))) 27 = true := by
  quickRfl

theorem kOb : allN 1408 (fun j => Nat.blt (actK M6 (fget V1408 j 22)) (pw2 22)) = true := by
  quickRfl

theorem kOc : Nat.beq (cntK 1408 (fun j => Nat.beq (actK M6 (fget V1408 j 22)) (fget V1408 j 22)))
    256 = true := by
  quickRfl

theorem act_eq (v : ℕ) : Native.actD 22 (genRows 6) v = actK M6 v := by
  obtain ⟨hs, hb⟩ := (shapeL_iff 22 (pw2 22) _).1 kRow _ (List.mem_singleton_self _)
  change Native.actD 22 n6RowArr[6]! v = _
  rw [actD_eq_actK hs (fun x hx => (hb x hx).trans_eq (pw2_eq 22)), Nat.eq_of_beq_eq_true kM]

theorem vec_eq {j : ℕ} (hj : j < 891) : n6VecArr[j]! = fget V891 j 22 := by
  obtain ⟨h1, h2⟩ := andB_eq_true.1 kV
  rw [← Nat.eq_of_beq_eq_true h2, fget_packA (fun x hx => ((boundL_iff _ _).1 h1 x hx).trans_eq
    (pw2_eq 22)) (by rw [kSizes.1]; exact hj)]

theorem tau_eq {j : ℕ} (hj : j < 1408) : o14VecArr[j]! = fget V1408 j 22 := by
  obtain ⟨h1, h2⟩ := andB_eq_true.1 kO
  rw [← Nat.eq_of_beq_eq_true h2, fget_packA (fun x hx => ((boundL_iff _ _).1 h1 x hx).trans_eq
    (pw2_eq 22)) (by rw [kSizes.2]; exact hj)]

theorem lt_of_blt {a : ℕ} (h : Nat.blt a (pw2 22) = true) : a < 2 ^ 22 := by
  rwa [Nat.blt_eq, pw2_eq] at h

theorem short_lt : ∀ j : Ω, Native.actD 22 (genRows 6) (shortVec j) < 2 ^ 22 := by
  intro j
  rw [act_eq, shortVec, vectors_getElem! j.2]
  exact lt_of_blt ((allN_iff _ _).1 kWb j j.2)

theorem short_card : (Finset.univ.filter fun j : Ω =>
    Native.actD 22 (genRows 6) (shortVec j) = shortVec j).card = 284 := by
  refine (card_filter_fin 2300 (fun k => Native.actD 22 (genRows 6) (Native.vectors ())[k]! =
    (Native.vectors ())[k]!) _ fun k hk => ?_).trans (Nat.eq_of_beq_eq_true kWc)
  rw [act_eq, vectors_getElem! hk, Nat.beq_eq]

theorem shift_lt : ∀ j : Fin 891,
    Native.actD 22 (genRows 6) (6144 ^^^ n6VecArr[(j : ℕ)]!) < 2 ^ 22 := by
  intro j
  rw [act_eq, vec_eq j.2]
  exact lt_of_blt ((allN_iff _ _).1 kVb j j.2)

theorem shift_card : (Finset.univ.filter fun j : Fin 891 =>
    Native.actD 22 (genRows 6) (6144 ^^^ n6VecArr[(j : ℕ)]!) = 6144 ^^^ n6VecArr[(j : ℕ)]!).card =
      27 := by
  refine (card_filter_fin 891 (fun k => Native.actD 22 (genRows 6) (6144 ^^^ n6VecArr[k]!) =
    6144 ^^^ n6VecArr[k]!) _ fun k hk => ?_).trans (Nat.eq_of_beq_eq_true kVc)
  rw [act_eq, vec_eq hk, Nat.beq_eq]
  rfl

theorem tau_lt : ∀ i : Fin 1408, Native.actD 22 (genRows 6) o14VecArr[(i : ℕ)]! < 2 ^ 22 := by
  intro i
  rw [act_eq, tau_eq i.2]
  exact lt_of_blt ((allN_iff _ _).1 kOb i i.2)

theorem tau_card : (Finset.univ.filter fun i : Fin 1408 =>
    Native.actD 22 (genRows 6) o14VecArr[(i : ℕ)]! = o14VecArr[(i : ℕ)]!).card = 256 := by
  refine (card_filter_fin 1408 (fun k => Native.actD 22 (genRows 6) o14VecArr[k]! =
    o14VecArr[k]!) _ fun k hk => ?_).trans (Nat.eq_of_beq_eq_true kOc)
  rw [act_eq, tau_eq hk, Nat.beq_eq]

end CertificateChecks.Batch3081

namespace Certificates

set_option maxRecDepth 100000 in
open CertificateChecks.Batch3081 in
open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary in
theorem certificate3081 : (∀ j : Ω, Native.actD 22 (CFSG.Monster.B.TwoA.Unitary.genRows 6) (shortVec j) < 2 ^ 22)
    ∧ ((Finset.univ.filter fun j : Ω => Native.actD 22 (CFSG.Monster.B.TwoA.Unitary.genRows 6) (shortVec j) = shortVec j).card =
       284)
    ∧ (∀ j : Fin 891,
       Native.actD 22 (CFSG.Monster.B.TwoA.Unitary.genRows 6) (6144 ^^^ n6VecArr[(j : ℕ)]!) < 2 ^ 22)
    ∧ ((Finset.univ.filter fun j : Fin 891 =>
       Native.actD 22 (CFSG.Monster.B.TwoA.Unitary.genRows 6) (6144 ^^^ n6VecArr[(j : ℕ)]!) = 6144 ^^^ n6VecArr[(j : ℕ)]!).card
           =
         27)
    ∧ (∀ i : Fin 1408, Native.actD 22 (CFSG.Monster.B.TwoA.Unitary.genRows 6) o14VecArr[(i : ℕ)]! < 2 ^ 22)
    ∧ ((Finset.univ.filter fun i : Fin 1408 =>
       Native.actD 22 (CFSG.Monster.B.TwoA.Unitary.genRows 6) o14VecArr[(i : ℕ)]! = o14VecArr[(i : ℕ)]!).card = 256) :=
  ⟨short_lt, short_card, shift_lt, shift_card, tau_lt, tau_card⟩

end Certificates
