module

public import Certificates.Data.KappaDN
public import Certificates.Kernel.EvenBN.K561001
public import Certificates.Kernel.EvenBN.Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch561001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelEvenBN CertificateChecks.KernelEvenBN.K561001
open Certificates.TitsAschbacherParrott Certificates.KappaD

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def rowK (M : Mat5) (i : Fin 5) : Nat :=
  (List.ofFn fun k : Fin 5 => ppw (V (bIdx k)) (M i k).val).foldr pc (pidn 1755 11)

theorem actsK : ((List.finRange 4).all fun j => (List.finRange 5).all fun i =>
    Nat.beq (pc (rowK (tMat j) i) (TitsN.S j.val)) (pc (TitsN.S j.val) (V (bIdx i)))) = true := by
  quickRfl

theorem foldr_eq : ∀ L : List Nat, (∀ x ∈ L, C x) →
    (L.map (unpack 1755 11)).foldr (compA 1755) (idA 1755) = unpack 1755 11 (L.foldr pc (pidn 1755 11)) ∧
      C (L.foldr pc (pidn 1755 11))
  | [], _ => ⟨CertificateChecks.KernelSporSch.TitsCentral.id_eq, canId⟩
  | x :: L, h => by
    obtain ⟨e, c⟩ := foldr_eq L fun y hy => h y (List.mem_cons_of_mem _ hy)
    have cx := h x (List.mem_cons_self ..)
    simp only [List.map_cons, List.foldr_cons]
    rw [e, cmpU cx c]
    exact ⟨rfl, cmpC cx c⟩

theorem bIdx_lt (k : Fin 5) : bIdx k < 13 := by revert k; decide

theorem rowArr_eq (M : Mat5) (i : Fin 5) :
    rowArr M i = unpack 1755 11 (rowK M i) ∧ C (rowK M i) := by
  have hL : ∀ x ∈ List.ofFn (fun k : Fin 5 => ppw (V (bIdx k)) (M i k).val), C x := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact powC (cV (bIdx_lt k))
  have e : (List.ofFn fun k : Fin 5 => powA (vA (bIdx k)) (M i k).val) =
      (List.ofFn fun k : Fin 5 => ppw (V (bIdx k)) (M i k).val).map (unpack 1755 11) := by
    have f : (fun k : Fin 5 => powA (vA (bIdx k)) (M i k).val) =
        (unpack 1755 11 ∘ fun k : Fin 5 => ppw (V (bIdx k)) (M i k).val) := by
      funext k
      rw [Function.comp_apply, vA_eq (bIdx_lt k), powU (cV (bIdx_lt k))]
    rw [List.map_ofFn, f]
  unfold rowArr rowK
  rw [e]
  exact foldr_eq _ hL

theorem acts_eq (j : Fin 4) (i : Fin 5) : actsOK j i =
    Nat.beq (pc (rowK (tMat j) i) (TitsN.S j.val)) (pc (TitsN.S j.val) (V (bIdx i))) := by
  obtain ⟨hr, cr⟩ := rowArr_eq (tMat j) i
  have cn : C (TitsN.S j.val) := allN_spec canN j.val (by omega)
  unfold actsOK conjEqA
  rw [hr, bindsN.2.2.2.2.1 j.val (by omega), vA_eq (bIdx_lt i), cmpU cr cn, cmpU cn (cV (bIdx_lt i)),
    eqU (cmpC cr cn) (cmpC cn (cV (bIdx_lt i)))]
  rfl

theorem all_of_chunks {α : Type} (p : α → Bool) (n : ℕ) : ∀ (K : ℕ) (L : List α), L.length ≤ n * K →
    (∀ k < K, ((L.drop (n * k)).take n).all p = true) → L.all p = true
  | 0, L, hl, _ => by
    have e : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst e
    rfl
  | K + 1, L, hl, h => by
    rw [← List.take_append_drop n L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks p n K (L.drop n) ?_ fun k hk => ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      omega
    · rw [List.drop_drop, Nat.add_comm n (n * k), ← Nat.mul_succ]
      exact h (k + 1) (by omega)

theorem closureK : closureOK (slList ()) (slRows ()) = true := by
  unfold closureOK
  rw [oneK, Bool.true_and]
  refine all_of_chunks _ 24 8 _ (by decide) fun k hk => ?_
  match k, hk with
  | 0, _ => exact clK0
  | 1, _ => exact clK1
  | 2, _ => exact clK2
  | 3, _ => exact clK3
  | 4, _ => exact clK4
  | 5, _ => exact clK5
  | 6, _ => exact clK6
  | 7, _ => exact clK7
  | k + 8, h => exact absurd h (by omega)

theorem wordsK : decide (∀ e₁ e₂ e₃ d₁ : ZMod 2,
    wordOKb (slRows ()) tMat (wordOf e₁ e₂ e₃ d₁) e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 = true) = true := by
  have z : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  refine decide_eq_true fun e₁ e₂ => ?_
  rcases z e₁ with rfl | rfl <;> rcases z e₂ with rfl | rfl
  exacts [of_decide_eq_true wK00, of_decide_eq_true wK01, of_decide_eq_true wK10,
    of_decide_eq_true wK11]

theorem kappa_d_check_0 : kappaDCheck () = true := by
  unfold kappaDCheck
  simp only []
  have hA : ((List.finRange 4).all fun j => (List.finRange 5).all fun i => actsOK j i) = true := by
    simp only [acts_eq]
    exact actsK
  rw [hA, closureK, wordsK]
  rfl

end CertificateChecks.Batch561001

namespace Certificates

open CertificateChecks

theorem certificate561001 : Certificates.KappaD.kappaDCheck () = true := by
  exact CertificateChecks.Batch561001.kappa_d_check_0

end Certificates
