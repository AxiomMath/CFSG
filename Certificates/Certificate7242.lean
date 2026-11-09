module

public import CFSG.Quasithin.H13.L32NG9MInputs
import all CFSG.Quasithin.H13.L32NG9MInputs
import Certificates.Kernel.G9M.Twin

public section

namespace CertificateChecks.Batch7242

open CertificateChecks.G9MK CFSG.Quasithin.H13.G9MCert CFSG.Quasithin.H13.Mat8Cert

set_option maxHeartbeats 0

private noncomputable def rowA (a : ℕ) : List (List ℕ) :=
  (List.range 16).flatMap fun b => (List.range 16).flatMap fun c =>
    (List.range 16).map fun d => [a, b, c, d]

private theorem all4_eq : all4 = (List.range 16).flatMap rowA := rfl

private noncomputable def normF (y : List ℕ) : Bool :=
  !(pow8K (blk y) 5 == one8 && blk y != one8) ||
    match inv4K (spinYK y) with
    | some di => verifyYK y (spinYK y) di
    | none => false

private noncomputable def invP (x : List ℕ) : Bool := mul8S (blk x) (blk x) == one8

private noncomputable def g5F (x : List ℕ) : Bool :=
  !relS5K (blk x) (blk y0) || (findConjK x y0 modelsS5).isSome

private noncomputable def ga5F (x : List ℕ) : Bool :=
  x == one4 || !relA5K (blk x) (blk y0) || (findConjK x y0 modelsA5).isSome

private noncomputable def invF (x : List ℕ) : Bool := !invP x || (g5F x && ga5F x)

private theorem norm_0 : (rowA 0).all normF = true := by decide +kernel
private theorem norm_1 : (rowA 1).all normF = true := by decide +kernel
private theorem norm_2 : (rowA 2).all normF = true := by decide +kernel
private theorem norm_3 : (rowA 3).all normF = true := by decide +kernel
private theorem norm_4 : (rowA 4).all normF = true := by decide +kernel
private theorem norm_5 : (rowA 5).all normF = true := by decide +kernel
private theorem norm_6 : (rowA 6).all normF = true := by decide +kernel
private theorem norm_7 : (rowA 7).all normF = true := by decide +kernel
private theorem norm_8 : (rowA 8).all normF = true := by decide +kernel
private theorem norm_9 : (rowA 9).all normF = true := by decide +kernel
private theorem norm_10 : (rowA 10).all normF = true := by decide +kernel
private theorem norm_11 : (rowA 11).all normF = true := by decide +kernel
private theorem norm_12 : (rowA 12).all normF = true := by decide +kernel
private theorem norm_13 : (rowA 13).all normF = true := by decide +kernel
private theorem norm_14 : (rowA 14).all normF = true := by decide +kernel
private theorem norm_15 : (rowA 15).all normF = true := by decide +kernel

private theorem inv_0 : (rowA 0).all invF = true := by decide +kernel
private theorem inv_1 : (rowA 1).all invF = true := by decide +kernel
private theorem inv_2 : (rowA 2).all invF = true := by decide +kernel
private theorem inv_3 : (rowA 3).all invF = true := by decide +kernel
private theorem inv_4 : (rowA 4).all invF = true := by decide +kernel
private theorem inv_5 : (rowA 5).all invF = true := by decide +kernel
private theorem inv_6 : (rowA 6).all invF = true := by decide +kernel
private theorem inv_7 : (rowA 7).all invF = true := by decide +kernel
private theorem inv_8 : (rowA 8).all invF = true := by decide +kernel
private theorem inv_9 : (rowA 9).all invF = true := by decide +kernel
private theorem inv_10 : (rowA 10).all invF = true := by decide +kernel
private theorem inv_11 : (rowA 11).all invF = true := by decide +kernel
private theorem inv_12 : (rowA 12).all invF = true := by decide +kernel
private theorem inv_13 : (rowA 13).all invF = true := by decide +kernel
private theorem inv_14 : (rowA 14).all invF = true := by decide +kernel
private theorem inv_15 : (rowA 15).all invF = true := by decide +kernel

private theorem norm_all : all4.all normF = true := by
  rw [all4_eq, List.all_flatMap, List.all_eq_true]
  intro a ha
  match a, List.mem_range.mp ha with
  | 0, _ => exact norm_0
  | 1, _ => exact norm_1
  | 2, _ => exact norm_2
  | 3, _ => exact norm_3
  | 4, _ => exact norm_4
  | 5, _ => exact norm_5
  | 6, _ => exact norm_6
  | 7, _ => exact norm_7
  | 8, _ => exact norm_8
  | 9, _ => exact norm_9
  | 10, _ => exact norm_10
  | 11, _ => exact norm_11
  | 12, _ => exact norm_12
  | 13, _ => exact norm_13
  | 14, _ => exact norm_14
  | 15, _ => exact norm_15
  | n + 16, h => exact absurd h (by omega)

private theorem inv_all : all4.all invF = true := by
  rw [all4_eq, List.all_flatMap, List.all_eq_true]
  intro a ha
  match a, List.mem_range.mp ha with
  | 0, _ => exact inv_0
  | 1, _ => exact inv_1
  | 2, _ => exact inv_2
  | 3, _ => exact inv_3
  | 4, _ => exact inv_4
  | 5, _ => exact inv_5
  | 6, _ => exact inv_6
  | 7, _ => exact inv_7
  | 8, _ => exact inv_8
  | 9, _ => exact inv_9
  | 10, _ => exact inv_10
  | 11, _ => exact inv_11
  | 12, _ => exact inv_12
  | 13, _ => exact inv_13
  | 14, _ => exact inv_14
  | 15, _ => exact inv_15
  | n + 16, h => exact absurd h (by omega)

private theorem split_all {α : Type} {l : List α} {p f g : α → Bool}
    (h : l.all (fun x => !p x || (f x && g x)) = true) :
    l.all (fun x => !p x || f x) = true ∧ l.all (fun x => !p x || g x) = true := by
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨fun x hx => (h x hx).imp_right And.left, fun x hx => (h x hx).imp_right And.right⟩

private theorem norm_k : normCheckK = true := by
  unfold normCheckK ords5K
  rw [List.all_filter]
  exact norm_all

private theorem s5_k : s5CheckK = true := by
  unfold s5CheckK invsK
  rw [List.all_filter]
  exact (split_all (p := invP) (f := g5F) (g := ga5F) inv_all).1

private theorem a5_k : a5CheckK = true := by
  unfold a5CheckK invsK
  rw [List.all_filter]
  exact (split_all (p := invP) (f := g5F) (g := ga5F) inv_all).2

theorem check : CFSG.Quasithin.H13.G9MCert.g9mCheck = true := by
  simp only [g9mCheck_eq, g9mCheckK, norm_k, s5_k, a5_k, Bool.and_self]

end CertificateChecks.Batch7242

namespace Certificates

theorem certificate7242 : CFSG.Quasithin.H13.G9MCert.g9mCheck = true :=
  CertificateChecks.Batch7242.check

end Certificates
