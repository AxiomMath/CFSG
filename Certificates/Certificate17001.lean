module

public import CFSG.Quasithin.Background.JonesParshallWords
public import CFSG.Quasithin.Background.JonesParshallSmallSLInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

namespace CertificateChecks.Batch17001

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

private theorem foxEvalM_sub {k n : ℕ} {R : Type*} [CommRing R] (mats : Fin k → Matrix (Fin n) (Fin n) R)
    (a b : Fin k → Fin n → R) (w : List (Fin k)) :
    foxEvalM mats (a - b) w = foxEvalM mats a w - foxEvalM mats b w := by
  induction w with
  | nil => simp [foxEvalM]
  | cons i w ih =>
    simp only [foxEvalM, ih, mulVec_sub, Pi.sub_apply]
    abel

private theorem foxEvalM_cob {k n : ℕ} {R : Type*} [CommRing R] (mats : Fin k → Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) (w : List (Fin k)) :
    foxEvalM mats (fun i => mats i *ᵥ v - v) w = wordEvalM mats w *ᵥ v - v := by
  induction w with
  | nil => simp [foxEvalM, wordEvalM]
  | cons i w ih =>
    simp only [foxEvalM, wordEvalM, ih, mulVec_sub, mulVec_mulVec]
    abel

private theorem fox_sub_cob {k n : ℕ} {R : Type*} [CommRing R] {mats : Fin k → Matrix (Fin n) (Fin n) R}
    {rels : List (List (Fin k))} (hrels : ∀ r ∈ rels, wordEvalM mats r = 1)
    {vals : Fin k → Fin n → R} (h : ∀ r ∈ rels, foxEvalM mats vals r = 0) (v : Fin n → R) :
    ∀ r ∈ rels, foxEvalM mats (vals - fun i => mats i *ᵥ v - v) r = 0 := fun r hr => by
  rw [foxEvalM_sub, h r hr, foxEvalM_cob, hrels r hr, one_mulVec, sub_self, sub_self]

private theorem tw4_spec_0 : ∀ i j : Fin 4, i ≠ j → wordEvalM mats4 (tw4 i j) = transvection i j 1 := by
  decide +kernel

private theorem rels4_spec_1 : ∀ r ∈ rels4, wordEvalM mats4 r = 1 := by
  decide +kernel

private theorem mats4_0_mulVec : ∀ v : Fin 4 → ZMod 2, mats4 0 *ᵥ v = ![v 0 + v 1, v 1, v 2, v 3] := by
  decide +kernel

private theorem mats4_1_mulVec : ∀ v : Fin 4 → ZMod 2, mats4 1 *ᵥ v = ![v 3, v 0, v 1, v 2] := by
  decide +kernel

private theorem mats5_0_mulVec : ∀ v : Fin 5 → ZMod 2,
    mats5 0 *ᵥ v = ![v 0 + v 1, v 1, v 2, v 3, v 4] := by
  decide +kernel

private theorem mats5_1_mulVec : ∀ v : Fin 5 → ZMod 2,
    mats5 1 *ᵥ v = ![v 4, v 0, v 1, v 2, v 3] := by
  decide +kernel

private theorem sol4_core : ∀ a b c e : ZMod 2,
    (∀ r ∈ rels4, foxEvalM mats4 ![![0, a, b, c], ![e, 0, 0, 0]] r = 0) →
    (![![0, a, b, c], ![e, 0, 0, 0]] : Fin 2 → Fin 4 → ZMod 2) = 0 := by
  decide +kernel

private theorem sol4_2 : ∀ v₁ v₂ : Fin 4 → ZMod 2, (∀ r ∈ rels4, foxEvalM mats4 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats4 0 *ᵥ v - v ∧ v₂ = mats4 1 *ᵥ v - v := by
  intro v₁ v₂ h
  let v : Fin 4 → ZMod 2 := ![v₁ 0 + v₂ 1, v₁ 0, v₁ 0 - v₂ 2, v₁ 0 - v₂ 2 - v₂ 3]
  have hform : (![v₁, v₂] - fun i => mats4 i *ᵥ v - v) =
      ![![0, v₁ 1, v₁ 2, v₁ 3], ![v₂ 0 - (v 3 - v 0), 0, 0, 0]] := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [mats4_0_mulVec, mats4_1_mulVec, v] <;> ring
  have hw := fox_sub_cob rels4_spec_1 h v
  rw [hform] at hw
  have h0 := sol4_core _ _ _ _ hw
  rw [← hform, sub_eq_zero] at h0
  exact ⟨v, congrFun h0 0, congrFun h0 1⟩

private theorem tw5_spec_3 : ∀ i j : Fin 5, i ≠ j → wordEvalM mats5 (tw5 i j) = transvection i j 1 := by
  decide +kernel

private theorem rels5_spec_4 : ∀ r ∈ rels5, wordEvalM mats5 r = 1 := by
  decide +kernel

private theorem sol5_core : ∀ a b c d e : ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![![0, a, b, c, d], ![e, 0, 0, 0, 0]] r = 0) →
    (![![0, a, b, c, d], ![e, 0, 0, 0, 0]] : Fin 2 → Fin 5 → ZMod 2) = 0 := by
  decide +kernel

private theorem sol5_all : ∀ v₁ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  intro v₁ v₂ h
  let v : Fin 5 → ZMod 2 :=
    ![v₁ 0 + v₂ 1, v₁ 0, v₁ 0 - v₂ 2, v₁ 0 - v₂ 2 - v₂ 3, v₁ 0 - v₂ 2 - v₂ 3 - v₂ 4]
  have hform : (![v₁, v₂] - fun i => mats5 i *ᵥ v - v) =
      ![![0, v₁ 1, v₁ 2, v₁ 3, v₁ 4], ![v₂ 0 - (v 4 - v 0), 0, 0, 0, 0]] := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [mats5_0_mulVec, mats5_1_mulVec, v] <;> ring
  have hw := fox_sub_cob rels5_spec_4 h v
  rw [hform] at hw
  have h0 := sol5_core _ _ _ _ _ hw
  rw [← hform, sub_eq_zero] at h0
  exact ⟨v, congrFun h0 0, congrFun h0 1⟩

private theorem sol5_0_5 : ∀ v₁ ∈ chunk5_0, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_1_6 : ∀ v₁ ∈ chunk5_1, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_2_7 : ∀ v₁ ∈ chunk5_2, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_3_8 : ∀ v₁ ∈ chunk5_3, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_4_9 : ∀ v₁ ∈ chunk5_4, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_5_10 : ∀ v₁ ∈ chunk5_5, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_6_11 : ∀ v₁ ∈ chunk5_6, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem sol5_7_12 : ∀ v₁ ∈ chunk5_7, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  fun v₁ _ => sol5_all v₁

private theorem cocycle3_one_13 : cocycle3 1 = 0 := by
  decide +kernel

private theorem cocycle3_gen0_14 : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 0 * g) = cocycle3 (gens3 0) + gens3 0 • cocycle3 g := by
  decide +kernel

private theorem cocycle3_gen1_15 : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 1 * g) = cocycle3 (gens3 1) + gens3 1 • cocycle3 g := by
  decide +kernel

private theorem cocycle3_not_16 : ¬ ∃ v : Fin 3 → ZMod 2,
    cocycle3 (gens3 0) = mats3 0 *ᵥ v - v ∧ cocycle3 (gens3 1) = mats3 1 *ᵥ v - v := by
  decide +kernel

private theorem sol3_17 : ∀ v₁ v₂ : Fin 3 → ZMod 2, (∀ r ∈ rels3, foxEvalM mats3 ![v₁, v₂] r = 0) →
    (∃ v, v₁ = mats3 0 *ᵥ v - v ∧ v₂ = mats3 1 *ᵥ v - v) ∨
      ∃ v, v₁ = mats3 0 *ᵥ v - v + cocycle3 (gens3 0) ∧
        v₂ = mats3 1 *ᵥ v - v + cocycle3 (gens3 1) := by
  decide +kernel

private theorem tw3_spec_18 : ∀ i j : Fin 3, i ≠ j → wordEvalM mats3 (tw3 i j) = transvection i j 1 := by
  decide +kernel

private theorem rels3_spec_19 : ∀ r ∈ rels3, wordEvalM mats3 r = 1 := by
  decide +kernel

end CertificateChecks.Batch17001

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix in
theorem certificate17001 : (
 ∀ i j : Fin 4, i ≠ j → wordEvalM mats4 (tw4 i j) = transvection i j 1 
)
    ∧ (
 ∀ r ∈ rels4, wordEvalM mats4 r = 1 
)
    ∧ (
 ∀ v₁ v₂ : Fin 4 → ZMod 2, (∀ r ∈ rels4, foxEvalM mats4 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats4 0 *ᵥ v - v ∧ v₂ = mats4 1 *ᵥ v - v 
)
    ∧ (
 ∀ i j : Fin 5, i ≠ j → wordEvalM mats5 (tw5 i j) = transvection i j 1 
)
    ∧ (
 ∀ r ∈ rels5, wordEvalM mats5 r = 1 
)
    ∧ (
 ∀ v₁ ∈ chunk5_0, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_1, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_2, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_3, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_4, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_5, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_6, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ ∈ chunk5_7, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v 
)
    ∧ (
 cocycle3 1 = 0 
)
    ∧ (
 ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 0 * g) = cocycle3 (gens3 0) + gens3 0 • cocycle3 g 
)
    ∧ (
 ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 1 * g) = cocycle3 (gens3 1) + gens3 1 • cocycle3 g 
)
    ∧ (
 ¬ ∃ v : Fin 3 → ZMod 2,
    cocycle3 (gens3 0) = mats3 0 *ᵥ v - v ∧ cocycle3 (gens3 1) = mats3 1 *ᵥ v - v 
)
    ∧ (
 ∀ v₁ v₂ : Fin 3 → ZMod 2, (∀ r ∈ rels3, foxEvalM mats3 ![v₁, v₂] r = 0) →
    (∃ v, v₁ = mats3 0 *ᵥ v - v ∧ v₂ = mats3 1 *ᵥ v - v) ∨
      ∃ v, v₁ = mats3 0 *ᵥ v - v + cocycle3 (gens3 0) ∧
        v₂ = mats3 1 *ᵥ v - v + cocycle3 (gens3 1) 
)
    ∧ (
 ∀ i j : Fin 3, i ≠ j → wordEvalM mats3 (tw3 i j) = transvection i j 1 
)
    ∧ (
 ∀ r ∈ rels3, wordEvalM mats3 r = 1 
) := by
  exact ⟨@CertificateChecks.Batch17001.tw4_spec_0, @CertificateChecks.Batch17001.rels4_spec_1, @CertificateChecks.Batch17001.sol4_2, @CertificateChecks.Batch17001.tw5_spec_3, @CertificateChecks.Batch17001.rels5_spec_4, @CertificateChecks.Batch17001.sol5_0_5, @CertificateChecks.Batch17001.sol5_1_6, @CertificateChecks.Batch17001.sol5_2_7, @CertificateChecks.Batch17001.sol5_3_8, @CertificateChecks.Batch17001.sol5_4_9, @CertificateChecks.Batch17001.sol5_5_10, @CertificateChecks.Batch17001.sol5_6_11, @CertificateChecks.Batch17001.sol5_7_12, @CertificateChecks.Batch17001.cocycle3_one_13, @CertificateChecks.Batch17001.cocycle3_gen0_14, @CertificateChecks.Batch17001.cocycle3_gen1_15, @CertificateChecks.Batch17001.cocycle3_not_16, @CertificateChecks.Batch17001.sol3_17, @CertificateChecks.Batch17001.tw3_spec_18, @CertificateChecks.Batch17001.rels3_spec_19⟩

end Certificates
