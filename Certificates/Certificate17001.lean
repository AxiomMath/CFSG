module

public import CFSG.Quasithin.Background.JonesParshallWords
public import CFSG.Quasithin.Background.JonesParshallSmallSLInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

namespace CertificateChecks.Batch17001

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

private theorem tw4_spec_0 : ∀ i j : Fin 4, i ≠ j → wordEvalM mats4 (tw4 i j) = transvection i j 1 := by
  decide +kernel

private theorem rels4_spec_1 : ∀ r ∈ rels4, wordEvalM mats4 r = 1 := by
  decide +kernel

private theorem sol4_2 : ∀ v₁ v₂ : Fin 4 → ZMod 2, (∀ r ∈ rels4, foxEvalM mats4 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats4 0 *ᵥ v - v ∧ v₂ = mats4 1 *ᵥ v - v := by
  decide +kernel

private theorem tw5_spec_3 : ∀ i j : Fin 5, i ≠ j → wordEvalM mats5 (tw5 i j) = transvection i j 1 := by
  decide +kernel

private theorem rels5_spec_4 : ∀ r ∈ rels5, wordEvalM mats5 r = 1 := by
  decide +kernel

private theorem sol5_0_5 : ∀ v₁ ∈ chunk5_0, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_1_6 : ∀ v₁ ∈ chunk5_1, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_2_7 : ∀ v₁ ∈ chunk5_2, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_3_8 : ∀ v₁ ∈ chunk5_3, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_4_9 : ∀ v₁ ∈ chunk5_4, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_5_10 : ∀ v₁ ∈ chunk5_5, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_6_11 : ∀ v₁ ∈ chunk5_6, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

private theorem sol5_7_12 : ∀ v₁ ∈ chunk5_7, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  decide +kernel

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
