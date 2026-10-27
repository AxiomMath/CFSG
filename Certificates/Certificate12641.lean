
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23Check
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Sporadic.Schreier.M23PinnedInputs
import Certificates.Kernel.M23Cent3.Final

public section

namespace Certificates

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23 CFSG.Sporadic.Th CFSG.Blueprint Subgroup in
theorem certificate12641 :
    (∀ t ∈ NativeSporadic.M23, orderOf t = 3 → ∃ g ∈ NativeSporadic.M23,
      t = g * wordG letG xW * g⁻¹) ∧
    closure {wordG letG c1W, wordG letG c2W} =
      NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))) ∧
    Nat.card ↥(NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23)))) =
      180 ∧
    (∀ y ∈ NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))),
      (orderOf y).Prime → orderOf y ≠ 3 → ∃ r ∈ [r0W, r1W, r2W],
        ∃ c ∈ NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))),
          y = c * wordG letG r * c⁻¹) ∧
    ∀ p ∈ [(r0W, h0W), (r1W, h1W), (r2W, h2W)],
      wordG letG p.2 ∈
        NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23))) ∧
      3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹)) := CFSG.KD.M23Cent3.m23_cent3_facts

end Certificates
