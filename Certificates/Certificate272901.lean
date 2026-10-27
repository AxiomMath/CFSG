module

public import Certificates.Data.Holder272.E29Words
public import Certificates.Data.Holder272.E29Model
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.CosPres.F272901A
import Certificates.Kernel.WrTwin.E29Props
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.KC.MiscCoset CFSG.KD.WrTwin CFSG.ClassicalInvolution.Q3.E29Data

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.E29Data CFSG.ClassicalInvolution.Q3.AE in
theorem certificate272901 :
    ((genSub {r : FreeGroup (Fin 56) | r ∈ e29Words.map FreeGroup.mk} [0, 1]).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 56) | r ∈ e29Words.map FreeGroup.mk} [0, 1]).index ≤ 10752) ∧
    (∀ d ∈ e29ConjData, mkQ 8 (nG d.1 * nG (2 * d.2.1 + d.2.2.1) * (nG d.1)⁻¹) =
      mkQ 8 (nWord d.2.2.2.1 d.2.2.2.2)) ∧
    (∀ j < 28, cycPerm8 (e29Conj.getD j []) ∈ agl32 ∧
      Equiv.Perm.sign (cycPerm8 (e29Conj.getD j [])) = 1) ∧
    (∀ s < 8, ∀ t < 8, s ≠ t → mkQ 8 ((n8 0).getD s 1) ≠ mkQ 8 ((n8 0).getD t 1)) ∧
    (∀ j < 28, ∀ k < 28, j ≠ k → ∀ W ∈ localWords29, mkQ 8 (nG (2 * j)) ≠ mkQ 8 (nWord k W)) ∧
    (∀ p ∈ e29Partners, p < 28 ∧ p ≠ 0 ∧ mkQ 8 (nG (2 * p) * nG (2 * p)) = mkQ 8 (nA * nA)) ∧
    (nY3 * nY3 * nY3 = 1 ∧
      (cycPerm8 e29Y3 ∈ agl32 ∧ Equiv.Perm.sign (cycPerm8 e29Y3) = 1) ∧
      (∀ r ∈ e29Y3Rows, mkQ 8 (nY3 * nG (2 * r.1 + r.2.1) * nY3⁻¹) = mkQ 8 (nWord r.1 r.2.2)) ∧
      ∀ k ∈ 0 :: e29Partners, mkQ 8 (nY3 * nG (2 * k)) ≠ mkQ 8 (nG (2 * k) * nY3)) ∧
    1344 ≤ (aglFin ()).card ∧ (evenFin0 ()).card = 64 :=
  ⟨TableFact.genSub_index e29Words (by norm_num) [0, 1] CFSG.KBFact.F272901a, e29_rows,
    e29_conj, e29_nodup, e29_distinct, e29_partner, e29_y3, le_card_aglFin, e29_even⟩

end Certificates
