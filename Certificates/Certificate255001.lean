module

public import Certificates.Data.Holder255.E64Words
public import Certificates.Data.Holder255.E64Model
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.CosPres.F255001
import Certificates.Kernel.WrTwin.E64Props
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.KC.MiscCoset CFSG.KD.WrTwin CFSG.ClassicalInvolution.Q3.E64Data

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.E64Data CFSG.ClassicalInvolution.Q3.AE in
theorem certificate255001 :
    ((genSub {r : FreeGroup (Fin 28) | r ∈ e64Words.map FreeGroup.mk} [0, 1]).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 28) | r ∈ e64Words.map FreeGroup.mk} [0, 1]).index ≤ 1344) ∧
    (∀ d ∈ e64ConjData,
      mG d.1 * mG (2 * d.2.1 + d.2.2.1) * (mG d.1)⁻¹ = mWord d.2.2.2.1 d.2.2.2.2) ∧
    (∀ j < 14, cycPerm (e64Conj.getD j []) ∈ l32 ∧
      Equiv.Perm.sign (cycPerm (e64Conj.getD j [])) = 1) ∧
    (m8 0).Nodup ∧
    (∀ j < 14, ∀ k < 14, j ≠ k → mG (2 * j) ∉ m8 k) ∧
    (e64JStar < 14 ∧ e64JStar ≠ 0 ∧ mG (2 * e64JStar) * mG (2 * e64JStar) = mA * mA) ∧
    (mY3 * mY3 * mY3 = 1 ∧
      (cycPerm [[0, 1, 3], [4, 5, 6]] ∈ l32 ∧ Equiv.Perm.sign (cycPerm [[0, 1, 3], [4, 5, 6]]) = 1) ∧
      (∀ r ∈ e64Y3Rows, mY3 * mG (2 * r.1 + r.2.1) * mY3⁻¹ = mWord r.1 r.2.2) ∧
      mY3 * mA ≠ mA * mY3 ∧ mY3 * mG (2 * e64JStar) ≠ mG (2 * e64JStar) * mY3) ∧
    (l32Fin ()).card = 168 ∧ (evenFin ()).card = 64 :=
  ⟨TableFact.genSub_index e64Words (by norm_num) [0, 1] CFSG.KBFact.F255001a, e64_rows_hold,
    e64_conj, e64_nodup, e64_distinct, e64_partner, e64_y3, card_l32Fin, e64_even⟩

end Certificates
