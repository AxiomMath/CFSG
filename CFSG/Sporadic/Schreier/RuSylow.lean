module

public import CFSG.Sporadic.Schreier.RuSylowC
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped IsMulCommutative

@[expose] def ruBitVec (b : ℕ) : Fin 3 → ZMod 2 := fun k => ((b / 2 ^ (k : ℕ) % 2 : ℕ) : ZMod 2)

@[expose] def ruQGen
    (k : Fin 3) : RuQ := QuotientGroup.mk (ruSGenS (![0, 2, 3] k))

@[expose] def ruLabelHom :
    Multiplicative (Fin 3 → ZMod 2) →* RuQ where
  toFun v := Additive.toMul (Fintype.linearCombination (ZMod 2)
    (fun k => Additive.ofMul (ruQGen k)) (Multiplicative.toAdd v))
  map_one' := by simp
  map_mul' v w := by simp [map_add]

theorem ruLabelHom_single
    (k : Fin 3) :
    ruLabelHom (Multiplicative.ofAdd (Pi.single k 1)) = ruQGen k := by
  simp [ruLabelHom, Fintype.linearCombination_apply_single]

theorem ruQ_closure :
    Subgroup.closure ((QuotientGroup.mk' ruRS) '' ruSGenSet) = ⊤ := by
  rw [← MonoidHom.map_closure, ruSGenSet_closure,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem ruQ_mk_S1 :
    (QuotientGroup.mk (ruSGenS 1) : RuQ) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ruS1_memR)

theorem ruLabelHom_surjective :
    Function.Surjective ruLabelHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← ruQ_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj, rfl⟩ := mem_ruSGenSet hx
  interval_cases j
  · exact ⟨_, ruLabelHom_single 0⟩
  · rw [QuotientGroup.mk'_apply, ruQ_mk_S1]
    exact Subgroup.one_mem _
  · exact ⟨_, ruLabelHom_single 1⟩
  · exact ⟨_, ruLabelHom_single 2⟩

theorem ruLabelHom_bijective :
    Function.Bijective ruLabelHom :=
  ruLabelHom_surjective.bijective_of_nat_card_le (by
    rw [card_ruQ, Nat.card_eq_fintype_card]
    rfl)

@[expose] def ruLabelEquiv :
    RuQ ≃* Multiplicative (Fin 3 → ZMod 2) :=
  (MulEquiv.ofBijective ruLabelHom ruLabelHom_bijective).symm

theorem ruLabelEquiv_apply
    {i : ℕ} (hi : i < 4) :
    ruLabelEquiv (QuotientGroup.mk (ruSGenS i)) =
      Multiplicative.ofAdd (ruBitVec (ruQuotientBits.getD i 0)) := by
  rw [ruLabelEquiv, MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply]
  interval_cases i
  · rw [show ruBitVec (ruQuotientBits.getD 0 0) = Pi.single 0 1 by decide, ruLabelHom_single]
    rfl
  · rw [show ruBitVec (ruQuotientBits.getD 1 0) = 0 by decide, ofAdd_zero, map_one, ruQ_mk_S1]
  · rw [show ruBitVec (ruQuotientBits.getD 2 0) = Pi.single 1 1 by decide, ruLabelHom_single]
    rfl
  · rw [show ruBitVec (ruQuotientBits.getD 3 0) = Pi.single 2 1 by decide, ruLabelHom_single]
    rfl

theorem AT_Ru_Sylow_center_and_abelianization :
    ruR = ⁅ruS, ruS⁆ ∧ ruR.subgroupOf ruS = commutator ruS ∧
      frattini ruS = ruR.subgroupOf ruS ∧ (ruR.subgroupOf ruS).Normal ∧
    CFSG.IsElementaryAbelian 2 (ruS ⧸ ruR.subgroupOf ruS) ∧
      Nat.card (ruS ⧸ ruR.subgroupOf ruS) = 8 ∧
    (Subgroup.center ruS).map ruS.subtype = Subgroup.zpowers ruZ ∧ orderOf ruZ = 2 ∧
      ruZ ∈ ruR ∧
    Nonempty ((ruS ⧸ (Subgroup.zpowers ruZ).subgroupOf ruS) ≃* ruImYS) ∧
      Nat.card ruImYS = 8192 ∧ Nat.card ruImYR = 1024 ∧ ⁅ruImYS, ruImYS⁆ = ruImYR ∧
    ∃ φ : (ruS ⧸ ruR.subgroupOf ruS) ≃* Multiplicative (Fin 3 → ZMod 2), ∀ i < 4,
      φ (QuotientGroup.mk (ruSGenS i)) =
        Multiplicative.ofAdd (ruBitVec (ruQuotientBits.getD i 0)) :=
  ⟨ruR_eq_commutator, ruRS_eq_commutator, frattini_ruS, ruRS_normal, ruQ_elem, card_ruQ,
    center_ruS, orderOf_ruZ, ruZ_memR, ruImYS_iso, card_ruImYS, card_ruImYR, ruImYS_commutator,
    ruLabelEquiv, fun _ hi => ruLabelEquiv_apply hi⟩

end CFSG.Sporadic.RuSchreier
