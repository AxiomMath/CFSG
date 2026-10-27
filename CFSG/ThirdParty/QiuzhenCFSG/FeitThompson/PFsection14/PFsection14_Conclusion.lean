module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: section conclusion
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-- Section 14 contradiction from `(14.2)` and Hypothesis `(14.1)`. -/
public theorem theorem_14_conclusion
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (theorem_14_2_a_data P U W2 p q ∧
        theorem_14_2_b_data Q W1 W2 U q) →
        False := by
  intro hctx h14
  have hqp : q < p := hctx.2
  rcases h14 with ⟨ha, hb⟩
  rcases ha with ⟨hfield, hconseq⟩
  rcases hconseq with ⟨hp, hq, _hPelem, _hUcomm, _hPcard, _hUcard,
    _hW2le, _hW2card, hA⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  rcases hfield with ⟨_hp', _hq', σ, hσinj, _hTop, _hPeq, hUeq, hP0eq⟩
  rcases hb with ⟨hQelem, hW2norm, y, hyQ, hW2ynorm⟩
  haveI : IsElementaryAbelian q Q := hQelem
  haveI : IsMulCommutative Q := hQelem.toIsMulCommutative
  have hp_ne_q : p ≠ q := by
    intro hpq_eq
    rw [hpq_eq] at hqp
    exact (Nat.lt_irrefl q) hqp
  have hcop : Nat.Coprime p (Nat.card Q) :=
    section14_coprime_card_of_isElementaryAbelian_of_ne hp hq hp_ne_q
  have hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q := by
    simpa [appendixCNormalizes, hP0eq] using hW2norm
  have hyQinv : y⁻¹ ∈ Q := Q.inv_mem hyQ
  have hP0yU :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y⁻¹)
        (Subgroup.map σ (appendixCUInH p q)) := by
    simpa [appendixCNormalizes, appendixCRightConjugate, hP0eq, hUeq] using hW2ynorm
  have hB : appendixCConditionB.{u} p q :=
    appendixCConditionB_of_embeddingData (p := p) (q := q) σ hσinj Q hcop
      y⁻¹ hyQinv hP0Q hP0yU
  have hA' : appendixCConditionA p q := by
    simpa [appendixCConditionA] using hA
  have hpq_le : p ≤ q := appendixC_theorem_C.{u} (p := p) (q := q) hA' hB
  exact (Nat.not_lt_of_ge hpq_le) hqp
end CFSG.Section14
