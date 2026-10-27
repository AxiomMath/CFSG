module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970 -- the [1]-statements 1.6/1.7 (sorrys until the Bender1970_* modules land; then re-exported proved)
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample -- minimalCounterexample_isSimple
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23IIHelpers -- oddCore_inversion_of_disjoint

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2 lemma 2.3 applications below the wrapper

The paper's Lemma 2.3 is cited wholesale from Bender [1, §1.6/7] ("On groups
with abelian Sylow 2-subgroups", Math. Z. 117 (1970), 164–176;
`books/bender-abelian-sylow2.pdf`).  This module sits BELOW
`GorensteinWalter.Section2.Basic` and holds the provable applications of the
[1]-statements that the per-theorem modules (`Lemma24`, `Lemma25`, `Lemma27`,
`Lemma28`, `Theorem26`, `Theorem210`) need — it was extracted from the
old `Section2/Lemma23.lean` (which imports `Basic`, making its helpers
unreachable from the per-theorem modules without a landing cycle).

Content:

* `lemma_2_3_ii_inverts_of_core_disjoint` — a legacy odd-core inversion
  utility (`oddCore_inversion_of_disjoint`), retained for callers that
  genuinely use `O_{2ᶜ}(M)`;
* `lemma_2_3_equalityAlternative_of_Fstar_contained` — the equality
  alternative of Lemma 2.3(iii) from [1, 1.6];
* `lemma_2_3_ii_coreDisjoint_prime_of_Fstar_le` — the first conjunct of
  Lemma 2.3(ii) for primes outside `π(F(Ĥ))` from [1, 1.7(i)], given
  `F*(Ĥ) ≤ M`;
* `lemma_2_3_ii_coreDisjoint_prime_of_controlCore` — the same from the
  control-core bridge.

These odd-core statements are not the paper's Lemma 2.3(ii).  The corrected
owner `Section2/Lemma23II.lean` formalizes
`F_{πᶜ}(M) = O_{πᶜ}(F(M))` for `π = π(F(Ĥ))` and proves it directly
from Bender 1.7(i).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## Legacy odd-core inversion utility

Given the first conjunct (`F₂'(M) ∩ Ĥ = 1`), the inversion conclusion follows
from Fact 1.5(ii): `D := O₂'(M)` is a `2'`-group acted on by the involution
`t` (`D ⊴ M` and `t ∈ M`), and its `t`-fixed part is trivial because
`C_D(t) = D ∩ C_G(t) = D ∩ H ≤ D ∩ Ĥ = 1` (the setup gives
`H = C_G(t) ≤ Ĥ`).  Fact 1.5(ii) then decomposes every `x ∈ D` uniquely as
`x = c · i` with `c` fixed by `t` and `i` inverted by `t`; the fixed part is
trivial, so `x` itself is inverted by `t`.
-/

/-- If the odd core of `M` avoids `Ĥ`, then `t` inverts it whenever
`t ∈ M`.  This valid specialization is retained for independent callers;
it is not the source-corrected `lemma_2_3_ii`. -/
public theorem lemma_2_3_ii_inverts_of_core_disjoint
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (M : Subgroup G)
    (hcore : oddCoreOf M ⊓ c.Hhat = ⊥) :
    c.t ∈ M → ∀ x : G, x ∈ (oddCoreOf M : Set G) → c.t * x * c.t⁻¹ = x⁻¹ := by
  exact oddCore_inversion_of_disjoint c M hcore

/-! ## Lemma 2.3(iii): the equality alternative via Bender [1, 1.6]

The paper's Lemma 2.3(iii) ("if we also have `M ↝ Ĥ`, then `Ĥ = M` unless
`F*(Ĥ)` and `F*(M)` are p-groups") is [1, 1.6] applied to the maximal pair
`(A, M)`: "Let A and B be different maximal subgroups of a simple group G
such that `F*(A) ⊆ B` and `F*(B) ⊆ A`.  Then `F*(A)` and `F*(B)` are
p-groups (for the same prime p)".  The relation-level bridge from the two
`NormalizerControlledBy` hypotheses is the control-core route of
`GorensteinWalter/Section2/ControlCore.lean` (the direct containment
bridge is false in general — see the module header); the containments are
therefore explicit hypotheses below, making this theorem a stronger
corollary of `lemma_2_3_of_controlCore`.  The `A = M` branch
is discharged first (repo protocol: prune easy branches early).
-/

/-- Lemma 2.3(iii) of Bender (p. 219), i.e. [1, 1.6], from the two
containments: if the generalized Fitting subgroups of the two maximal
subgroups `A`, `M` are mutually contained (`F*(A) ≤ M`, `F*(M) ≤ A`), then
either `A = M` or `F*(A)` and `F*(M)` are p-groups for one common prime
`p`.  The `NormalizerControlledBy` hypotheses are carried over from
`lemma_2_3` in `Section2/Basic.lean`; the paper's bridge from them to the
two containments is the control-core route of `Section2/ControlCore.lean`
(the direct containment is false in general: S₄ counterexample), so this
theorem is the stronger-containment form of
`lemma_2_3_of_controlCore` — see the module header and
`node_graph/section2/lemma_2_3.md`. -/
public theorem lemma_2_3_equalityAlternative_of_Fstar_contained
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    {A M : Subgroup G}
    (hA : IsCoatom A) (hM : IsCoatom M)
    (_hAM : NormalizerControlledBy A M) (_hMA : NormalizerControlledBy M A)
    (hFAM : generalizedFittingSubgroupOf A ≤ M)
    (hFMA : generalizedFittingSubgroupOf M ≤ A) :
    A = M ∨
      ∃ p : ℕ, p.Prime ∧
        IsPGroup p (generalizedFittingSubgroupOf A) ∧
          IsPGroup p (generalizedFittingSubgroupOf M) := by
  by_cases h : A = M
  · exact Or.inl h
  · exact Or.inr (bender1970_1_6_maximalSubgroups_pGroups
      (minimalCounterexample_isSimple hmin) A M hA hM h hFAM hFMA)

/-! ## Prime-wise Bender 1.7(i) consequences

For every prime outside `π(F(Ĥ))`, [1, 1.7(i)] — "O_q(B) ∩ A = 1 for
`q ∈ π(F(A))'`" — applies with `A := Ĥ`, `B := M`, and the subnormal
subgroup `S := F*(Ĥ)` of `F*(Ĥ)` (the centralizer condition
`C_{F*(Ĥ)}(S) ≤ S` is then trivially `Z(F*(Ĥ)) ≤ F*(Ĥ)`), giving
`O_q(M) ∩ Ĥ = 1` for every prime `q ∉ π(F(Ĥ))`.  The hypotheses needed:
`G` simple (from `hmin` via `minimalCounterexample_isSimple`), `Ĥ` maximal
(from the setup), and the bridge `F*(Ĥ) ≤ M` (an explicit hypothesis — not
derivable from `NormalizerControlledBy`, see the module header).  The
corrected Lemma 2.3(ii) uses only the primes outside `π(F(Ĥ))`,
because its subgroup is `O_{πᶜ}(F(M))`.
-/

/-- Prime-wise Bender 1.7(i), for primes outside `π(F(Ĥ))`: given
`F*(Ĥ) ≤ M` (the explicit-containment bridge), every `q`-core of `M`
with `q ∉ π(F(Ĥ))` avoids `Ĥ` — i.e. `O_q(M) ∩ Ĥ = 1` — by Bender [1,
1.7(i)] applied with `A := Ĥ`, `B := M`, `S := F*(Ĥ)`.  The control-core analogue
(`lemma_2_3_ii_coreDisjoint_prime_of_controlCore` below) consumes the
bridge output `ControlCore c.Hhat M` instead of the containment. -/
public theorem lemma_2_3_ii_coreDisjoint_prime_of_Fstar_le
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hFstar : generalizedFittingSubgroupOf c.Hhat ≤ M) :
    ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (fittingSubgroupOf c.Hhat) →
      qCoreOf M q ⊓ c.Hhat = ⊥ := by
  intro q hq hqπ
  have hSsub : ((generalizedFittingSubgroupOf c.Hhat).subgroupOf
      (generalizedFittingSubgroupOf c.Hhat)).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  have hCS : generalizedFittingSubgroupOf c.Hhat ⊓
      Subgroup.centralizer ((generalizedFittingSubgroupOf c.Hhat : Set G)) ≤
        generalizedFittingSubgroupOf c.Hhat := by
    intro x hx
    exact hx.1
  exact bender1970_1_7_i_oddCoreDisjoint (minimalCounterexample_isSimple hmin)
    c.Hhat c.Hhat_maximal (generalizedFittingSubgroupOf c.Hhat) le_rfl hSsub hCS
    hFstar q hq hqπ

/-- Prime-wise Bender 1.7(i), for primes outside `π(F(Ĥ))`, from the
control-core bridge: given `ControlCore c.Hhat M` (the hypothesis shape of
[1, 1.7] produced by the bridge in `Section2/ControlCore.lean`), every
`q`-core of `M` with `q ∉ π(F(Ĥ))` avoids `Ĥ` — i.e. `O_q(M) ∩ Ĥ = 1` — by
Bender [1, 1.7(i)] applied with `A := Ĥ`, `B := M`, and the control-core
witness as `S`.  This is the control-core analogue of
`lemma_2_3_ii_coreDisjoint_prime_of_Fstar_le`. -/
public theorem lemma_2_3_ii_coreDisjoint_prime_of_controlCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hC : ControlCore c.Hhat M) :
    ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (fittingSubgroupOf c.Hhat) →
      qCoreOf M q ⊓ c.Hhat = ⊥ := by
  rcases hC with ⟨S, _hSne, hSF, hSB, hSsub, hCS⟩
  exact bender1970_1_7_i_oddCoreDisjoint (minimalCounterexample_isSimple hmin)
    c.Hhat c.Hhat_maximal S hSF hSsub hCS hSB

end CFSG.GorensteinWalter
