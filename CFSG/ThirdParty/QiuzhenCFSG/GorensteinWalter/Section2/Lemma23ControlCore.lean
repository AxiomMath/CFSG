module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.3(iii) from the control cores: the arrow alternative

This module sits ABOVE the `Bender1970_*` per-statement modules: it consumes
the (proved) Bender [1] statements 1.7(i)/(iii) together with the F*-theory
of `ControlCore` to discharge the equality alternative of Lemma 2.3(iii).
It lives above the wrapper `GorensteinWalter.Section2.Bender1970` so that the
wrapper can import the per-statement modules at landing without an import
cycle: `Basic.lean` imports THIS module (instead of `ControlCore.lean`
directly) for `lemma_2_3_of_controlCore`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u v

/-! ## Lemma 2.3(iii) from the control cores: the arrow alternative -/

/-- The arrow form of Bender [1, 1.6/1.7] on the control cores: if the two
maximal subgroups `A`, `M` of the simple group `G` control-core each other,
then either `A = M` or `F*(A)` and `F*(M)` are `p`-groups for one common
prime `p`.

In the multi-prime branch, [1, 1.7(iii)] with the opposite core as its
`Sbar` gives `A = M`.  In the one-prime branch, `F*(A)` is a `p`-group and
`F*(M)` a `q`-group; if `p ≠ q`, [1, 1.7(i)] gives `O_q(M) ⊓ A = ⊥`, while
`F*(M) = F(M) = O_q(M)` (the layer is trivial in a `q`-group), so the
reverse core `Sbar ≤ F*(M) = O_q(M)` lies in `A` — a contradiction.  Hence
`p = q`. -/
public theorem lemma_2_3_of_controlCore {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) {A M : Subgroup G}
    (hA : IsCoatom A) (hM : IsCoatom M)
    (hAM : ControlCore A M) (hMA : ControlCore M A) :
    A = M ∨
      ∃ p : ℕ, p.Prime ∧
        IsPGroup p (generalizedFittingSubgroupOf A) ∧
          IsPGroup p (generalizedFittingSubgroupOf M) := by
  classical
  by_cases hAMeq : A = M
  · exact Or.inl hAMeq
  · rcases hAM with ⟨S, _hSne, hSF, hSB, hSsub, hSC⟩
    rcases hMA with ⟨Sbar, hSbarne, hSbarF, hSbarA, hSbarsub, hSbarC⟩
    by_cases hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
        2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf M))
    · -- multi-prime branch: [1, 1.7(iii)]
      have hAeq : A = M := bender1970_1_7_iii_equalityOfMaximal hsimple A hA S hSF hSsub hSC
        hSB hM hpi ⟨Sbar, hSbarA, hSbarF, hSbarsub, hSbarC⟩
      exact False.elim (hAMeq hAeq)
    · -- one-prime branch
      have hpiA : Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ≤ 1 := by omega
      have hpiM : Nat.card (primesOfOrder (generalizedFittingSubgroupOf M)) ≤ 1 := by omega
      have hFAn : generalizedFittingSubgroupOf A ≠ ⊥ := by
        intro hbot
        have hSbot : S ≤ ⊥ := by
          intro x hx
          simpa [hbot] using hSF hx
        exact _hSne (le_bot_iff.mp hSbot)
      have hFMn : generalizedFittingSubgroupOf M ≠ ⊥ := by
        intro hbot
        have hSbot : Sbar ≤ ⊥ := by
          intro x hx
          simpa [hbot] using hSbarF hx
        exact hSbarne (le_bot_iff.mp hSbot)
      obtain ⟨p, hp0⟩ := primesOfOrder_nonempty_of_ne_bot (generalizedFittingSubgroupOf A) hFAn
      obtain ⟨q, hq0⟩ := primesOfOrder_nonempty_of_ne_bot (generalizedFittingSubgroupOf M) hFMn
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [primesOfOrder] using hp0)
      have hq : q.Prime := Nat.prime_of_mem_primeFactors (by simpa [primesOfOrder] using hq0)
      have hpfA : ((Nat.card (↥(generalizedFittingSubgroupOf A))).primeFactors).card ≤ 1 := by
        have hset : primesOfOrder (generalizedFittingSubgroupOf A) =
            ↑((Nat.card ↥(generalizedFittingSubgroupOf A)).primeFactors) := by
          ext q
          rfl
        have hcard : Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) =
            ((Nat.card ↥(generalizedFittingSubgroupOf A)).primeFactors).card := by
          rw [hset]
          exact (Nat.card_coe_set_eq
            ((Nat.card ↥(generalizedFittingSubgroupOf A)).primeFactors : Set ℕ)).trans
            (Set.ncard_coe_finset (Nat.card ↥(generalizedFittingSubgroupOf A)).primeFactors)
        rw [← hcard]
        exact hpiA
      have hpfM : ((Nat.card (↥(generalizedFittingSubgroupOf M))).primeFactors).card ≤ 1 := by
        have hset : primesOfOrder (generalizedFittingSubgroupOf M) =
            ↑((Nat.card ↥(generalizedFittingSubgroupOf M)).primeFactors) := by
          ext q
          rfl
        have hcard : Nat.card (primesOfOrder (generalizedFittingSubgroupOf M)) =
            ((Nat.card ↥(generalizedFittingSubgroupOf M)).primeFactors).card := by
          rw [hset]
          exact (Nat.card_coe_set_eq
            ((Nat.card ↥(generalizedFittingSubgroupOf M)).primeFactors : Set ℕ)).trans
            (Set.ncard_coe_finset (Nat.card ↥(generalizedFittingSubgroupOf M)).primeFactors)
        rw [← hcard]
        exact hpiM
      have hAp_unique : ∀ r : ℕ, r ∈ primesOfOrder (generalizedFittingSubgroupOf A) → r = p := by
        intro r hr
        have hrpf : r ∈ (Nat.card (↥(generalizedFittingSubgroupOf A))).primeFactors := by
          simpa [primesOfOrder] using hr
        exact (Finset.card_le_one.mp hpfA) r hrpf p hp0
      have hMq_unique : ∀ r : ℕ, r ∈ primesOfOrder (generalizedFittingSubgroupOf M) → r = q := by
        intro r hr
        have hrpf : r ∈ (Nat.card (↥(generalizedFittingSubgroupOf M))).primeFactors := by
          simpa [primesOfOrder] using hr
        exact (Finset.card_le_one.mp hpfM) r hrpf q hq0
      have hAp : IsPGroup p (generalizedFittingSubgroupOf A) := by
        refine isPGroup_of_primeFactors_subset_singleton (generalizedFittingSubgroupOf A) hp ?_
        intro r hr
        exact hAp_unique r (by simpa [primesOfOrder] using hr)
      have hMq : IsPGroup q (generalizedFittingSubgroupOf M) := by
        refine isPGroup_of_primeFactors_subset_singleton (generalizedFittingSubgroupOf M) hq ?_
        intro r hr
        exact hMq_unique r (by simpa [primesOfOrder] using hr)
      by_cases hpq : p = q
      · exact Or.inr ⟨p, hp, hAp, by simpa [hpq] using hMq⟩
      · -- p ≠ q: contradiction via [1, 1.7(i)]
        have hqπ : q ∉ primesOfOrder (fittingSubgroupOf A) := by
          intro hq'
          have hq'' : q ∈ primesOfOrder (generalizedFittingSubgroupOf A) :=
            primesOfOrder_subset_of_le (le_sup_left : fittingSubgroupOf A ≤
              generalizedFittingSubgroupOf A) hq'
          exact hpq (hAp_unique q hq'').symm
        have hcore : qCoreOf M q ⊓ A = ⊥ :=
          bender1970_1_7_i_oddCoreDisjoint hsimple A hA S hSF hSsub hSC hSB q hq hqπ
        have hEbot : componentLayerOf M = ⊥ :=
          componentLayerOf_eq_bot_of_isPGroup M hq hMq
        have hFqcore : qCoreOf M q = fittingSubgroupOf M :=
          qCoreOf_eq_fittingSubgroupOf_of_isPGroup M hq hMq
        have hFstar_eq : generalizedFittingSubgroupOf M = qCoreOf M q := by
          calc
            generalizedFittingSubgroupOf M = fittingSubgroupOf M ⊔ componentLayerOf M := rfl
            _ = fittingSubgroupOf M ⊔ ⊥ := by rw [hEbot]
            _ = fittingSubgroupOf M := by simp
            _ = qCoreOf M q := hFqcore.symm
        have hSbarF' : Sbar ≤ qCoreOf M q := by
          intro x hx
          have hxF : x ∈ generalizedFittingSubgroupOf M := hSbarF hx
          simpa [hFstar_eq] using hxF
        have hSbarle : Sbar ≤ qCoreOf M q ⊓ A := by
          intro x hx
          exact ⟨hSbarF' hx, hSbarA hx⟩
        have hSbarlebot : Sbar ≤ ⊥ := by
          intro x hx
          have hx' : x ∈ qCoreOf M q ⊓ A := hSbarle hx
          simpa [hcore] using hx'
        exact False.elim (hSbarne (le_bot_iff.mp hSbarlebot))

end CFSG.GorensteinWalter
