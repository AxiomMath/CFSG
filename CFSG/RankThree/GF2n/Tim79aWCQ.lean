module

public import CFSG.RankThree.GF2n.Tim79aMinCex

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

@[expose] def Tim79aStatementWCQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pCore 2 G = ⊥ →
    ∀ M : Subgroup G, IsMaximalTwoLocal M → generalizedFitting M = pCore 2 M →
    ∀ V : Subgroup G, Maximal (fun U : Subgroup G => U ≤ M ∧
      M ≤ Subgroup.normalizer (U : Set G) ∧ IsMulCommutative U) V →
    Assembly.IsElemAbelian 2 V → IsTI V → 4 ≤ Nat.card V →
    WeaklyClosedIn V (inSubgroup (pCore 2) M) →
    WeaklyClosedIn V M ∨
      ∀ H : Subgroup G, inSubgroup (pCore 2) H ≠ ⊥ →
        inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) ≤ H →
        V ≤ inSubgroup (pCore 2) H

namespace Tim79a

variable {G : Type} [Group G]

structure MinCexWCQ (M V Q P H : Subgroup G) : Prop extends MinCex M V Q P H where
  wcQ : WeaklyClosedIn V Q

theorem tim79aStatementWCQ_of_not_minCexWCQ
    (h : ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), ¬ MinCexWCQ M V Q P H) :
    Tim79aStatementWCQ := by
  intro G _ _ ho M hM hF V hV hel hTI h4 hwc
  by_contra hcon
  push Not at hcon
  obtain ⟨hnwc, H₀, hO₀, hP₀, hV₀⟩ := hcon
  set Q := inSubgroup (pCore 2) M with hQ
  set P := Q ⊓ Subgroup.centralizer (V : Set G) with hP
  obtain ⟨H, hH, hmin⟩ := Set.Finite.exists_minimalFor id
    {K : Subgroup G | P ≤ K ∧ inSubgroup (pCore 2) K ≠ ⊥ ∧ ¬ V ≤ inSubgroup (pCore 2) K}
    (Set.toFinite _) ⟨H₀, hP₀, hO₀, hV₀⟩
  refine h G M V Q P H ⟨⟨ho, hM, hF, hV, hel, hTI, h4, hQ, hP, hnwc, hH.1, hH.2.1, hH.2.2, ?_⟩,
    hwc⟩
  intro K hPK hOK hKH
  by_contra hVK
  exact absurd (hmin ⟨hPK, hOK, hVK⟩ hKH.le) (not_le_of_gt hKH)

end Tim79a

end CFSG.RankThree.GF2n
