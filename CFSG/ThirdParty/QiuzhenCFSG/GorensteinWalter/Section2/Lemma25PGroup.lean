module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedFittingSubgroupConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma24

namespace CFSG
end CFSG
open CFSG

/-!
# The `p`-group branch of Gorenstein--Walter Lemma 2.5

If `F*(A)` is a `p`-group and `O_{2'}(A)` is nontrivial, then `p` is odd.
Exact conjugation transport makes `F*(A^g)` a `p`-group too, so the proved
Glauberman application in Lemma 2.4 forces `A = A^g`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem lemma25_le_qCoreOf_of_isNormalIn_pGroup
    {G : Type u} [Group G] [Finite G]
    (A Q : Subgroup G) (p : ℕ) (_hp : p.Prime)
    (hQA : Q ≤ A) (hQ : IsNormalIn Q A) (hQp : IsPGroup p Q) :
    Q ≤ qCoreOf A p := by
  let : Fact p.Prime := ⟨_hp⟩
  have hQsub : Q.subgroupOf A ≤ pCore p (↑A) :=
    le_sSup ⟨Subgroup.normal_subgroupOf_of_le_normalizer (H := A) (N := Q)
      (le_normalizer_of_isNormalIn hQ),
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm⟩
  have hmap := Subgroup.map_mono (f := A.subtype) hQsub
  have hQmap : (Q.subgroupOf A).map A.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQA
  simpa [qCoreOf, hQmap] using hmap

private theorem lemma25_oddCoreOf_isNormalIn
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    IsNormalIn (oddCoreOf A) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
    exact a.2
  · intro a ha x hx
    rcases Subgroup.mem_map.mp hx with ⟨xA, hxA, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨a, ha⟩ : ↑A) * xA * (⟨a, ha⟩ : ↑A)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↑A)).conj_mem xA hxA ⟨a, ha⟩

private theorem lemma25_prime_odd_of_oddCore_ne_bot_of_fstar_isPGroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hoddCore : oddCoreOf A ≠ ⊥)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf A)) :
    Odd p := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · have hFleQ : generalizedFittingSubgroupOf A ≤ qCoreOf A 2 :=
      lemma25_le_qCoreOf_of_isNormalIn_pGroup A
        (generalizedFittingSubgroupOf A) 2 Nat.prime_two
        (fstar_generalizedFittingSubgroupOf_le A)
        (fstar_generalizedFittingSubgroupOf_isNormalIn A) hAp
    have hOleC : oddCoreOf A ≤
        Subgroup.centralizer ((generalizedFittingSubgroupOf A : Set G)) := by
      exact (pPrimeCore_map_le_centralizer_pCore_map (p := 2) A).trans
        (Subgroup.centralizer_le (show
          (generalizedFittingSubgroupOf A : Set G) ⊆ (qCoreOf A 2 : Set G) from hFleQ))
    have hOleFstar : oddCoreOf A ≤ generalizedFittingSubgroupOf A := by
      intro x hx
      exact centralizer_intersection_fstar_le_fstar A
        ⟨hOleC hx, (lemma25_oddCoreOf_isNormalIn A).1 hx⟩
    have hO2 : IsPGroup 2 (oddCoreOf A) := IsPGroup.to_le hAp hOleFstar
    have hcard : Nat.card (↑(oddCoreOf A)) = Nat.card (↑(pPrimeCore 2 (↑A))) :=
      Subgroup.card_map_of_injective A.subtype_injective
    have hcop : Nat.Coprime 2 (Nat.card (↑(oddCoreOf A))) := by
      rw [hcard]
      exact pPrimeCore_coprime_card (p := 2) (G := ↑A)
    have hbot : oddCoreOf A = ⊥ := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact section8_eq_bot_of_isPGroup_of_coprime hO2 hcop
    exact (hoddCore hbot).elim
  · exact hpodd

/-- The `p`-group branch of Lemma 2.5.  A nontrivial odd core forces the
common generalized-Fitting prime to be odd, so Lemma 2.4 applies. -/
public theorem eq_conjugateSubgroup_of_controlled_conjugate_of_oddCore_ne_bot_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (g : G)
    (hcontrol : NormalizerControlledBy c.Hhat (conjugateSubgroup c.Hhat g))
    (hodd : oddCoreOf c.Hhat ≠ ⊥)
    {p : ℕ} (hp : p.Prime)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf c.Hhat)) :
    c.Hhat = conjugateSubgroup c.Hhat g := by
  have hpodd : Odd p :=
    lemma25_prime_odd_of_oddCore_ne_bot_of_fstar_isPGroup c.Hhat hp hodd hAp
  have hBp : IsPGroup p
      (generalizedFittingSubgroupOf (conjugateSubgroup c.Hhat g)) := by
    rw [generalizedFittingSubgroupOf_conjugateSubgroup]
    exact hAp.map (MulAut.conj g).toMonoidHom
  have hBmax : IsCoatom (conjugateSubgroup c.Hhat g) := by
    dsimp [conjugateSubgroup]
    exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup c.Hhat).2
      c.Hhat_maximal
  exact lemma_2_4 hmin c.Hhat_maximal hBmax hcontrol hp hpodd hAp hBp

end CFSG.GorensteinWalter
