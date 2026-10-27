module

public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProofJ2
import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec3
  CFSG.RankThree.PartTwo.Sec15.Item322Scope

theorem item3_22TwoJ_holds :
    Item3_22TwoJ := by
  intro X _ _ hF ⟨e⟩ R hQR ⟨eR⟩ _ hz
  have hCQ : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X := by
    rw [← hF]
    exact CFSG.centralizer_generalizedFitting_le X
  set Q := CFSG.pCore 2 X with hQ
  have hQn : Q.Normal := CFSG.pCore_normal
  set V := omegaG Q with hVdef
  have hVn : V.Normal := omegaG_normal hQn
  have hVQ : V ≤ Q := omegaG_le Q
  have hVel : IsElemTwo V := isElemTwo_omegaG Q
  have hQV : Q ≤ Subgroup.centralizer (V : Set X) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have hZR : (omegaOneCenter (⊤ : Subgroup R)).map R.subtype ≤ V := by
    rw [map_omegaOneCenter, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    intro z hz
    have hzQ : z ∈ Q := hCQ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (hz.2.1 q (hQR hq)).symm)
    exact ⟨hzQ, fun x hx => hz.2.1 x (hQR hx), hz.2.2⟩
  have hVZ : ¬ V ≤ Subgroup.center X := fun h => hz (hZR.trans h)
  have hRQ : Q.relIndex R = 4 := by
    have h := Subgroup.relIndex_ker R (QuotientGroup.mk' Q)
    rw [QuotientGroup.ker_mk'] at h
    rw [h, Nat.card_congr eR.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hAQ : ∀ A ∈ famG R 0, A ≤ Q := by
    intro A hA a ha
    by_contra haQ
    have h4 := four_lt_relIndex_centralizer e hVn hVel hQV hVZ haQ
      (by rw [hA.2.1.2 a ha]; exact Q.one_mem)
    have hstd := relIndex_centralizer_le_of_famG (hVQ.trans hQR) hVel hA
    have h1 : (Subgroup.centralizer ({a} : Set X)).relIndex V ≤
        (Subgroup.centralizer (A : Set X)).relIndex V :=
      Subgroup.relIndex_le_of_le_left
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
        (relIndex_ne_zero_of_finite _ _)
    have h2 : (Subgroup.centralizer (V : Set X)).relIndex A ≤ Q.relIndex A :=
      Subgroup.relIndex_le_of_le_left hQV (relIndex_ne_zero_of_finite _ _)
    have h3 : Q.relIndex A ≤ Q.relIndex R :=
      Subgroup.relIndex_le_of_le_right hA.1 (relIndex_ne_zero_of_finite _ _)
    rw [pow_zero, one_mul] at hstd
    omega
  rw [map_higherElemThompson R 0]
  exact jG_normal fun g A hA a ha => hQR (hQn.conj_mem a (hAQ A hA ha) g)

end CFSG.RankThree.PartTwo.Sec15
