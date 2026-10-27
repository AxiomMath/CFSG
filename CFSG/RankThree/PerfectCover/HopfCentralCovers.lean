module

public import CFSG.Foundations.Basic
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import CFSG.RankThree.PerfectCover.HopfFormula
import CFSG.RankThree.PerfectCover.HopfCentralCoversSylow
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
import CFSG.RankThree.PerfectCover.HopfCentralCoversOdd
import CFSG.RankThree.PerfectCover.HopfCentralCoversLift

public section

namespace CFSG.RankThree.PerfectCover

theorem hopf_central_cover_consequences (X : Type) [Group X] :
    ((∀ S : Sylow 2 (CFSG.Open.griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (CFSG.Open.griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  constructor
  · intro hM L _ _ hL he
    obtain ⟨e⟩ := he
    let q := centralQuotientMap e
    have hq : Function.Surjective q := centralQuotientMap_surjective e
    have hk : q.ker = Subgroup.center L := centralQuotientMap_ker e
    have hkc : q.ker ≤ Subgroup.center L := hk.le
    let : Group.IsPerfect L := hL.1
    let : Finite X := finite_of_surjective_monoidHom q hq
    let : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hL e
    let : Finite (hopfMultiplier X) := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
    let : Finite (CFSG.Open.griessHopfMultiplier X) :=
      Finite.of_equiv (hopfMultiplier X) (hopfMultiplierEquivGriess X).symm.toEquiv
    let ψ : CFSG.Open.griessHopfMultiplier X →* q.ker :=
      (hopfMultiplierToKer q hq hkc).comp (hopfMultiplierEquivGriess X).toMonoidHom
    have hψ : Function.Surjective ψ :=
      (hopfMultiplierToKer_surjective q hq hkc).comp (hopfMultiplierEquivGriess X).surjective
    have hbound := sylow_two_card_le_of_surjective ψ hψ hM
    rw [← hk]
    exact hbound
  · intro hM L L' _ _ _ _ hL hL' hc hc' he he'
    obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := he'
    let q := centralQuotientMap e
    let q' := centralQuotientMap e'
    have hq : Function.Surjective q := centralQuotientMap_surjective e
    have hq' : Function.Surjective q' := centralQuotientMap_surjective e'
    have hk : q.ker = Subgroup.center L := centralQuotientMap_ker e
    have hk' : q'.ker = Subgroup.center L' := centralQuotientMap_ker e'
    let : Group.IsPerfect L := hL.1
    let : Group.IsPerfect L' := hL'.1
    let : Finite X := finite_of_surjective_monoidHom q hq
    let : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hL e
    let : Finite (hopfMultiplier X) := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
    let : Finite (CFSG.Open.griessHopfMultiplier X) :=
      Finite.of_equiv (hopfMultiplier X) (hopfMultiplierEquivGriess X).symm.toEquiv
    obtain ⟨m, hm, hcard⟩ := card_eq_two_mul_odd_of_sylow hM
    have hcardM : Nat.card (hopfMultiplier X) = Nat.card q.ker * m := by
      rw [hk, hc, ← hcard]
      exact (Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv).symm
    have htwo : IsPGroup 2 q'.ker :=
      IsPGroup.of_card (n := 1) (by simpa only [hk', pow_one] using hc')
    obtain ⟨α, hα, _⟩ := exists_lift_of_odd_index hL.1 hL'.1
      q hq hk.le q' hq' hk'.le htwo m hm hcardM
    have hcards : Nat.card L = Nat.card L' := by
      rw [card_eq_card_mul_card_ker q hq, card_eq_card_mul_card_ker q' hq',
        hk, hk', hc, hc']
    exact ⟨MulEquiv.ofBijective α ((Nat.bijective_iff_surjective_and_card α).mpr ⟨hα, hcards⟩)⟩

end CFSG.RankThree.PerfectCover
