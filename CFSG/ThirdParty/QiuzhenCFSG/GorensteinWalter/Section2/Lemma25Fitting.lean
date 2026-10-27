module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FittingSubgroupConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17ii

namespace CFSG
end CFSG
open CFSG

/-!
# The Fitting-subgroup half of Gorenstein--Walter Lemma 2.5

In the non-`p` branch, Bender 1.7(ii) forces the Fitting subgroup of the
controlled conjugate back into the original maximal subgroup.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem lemma25_isPGroup_of_pResidualOf_eq_bot
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hRes : pResidualOf H p = ⊥) :
    IsPGroup p H := by
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (H ⧸ (pResidualOf H p).subgroupOf H) :=
    fstar_isPGroup_quotient_pResidualOf H p hp
  have hResbot : (pResidualOf H p).subgroupOf H = ⊥ := by
    ext x
    simp [hRes]
  have hcard' : Nat.card (H ⧸ (pResidualOf H p).subgroupOf H) = Nat.card H :=
    Nat.card_congr ((Subgroup.quotientEquivOfEq hResbot).trans
      QuotientGroup.quotientBot.toEquiv)
  rcases IsPGroup.iff_card.mp hQ with ⟨n, hn⟩
  refine IsPGroup.of_card (n := n) ?_
  rw [← hcard']
  exact hn

private theorem lemma25_pResidualOf_generalizedFitting_isNormalIn
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) :
    IsNormalIn (pResidualOf (generalizedFittingSubgroupOf A) p) A := by
  let R : Subgroup G := pResidualOf (generalizedFittingSubgroupOf A) p
  have hKmap : (R.subgroupOf (generalizedFittingSubgroupOf A)).map
      (generalizedFittingSubgroupOf A).subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le
      (pResidualOf_le (generalizedFittingSubgroupOf A) p)
  have h := fstar_characteristic_subgroupOf_map_normal_in
    (F := generalizedFittingSubgroupOf A)
    (K := R.subgroupOf (generalizedFittingSubgroupOf A))
    (fstar_pResidualOf_subgroupOf_characteristic
      (generalizedFittingSubgroupOf A) p)
    (fstar_generalizedFittingSubgroupOf_isNormalIn A)
  simpa [R, hKmap] using h

private theorem lemma25_normalizer_pResidualOf_generalizedFitting_eq
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (p : ℕ)
    (hne : pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥) :
    Subgroup.normalizer
      ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) = A := by
  let R : Subgroup G := pResidualOf (generalizedFittingSubgroupOf A) p
  let N : Subgroup G := Subgroup.normalizer (R : Set G)
  have hRnormA : IsNormalIn R A := by
    simpa [R] using lemma25_pResidualOf_generalizedFitting_isNormalIn A p
  have hAleN : A ≤ N := le_normalizer_of_isNormalIn hRnormA
  have hNne_top : N ≠ ⊤ := by
    intro htop
    have hRnormG : R.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hRnormG; hsimple.eq_bot_or_eq_top_of_normal R) with hbot | htopR
    · exact hne hbot
    · have hAtop : A = ⊤ := by
        have hTopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          have hxR : x ∈ R := by
            rw [htopR]
            exact hx
          exact (pResidualOf_le (generalizedFittingSubgroupOf A) p).trans
            (fstar_generalizedFittingSubgroupOf_le A) hxR
        exact le_antisymm le_top hTopLeA
      exact hA.1 hAtop
  refine le_antisymm ?_ hAleN
  intro x hx
  by_cases hEq : A = N
  · rw [hEq]
    exact hx
  · have hlt : A < N := lt_of_le_of_ne hAleN (by intro h; exact hEq h)
    have htop := hA.2 N hlt
    exact False.elim (hNne_top htop)

private theorem lemma25_qCoreOf_le_of_not_pGroup
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓
      Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    (hnp : ∀ p : ℕ, p.Prime →
      ¬ IsPGroup p (generalizedFittingSubgroupOf A))
    {p : ℕ} (hp : p.Prime)
    (hpA : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    qCoreOf B p ≤ A := by
  have hRes : pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥ := by
    intro hbot
    exact hnp p hp (lemma25_isPGroup_of_pResidualOf_eq_bot
      (generalizedFittingSubgroupOf A) p hp hbot)
  have hcomm :
      ⁅qCoreOf B p, pResidualOf (generalizedFittingSubgroupOf A) p⁆ = ⊥ :=
    bender1970_1_7_ii_commutator_pResidual hsimple A hA S hSF hSsub hCS
      hSB p hp hpA
  have hCle : qCoreOf B p ≤
      Subgroup.centralizer
        ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := qCoreOf B p)
      (H₂ := pResidualOf (generalizedFittingSubgroupOf A) p)).1 hcomm
  have hN : Subgroup.normalizer
      ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) = A :=
    lemma25_normalizer_pResidualOf_generalizedFitting_eq
      hsimple A hA p hRes
  exact hCle.trans
    ((Subgroup.centralizer_le_normalizer _).trans (le_of_eq hN))

private theorem lemma25_mem_primesOfOrder_of_qCoreOf_ne_bot
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hQ : qCoreOf A p ≠ ⊥) :
    p ∈ primesOfOrder (fittingSubgroupOf A) := by
  let F : Subgroup G := fittingSubgroupOf A
  let Q : Subgroup G := qCoreOf A p
  have hQleF : Q ≤ F := fstar_qCoreOf_le_fittingSubgroupOf A p hp
  have hQnt : Nontrivial (↥Q) := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ
  have : Fact p.Prime := ⟨hp⟩
  rcases exists_ne (1 : ↥Q) with ⟨xQ, hxne⟩
  let x : G := (xQ : ↥Q)
  rcases IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup A p) xQ with ⟨k, hk⟩
  have hkpos : k ≠ 0 := by
    intro hk0
    have hord : orderOf xQ = 1 := by simpa [hk0] using hk
    exact hxne (orderOf_eq_one_iff.mp hord)
  have hpdvd : p ∣ orderOf xQ := by
    rw [hk]
    exact dvd_pow_self p hkpos
  have hordG : orderOf x = orderOf xQ :=
    orderOf_injective Q.subtype Q.subtype_injective xQ
  have hpdvdG : p ∣ orderOf x := by
    rw [hordG]
    exact hpdvd
  have hxG : x ∈ F := hQleF xQ.2
  have hordF : orderOf x ∣ Nat.card (↥F) := by
    have : Fintype (↥F) := Fintype.ofFinite _
    let xF : ↥F := ⟨x, hxG⟩
    have hord : orderOf xF = orderOf x :=
      (orderOf_injective F.subtype F.subtype_injective xF).symm
    simpa [hord] using orderOf_dvd_card (G := ↥F) (x := xF)
  have hpdvdF : p ∣ Nat.card (↥F) := hpdvdG.trans hordF
  have hpf : p ∈ (Nat.card (↥F)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvdF, Nat.card_pos.ne'⟩
  simpa [primesOfOrder] using hpf

/-- In the non-`p` branch of Lemma 2.5, the Fitting subgroup of the
controlled conjugate lies in the original maximal subgroup. -/
public theorem fittingSubgroupOf_conjugateSubgroup_le_of_controlCore_of_not_isPGroup
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A) (g : G)
    (hC : ControlCore A (conjugateSubgroup A g))
    (hnp : ∀ p : ℕ, p.Prime →
      ¬ IsPGroup p (generalizedFittingSubgroupOf A)) :
    fittingSubgroupOf (conjugateSubgroup A g) ≤ A := by
  rcases hC with ⟨S, _hSne, hSF, hSB, hSsub, hCS⟩
  have hcardF : Nat.card ↥(fittingSubgroupOf (conjugateSubgroup A g)) =
      Nat.card ↥(fittingSubgroupOf A) := by
    rw [fittingSubgroupOf_conjugateSubgroup A g]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [fstar_fittingSubgroupOf_eq_iSup_qCoreOf]
  refine iSup_le fun q => ?_
  let p : ℕ := q.1.1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hq : qCoreOf (conjugateSubgroup A g) p = ⊥
  · exact hq ▸ bot_le
  · have hpB : p ∈ primesOfOrder
        (fittingSubgroupOf (conjugateSubgroup A g)) :=
      lemma25_mem_primesOfOrder_of_qCoreOf_ne_bot
        (conjugateSubgroup A g) p hp hq
    have hpA : p ∈ primesOfOrder (fittingSubgroupOf A) := by
      simpa [primesOfOrder, hcardF] using hpB
    exact lemma25_qCoreOf_le_of_not_pGroup hsimple A hA S hSF hSsub hCS
      hSB hnp hp hpA

end CFSG.GorensteinWalter
