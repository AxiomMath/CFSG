module

import CFSG.RankThree.PartOne.KF.F128Cls
import CFSG.RankThree.PartOne.S11c.OddG2Plane
import CFSG.RankThree.Chevalley.SteinbergCFOddFourCommutingSL2
import CFSG.RankThree.Chevalley.SteinbergCFTwistedE6CommutingSL2
import CFSG.RankThree.Chevalley.SteinbergCFTrialityDefiningComponent
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.Assembly.RankThreeEven (localRank)

open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo innerAut)



theorem outerComp_of_three_le_localRank {p : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime)
    (h : 3 ≤ localRank p T) : OuterComp p T :=
  fun hLR => (false_of_three_le_localRank hp hLR h).elim

theorem four_mul_le_localRank_of_SL2 {G : Type} [Group G] [Finite G] {k : Type} [Field k]
    [Finite k] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : Nat.card k = p ^ f)
    (ι : Fin 4 → (Matrix.SpecialLinearGroup (Fin 2) k →* G)) (hι : ∀ i, Function.Injective (ι i))
    (hc : ∀ i j, i ≠ j → ∀ A B, ι i A * ι j B = ι j B * ι i A) : 4 * f ≤ localRank p G := by
  have : Fintype k := Fintype.ofFinite k
  have h := CFSG.RankThree.PartTwo.Census.Exceptional.sum_le_localRank_of_commuting_SL2 hp hp2
    (0 : Fin 4) (K := fun _ => k) (fun _ => f)
    (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hk) ι hι hc
  simpa [mul_comm] using h

theorem four_le_localRank_untwisted {T : Type} [Group T] [Finite T] {τ : Tag} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hm : UntwistedChevalleyModel T τ (p ^ f)) : 4 ≤ localRank p T := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have hchar : ringChar K ≠ 2 := by
    rw [CFSG.RankThree.Chevalley.ringChar_eq_of_card hp hf hK]
    exact hp2
  obtain ⟨ι, hι, hc⟩ :=
    CFSG.RankThree.Chevalley.higher_ordinary_exceptional_four_commuting_faithful_SL2 K hchar τ hτ
  have : Finite (adjointGroup τ K) := Finite.of_equiv T e.toEquiv
  have h := four_mul_le_localRank_of_SL2 hp hp2 hK ι hι hc
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
  omega

theorem four_le_localRank_twistedE6 {T : Type} [Group T] [Finite T] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : TwistedChevalleyModel T .E6 (p ^ f)) :
    4 ≤ localRank p T := by
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm
  have hK2 : Nat.card K = (p ^ f) ^ 2 := hcard
  have hchar : ringChar K ≠ 2 := by
    rw [CFSG.RankThree.Chevalley.ringChar_eq_of_card hp (by omega : 1 ≤ f * 2)
      (by rw [hK2, ← pow_mul])]
    exact hp2
  obtain ⟨ι, hι, hc⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_four_commuting_faithful_fixed_SL2 K hchar σ.toRingHom
  have hk : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = p ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hp hf hK2 (σ := σ.toRingHom) hσ
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv T e.toEquiv
  have h := four_mul_le_localRank_of_SL2 hp hp2 hk ι hι hc
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
  omega

theorem four_le_localRank_trialityD4 {T : Type} [Group T] [Finite T] {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hZ : Subgroup.center T = ⊥)
    (hm : TwistedChevalleyModel T .D4 (p ^ f)) : 4 ≤ localRank p T := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  have h := CFSG.RankThree.Chevalley.four_mul_le_localRank_of_triality hp (by omega) hf hK hσ
    ((Sec66T.centerQuotientEquivSelf hZ).trans e)
  omega

theorem two_mul_le_localRank_g2 {T : Type} [Group T] [Finite T] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : UntwistedChevalleyModel T .G2 (p ^ f)) :
    2 * f ≤ localRank p T := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have hchar : ringChar K ≠ 2 := by
    rw [CFSG.RankThree.Chevalley.ringChar_eq_of_card hp hf hK]
    exact hp2
  obtain ⟨ι₁, ι₂, h₁, h₂, hcomm⟩ := CFSG.RankThree.Chevalley.G2_two_commuting_faithful_SL2 K hchar
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv T e.toEquiv
  have : Fintype K := Fintype.ofFinite K
  have h := CFSG.RankThree.PartTwo.Census.Exceptional.sum_le_localRank_of_commuting_SL2 hp hp2
    (0 : Fin 2) (K := fun _ => K) (fun _ => f)
    (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hK) ![ι₁, ι₂]
    (fun i => by fin_cases i <;> assumption) (fun i j hij A B => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm A B
      · exact (hcomm B A).symm
      · exact absurd rfl hij)
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
  simpa [mul_comm] using h

theorem outerComp_g2 {T : Type} [Group T] [Finite T] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmod : ChevalleyExceptionalModel T .G2 p f) : OuterComp p T := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hmod.1.2.1
  intro hLR β hβp hβout _
  exfalso
  have h2 := two_mul_le_localRank_g2 hp (by omega) hf hmod.2
  have hlr : localRank p T ≤ 2 := by
    by_contra h
    exact false_of_three_le_localRank hp hLR (by omega)
  have hf1 : f = 1 := by omega
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ (innerAut T).one_mem)
  have hord : orderOf β = p := orderOf_eq_prime hβp hβ1
  exact hβout (g2_prime_order_automorphism_inner hp (by omega) hmod
    ⟨fun _ => hf1, fun h => by omega⟩ hp (by omega) β hord)

theorem outerComp_exceptional {T : Type} [Group T] [Finite T] {t : StatedLieTag} {p f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hZ : Subgroup.center T = ⊥)
    (hmod : ChevalleyExceptionalModel T t p f) : OuterComp p T := by
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨-, hm⟩ := id hmod
  cases t
  all_goals first
    | exact hm.elim
    | exact outerComp_g2 hp hp5 hmod
    | (refine outerComp_of_three_le_localRank hp ?_
       have := four_le_localRank_untwisted hp (by omega) hf (by simp) hm
       omega)
    | (refine outerComp_of_three_le_localRank hp ?_
       have := four_le_localRank_twistedE6 hp (by omega) hf hm
       omega)
    | (refine outerComp_of_three_le_localRank hp ?_
       have := four_le_localRank_trialityD4 hp hp5 hf hZ hm
       omega)

end CFSG.RankThree.PartOne.FOCD
