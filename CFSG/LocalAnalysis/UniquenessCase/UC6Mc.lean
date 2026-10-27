module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC6S17
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.LocalAnalysis.UniquenessCase.UC6P16Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

structure Mc614 (G : Type) [Group G] [Finite G] where
  hS : Standing4 G
  hU : uniqueFourUnique G
  S : Setup4 G
  hC : TheoremCAt S.M
  hσ1 : uniqueFourSigma S.M ⊆ SigmaOne4 G
  r : ℕ
  R : Subgroup G
  E : Subgroup G
  d : Data614 S.M r R E
  hrσ : r ∉ uniqueFourSigma S.M
  hns : ¬ IsStronglyPEmbedded r S.M

namespace Mc614

variable {G : Type} [Group G] [Finite G] (c : Mc614 G)

abbrev M : Subgroup G := c.S.M

theorem M_ne_top : c.M ≠ ⊤ := by
  haveI := c.hS.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top c.hS.nonab c.S.maxLocal.1

theorem R_le_M : c.R ≤ c.M := c.d.sylow.le

theorem E_le_R : c.E ≤ c.R := fun _ hx => (c.d.E_le hx).1

theorem rank_le_three : Open.pRank c.r c.R ≤ 3 :=
  (CFSG.PreuniquenessRankFour.Helpers.pRank_mono c.r c.d.prime c.R_le_M).trans
    (pRank_le_three_of_not_mem_sigma c.hU c.S.maxLocal c.d.prime c.d.odd c.hrσ)

theorem exists_Z : ∃ Z : Subgroup G, Z ≤ c.R ∧ Nat.card Z = c.r ∧
    ¬ centralizer (Z : Set G) ≤ c.M :=
  exists_Z_of_not_isStronglyPEmbedded c.S.maxLocal c.M_ne_top c.hC c.d.prime c.d.odd c.d.sylow
    c.d.E_le c.d.E_el c.d.E_card c.d.E_gamma c.hns

structure IsZ (Z : Subgroup G) : Prop where
  le : Z ≤ c.R
  card : Nat.card Z = c.r
  not_le : ¬ centralizer (Z : Set G) ≤ c.M

variable {c}

theorem IsZ.not_normalizer_le {Z : Subgroup G} (hZ : c.IsZ Z) :
    ¬ normalizer (Z : Set G) ≤ c.M :=
  fun h => hZ.not_le ((Subgroup.centralizer_le_normalizer (Z : Set G)).trans h)

theorem IsZ.E_le_centralizer {Z : Subgroup G} (hZ : c.IsZ Z) :
    c.E ≤ centralizer (Z : Set G) := fun e he => by
  rw [mem_centralizer_iff]
  intro z hz
  exact (mem_centralizer_iff.1 (c.d.E_le he).2 z (hZ.le hz))

theorem IsZ.not_le_E {Z : Subgroup G} (hZ : c.IsZ Z) : ¬ Z ≤ c.E := by
  intro hZE
  have hZ1 : Z ≠ ⊥ := by
    intro h
    have : c.r = 1 := by rw [← hZ.card, h]; exact Subgroup.card_bot
    exact c.d.prime.ne_one this
  have hZp : IsPGroup c.r Z := (IsElemAbelian.isPGroup c.d.E_el).to_le hZE
  have hN : normalizer (Z : Set G) ≤ rankThreeGamma 1 c.r c.E :=
    CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 c.r c.E Z hZE
      (one_le_pRank_of_ne_bot c.d.prime hZp hZ1)
  exact hZ.not_normalizer_le (hN.trans c.d.E_gamma)

theorem IsZ.R_sylow {Z : Subgroup G} (_hZ : c.IsZ Z) (hRC : c.R ≤ centralizer (Z : Set G)) :
    IsSylowOf c.r c.R (centralizer (Z : Set G)) := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  have hRp : IsPGroup c.r c.R := c.d.sylow.isPGroup
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_ge hRC hRp
  have hE1 : c.E ≠ ⊥ := by
    intro h
    have : c.r ^ 2 = 1 := by rw [← c.d.E_card, h]; exact Subgroup.card_bot
    rcases pow_eq_one_iff.1 this with h1 | h1
    · exact c.d.prime.ne_one h1
    · exact two_ne_zero h1
  have hNR : normalizer (c.R : Set G) ≤ c.M :=
    c.d.normalizer_le_of_le_pGroup c.hC le_rfl hE1 c.E_le_R hRp
  by_cases hSR : c.R = S
  · rw [hSR]
    exact hS
  · exfalso
    have hlt : c.R < S := lt_of_le_of_ne hRS hSR
    have hN : c.R < S ⊓ normalizer (c.R : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer c.r
        c.d.prime S c.R hS.isPGroup hlt
    have hNM : S ⊓ normalizer (c.R : Set G) ≤ c.M := fun x hx => hNR hx.2
    have hNp : IsPGroup c.r (S ⊓ normalizer (c.R : Set G) : Subgroup G) :=
      hS.isPGroup.to_inf_left
    have := c.d.sylow.eq_of_le hN.le hNM hNp
    exact hN.ne this.symm

theorem IsZ.p16_hyp {Z : Subgroup G} (hZ : c.IsZ Z)
    (h69 : R6_9 (dataOfSetup4 c.hS c.hU c.S)) :
    ∀ P : Subgroup G, P ≤ c.R → Z ≤ P →
      (∀ z ∈ Z, ∀ p ∈ P, ∀ q ∈ P, (z * p * z⁻¹ * p⁻¹) * q = q * (z * p * z⁻¹ * p⁻¹)) →
      ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z := by
  intro P hPR hZP hZ2
  have hsub : (dataOfSetup4 c.hS c.hU c.S).sig ⊆ (dataOfSetup4 c.hS c.hU c.S).sig1 :=
    fun p hp => ⟨hp, c.hσ1 hp⟩
  have hEM : c.E ≤ c.M := fun x hx => c.R_le_M (c.E_le_R hx)
  have key := h69 hsub c.r c.d.prime c.d.odd c.E hEM c.d.E_el c.d.E_card c.d.E_gamma c.r Z
    c.d.prime (hZ.le.trans c.R_le_M) hZ.card
    (hZ.E_le_centralizer.trans (Subgroup.centralizer_le_normalizer (Z : Set G)))
    hZ.not_normalizer_le P (hPR.trans c.R_le_M) (c.d.sylow.isPGroup.to_le hPR) hZP
  have hZ2P : Z ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype := by
    intro z hz
    refine ⟨⟨z, hZP hz⟩, ?_, rfl⟩
    show (⟨z, hZP hz⟩ : ↥P) ∈ Subgroup.upperCentralSeries ↥P (1 + 1)
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro q
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa [commutatorElement_def] using (hZ2 z hz q q.2 g g.2).symm
  intro z hz p hp
  obtain ⟨z', hz', hz'z⟩ := key.2.2 hZ2P hz
  have := Subgroup.mem_center_iff.1 hz' ⟨p, hp⟩
  have h2 := congrArg Subtype.val this
  simp only [Subgroup.coe_mul] at h2
  rw [← hz'z]
  exact h2.symm

theorem IsZ.sixteen {Z : Subgroup G} (hZ : c.IsZ Z) (h69 : R6_9 (dataOfSetup4 c.hS c.hU c.S)) :
    (∀ a ∈ Z ⊔ c.E, ∀ x ∈ c.R, a * x = x * a) ∧ (∀ x ∈ c.R, x ^ c.r = 1 → x ∈ Z ⊔ c.E) :=
  p16_core c.d.prime c.d.sylow.isPGroup c.rank_le_three
    (fun e he x hx => (mem_centralizer_iff.1 (c.d.E_le he).2 x hx).symm) c.E_le_R c.d.E_el
    c.d.E_card hZ.le hZ.card hZ.not_le_E (hZ.p16_hyp h69)

theorem IsZ.R_le_centralizer {Z : Subgroup G} (hZ : c.IsZ Z)
    (h69 : R6_9 (dataOfSetup4 c.hS c.hU c.S)) : c.R ≤ centralizer (Z : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro z hz
  exact (hZ.sixteen h69).1 z (mem_sup_left hz) x hx

end Mc614

end CFSG.LocalAnalysis.UniquenessCase.UC6
