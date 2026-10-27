module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4TwoPow
public import CFSG.LocalAnalysis.UniqueFourCatalog.TwistedOddInputs
public import CFSG.LieType.HighestRoot.CentTriality
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.ClassicalInvolution.Orders.Twisted
import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.LieType.HighestRoot
open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open scoped MatrixGroups

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section TrialityD4Odd

private theorem td4Odd_rankOne_eq_range {I : Type*} [DecidableEq I] {G : Type*} {F : Type}
    [Group G] [Field F] {X : (I → ℤ) → Subgroup G} {i : I}
    (φ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (hu : ∀ c, φ (sl2Upper c) ∈ X (Pi.single i 1))
    (hl : ∀ c, φ (sl2Lower c) ∈ X (-Pi.single i 1))
    (hpu : ∀ g ∈ X (Pi.single i 1), ∃ c, φ (sl2Upper c) = g)
    (hpl : ∀ g ∈ X (-Pi.single i 1), ∃ c, φ (sl2Lower c) = g) :
    rankOne X i = φ.range := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := hpu g hg
    exact ⟨_, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := hpl g hg
    exact ⟨_, rfl⟩
  · rintro _ ⟨s, rfl⟩
    have hcl : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (rankOne X i).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact Subgroup.mem_sup_left (hu c)
      · exact Subgroup.mem_sup_right (hl c)
    exact hcl (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s)

private def td4OddNegOne (F : Type) [Field F] : SL(2, F) :=
  ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩

private theorem td4OddNegOne_comm {F : Type} [Field F] (s : SL(2, F)) :
    s * td4OddNegOne F = td4OddNegOne F * s := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [td4OddNegOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem td4OddNegOne_mul_self {F : Type} [Field F] :
    td4OddNegOne F * td4OddNegOne F = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [td4OddNegOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem td4OddNegOne_ne_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    td4OddNegOne F ≠ 1 := by
  intro h
  have := congrArg (fun s : SL(2, F) => (s : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [td4OddNegOne] at this
  exact h2 (by linear_combination -this)

variable {K : Type} [Field K] {σ : K →+* K}

theorem card_fixedField_of_card_cube [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (fixedField σ) = p ^ f := by
  let a : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.D4) hp hf hK hσq a
  have h1 : (TwistTag.D4.orbit a).card = 1 := by decide
  have e : orbitField TwistTag.D4 K σ a = fixedField σ := by
    unfold orbitField
    rw [h1, pow_one]
  rw [e, h1, pow_one] at h
  exact h

set_option linter.unusedSectionVars false


theorem rankOne_long_eq_range (hσ : ∀ c, σ (σ (σ c)) = c) :
    rankOne (twistedRootGroup σ) (ng 0) = (slLong σ hσ).range := by
  have hu : ∀ c, slLong σ hσ (sl2Upper c) ∈ twistedRootGroup σ (Pi.single (ng 0) 1) :=
    fun c => by
      show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
      rw [Subgroup.mem_subgroupOf, slLong_val, slLongE_upper]
      exact xPar_single_two_mem_twisted hσ c.2
  have hl : ∀ c, slLong σ hσ (sl2Lower c) ∈ twistedRootGroup σ (-Pi.single (ng 0) 1) :=
    fun c => by
      show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
      rw [Subgroup.mem_subgroupOf, slLong_val, slLongE_lower]
      exact xPar_neg_single_two_mem_twisted hσ c.2
  refine td4Odd_rankOne_eq_range (slLong σ hσ) hu hl ?_ ?_
  · intro g hg
    have hg' : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) :=
      Subgroup.mem_subgroupOf.1 hg
    obtain ⟨c, hc, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
      proj_single_two rho_single_two _).1 hg'
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    rw [slLong_val, slLongE_upper, hgc]
  · intro g hg
    have hg' : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (-Pi.single (ng 0) 1) :=
      Subgroup.mem_subgroupOf.1 hg
    obtain ⟨c, hc, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
      (isRoot_neg_single d4 (nd 2)) proj_neg_single_two rho_neg_single_two _).1 hg'
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    rw [slLong_val, slLongE_lower, hgc]

theorem not_isCharTwoType_twistedGroup_odd [Finite K] [Finite (twistedGroup σ)] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 4 ≤ p ^ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (p ^ f)) :
    ¬ IsCharTwoType (twistedGroup σ) := by
  have hq2 : 2 ≤ p ^ f := by omega
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hK hσq
  have hF : Nat.card (fixedField σ) = p ^ f := card_fixedField_of_card_cube hp hf hK hσq
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := p) (f := f * 3) (by rw [hK, pow_mul])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hgF : ∀ g : twistedGroup σ, td4Incl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ := fun g => by
    rw [← CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
      hK2 hq2 hK hσq]
    exact Subgroup.mem_map_of_mem _ g.2
  have h2F : (2 : fixedField σ) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card (fixedField σ) (hF ▸ hodd)
  set J : Subgroup (twistedGroup σ) := (slLong σ hσ).range with hJ
  let eJ : J ≃* SL(2, fixedField σ) := (MonoidHom.ofInjective (slLong_injective hσ)).symm
  set z : twistedGroup σ := slLong σ hσ (td4OddNegOne (fixedField σ)) with hz
  have hzJ : z ∈ J := ⟨_, rfl⟩
  have hz1 : z ≠ 1 := fun h =>
    td4OddNegOne_ne_one h2F (slLong_injective hσ (h.trans (map_one _).symm))
  have hz2 : z * z = 1 := by
    rw [hz, ← map_mul, td4OddNegOne_mul_self, map_one]
  have hord : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two, hz2]) hz1
  have hzr : z ∈ rankOne (twistedRootGroup σ) (ng 0) := by
    rw [rankOne_long_eq_range hσ]
    exact hzJ
  have hCN : Subgroup.centralizer ({z} : Set (twistedGroup σ)) ≤
      Subgroup.normalizer (J : Set (twistedGroup σ)) := by
    have := centralizer_le_normalizer_td4 hK2 hσ hgF hzr hord
    rwa [rankOne_long_eq_range hσ] at this
  have hJC : J ≤ Subgroup.centralizer ({z} : Set (twistedGroup σ)) := by
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hz, ← map_mul, ← map_mul, td4OddNegOne_comm]
  have h4 : 4 ≤ Nat.card (fixedField σ) := hF ▸ hq
  have hnot :=
    CFSG.RankThree.PartTwo.Census.Carrier.not_isCharTwoType_of_involution_centralizer_component
    (M := twistedGroup σ) (C := (⊤ : Subgroup (twistedGroup σ))) (d := z) (Subgroup.mem_top z)
    hz1 hz2 (S := J) (Q₁ := J) (Q₂ := ⊥) (sup_bot_eq J).symm (le_inf le_top hJC)
    (fun g hg => hCN hg.2) bot_le (F := fixedField σ) h4 (hF ▸ hodd) eJ
  exact fun h => hnot (CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv
    (Subgroup.topEquiv (G := twistedGroup σ)).symm h)

theorem nonempty_derivedCentralQuotient_equiv_twistedGroup [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    Nonempty (DerivedCentralQuotient (twistedFixedGroup .D4 K σ) ≃* twistedGroup σ) := by
  let eD := twistedGroupEquivDerived σ hq hK hσq
  have hZ := CFSG.SectionRank.center_eq_bot_of_mulEquiv' eD
    (CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card hq hK hσq)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eD.symm)⟩

theorem false_of_trialityD4_odd {G : Type} [Group G] [Finite G] (hS : Standing4 G) {p f : ℕ}
    (hp2 : p ≠ 2) (h : ChevalleyExceptionalModel G .trialityD4 p f) : False := by
  obtain ⟨⟨hpp, hf, -⟩, hm⟩ := h
  obtain ⟨K, hKF, hKfin, hK, σ, hσ, ⟨e⟩⟩ := hm
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  have hp3 : 3 ≤ p ^ f := by
    have h2 : 2 ≤ p := hpp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hq2 : 2 ≤ p ^ f := by omega
  by_cases hq3 : p ^ f = 3
  · have hcard : Nat.card G = CFSG.Open.ordTrialityD4 (p ^ f) :=
      CFSG.ClassicalInvolution.card_of_twistedChevalleyModel_D4_of_ne_two hpp hp2 hf
        ⟨K, hKF, hKfin, hK, σ, hσ, ⟨e⟩⟩
    have h256 := hS.two_pow_eight_dvd_card
    rw [hcard, hq3] at h256
    exact absurd h256 (by unfold CFSG.Open.ordTrialityD4; norm_num)
  · haveI : Finite K := hKfin
    obtain ⟨eS⟩ := nonempty_derivedCentralQuotient_equiv_twistedGroup hq2 hK3 hσ
    let e' : G ≃* twistedGroup σ := e.trans eS
    haveI : Finite (twistedGroup σ) := Finite.of_equiv G e'.toEquiv
    exact hS.false_of_not_isCharTwoType e'
      (not_isCharTwoType_twistedGroup_odd hpp hp2 hf (by omega) hK3 hσ)

theorem trialityD4OddExclusion : TrialityD4OddExclusion :=
  fun _ _ _ hS _ _ hp2 h => false_of_trialityD4_odd hS hp2 h

end TrialityD4Odd

end CFSG.LocalAnalysis.UniqueFourCatalog
