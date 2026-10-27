module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem crsl_three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * k + 1) = x at h ⊢
  omega

private theorem crsl_split_of_odd {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twB2 ∨ lab.tag = .twF4) : LargeEvenSplit 3 lab := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab ⊢
  rcases ht with rfl | rfl
  · exact Or.inr (Or.inl ⟨fun h => h, (fun h => nomatch h),
      crsl_three_dvd_two_pow_add_one hlab.2.2.1⟩)
  · exact Or.inr (Or.inl ⟨fun h => h, (fun h => nomatch h),
      crsl_three_dvd_two_pow_add_one hlab.2.2.1⟩)

private theorem crsl_split_of_one {lab : LargeEvenLabel} (h : lab.n = 1) : LargeEvenSplit 3 lab :=
  Or.inr (Or.inr (Or.inr ⟨h, rfl⟩))

private theorem crsl_n_eq_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .G2der ∨ lab.tag = .twF4der) : lab.n = 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab ⊢
  rcases ht with rfl | rfl
  · exact hlab.2.2
  · exact hlab.2.2

theorem ggCSR_twB2 {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twB2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 :=
  TableBExc.largeEvenLabelAll_card_lt_twB2 Nat.prime_three hlab ht
    (crsl_split_of_odd hlab (Or.inl ht))

theorem ggCSR_twF4
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 :=
  TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
    (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
    Nat.prime_three hlab ht (crsl_split_of_odd hlab (Or.inr ht))

theorem ggCSR_B2der {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .B2der) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 :=
  largeEvenLabelAll_card_lt_b2derThree (p := 3) (lab := lab) ⟨rfl, ht⟩

theorem ggCSR_G2der
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2der) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 :=
  TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der Nat.prime_three hlab ht
    (crsl_split_of_one (crsl_n_eq_one hlab (Or.inl ht)))

theorem ggCSR_twF4der
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4der) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 :=
  TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der TableBExcSmallRest.ggTitsThreeRankInput_holds
    Nat.prime_three hlab ht (crsl_split_of_one (crsl_n_eq_one hlab (Or.inr ht)))

section AllFixed


private theorem halfSplit_small_twisted_split {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (ht : lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der)
    (h : LargeEvenHalfSplit p lab c) : LargeEvenSplit p lab := by
  rcases h with h | h | h | h | h | h
  · exact h
  all_goals rcases ht with ht | ht | ht <;> simp_all

theorem ggAllFixedArithMarking_no_small_twisted (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hAll : GGInnerDiagAll p B Bs x L D J) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) :
    LargeEvenMarking ↥X fun lab R _ I F θ =>
      ¬ (lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der) ∧
      LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥) ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' : ↥X => (l' : G) = b⁻¹ * l * b) φ) ∧
        GGRawInnField p R I F ∧ IsElemAbelian p (ggBeta X θ hN).range ∧
        ((ggBeta X θ hN).range : Set (MulAut R)) ⊆ I ∧
        p ^ 3 ≤ Nat.card (ggBeta X θ hN).range := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hperf, lab, hlab, hdatum⟩ := ggAllFixedArithMarking hRig hraw hiso hcfg hAll hX
  have hnot : ¬ (lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der) := by
    intro ht
    obtain ⟨_, _, _, _, _, _, _, hHalf, _⟩ := largeEvenRawDatum_exists hdatum
    have hs : LargeEvenSplit p lab := halfSplit_small_twisted_split ht hHalf
    have hlt : LargeEvenLabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3 := by
      rcases ht with ht | ht | ht
      · exact TableBExc.largeEvenLabelAll_card_lt_twB2 hp hlab ht hs
      · by_cases hp3 : p = 3
        · subst p
          exact ggCSR_twF4 hlab ht
        · exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three hp3 hp hlab ht hs
      · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab ht hs
    obtain ⟨R, _, I, _, ⟨_, _, θ, hP⟩, hbound⟩ :=
      largeEvenRawDatum_exists (hlt _ hdatum)
    obtain ⟨_, hN, _, _, hE, hEI, hE3⟩ := hP
    exact (not_lt_of_ge hE3) (hbound (ggBeta X θ hN).range hEI hE)
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hdatum⟩
  rintro R _ I F ⟨hs, hna, θ, hP⟩
  exact ⟨hs, hna, θ, hnot, hP⟩

end AllFixed

end CFSG.StandardType

end
