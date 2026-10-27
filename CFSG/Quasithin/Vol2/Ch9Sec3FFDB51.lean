module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Alg
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D

public section

namespace CFSG.Quasithin.H13.Ch9.FFD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Vol2.Ch10.SecB.C11AmS
open scoped commutatorElement IsMulCommutative

section Factor

theorem not_noOrderFour_of_isAlt7 {X : Type} [Group X] (h : IsAlt 7 X) :
    ¬ L246C127.NoOrderFour X := by
  obtain ⟨e⟩ := h
  intro hX
  exact L246C127.not_noOrderFour_alt (n := 7) (by norm_num) (hX.of_mulEquiv e.symm)

theorem noOrderFour_subgroup {X : Type} [Group X] (h : L246C127.NoOrderFour X) (H : Subgroup X) :
    L246C127.NoOrderFour ↥H := by
  intro g hg
  have h4 : (g : X) ^ 4 = 1 := by rw [← Subgroup.coe_pow, hg, Subgroup.coe_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h _ h4

theorem noOrderFour_of_surjective {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type}
    [Group X] (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) →* X) (hπ : Function.Surjective π) :
    L246C127.NoOrderFour X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : L246C127.NoOrderFour ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    L246C127.NoOrderFour.of_mulEquiv (specialLinearGroupEquivStatedSL 2 F).symm
      (L246C127.noOrderFour_sl2 F)
  intro x hx
  by_contra hx2
  obtain ⟨g, rfl⟩ := hπ x
  have ho : orderOf (π g) = 2 ^ 2 :=
    orderOf_eq_prime_pow (by rw [pow_one]; exact hx2)
      (by rw [show 2 ^ (1 + 1) = 4 by rfl]; exact hx)
  have hpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨k, hk⟩ : 4 ∣ orderOf g := by
    have := orderOf_map_dvd π g
    rw [ho] at this
    exact this
  have h4 : (g ^ k) ^ 4 = 1 := by rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  have h2 := hS _ h4
  have hdvd : orderOf g ∣ k * 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_mul, h2])
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

theorem not_five_dvd_card_sl3 {F : Type} [Field F] [Finite F] {m : ℕ} (hm : Odd m)
    (hF : Nat.card F = 2 ^ m) : ¬ 5 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := by
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, hF]
  set q : ℕ := 2 ^ m with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hq5 : q % 5 = 2 ∨ q % 5 = 3 := by
    obtain ⟨k, rfl⟩ := hm
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [hq, show 2 * (j + j) + 1 = 4 * j + 1 by ring, pow_succ, pow_mul, Nat.mul_mod,
        Nat.pow_mod]
      norm_num
    · right
      rw [hq, show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring, pow_add, pow_mul, Nat.mul_mod,
        Nat.pow_mod]
      norm_num
  intro h
  have h0 := (ZMod.natCast_eq_zero_iff _ 5).mpr h
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  push_cast [Nat.cast_sub h2, Nat.cast_sub h3] at h0
  rw [← ZMod.natCast_mod q 5] at h0
  rcases hq5 with h5 | h5 <;> rw [h5] at h0 <;> revert h0 <;> decide

theorem notB56Factor_of_isAlt7 {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}
    (hK : IsAlt 7 ↥K) : InternalSec.NotB56Factor K := by
  intro X hKX _ hX
  have hX4 : ¬ L246C127.NoOrderFour ↥X := fun h => not_noOrderFour_of_isAlt7 hK
    ((noOrderFour_subgroup h (K.subgroupOf X)).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKX).symm)
  have hcardK : Nat.card ↥K = 2520 := by
    obtain ⟨e⟩ := hK
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hfinK : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hcardK]; norm_num)
  have hdvd : 2520 ∣ Nat.card ↥X := by
    rw [← hcardK]
    exact Subgroup.card_dvd_of_le hKX
  have hXpos : Nat.card ↥X ≠ 0 → 2520 ≤ Nat.card ↥X := fun h => Nat.le_of_dvd (by omega) hdvd
  rcases hX with (⟨n, F, _, _, -, hF, he⟩ | he | ⟨m, F, _, _, -, hmo, hF, he⟩) | he | he |
      ⟨n, F, _, _, hF, π, hπ⟩
  · obtain ⟨e⟩ := he
    have := Fintype.ofFinite F
    have : CharP F 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    exact hX4 (noOrderFour_of_surjective e.symm.toMonoidHom e.symm.surjective)
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := he
    have h5 : 5 ∣ Nat.card ↥X := (by norm_num : 5 ∣ 2520).trans hdvd
    rw [Nat.card_congr e.toEquiv] at h5
    exact not_five_dvd_card_sl3 hmo hF h5
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three,
      Nat.card_zmod] at hdvd
    exact absurd hdvd (by decide)
  · have := Fintype.ofFinite F
    have : CharP F 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    exact hX4 (noOrderFour_of_surjective π hπ)

end Factor

section Offender

variable {G : Type} [Group G] [Finite G] {S L Y W K : Subgroup G} [IsMulCommutative ↥W]

theorem exists_offender_of_commutator (hWe : IsElemAbelian 2 W) (hred : IsTwoReducedIn Y W)
    (hSY : IsSylowTwoOf S Y) (hLY : L ≤ Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple ↥(autOn L W)) (hKL : K ≤ L)
    (hKJ : ¬ ⁅K, thompsonJ S⁆ ≤ Subgroup.centralizer (W : Set G)) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W := by
  have hTN : S ≤ Subgroup.normalizer (L : Set G) := hSY.1.trans hYL
  have hTW : S ≤ Subgroup.normalizer (W : Set G) := hSY.1.trans hred.2.1
  have hnorm : ∀ A : Subgroup G, A ≤ S →
      autOn A W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := InternalSec.autOn_normal_of (U := W) (hAT.trans hTN)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ⁅autOn L W, autOn A W⁆ = autOn L W
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ Subgroup.centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, Subgroup.commutator_bot_right] at hLA
      refine not_commute_of_isQuasisimple1527d hq fun a ha b hb => ?_
      rw [← hLA, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hSY hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian S A →
        autOn A W ≤ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) := by
      intro A hA
      rcases commutator_eq_or_eq_bot1527d hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S' : Subgroup G :=
      ((Subgroup.centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
        (Subgroup.normalizer (W : Set G)).subtype with hS'
    have hJS' : thompsonJ S ≤ S' := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ Subgroup.normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply hKJ
    rw [Subgroup.commutator_le]
    intro k hk j hj
    obtain ⟨g, hg, rfl⟩ := hJS' hj
    have hkN : k ∈ Subgroup.normalizer (W : Set G) := hred.2.1 (hLY (hKL hk))
    have hkA : conjAct W ⟨k, hkN⟩ ∈ autOn L W := Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hKL hk, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hg) _ hkA
    have h1 : conjAct W ⁅(⟨k, hkN⟩ : Subgroup.normalizer (W : Set G)), g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc
    exact A4.conjAct_eq_one_iff.mp h1

end Offender

section B51

variable {G : Type} [Group G] [Finite G]

theorem b51_alt7 (h51 : AsB51) (h56 : AsB56) {Y T K KY V : Subgroup G} [IsMulCommutative ↥V]
    (hSQ : SQTKGroup ↥Y)
    (hT : IsSylowTwoOf T Y) (hKKY : K ≤ KY) (hKYY : KY ≤ Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y V)
    (hA7 : IsAlt 7 ↥(autOn KY V)) (hJ : ¬ ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G)) :
    IsIntDirect (commV (autOn KY V)) (fixV (autOn KY V)) ⊤ ∧
      (AlternatingNatural (autOn KY V) (commV (autOn KY V)) ⊥ 7 ∨
        A7Four (autOn KY V) (commV (autOn KY V)) ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hKYN : KY ≤ Subgroup.normalizer (V : Set G) := hKYY.trans hred.2.1
  have hq : CFSG.IsQuasisimple ↥(autOn KY V) := K7.isQuasisimple_A7 (Or.inl hA7)
  have hcard : Nat.card ↥(autOn KY V) = 2520 := by
    obtain ⟨e⟩ := hA7
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hSKY : SQTKGroup ↥KY := K8.sqtkGroup_of_le hSQ hKYY
  have hSA : SQTKGroup ↥(autOn KY V) :=
    ⟨K8.stronglyQuasithin_of_card hcard,
      (hSKY.2.quotient (InternalSec.autOnHom hKYN).ker).of_mulEquiv
        (QuotientGroup.quotientKerEquivOfSurjective _
          (InternalSec.autOnHom_surjective hKYN)).symm⟩
  have hO2 : pCoreOf 2 (autOn Y V) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  obtain ⟨A, -, hA, hLA⟩ := exists_offender_of_commutator hVe hred hT hKYY hYKY hq hKKY hJ
  have hV2 : ∀ w ∈ V, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hVe.2 w hw
  obtain ⟨hB, -⟩ := InternalSec.b51Hyp_ffJ_autOn_of_b56_of_notFactor h56 hV2 hred.2.1 hKYY hYKY
    hSQ hO2 hq hSA hA hLA (notB56Factor_of_isAlt7 hA7)
  have hV2' : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  obtain ⟨hP1, hP2, -⟩ := h51 ↥V hV2' _ _ hB
  have hshape := K8.part1_shape hP1 (Or.inl hcard)
  have hdir := K8.part2_direct hP2 hcard
  have hZ0 : fixV (autOn KY V) ⊓ commV (autOn KY V) = ⊥ := by
    rw [inf_comm]
    exact hdir.2
  rw [hZ0] at hshape
  exact ⟨hdir, hshape⟩

end B51

end CFSG.Quasithin.H13.Ch9.FFD
