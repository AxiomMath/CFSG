module

public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGOneFiveRank
import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOmega
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Alt
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.Quasithin.Background.A1cA132Action
import CFSG.Quasithin.Background.A1cA133Three
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152He4Core
import CFSG.Quasithin.EmptyFaithful.S153Baum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley TableB

theorem exists_transvection_of_SC_small {R : Type} [Group R] [Finite R] {p : ℕ} (hp : p.Prime)
    {A : Subgroup R} (hA : IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A)
    {E : Subgroup R} (hE : IsElemAbelian p E) (hle : Nat.card E ≤ p ^ 2)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set R), g ^ p = 1 → g ∈ E) :
    ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection p φ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer (E : Set R) with hC
  have hEC : E ≤ C := fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  set S : Set (Subgroup R) := {Q | Q ≤ C ∧ IsPGroup p Q ∧ E ≤ Q} with hS
  obtain ⟨Q, -, hQmax⟩ := (Set.toFinite S).exists_le_maximal
    (show E ∈ S from ⟨hEC, hE.isPGroup, le_rfl⟩)
  obtain ⟨hQC, hQp, hEQ⟩ := hQmax.prop
  have hNE : ∀ n ∈ Subgroup.normalizer (Q : Set R), n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hxQ : n * x * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hn x).1 (hEQ hx)
      refine hSC _ (hQC hxQ) ?_
      rw [conj_pow, hE.2 x hx, mul_one, mul_inv_cancel]
    · have hxQ : x ∈ Q := (Subgroup.mem_normalizer_iff.1 hn x).2 (hEQ hx)
      refine hSC _ (hQC hxQ) ?_
      have h1 := hE.2 _ hx
      rwa [conj_pow, conj_eq_one_iff] at h1
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  by_cases hQP' : Q = P
  ·
    exfalso
    obtain ⟨g, hg⟩ := GGL48.exists_conj_mem_of_isPGroup hA.isPGroup P
    have hmap : A.map (MulAut.conj g).toMonoidHom ≤ E := by
      rintro _ ⟨a, ha, rfl⟩
      have hgQ : g * a * g⁻¹ ∈ Q := hQP' ▸ hg a ha
      refine hSC _ (hQC hgQ) ?_
      change (g * a * g⁻¹) ^ p = 1
      rw [conj_pow, hA.2 a ha, mul_one, mul_inv_cancel]
    have h1 : Nat.card A ≤ Nat.card E := by
      rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective]
      exact Subgroup.card_le_of_le hmap
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  · have hlt : Q < P := lt_of_le_of_ne hQP hQP'
    obtain ⟨n, hnP, hnN, hnQ⟩ := exists_mem_normalizer_not_mem P.isPGroup' hlt
    have hnE := hNE n hnN
    have hnC : n ∉ C := by
      intro hnC
      have hmem : Q ⊔ Subgroup.zpowers n ∈ S :=
        ⟨sup_le hQC (Subgroup.zpowers_le.2 hnC),
          P.isPGroup'.to_le (sup_le hQP (Subgroup.zpowers_le.2 hnP)), hEQ.trans le_sup_left⟩
      exact hnQ (hQmax.2 hmem le_sup_left
        (le_sup_right (a := Q) (Subgroup.mem_zpowers n)))
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    have hnk : n ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, OneMemClass.coe_one] at this
    obtain ⟨B, hBE, hcard, hnB⟩ : ∃ B : Subgroup R, B ≤ E ∧ Nat.card E ≤ p * Nat.card B ∧
        n ∈ Subgroup.centralizer (B : Set R) := by
      by_cases hEp : Nat.card E ≤ p
      · refine ⟨⊥, bot_le, by rw [Subgroup.card_bot, mul_one]; exact hEp, ?_⟩
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [show h = 1 from Subgroup.mem_bot.1 hh, one_mul, mul_one]
      · have hE1 : E ≠ ⊥ := by
          intro h
          rw [h, Subgroup.card_bot] at hEp
          exact hEp hp.one_lt.le
        obtain ⟨z, hz, hz1, hzc⟩ := CFSG.Quasithin.S15223.exists_centralized_ne_one
          (P.isPGroup'.to_le (Subgroup.zpowers_le.2 hnP)) hE.isPGroup
          (Subgroup.zpowers_le.2 hnE) hE1
        have hzn : Commute z n := (hzc n (Subgroup.mem_zpowers n)).symm
        refine ⟨Subgroup.zpowers z, Subgroup.zpowers_le.2 hz, ?_, ?_⟩
        · rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 z hz) hz1, ← sq]
          exact hle
        · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
          exact (hzn.zpow_left j).eq
    rcases mem_centralizer_or_ggIsTransvection hp hBE hE hcard hnE hnB hnk with h | h
    · exact absurd h hnC
    · exact ⟨ggConjAut E hnE, ggConjAut_mem_ggInduced (Subgroup.mem_top n) hnE, h⟩

theorem ggF4ThreeSCTransvInput_of_cube
    (hb : GGF4ThreeSCCubeInput) : GGF4ThreeSCTransvInput := by
  intro K _ _ _ hq E hE hle hSC
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h9 : Nat.card E ≤ 3 ^ 2
  · have hd : 3 ∣ Nat.card K ^ 2 - 1 := by
      have h := Nat.sq_sub_sq (Nat.card K) 1
      rw [one_pow] at h
      rw [h]
      exact Dvd.dvd.mul_right hq _
    obtain ⟨A, hA, hA3⟩ :=
      ExcFieldAutCentRankF4.exists_elemAbelian_pow_three_le Nat.prime_three (by norm_num) hd
    exact exists_transvection_of_SC_small Nat.prime_three hA hA3 hE h9 hSC
  · haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hE.isPGroup
    have hk3 : k = 3 := by
      rw [hk] at hle h9
      have h1 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
      have h2 : ¬ k ≤ 2 := fun h => h9 (Nat.pow_le_pow_right (by norm_num) h)
      omega
    exact hb K hq E hE (hk.trans (by rw [hk3])) hSC

theorem ggF4ThreeNbrRankInput_of_cube
    (hb : GGF4ThreeSCCubeInput) : GGF4ThreeNbrRankInput :=
  ggF4ThreeNbrRankInput_of_KG1 (ggF4ThreeSCTransvInput_of_cube hb)

theorem ggRow_absurd_F4Three_of_cube
    (hb : GGF4ThreeSCCubeInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G}
    (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) (hrow : GGF4ThreeMarking Bs K) : False :=
  ggRow_absurd_F4Three_of_KG1 (ggF4ThreeSCTransvInput_of_cube hb) hcfg hpres hle3 hle hrow

end CFSG.StandardType
