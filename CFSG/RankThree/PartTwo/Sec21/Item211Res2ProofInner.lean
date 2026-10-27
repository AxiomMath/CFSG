module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofLStar
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.Sec4.Item462ProofUL
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec11.Item119Used
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Blueprint

namespace Item211Res2Proof

section Basic

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hz', map_one])

theorem not_mem_of_center_eq_bot {L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hZ : Subgroup.center (lBar L) = ⊥) : c ∉ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcL
  set c' : L := ⟨c, hcL⟩ with hc'
  have hcZ : (c' : lBar L) ∈ Subgroup.center (lBar L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2))
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcZ
  have hord : orderOf (⟨c', hcZ⟩ : aschbacherSolvableCore 3 L) = 3 := by
    rw [Subgroup.orderOf_mk, hc', Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc3 hc1
  exact three_not_dvd_card_aschbacherSolvableCore (hord ▸ orderOf_dvd_natCard _)

omit [Finite G] in
theorem le_centralizer_of_mem {A : Subgroup G} {c : G} (hA : IsElemAbelian 3 A) (hcA : c ∈ A) :
    A ≤ Subgroup.centralizer ({c} : Set G) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨c, hcA⟩))

omit [Finite G] in
theorem three_dvd_card_center_centralizer {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    3 ∣ Nat.card (Subgroup.center (Subgroup.centralizer ({c} : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G)
  have hc'Z := Sec11.mk_mem_center_centralizer c
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'
  have hc'o : orderOf c' = 3 := by
    rw [hc', Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc3 hc1
  rw [← hc'o, show orderOf c' = orderOf (⟨c', hc'Z⟩ : Subgroup.center C) from
    (Subgroup.orderOf_mk c' hc'Z).symm]
  exact orderOf_dvd_natCard _

end Basic

section Sub

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_eq_of_not_inducesOuterTheta {A L : Subgroup G} {c : G}
    (hAF : A ∈ partTwoF G) (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G))
    (hZ : Subgroup.center (lBar L) = ⊥) {x : G} (hxA : x ∈ A)
    (hx : ¬ Sec4.InducesOuterTheta x L) :
    ∃ l ∈ L, ∃ w ∈ Subgroup.zpowers c, l * w = x := by
  have hAe : IsElemAbelian 3 A := hAF.1
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hAC : A ≤ C := le_centralizer_of_mem hAe hcA
  obtain ⟨L', hL', rfl⟩ := hLc
  set A' := A.subgroupOf C with hA'def
  have hmax : Maximal (fun B : Subgroup C => IsElemAbelian 3 B) A' :=
    Sec11.maximal_subgroupOf_of_le hAF.2.1 hAe hAC
  set c' : C := ⟨c, hAC hcA⟩ with hc'def
  have hc'Z : c' ∈ Subgroup.center C := Sec11.mk_mem_center_centralizer c
  have hAL' : A' ≤ Subgroup.normalizer (L' : Set C) := fun a ha =>
    (Sec13.coe_mem_normalizer_map_iff C).mp (hAL (Subgroup.mem_subgroupOf.mp ha))
  have hθ : ∀ w : C, w ∈ (aschbacherSolvableCore 3 L').map L'.subtype ↔
      (w : G) ∈ (aschbacherSolvableCore 3 (L'.map C.subtype)).map (L'.map C.subtype).subtype := by
    intro w
    have e1 := Sec11.inSubgroup_theta_map_subtype_sub L'
    change w ∈ inSubgroup (aschbacherSolvableCore 3) L' ↔
      (w : G) ∈ inSubgroup (aschbacherSolvableCore 3) (L'.map C.subtype)
    rw [e1]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := Subtype.ext hww'
      rw [← this]
      exact hw'
  have hsec : Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) =
      (Subgroup.zpowers c' : Set C) := by
    ext z
    have hz : z ∈ Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) ↔
        (z : G) ∈ Late.sectionCentralizer A (L'.map C.subtype)
          ((aschbacherSolvableCore 3 (L'.map C.subtype)).map (L'.map C.subtype).subtype) := by
      constructor
      · rintro ⟨hzA, hzL⟩
        refine ⟨Subgroup.mem_subgroupOf.mp hzA, fun y hy => ?_⟩
        obtain ⟨y', hy', rfl⟩ := hy
        have := (hθ _).mp (hzL y' hy')
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact this
      · rintro ⟨hzA, hzY⟩
        refine ⟨Subgroup.mem_subgroupOf.mpr hzA, fun y hy => (hθ _).mpr ?_⟩
        have := hzY (y : G) ⟨y, hy, rfl⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact this
    rw [hz, hsc, SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [hc'def] using hk)⟩
    · intro h1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [hc'def]⟩
  have hinf : A' ⊓ Sec4.thetaQuotCentralizer L' = Subgroup.zpowers c' := by
    have h1 := Sec13.sectionCentralizer_eq_inf hAL'
    rw [hsec] at h1
    exact (SetLike.coe_injective h1).symm
  have hCA' : ∀ y ∈ A', y ∈ Sec4.thetaQuotCentralizer L' ↔ y ∈ Subgroup.zpowers c' := by
    intro y hy
    rw [← hinf]
    exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
  have hZ' : Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') = ⊥ :=
    center_eq_bot_of_mulEquiv (Sec13.thetaQuotEquivSub C L') hZ
  set x' : C := ⟨x, hAC hxA⟩ with hx'def
  have hx' : ¬ Sec4.InducesOuterTheta x' L' := fun h =>
    hx ((Sec8.Item82OneProof.inducesOuterTheta_sub_iff C L' x').mp h)
  have hmem := Sec4.Item462Proof.mem_sup_zpowers_of_not_inducesOuterTheta hmax hL' hAL' hCA' hZ'
    (Subgroup.mem_subgroupOf.mpr hxA : x' ∈ A') hx'
  have : (Subgroup.zpowers c').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc'Z)
  obtain ⟨l, hl, w, hw, hlw⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  refine ⟨l, ⟨l, hl, rfl⟩, w, ?_, congrArg Subtype.val hlw⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [hc'def]⟩

theorem false_of_projSU_four
    (hin : Sec4.Inputs47NoD4) (hG : TheoremFourHyp G) {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {L : Subgroup G} (hLc : L ∈ thetaComponentsAt 3 c) {n : ℕ} (hn : 1 ≤ n)
    (e : lBar L ≃* projSU 4 2 n) {x : G} (hxc : x ∈ Subgroup.centralizer ({c} : Set G))
    (hx3 : x ^ 3 = 1) (hout : Sec4.InducesOuterTheta x L) : False := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  obtain ⟨L', hL', rfl⟩ := hLc
  have hC4 : SectionFourHyp C := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hc1)
  have h3 := three_dvd_card_center_centralizer hc3 hc1
  set x' : C := ⟨x, hxc⟩ with hx'def
  have hx3' : x' ^ 3 = 1 := Subtype.ext (by simpa [hx'def] using hx3)
  have hout' : Sec4.InducesOuterTheta x' L' :=
    (Sec8.Item82OneProof.inducesOuterTheta_sub_iff C L' x').mpr hout
  exact Sec4.false_of_projSU_four_even hin hC4 h3 hL'.2.2 hn
    ((Sec13.thetaQuotEquivSub C L').trans e) hx3' hout'

end Sub

section Cases


variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_and_inner (hin : Sec4.Inputs47NoD4) (hG : TheoremFourHyp G)
    {A L : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hLc : L ∈ thetaComponentsAt 3 c) (hAe : IsElemAbelian 3 A)
    (hAC : A ≤ Subgroup.centralizer ({c} : Set G)) (hq : IsQuasisimple (lBar L))
    (hnf : ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field) (hcase : Case2130 A L) :
    Subgroup.center (lBar L) = ⊥ ∧ ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcase with ⟨he, -⟩ | ⟨he | he, -⟩ |
      ⟨⟨n, hn0, hnev, he | he⟩ | he, -⟩ | ⟨⟨n, hn1, -, he⟩, -⟩ <;> obtain ⟨e⟩ := he
  ·
    refine ⟨center_eq_bot_of_mulEquiv e
      (hin.centerSporadic .M22 (by simp [Sec4.sporadicCovers46])), fun x hx hout => ?_⟩
    exact Sec4.false_of_cubeInner e (Sec4.cubeInner_of_not_three_dvd_card_outer
      (hin.outSporadic .M22 (Or.inl (by simp [Sec4.sporadics46])))) (hAe.2 x hx) hout
  ·
    have := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e, fun x hx hout => ?_⟩
    exact Sec4.false_of_cubeInner e (Sec4.cubeInner_of_not_three_dvd_card_outer
      (hin.outSporadic .M23 (Or.inl (by simp [Sec4.sporadics46])))) (hAe.2 x hx) hout
  ·
    have e' : lBar L ≃* NativeSporadic.Carrier .HS := e
    have hs : IsSimpleGroup (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
    have hcard : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
    refine ⟨center_eq_bot_of_mulEquiv e' (Sec4.center_eq_bot_of_isSimpleGroup_of_not_prime
      (by rw [hcard]; norm_num)), fun x hx hout => ?_⟩
    exact Sec4.false_of_cubeInner e' (Sec4.cubeInner_of_not_three_dvd_card_outer
      (hin.outSporadic .HS (Or.inl (by simp [Sec4.sporadics46])))) (hAe.2 x hx) hout
  ·
    have hK : Nat.card (GaloisField 2 n) = 2 ^ n := Sec4.card_galoisField 2 n hn0
    have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [hK]
      obtain ⟨k, rfl⟩ := hnev
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 n))) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp _ 2 (by norm_num)
        (Or.inl (Or.inr h4))
    set E := e.trans (Sec4.projSpEquivStatedProj 2 (GaloisField 2 n)) with hE
    refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq E, fun x hx hout => ?_⟩
    rcases KFacts.inducesKindPSp4Even_diagonal_or_field L (hAe.2 x hx) hout E with hd | hf
    · exact Sec4.false_of_inducesKind_diagonal Sec4.psp4Even_inndiag_cube hd (hAe.2 x hx)
    · exact hnf x hx (KFacts.InducesStdKind.psp4even (GaloisField 2 n) ⟨E, hf⟩)
  ·
    have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU (by norm_num) hn0
    refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e, fun x hx hout => ?_⟩
    exact false_of_projSU_four hin hG hc3 hc1 hLc hn0 e (hAC hx) (hAe.2 x hx) hout
  ·
    have : IsSimpleGroup (projSU 5 2 2) := isSimpleGroup_projSU (by norm_num) (by norm_num)
    refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e, fun x hx hout => ?_⟩
    exact Sec4.false_of_cubeInner e (Sec4.cubeInner_of_not_three_dvd_card_outer
      Sec4.outU54_holds) (hAe.2 x hx) hout
  ·
    have hn : 1 ≤ n := hn1.le
    have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU (by norm_num) hn
    refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e, fun x hx hout => ?_⟩
    exact false_of_projSU_four hin hG hc3 hc1 hLc hn e (hAC hx) (hAe.2 x hx) hout

end Cases

end Item211Res2Proof

open Item211Res2Proof

section Certs


theorem item2130LStarInner_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hin : Sec4.Inputs47NoD4) : Item2130LStarInner := by
  intro G _ _ A E U c L hpair hnf hcase
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAF : A ∈ partTwoF G := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hG := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L hLc
  have hq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_mem hAe hcA
  obtain ⟨hZ, hinner⟩ := center_eq_bot_and_inner hin hG hc3 hc1 hLc hAe hAC hq
    (fun x hx => (hnf x hx).1) hcase
  have hcL : c ∉ L := not_mem_of_center_eq_bot hLC hc3 hc1 hZ
  refine ⟨hcL, ?_⟩
  have hsup : A ≤ (A ⊓ L) ⊔ Subgroup.zpowers c := by
    intro x hx
    obtain ⟨l, hl, w, hw, hlw⟩ :=
      exists_mul_eq_of_not_inducesOuterTheta hAF hcA hLc hAL hsc hZ hx (hinner x hx)
    have hwA : w ∈ A := Subgroup.zpowers_le.mpr hcA hw
    have hlA : l ∈ A := by
      have h1 := A.mul_mem hx (A.inv_mem hwA)
      rwa [← hlw, mul_inv_cancel_right] at h1
    rw [← hlw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlA, hl⟩) (Subgroup.mem_sup_right hw)
  have heq : (A ⊓ L) ⊔ Subgroup.zpowers c = A :=
    le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr hcA)) hsup
  have hcard := Sec4.card_sup_zpowers_of_not_mem (E := A ⊓ L) hc3
    (fun a ha => congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha.1⟩ ⟨c, hcA⟩))
    (fun h => hcL h.2)
  rw [heq] at hcard
  rw [hcard, mul_comm]

end Certs

end CFSG.RankThree.PartTwo.Sec21
