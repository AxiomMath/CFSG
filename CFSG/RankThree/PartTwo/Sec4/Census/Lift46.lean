module

public import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.Milestones.LC_GL_local_rank_bounds
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (localRank)

theorem isPGroup_center_of_theta_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (hθ : aschbacherSolvableCore 3 Q = ⊥) : IsPGroup 3 (Subgroup.center Q) := by
  have hr : ∀ r : ℕ, r.Prime → r ≠ 3 → ∀ y ∈ Subgroup.center Q, orderOf y = r → False := by
    intro r hr hr3 y hy hyr
    have hN : (Subgroup.zpowers y).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hy hn) g, mul_inv_cancel_right]
      exact hn⟩
    have hsol : Group.IsSolvable (Subgroup.zpowers y) := Group.isSolvable_of_comm fun a b => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
        exact (Commute.zpow_zpow_self y i j).eq)
    have hcard : ¬ 3 ∣ Nat.card (Subgroup.zpowers y) := by
      rw [Nat.card_zpowers, hyr]
      intro h
      exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h).symm
    have hle := (solvable_prime_complement_core_characterization (H := Q) Nat.prime_three).2.2.2.1
      _ hN hsol hcard
    rw [hθ, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    rw [hle, orderOf_one] at hyr
    exact hr.one_lt.ne hyr
  intro g
  obtain ⟨a, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  by_cases hm1 : m = 1
  · refine ⟨a, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hn, hm1, mul_one]
  · exfalso
    obtain ⟨r, hrp, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have hr3 : r ≠ 3 := fun h => hm3 (h ▸ hrm)
    have hrn : r ∣ orderOf g := hn ▸ Dvd.dvd.mul_left hrm _
    exact hr r hrp hr3 ((g ^ (orderOf g / r) : Subgroup.center Q) : Q) (g ^ (orderOf g / r)).2
      (by rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div (orderOf_pos g).ne' hrn])

theorem isPGroup_center_thetaQuotient (L : Type*) [Group L] [Finite L] :
    IsPGroup 3 (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) :=
  isPGroup_center_of_theta_eq_bot (theta_quotient_core_and_ranks (G := L)).1

theorem not_mem_of_center_eq_bot {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.center G) (hz3 : orderOf z = 3)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) : z ∉ L := by
  intro hzL
  set z' : L := ⟨z, hzL⟩
  have hc : ((z' : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext ((Subgroup.mem_center_iff.mp hz) y))
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  have hord : orderOf (⟨z', hc⟩ : aschbacherSolvableCore 3 L) = 3 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hz3
  exact three_not_dvd_card_aschbacherSolvableCore (hord ▸ orderOf_dvd_natCard _)

theorem exists_orderOf_eq_three_of_dvd {G : Type*} [Group G] [Finite G]
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) : ∃ z ∈ Subgroup.center G, orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem isElemAbelian_map_subtype {G : Type*} [Group G] {L : Subgroup G} {p : ℕ} {S : Subgroup L}
    (hS : CFSG.Assembly.IsElemAbelian p S) :
    CFSG.Assembly.IsElemAbelian p (S.map L.subtype) := CFSG.Open.IsElemAbelian.map hS _

theorem inf_zpowers_eq_bot_of_not_mem {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z : G}
    {p : ℕ} (hp : p.Prime) (hzp : orderOf z = p) (hzL : z ∉ L) :
    L ⊓ Subgroup.zpowers z = ⊥ := by
  have hcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzp]
  have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcard]; exact hp⟩
  rw [eq_bot_iff]
  intro x ⟨hxL, hxz⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (L.subgroupOf (Subgroup.zpowers z)) with h | h
  · have hx : (⟨x, hxz⟩ : Subgroup.zpowers z) ∈ L.subgroupOf (Subgroup.zpowers z) := hxL
    rw [h] at hx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hx))
  · exfalso
    have hz : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
        L.subgroupOf (Subgroup.zpowers z) := by
      rw [h]
      trivial
    exact hzL hz

theorem localRank_add_one_le_of_central {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (N : Subgroup L) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {z : G} (hz : z ∈ Subgroup.center G)
    (hz3 : orderOf z = 3) (hzL : z ∉ L) (hpos : 0 < localRank 3 (L ⧸ N)) :
    localRank 3 (L ⧸ N) + 1 ≤ localRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, ⟨U, hU0, hU2, rfl⟩, hHk⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3 Nat.prime_three (L ⧸ N)
      hpos
  obtain ⟨E, hEH, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt
    (Subgroup.normalizer (U : Set (L ⧸ N)))
  obtain ⟨S, hSE, hS, hScard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN hE
  set D : Subgroup L := U.comap (QuotientGroup.mk' N) with hDdef
  have hSD : S ≤ Subgroup.normalizer (D : Set L) := by
    intro s hs
    have hsE : (QuotientGroup.mk' N) s ∈ Subgroup.normalizer (U : Set (L ⧸ N)) := hEH (hSE hs)
    rw [Subgroup.mem_normalizer_iff] at hsE ⊢
    intro d
    change (QuotientGroup.mk' N) d ∈ U ↔ (QuotientGroup.mk' N) (s * d * s⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hsE _
  have hDcard : Nat.card D = Nat.card N * Nat.card U :=
    QuotientGroup.card_preimage_mk N (U : Set (L ⧸ N))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hU0 ((Subgroup.card_eq_one).mp hm)
  set S' : Subgroup G := S.map L.subtype
  set D' : Subgroup G := D.map L.subtype
  have hD'card : Nat.card D' = Nat.card N * 2 ^ m := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hDcard, hm]
  have hcop : Nat.Coprime 3 (Nat.card D') := by
    rw [hD'card]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
      (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card D' := by
    rw [hD'card]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hS' : CFSG.Assembly.IsElemAbelian 3 S' := isElemAbelian_map_subtype hS
  have hS'L : S' ≤ L := Subgroup.map_subtype_le _
  have hzc : z ∈ Subgroup.centralizer (S' : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => (Subgroup.mem_center_iff.mp hz) g
  have hdisj : S' ⊓ Subgroup.zpowers z = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hS'L).trans
      (inf_zpowers_eq_bot_of_not_mem Nat.prime_three hz3 hzL).le)
  obtain ⟨hWcard, hWc, hWe⟩ := card_sup_zpowers_of_disjoint hzc hS'.1 hS'.2 hz3 hdisj
  have hWD : S' ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (D' : Set G) := by
    refine sup_le ((Subgroup.map_mono hSD).trans (Subgroup.le_normalizer_map L.subtype)) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    rw [← (Subgroup.mem_center_iff.mp hz) h, mul_inv_cancel_right]
  have hk : Nat.card (S' ⊔ Subgroup.zpowers z : Subgroup G) =
      3 ^ (localRank 3 (L ⧸ N) + 1) := by
    rw [hWcard, Subgroup.card_map_of_injective L.subtype_injective, hScard, hEcard, pow_succ,
      hHk]
    rfl
  exact CFSG.RankThree.Classical2.le_localRank_of_normalizes Nat.prime_three hWD ⟨hWc, hWe⟩ hk
    hcop h2

theorem SectionFourHyp.localRank_three_le {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G) :
    localRank 3 G ≤ 3 :=
  ((CFSG.Milestones.lc_gl_local_rank_bounds G).1 3 Nat.prime_three (by norm_num)).2.trans
    hG.evenRank_le

theorem localRank_thetaQuotient_le_two {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    {L : Subgroup G} {z : G} (hz : z ∈ Subgroup.center G) (hz3 : orderOf z = 3) (hzL : z ∉ L) :
    localRank 3 (L ⧸ aschbacherSolvableCore 3 L) ≤ 2 := by
  by_contra h
  have h1 := localRank_add_one_le_of_central L (aschbacherSolvableCore 3 L)
    three_not_dvd_card_aschbacherSolvableCore hz hz3 hzL (by omega)
  have h3 := SectionFourHyp.localRank_three_le hG
  omega

theorem isSimpleGroup_of_center_eq_bot {X : Type*} [Group X] (hq : IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem exists_ne_of_isQuasisimple {X : Type*} [Group X] (hq : IsQuasisimple X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      refine ⟨a, b, fun h => hab ?_⟩
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem sectionFourHyp_thetaQuotient (h41 : Item4_1) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) :
    SectionFourHyp (L ⧸ aschbacherSolvableCore 3 L) :=
  sectionFourHyp_of_section h41 hG L _ hL.2.2

end CFSG.RankThree.PartTwo.Sec4.Census
