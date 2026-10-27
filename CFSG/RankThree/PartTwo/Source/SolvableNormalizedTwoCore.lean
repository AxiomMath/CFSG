module

public import CFSG.RankThree.LocalRank.PartTwoCollections
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.NormalizedElementarySubgroup
import CFSG.RankThree.PartTwo.Source.PiecesContradiction
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Source

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank

variable {G : Type*} [Group G] [Finite G]

theorem card_inf_centralizer_le {r : ℕ} (hr : r.Prime) (hloc : localRank r G < 3)
    {Y S : Subgroup G} (hYe : IsElemAbelian r Y) (hYp : IsPGroup r Y) (hS : IsPGroup 2 S) {t : G}
    (htS : t ∈ S) (ht1 : t ≠ 1) :
    Nat.card (Y ⊓ Subgroup.centralizer {t} : Subgroup G) ≤ r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have hT : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :=
    ⟨Subgroup.zpowers t, Subgroup.zpowers_ne_bot.mpr ht1,
      hS.to_le (Subgroup.zpowers_le.mpr htS), rfl⟩
  obtain ⟨k, hk⟩ := (hYp.to_le (inf_le_left : Y ⊓ Subgroup.centralizer {t} ≤ Y)).exists_card_eq
  have hle : Y ⊓ Subgroup.centralizer {t} ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    refine inf_le_right.trans ?_
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hkr : k ≤ localRank r G :=
    (le_assembly_pRank hr hle (isElemAbelian_of_le hYe inf_le_left) hk).trans
      (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr _ hT)
  rw [hk]
  exact Nat.pow_le_pow_right hr.pos (by omega)

theorem le_aschCore_self {A : Subgroup G} (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) :
    A ≤ aschCore 2 3 A := by
  have h3 : 3 ≤ CFSG.Assembly.pRank 3 A :=
    le_assembly_pRank Nat.prime_three le_rfl hA (by rw [hA27]; norm_num)
  refine Subgroup.le_normalizer.trans (le_sSup ⟨A, le_rfl, by omega, ?_, rfl⟩)
  have hAC : A ⊓ Subgroup.centralizer (A : Set G) = A := by
    refine inf_of_le_left fun a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  rwa [hAC, sup_idem]

theorem pCoreOf_two_ne_bot_of_aschCore_le (hchar : IsCharTwoType G)
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) {A X : Subgroup G}
    (hA : A ∈ partTwoE G) (hX1 : X ≠ ⊥) (hXs : Group.IsSolvable X) (hX3 : ¬ 3 ∣ Nat.card X)
    (hΓ : aschCore 2 3 A ≤ Subgroup.normalizer (X : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  intro hO2
  obtain ⟨r, hr, hr5, Y, hY1, -, hYc, hYr, hYp, hΓY⟩ :=
    exists_elementary_normalized hX1 hXs hX3 hO2 hΓ
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hAe : IsElemAbelian 3 A := hA.1
  have hA27 : Nat.card A = 27 := hA.2.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := (le_aschCore_self hAe hA27).trans hΓY
  obtain ⟨S₀, hS₀2, hAS₀, hfaith₀⟩ := exists_faithful_twoSubgroup hchar hA
  obtain ⟨S, ⟨hSS₀, hAS, hfaith⟩, hmin⟩ := exists_minimal_subgroup
    (fun S : Subgroup G => S ≤ S₀ ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      A ⊓ Subgroup.centralizer (S : Set G) = ⊥) ⟨le_rfl, hAS₀, hfaith₀⟩
  have hS2 : IsPGroup 2 S := hS₀2.to_le hSS₀
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) :=
    (le_aschCore_of_le_normalizer hAe hA27 hS2 hAS).trans hΓY
  have hSfaith : S ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
    by_contra hne
    apply hY1
    refine eq_bot_of_twoSubgroup_le_centralizer hchar hAe hA27 hr2 hYp hΓY
      (hS2.to_le inf_le_left) hne ?_ inf_le_right
    exact (le_inf hAS fun a ha => mem_normalizer_centralizer (hAY ha)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hact : SmallFixedAction r Y S :=
    ⟨hYc, hYr, hSY, hSfaith, fun t ht ht1 =>
      card_inf_centralizer_le hr (hloc r hr (by omega)) ⟨hYc, hYr⟩ hYp hS2 ht ht1⟩
  obtain ⟨Xs, hXsA, -, -, hpiece, hcomm, hsup, hAN, hXc⟩ :=
    minimal_faithful_central_product (n := 3) hAe (by rw [hA27]; norm_num) hS2 hAS hfaith
      fun T' hT' hAT' hfT' => hmin T' hT' ⟨hT'.trans hSS₀, hAT', hfT'⟩
  have hgen : ∀ i, ∃ x ∈ Xs i, x ≠ 1 := by
    intro i
    have hne : Xs i ≠ ⊥ := by
      intro h
      have h3 := (hXsA i).2
      rw [h, Subgroup.card_bot] at h3
      omega
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  choose x hxX hx1 using hgen
  have hx3 : ∀ i, x i ^ 3 = 1 := by
    intro i
    have h := pow_card_eq_one' (G := Xs i) (x := ⟨x i, hxX i⟩)
    rw [(hXsA i).2] at h
    exact congrArg Subtype.val h
  have hPS : ∀ i, ⁅Xs i, S⁆ ≤ S := fun i =>
    (le_iSup (fun j => (⁅Xs j, S⁆ : Subgroup G)) i).trans hsup.le
  have hxP : ∀ i j, i ≠ j → x i ∈ Subgroup.centralizer ((⁅Xs j, S⁆ : Subgroup G) : Set G) :=
    fun i j hij => hXc i j hij (hxX i)
  have hxC : ∀ i, x i ∉ Subgroup.centralizer ((⁅Xs i, S⁆ : Subgroup G) : Set G) := by
    intro i hxi
    apply hx1 i
    have hall : ∀ j, x i ∈ Subgroup.centralizer ((⁅Xs j, S⁆ : Subgroup G) : Set G) := by
      intro j
      by_cases hij : i = j
      · subst hij
        exact hxi
      · exact hxP i j hij
    have hSx : S ≤ Subgroup.centralizer {x i} := by
      rw [← hsup]
      refine iSup_le fun j p hp => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hall j) p hp)
    have hmem : x i ∈ A ⊓ Subgroup.centralizer (S : Set G) :=
      Subgroup.mem_inf.mpr ⟨(hXsA i).1 (hxX i), Subgroup.mem_centralizer_iff.mpr fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.mp (hSx hs)⟩
    rw [hfaith] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact SmallFixedAction.false_of_pieces hr2 hact (fun i => ⁅Xs i, S⁆) hPS hpiece
    (fun i j hij => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i j hij)) x hx3
    (fun i => hAN i ((hXsA i).1 (hxX i))) hxC hxP

theorem rank3II_6_2 (hchar : IsCharTwoType G)
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) {A X : Subgroup G}
    (hA : A ∈ partTwoE G) (hX1 : X ≠ ⊥) (hXs : Group.IsSolvable X) (hX3 : ¬ 3 ∣ Nat.card X)
    (hΓ : aschCore 2 3 A ≤ Subgroup.normalizer (X : Set G)) :
    pCoreOf 2 X ≠ ⊥ ∧ A ∈ partTwoT G := by
  have hO2 := pCoreOf_two_ne_bot_of_aschCore_le hchar hloc hA hX1 hXs hX3 hΓ
  exact ⟨hO2, hA, Subgroup.normalizer (pCoreOf 2 X : Set G),
    ⟨_, hO2, isPGroup_pCoreOf_two X, rfl⟩,
    hΓ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)⟩

end CFSG.RankThree.PartTwo.Source
