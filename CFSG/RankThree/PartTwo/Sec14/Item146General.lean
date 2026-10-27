module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.Milestones.CL_LIT_signalizer_functor_theorem
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
  CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS

section Helpers

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem isKGroupCat_of_ne_top_of_kProper (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) {X : Subgroup G} (hX : X ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat X :=
  ((KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hK X hX).mono_of_finite
    hbridge).kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple

theorem exists_eq_zpowers_of_mem_signalizerFunctorEk {S : Subgroup G}
    (hS : S ∈ CFSG.Open.signalizerFunctorEk 3 1 A) :
    ∃ b ∈ A, b ≠ 1 ∧ S = Subgroup.zpowers b := by
  obtain ⟨hSA, hS3⟩ := hS
  rw [pow_one] at hS3
  have hSbot : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS3
    omega
  obtain ⟨⟨b, hbS⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSbot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hord : orderOf b = 3 := by
    have hdvd : orderOf b ∣ 3 := hS3 ▸ Subgroup.orderOf_dvd_natCard S hbS
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1'
    · exact h
  refine ⟨b, hSA hbS, hb1', ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbS) ?_).symm
  rw [Nat.card_zpowers, hord, hS3]

omit [Finite G] in
theorem zpowers_mem_signalizerFunctorEk (hA : IsE27 A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.zpowers a ∈ CFSG.Open.signalizerFunctorEk 3 1 A := by
  refine ⟨Subgroup.zpowers_le.mpr ha, ?_⟩
  rw [pow_one, Nat.card_zpowers]
  exact orderOf_eq_prime (hA.1.2 a ha) ha1

omit [Finite G] in
theorem centralizer_zpowers_eq_singleton (b : G) :
    Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite G] in
theorem le_normalizer_centralizer_of_le (hAab : IsMulCommutative A) {S : Subgroup G}
    (hSA : S ≤ A) :
    A ≤ Subgroup.normalizer ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  refine le_trans (fun x hx => ?_) Subgroup.le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact congrArg Subtype.val (hAab.is_comm.comm ⟨s, hSA hs⟩ ⟨x, hx⟩)

omit [Finite G] in
theorem le_normalizer_delta (X : Subgroup G) :
    A ≤ Subgroup.normalizer ((delta A LB X : Subgroup G) : Set G) :=
  le_normalizer_sSup fun _ hQ => hQ.1.1.2.2

omit [Finite G] in
theorem delta_inf_centralizer_mem (h443 : Item1443 A LB) {Y : Subgroup G}
    (hY : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3)) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    delta A LB (Y ⊓ Subgroup.centralizer {b}) ∈
      collectionIn (scriptQ A LB) (Subgroup.centralizer {b}) := by
  refine h443 b hb hb1 _ (fun Q hQ => ⟨hQ.1, hQ.2.trans inf_le_right⟩) ⟨le_top, ?_, ?_⟩
  · exact isPiSubgroup_piCompl_of_le hY.2.1 ((delta_le _).trans inf_le_left)
  · exact le_normalizer_delta _

end Helpers

section General

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem rank3II_14_6_of_item1443 (hA : IsE27 A)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (h443 : Item1443 A LB)
    {Y : Subgroup G} (hYΔ : Y = delta A LB Y) (hY : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Y ⊓ Subgroup.centralizer {a} = delta A LB (Y ⊓ Subgroup.centralizer {a}) ∧
      delta A LB (Y ⊓ Subgroup.centralizer {a}) ∈
        collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
  have hAab : IsMulCommutative A := hA.1.1
  have hY3 : ¬ 3 ∣ Nat.card Y := (isPiSubgroup_piCompl_iff Nat.prime_three Y).mp hY.2.1
  let Θ : Subgroup G → Subgroup G := fun S => delta A LB (Y ⊓ Subgroup.centralizer (S : Set G))
  have hΘY : ∀ S, Θ S ≤ Y := fun S => (delta_le _).trans inf_le_left
  have hΘb : ∀ b : G, Θ (Subgroup.zpowers b) = delta A LB (Y ⊓ Subgroup.centralizer {b}) := by
    intro b
    show delta A LB (Y ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) = _
    rw [centralizer_zpowers_eq_singleton]
  have hΘQ : ∀ S ∈ CFSG.Open.signalizerFunctorEk 3 1 A, Θ S ∈ scriptQ A LB := by
    intro S hS
    obtain ⟨b, hb, hb1, rfl⟩ := exists_eq_zpowers_of_mem_signalizerFunctorEk hS
    rw [hΘb]
    exact (delta_inf_centralizer_mem h443 hY hb hb1).1
  have hG3 : 3 ∣ Nat.card G := by
    have h27 := Subgroup.card_subgroup_dvd_card A
    rw [hA.2] at h27
    exact (by norm_num : (3 : ℕ) ∣ 27).trans h27
  have hΘtop : ∀ S, Θ S ≠ ⊤ := by
    intro S htop
    apply hY3
    have h1 : Nat.card (⊤ : Subgroup G) ∣ Nat.card Y := by
      rw [← htop]
      exact Subgroup.card_dvd_of_le (hΘY S)
    rw [Subgroup.card_top] at h1
    exact hG3.trans h1
  have hrank : 3 ^ (1 + 2) ≤ Nat.card A := (by norm_num : (3 : ℕ) ^ (1 + 2) = 27).le.trans hA.2.ge
  obtain ⟨-, hW, hWle, -⟩ := CFSG.Milestones.cl_lit_signalizer_functor_theorem_1 G 3
    Nat.prime_three 1 le_rfl A ⟨hA.1.1, hA.1.2⟩ hrank Θ
    (fun S _ => (delta_le _).trans inf_le_right)
    (fun S _ => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hY3 (h3.trans (Subgroup.card_dvd_of_le (hΘY S))))
    (fun S _ => le_normalizer_delta _)
    (fun S hS S' hS' => le_delta
      (mem_scriptQ_of_le (hΘQ S hS) inf_le_left
        (le_normalizer_inf (le_normalizer_delta _)
          (le_normalizer_centralizer_of_le hAab hS'.1)))
      (le_inf (inf_le_left.trans (hΘY S)) inf_le_right))
    (fun S _ => isKGroupCat_of_ne_top_of_kProper CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge hK
      (hΘtop S))
  have hYW : Y = ⨆ (S : Subgroup G) (_ : S ∈ CFSG.Open.signalizerFunctorEk 3 1 A), Θ S := by
    refine le_antisymm ?_ (iSup₂_le fun S _ => hΘY S)
    conv_lhs => rw [hYΔ]
    refine sSup_le fun Q hQ => hWle Q hQ.1.1.2.2 fun S hS => ?_
    exact le_delta (mem_scriptQ_of_le hQ.1 inf_le_left
      (le_normalizer_inf hQ.1.1.2.2 (le_normalizer_centralizer_of_le hAab hS.1)))
      (inf_le_inf_right _ hQ.2)
  have hS := zpowers_mem_signalizerFunctorEk hA ha ha1
  refine ⟨?_, delta_inf_centralizer_mem h443 hY ha ha1⟩
  have h2 := hW _ hS
  rw [← hYW, centralizer_zpowers_eq_singleton, hΘb] at h2
  exact h2

theorem item146_of_item1443 (hA : IsE27 A)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (h443 : Item1443 A LB) :
    Item146 A LB :=
  fun _ hY hYΔ _ ha ha1 => rank3II_14_6_of_item1443 hA hK h443 hYΔ hY ha ha1

theorem item146_of_sec14Std {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h443 : Item1443 A (lB A)) : Item146 A (lB A) :=
  item146_of_item1443 (isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE)
    h.toTheoremFourHyp.kProper h443

theorem item146_of_concl {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h142 : Concl142 A (lB A)) (h143 : Concl143 A (lB A)) : Item146 A (lB A) :=
  item146_of_sec14Std h (rank3II_14_4_3_reduction h142 h143)

theorem item146_forall_of_concl
    (h142 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → Concl142 A (lB A))
    (h143 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → Concl143 A (lB A)) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → Item146 A (lB A) :=
  fun G _ _ A c L h => item146_of_concl h (h142 G A c L h) (h143 G A c L h)

end General

end CFSG.RankThree.PartTwo.Sec14
