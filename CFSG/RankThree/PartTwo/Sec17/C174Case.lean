module

public import CFSG.RankThree.PartTwo.Sec17.C174H
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.Quasithin.H13.A7SectionRank

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

section Certificates


theorem e3core_exists_hom_img148 {Y X : Subgroup G} [(ker148 A Y).Normal] (hX : X ≤ Y) :
    ∃ φ : ↥X →* ↥(img148 A Y X), Function.Surjective φ := by
  have hXYA : X ≤ Y ⊔ A := hX.trans le_sup_left
  let φ₀ : ↥X →* (↥(Y ⊔ A) ⧸ ker148 A Y) :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hXYA)
  refine ⟨MonoidHom.codRestrict φ₀ (img148 A Y X) ?_, ?_⟩
  · intro x
    exact mem_img148_iff.mpr ⟨(x : G), hXYA x.2, x.2, rfl⟩
  · intro y
    obtain ⟨g, hg, hgX, hmk⟩ := mem_img148_iff.mp y.2
    exact ⟨⟨g, hgX⟩, Subtype.ext hmk⟩

theorem false_of_img148_simple_core {LB : Subgroup G → Subgroup G} {Y H : Subgroup G}
    [(ker148 A Y).Normal]
    (hs : IsSimpleGroup ↥(img148 A Y (deltaZero A LB Y)))
    (hna : ∃ a b : ↥(img148 A Y (deltaZero A LB Y)), a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card ↥(img148 A Y (deltaZero A LB Y)))
    (hND : deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔ deltaZero A LB (Y ⊓ H))
    (hS : SolvMod3' (Y ⊓ H)) : False := by
  have hD0K : deltaZero A LB (Y ⊓ H) ≤ deltaZero A LB Y := deltaZero_mono inf_le_left
  have hD0Z : deltaZero A LB (Y ⊓ H) ≤ Y ⊓ H := deltaZero_le (Y ⊓ H)
  obtain ⟨φ, hφ⟩ :=
    e3core_exists_hom_img148 (A := A) (Y := Y) (X := deltaZero A LB Y) (deltaZero_le Y)
  have hN3' : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(deltaZero A LB Y)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hND' : CFSG.pPrimeCore 3 ↥(deltaZero A LB Y) ⊔
      (deltaZero A LB (Y ⊓ H)).subgroupOf (deltaZero A LB Y) = ⊤ := by
    have h1 : (pPrimeCoreOf 3 (deltaZero A LB Y) ⊔ deltaZero A LB (Y ⊓ H)).subgroupOf
        (deltaZero A LB Y) = ⊤ := by
      rw [← hND, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup (pPrimeCoreOf_le 3 (deltaZero A LB Y)) hD0K] at h1
    have h2 : (pPrimeCoreOf 3 (deltaZero A LB Y)).subgroupOf (deltaZero A LB Y) =
        CFSG.pPrimeCore 3 ↥(deltaZero A LB Y) := by
      unfold pPrimeCoreOf
      exact Subgroup.comap_map_eq_self_of_injective (deltaZero A LB Y).subtype_injective _
    rw [h2] at h1
    exact h1
  obtain ⟨N, hNn, hN3, hsolv⟩ := hS
  let ι : ↥((deltaZero A LB (Y ⊓ H)).subgroupOf (deltaZero A LB Y)) →* ↥(Y ⊓ H) :=
    (Subgroup.inclusion hD0Z).comp (Subgroup.subgroupOfEquivOfLe hD0K).toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hD0Z).comp (Subgroup.subgroupOfEquivOfLe hD0K).injective
  let ψ : ↥((deltaZero A LB (Y ⊓ H)).subgroupOf (deltaZero A LB Y)) →*
      ↥(Y ⊓ H) ⧸ N :=
    (QuotientGroup.mk' N).comp ι
  have hψ : ¬ 3 ∣ Nat.card ψ.ker := by
    have hdvd : Nat.card ψ.ker ∣ Nat.card N := by
      let f : ψ.ker →* N := MonoidHom.codRestrict (ι.comp ψ.ker.subtype) N (fun x => by
        have hx : (QuotientGroup.mk' N) (ι x.1) = 1 := MonoidHom.mem_ker.mp x.2
        exact (QuotientGroup.eq_one_iff _).mp hx)
      have hf : Function.Injective f := by
        intro x y hxy
        have hxy' : ι x.1 = ι y.1 := congrArg Subtype.val hxy
        exact Subtype.ext (hι hxy')
      exact Subgroup.card_dvd_of_injective f hf
    intro h3'
    exact hN3 (dvd_trans h3' hdvd)
  exact false_of_simple_image_solvable_mod hna h3 φ hφ hN3' hND' ψ hψ

structure LemmaEData (A : Subgroup G) (c : G) (L Y₀ Y : Subgroup G) : Prop where
  std : Sec17Std G A c L Y₀
  omega : omegaA A = {Subgroup.zpowers c}
  notJ2 : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem : Y ∈ scriptY A
  rank : CFSG.Open.pRank 3 Y ≤ 1
  lY : ¬ 3 ∣ Nat.card ↥(L ⊓ Y)
  solv : SolvMod3' (Y ⊓ nH c)

theorem E3two_transfer {Γ M : Type} [Group Γ] [Group M] (e : Γ ≃* M)
    (hna : ∃ a b : M, a * b ≠ b * a) : ∃ a b : Γ, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h2 := congrArg e h
  simpa using h2

theorem E3two_dvd_of_equiv {Γ M : Type} [Group Γ] [Group M] (e : Γ ≃* M)
    (h3 : 3 ∣ Nat.card M) : 3 ∣ Nat.card Γ := by
  rw [Nat.card_congr e.toEquiv]
  exact h3

theorem E3two_three_dvd_of_pRank_two {X : Type} [Group X] [Finite X]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : 3 ∣ Nat.card X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  have hd : Nat.card E ∣ Nat.card X := Subgroup.card_subgroup_dvd_card E
  rw [hE] at hd
  exact dvd_trans (dvd_pow_self 3 two_ne_zero) hd

theorem E3two_nonabelian_of_not_solvable {Γ : Type} [Group Γ]
    (h : ¬ Group.IsSolvable Γ) : ∃ a b : Γ, a * b ≠ b * a := by
  by_contra hc
  exact h (Group.isSolvable_of_comm fun a b => by
    by_contra hab
    exact hc ⟨a, b, hab⟩)

theorem E3two_three_dvd_of_isLThreeEpsAt {Γ : Type} [Group Γ] {p f : ℕ} [Fact p.Prime]
    (h : IsLThreeEpsAt Γ p f) : 3 ∣ Nat.card Γ := by
  rcases h with he | ⟨hlt, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    exact CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSL e
  · have hf : f ≠ 0 := by
      rintro rfl
      simp at hlt
    exact CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSU hf e

theorem E3two_a7 {Γ : Type} [Group Γ] (e : Γ ≃* alternatingGroup (Fin 7)) :
    IsSimpleGroup Γ ∧ (∃ a b : Γ, a * b ≠ b * a) ∧ 3 ∣ Nat.card Γ := by
  have hsA : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · by_contra hc
    have hA : ∀ a b : alternatingGroup (Fin 7), a * b = b * a := by
      intro a b
      have h1 : ∀ x y : Γ, x * y = y * x := fun x y => by
        by_contra hxy
        exact hc ⟨x, y, hxy⟩
      have h2 := congrArg e (h1 (e.symm a) (e.symm b))
      simpa using h2
    have hcomm : IsMulCommutative (alternatingGroup (Fin 7)) := ⟨⟨hA⟩⟩
    have h7 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 7)).mp hcomm
    simp at h7
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

theorem eq_L_of_mem_lA
    (h : Sec14Std G A c L) (hΩ : omegaA A = {Subgroup.zpowers c}) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') : L' = L := by
  have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
    rw [hΩ] at hc'
    exact Set.mem_singleton_iff.mp hc'
  exact CFSG.RankThree.PartTwo.Sec15.Proof1515.eq_of_mem_lA_of_zpowers_eq h
    (three_dvd_card_L h) hcc hL'

theorem img148_simple_of_case148Two
    {Y : Subgroup G} [(ker148 A Y).Normal] (hd : LemmaEData A c L Y₀ Y)
    (h2 : Case148Two A (lB A) Y) :
    IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) Y)) ∧
      (∃ a b : ↥(img148 A Y (deltaZero A (lB A) Y)), a * b ≠ b * a) ∧
      3 ∣ Nat.card ↥(img148 A Y (deltaZero A (lB A) Y)) ∧
      deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
        deltaZero A (lB A) (Y ⊓ nH c) := by
  obtain ⟨c', hcOm, hΔ, L', hL', hcases⟩ := h2
  have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
    rw [hd.omega] at hcOm
    exact Set.mem_singleton_iff.mp hcOm
  have hL : L' = L := eq_L_of_mem_lA hd.std.toSec14Std hd.omega hcOm hL'
  have hΔ' : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ nH c) := by
    rw [hcc] at hΔ
    exact hΔ
  have key : IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) Y)) ∧
      (∃ a b : ↥(img148 A Y (deltaZero A (lB A) Y)), a * b ≠ b * a) ∧
      3 ∣ Nat.card ↥(img148 A Y (deltaZero A (lB A) Y)) := by
    rcases hcases with hi | ⟨-, hA7⟩ | ⟨p, f, m, hp, -, -, -, hS⟩ | ⟨hJ, -⟩
    · rw [hL] at hi
      obtain ⟨e⟩ := hi
      have hs := (lBar_simple_and_pRank hd.std.toSec14Std).1
      have h3 := E3two_three_dvd_of_pRank_two (lBar_simple_and_pRank hd.std.toSec14Std).2
      exact ⟨e.isSimpleGroup, E3two_transfer e (lBar_nonabelian hd.std.toSec14Std),
        E3two_dvd_of_equiv e h3⟩
    · obtain ⟨e⟩ := hA7
      exact E3two_a7 e
    · have hS' := CFSG.RankThree.PartTwo.Sec15.KSL3Two.isSimpleGroup_and_not_isSolvable hS
      exact ⟨hS'.1, E3two_nonabelian_of_not_solvable hS'.2,
        E3two_three_dvd_of_isLThreeEpsAt hS⟩
    · rw [hL] at hJ
      exact (hd.notJ2 hJ).elim
  exact ⟨key.1, key.2.1, key.2.2, hΔ'⟩

theorem false_of_case148Three
    {Y : Subgroup G} [(ker148 A Y).Normal] (hd : LemmaEData A c L Y₀ Y)
    (h3 : Case148Three A (lB A) Y) : False := by
  obtain ⟨c', -, L', hc', hL', hJ, -⟩ := h3
  have hL : L' = L := eq_L_of_mem_lA hd.std.toSec14Std hd.omega hc' hL'
  rw [hL] at hJ
  exact hd.notJ2 hJ

theorem false_of_case148Six
    {Y : Subgroup G} [(ker148 A Y).Normal] (hd : LemmaEData A c L Y₀ Y)
    (h6 : Case148Six A (lB A) Y) : False := by
  obtain ⟨-, -, h6⟩ := h6
  rw [hd.omega, Set.ncard_singleton] at h6
  omega

theorem false_of_case148Four {Y : Subgroup G} [(ker148 A Y).Normal]
    (hd : LemmaEData A c L Y₀ Y) (h4 : Case148Four A (lB A) Y) : False := by
  obtain ⟨⟨e⟩, -, -⟩ := h4
  have h10 : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 10))) = 3 :=
    CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank.2.2.2.2
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img148 A Y (deltaZero A (lB A) Y))) = 3 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e, h10]
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img148 A Y (deltaZero A (lB A) Y))) ≤ 1 :=
    (pRank_three_img148_le hd.mem.2 (deltaZero_le (A := A) (LB := lB A) Y)).trans hd.rank
  rw [h1] at h2
  omega

theorem false_of_case148Five
    {Y : Subgroup G} [(ker148 A Y).Normal] (hd : LemmaEData A c L Y₀ Y)
    (h5 : Case148Five A (lB A) Y) : False := by
  obtain ⟨c5, hcA, L5, n, m, -, -, hn, -, hiso, -⟩ := h5
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img148 A Y (deltaZero A (lB A) Y))) :=
    two_le_pRank_three_of_isoLThreePi (by omega) hiso
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img148 A Y (deltaZero A (lB A) Y))) ≤ 1 :=
    (pRank_three_img148_le hd.mem.2 (deltaZero_le (A := A) (LB := lB A) Y)).trans hd.rank
  exact absurd (le_trans h2 h1) (by norm_num)

theorem not_three_dvd_img148_of_case148Seven
    {Y : Subgroup G} [(ker148 A Y).Normal]
    (hd : LemmaEData A c L Y₀ Y) (h7 : Case148Seven A (lB A) Y) :
    ¬ 3 ∣ Nat.card ↥(img148 A Y (deltaZero A (lB A) Y)) := by
  obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, _, _, ha₁, ha₂, hL₁, hL₂, hJ₁, hJ₂,
    hsup, hinf, hcomm, -⟩ := h7
  have hL₁' : L₁ = L := eq_L_of_mem_lA hd.std.toSec14Std hd.omega ha₁ hL₁
  have hL₂' : L₂ = L := eq_L_of_mem_lA hd.std.toSec14Std hd.omega ha₂ hL₂
  rw [hL₁'] at hJ₁
  rw [hL₂'] at hJ₂
  have hprime : ∀ J : Subgroup G, J ≤ L ⊓ Y → ¬ 3 ∣ Nat.card ↥(img148 A Y J) := by
    intro J hJle h
    have hXYA : J ≤ Y ⊔ A := hJle.trans (inf_le_right.trans le_sup_left)
    have h1 : 3 ∣ Nat.card ↥J :=
      h.trans (CFSG.RankThree.PartTwo.Sec14.Main148.card_img148_dvd hXYA)
    have h2 : 3 ∣ Nat.card ↥(L ⊓ Y) := h1.trans (Subgroup.card_dvd_of_le hJle)
    exact hd.lY h2
  have hc : ∀ x ∈ img148 A Y J₁, ∀ y ∈ img148 A Y J₂, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (img148 A Y J₁) (img148 A Y J₂) hc).1
  rw [hinf, Subgroup.card_bot, mul_one, hsup] at hcard
  rw [hcard]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
  · exact hprime J₁ hJ₁ h1
  · exact hprime J₂ hJ₂ h1

theorem case148One_of_lemmaE
    {Y : Subgroup G} (h148 : Item148 A (lB A)) (hd : LemmaEData A c L Y₀ Y) :
    Case148One A (lB A) Y := by
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hd.mem.2
  letI := ker148_normal hAY
  obtain ⟨hnorm, hcases⟩ := (item148_iff A (lB A)).mp h148 Y hd.mem
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact h1
  · obtain ⟨hs, hna, h3', hND⟩ := img148_simple_of_case148Two hd h2
    exact (false_of_img148_simple_core hs hna h3' hND hd.solv).elim
  · exact (false_of_case148Three hd h3).elim
  · exact (false_of_case148Four hd h4).elim
  · exact (false_of_case148Five hd h5).elim
  · exact (false_of_case148Six hd h6).elim
  · exact case148One_of_img_three_prime hAY hnorm (not_three_dvd_img148_of_case148Seven hd h7)

end Certificates

end CFSG.RankThree.PartTwo.Sec17.C174
