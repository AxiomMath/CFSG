module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarOuter
import CFSG.RankThree.PartTwo.Late.Glue
import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.RankThree.PartOne.OutStructure (OutPNice)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_normal_of_outPNice {X : Type} [Group X] (h : OutPNice 3 X) {φ ψ : MulAut X}
    (hφ : ∃ k : ℕ, φ ^ 3 ^ k = 1) (hφI : φ ∉ innAut X) (hψ : ψ ^ 3 = 1) :
    ∃ D : Subgroup (MulAut X), D.Normal ∧ innAut X ≤ D ∧
      (∀ δ ∈ D, ∀ k : ℕ, δ ^ 3 ^ k ∈ innAut X → δ ∈ innAut X) ∧ ∃ m : ℤ, ψ * φ ^ m ∈ D := by
  obtain ⟨D, E, hID, hD1, hE1, hE2, hC⟩ := h
  have hDE : D ≤ E := fun δ hδ => hE1 δ ⟨0, by simpa using hδ⟩
  have hDn : D.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by rw [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hE2 g n (hDE hn)) hn⟩
  obtain ⟨k, hk⟩ := hφ
  have hφE : φ ∈ E := hE1 φ ⟨k, by rw [hk]; exact hID (Subgroup.one_mem _)⟩
  have hψE : ψ ∈ E := hE1 ψ ⟨1, by rw [pow_one, hψ]; exact hID (Subgroup.one_mem _)⟩
  have hφD : φ ∉ D := fun hd => hφI (hD1 φ hd k (by rw [hk]; exact Subgroup.one_mem _))
  refine ⟨D, hDn, hID, fun δ hδ k hk' => hD1 δ hδ k hk', ?_⟩
  by_cases hψD : ψ ∈ D
  · exact ⟨0, by rw [zpow_zero, mul_one]; exact hψD⟩
  · rcases hC ψ hψE φ hφE
        ⟨1, by rw [pow_one, hψ]; exact hID (Subgroup.one_mem _)⟩
        ⟨k, by rw [hk]; exact hID (Subgroup.one_mem _)⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m, hm⟩
    · have hmod : ψ ^ m = ψ ^ (m % 3) :=
        zpow_eq_zpow_emod (x := ψ) m (n := (3 : ℤ)) (by simpa using hψ)
      have hlt : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
      have hge : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
      rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h0 | h1 | h2
      · exact absurd (by simpa [hmod, h0] using hm) hφD
      · refine ⟨1, ?_⟩
        have hm' : φ * ψ ∈ D := by rwa [hmod, h1, zpow_one] at hm
        rw [zpow_one]
        have he : ψ * φ = φ⁻¹ * (φ * ψ) * φ := by group
        rw [he]
        simpa using hDn.conj_mem (φ * ψ) hm' φ⁻¹
      · refine ⟨-1, ?_⟩
        have hm' : φ * ψ ^ (2 : ℤ) ∈ D := by rwa [hmod, h2] at hm
        have hzm : ψ ^ (-2 : ℤ) = ψ := by
          have h := zpow_eq_zpow_emod (x := ψ) (-2 : ℤ) (n := (3 : ℤ)) (by simpa using hψ)
          rw [h, show (-2 : ℤ) % 3 = 1 by norm_num, zpow_one]
        have hinv : (ψ ^ (2 : ℤ))⁻¹ = ψ := by rw [← zpow_neg, hzm]
        have hthis : (φ * ψ ^ (2 : ℤ))⁻¹ = ψ * φ⁻¹ := by rw [mul_inv_rev, hinv]
        rw [zpow_neg_one, ← hthis]
        exact D.inv_mem hm'

private theorem not_dvd_relIndex_of_no_three_element {G : Type*} [Group G] [Finite G]
    {D I : Subgroup G} [I.Normal]
    (hD : ∀ δ ∈ D, ∀ k : ℕ, δ ^ 3 ^ k ∈ I → δ ∈ I) : ¬ 3 ∣ I.relIndex D := by
  intro h3
  have hcard : 3 ∣ Nat.card (D ⧸ I.subgroupOf D) := by
    rw [← Subgroup.index_eq_card]
    exact h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (I.subgroupOf D) x
  have hx1 : (QuotientGroup.mk d : D ⧸ I.subgroupOf D) ^ 3 = 1 := by
    rw [← hx]; exact pow_orderOf_eq_one _
  have hx3 : d ^ 3 ∈ I.subgroupOf D := by
    apply (QuotientGroup.eq_one_iff (d ^ 3)).mp
    rw [QuotientGroup.mk_pow]
    exact hx1
  have hdne : d ∉ I.subgroupOf D := by
    intro hd
    have h1 : (QuotientGroup.mk' (I.subgroupOf D)) d = 1 :=
      (QuotientGroup.eq_one_iff d).mpr hd
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hdI : (d : G) ∈ I := hD (d : G) d.2 1 (by
    have := Subgroup.mem_subgroupOf.mp hx3
    simpa using this)
  exact hdne (Subgroup.mem_subgroupOf.mpr hdI)

theorem isSylowOf_sup_of_outPNice {G : Type*} [Group G] [Finite G] {D I R : Subgroup G}
    [D.Normal] [I.Normal] (hID : I ≤ D) (hD : ∀ δ ∈ D, ∀ k : ℕ, δ ^ 3 ^ k ∈ I → δ ∈ I)
    (hR : IsPGroup 3 R) (hS : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ I) I) :
    CFSG.ABGLocalTools.IsSylowOf 3 R (D ⊔ R) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS ⊢
  obtain ⟨hRI, hRp, hndvdI⟩ := hS
  refine ⟨le_sup_right, hR, ?_⟩
  rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal D R]
  have hinf : D ⊓ R = I ⊓ R := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxD, hxR⟩
      obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
      exact ⟨hD x hxD k (by rw [show x ^ 3 ^ k = 1 from by simpa using hk]; exact I.one_mem),
        hxR⟩
    · rintro x ⟨hxI, hxR⟩
      exact ⟨hID hxI, hxR⟩
  have hrel : R.relIndex D = (R ⊓ I).relIndex I * I.relIndex D := by
    rw [← Subgroup.inf_relIndex_right R D, inf_comm R D, inf_comm R I, hinf]
    exact (Subgroup.relIndex_mul_relIndex (H := I ⊓ R) (K := I) (L := D)
      inf_le_left hID).symm
  intro h3
  have h3' : 3 ∣ (R ⊓ I).relIndex I * I.relIndex D := by
    rw [hrel] at h3
    exact h3
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp h3' with h | h
  · exact hndvdI h
  · exact not_dvd_relIndex_of_no_three_element hD h

theorem le_pRank_of_isSylowOf {G : Type*} [Group G] [Finite G] {R M Q : Subgroup G} {r : ℕ}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hQM : Q ≤ M) (hQ : IsElemAbelian 3 Q)
    (hQr : Nat.card Q = 3 ^ r) : r ≤ pRank 3 R := by
  obtain ⟨S, hS⟩ := hR
  have hQ' : IsPGroup 3 (Q.subgroupOf M) :=
    (CFSG.Open.IsElemAbelian.isPGroup hQ).comap_subtype
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Late.exists_map_conj_le_sylow hQ' S
  have hA_le : ((Q.subgroupOf M).map (MulAut.conj g).toMonoidHom).map M.subtype ≤ R := by
    rw [← hS]
    exact Subgroup.map_mono hg
  let A : Subgroup ↥R :=
    ((Q.subgroupOf M).map (MulAut.conj g).toMonoidHom).map M.subtype |>.subgroupOf R
  have hAelem : IsElemAbelian 3 A := by
    show IsElemAbelian 3 ((((Q.subgroupOf M).map (MulAut.conj g).toMonoidHom).map
      M.subtype).subgroupOf R)
    exact CFSG.Open.IsElemAbelian.subgroupOf
      (CFSG.Open.IsElemAbelian.map
        (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hQ M)
          (MulAut.conj g).toMonoidHom) M.subtype) R
  have hAcard : Nat.card A = 3 ^ r := by
    calc Nat.card A
        = Nat.card (((Q.subgroupOf M).map (MulAut.conj g).toMonoidHom).map M.subtype) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv
      _ = Nat.card ((Q.subgroupOf M).map (MulAut.conj g).toMonoidHom) :=
          Subgroup.card_map_of_injective M.subtype_injective
      _ = Nat.card (Q.subgroupOf M) :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = Nat.card Q := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
      _ = 3 ^ r := hQr
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥R]
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hAelem hAcard

private theorem map_conj_sup_zpowers_commute {X : Type} [Group X] {ψ : MulAut X} {E : Subgroup X}
    (hfix : E ≤ fixedSubgroup ψ) :
    ∀ a ∈ E.map (MulAut.conj : X →* MulAut X), ∀ b ∈ Subgroup.zpowers ψ, a * b = b * a := by
  intro a ha b hb
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc : Commute (MulAut.conj e) ψ :=
    CFSG.SeitzReduction.RankOne.mulAut_conj_commute_of_fixed (x := ψ) (c := e) (hfix he)
  exact (hc.zpow_right n).eq

private theorem card_map_conj_sup_zpowers {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) {ψ : MulAut X} (hψ : ψ ^ 3 = 1) (hψI : ψ ∉ innAut X)
    {E : Subgroup X} (hfix : E ≤ fixedSubgroup ψ) {r : ℕ} (hEr : Nat.card E = 3 ^ r) :
    Nat.card (E.map (MulAut.conj : X →* MulAut X) ⊔ Subgroup.zpowers ψ :
      Subgroup (MulAut X)) = 3 ^ (r + 1) := by
  have hψ1 : ψ ≠ 1 := fun h => hψI (h.symm ▸ (innAut X).one_mem)
  have hcardψ : Nat.card (Subgroup.zpowers ψ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hψ hψ1]
  have hψA : ψ ∉ E.map (MulAut.conj : X →* MulAut X) := by
    rintro ⟨e, _, he⟩
    exact hψI ⟨e, he⟩
  have hpsiC : ψ ∈ Subgroup.centralizer
      ((E.map (MulAut.conj : X →* MulAut X)) : Set (MulAut X)) :=
    Subgroup.mem_centralizer_iff.mpr (fun a ha =>
      map_conj_sup_zpowers_commute hfix a ha ψ (Subgroup.mem_zpowers ψ))
  have hnormal : Subgroup.zpowers ψ ≤ Subgroup.normalizer
      ((E.map (MulAut.conj : X →* MulAut X)) : Set (MulAut X)) :=
    (Subgroup.zpowers_le.mpr hpsiC).trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint (E.map (MulAut.conj : X →* MulAut X)) (Subgroup.zpowers ψ) := by
    rw [Subgroup.disjoint_def]
    intro g hgA hgB
    haveI : Fact (Nat.card (Subgroup.zpowers ψ)).Prime := ⟨by rw [hcardψ]; norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        ((E.map (MulAut.conj : X →* MulAut X)).subgroupOf (Subgroup.zpowers ψ)) with h | h
    · have hg : (⟨g, hgB⟩ : Subgroup.zpowers ψ) ∈
          (E.map (MulAut.conj : X →* MulAut X)).subgroupOf (Subgroup.zpowers ψ) := hgA
      rw [h] at hg
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hg)
    · exfalso
      have hf : (⟨ψ, Subgroup.mem_zpowers ψ⟩ : Subgroup.zpowers ψ) ∈
          (E.map (MulAut.conj : X →* MulAut X)).subgroupOf (Subgroup.zpowers ψ) := by
        rw [h]; trivial
      exact hψA hf
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormal hdisj,
    Subgroup.card_map_of_injective (CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot hc),
    hEr, hcardψ, pow_succ]

theorem exists_elemAbelian_sup_zpowers {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) {ψ : MulAut X} (hψ : ψ ^ 3 = 1) (hψI : ψ ∉ innAut X)
    (E : Subgroup X) (hE : IsElemAbelian 3 E) (hfix : E ≤ fixedSubgroup ψ) {r : ℕ}
    (hEr : Nat.card E = 3 ^ r) :
    ∃ Q : Subgroup (MulAut X), Q ≤ innAut X ⊔ Subgroup.zpowers ψ ∧ IsElemAbelian 3 Q ∧
      Nat.card Q = 3 ^ (r + 1) := by
  refine ⟨E.map (MulAut.conj : X →* MulAut X) ⊔ Subgroup.zpowers ψ, ?_, ?_, ?_⟩
  · exact sup_le ((Subgroup.map_le_range (MulAut.conj : X →* MulAut X) E).trans le_sup_left)
      le_sup_right
  · exact (hE.map (MulAut.conj : X →* MulAut X)).sup_of_commute
      (isElemAbelian_zpowers hψ) (map_conj_sup_zpowers_commute hfix)
  · exact card_map_conj_sup_zpowers hc hψ hψI hfix hEr

theorem k2Simple_of_parts
    (h : ∀ (X : Type) [Group X] [Finite X] (fam : LieFam811) (r f : ℕ),
      IsLieFam811 X fam r f → OutPNice 3 X ∧ Exists3 X ∧ OuterFixed3 X) : K2Simple := by
  intro X _ _ fam q f hfam hc R hR hSyl hnot
  obtain ⟨hON, hE3, hF3⟩ := h X fam q f hfam
  obtain ⟨φ, hφR, hφI⟩ := Set.not_subset.mp hnot
  have hφp : ∃ k : ℕ, φ ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hR ⟨φ, hφR⟩
    exact ⟨k, by simpa using hk⟩
  obtain ⟨ψ, hψ, hψI⟩ := hE3 ⟨φ, hφI, hφp⟩
  obtain ⟨E, hEfix, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num : 1 < 3) (fixedSubgroup ψ)
  obtain ⟨Q, hQle, hQelem, hQcard⟩ :=
    exists_elemAbelian_sup_zpowers hc hψ hψI E hEelem hEfix hEcard
  obtain ⟨D, hDnorm, hID, hD1, m, hm⟩ := exists_normal_of_outPNice hON hφp hφI hψ
  have hψDR : ψ ∈ (D ⊔ R : Subgroup (MulAut X)) := by
    have h1 : ψ * φ ^ m ∈ (D ⊔ R : Subgroup (MulAut X)) := Subgroup.mem_sup_left hm
    have h2 : φ ^ (-m) ∈ (D ⊔ R : Subgroup (MulAut X)) :=
      Subgroup.mem_sup_right (R.zpow_mem hφR (-m))
    have he : (ψ * φ ^ m) * φ ^ (-m) = ψ := by
      rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    rw [← he]
    exact mul_mem h1 h2
  have hQm : Q ≤ D ⊔ R :=
    hQle.trans (sup_le (hID.trans le_sup_left) (Subgroup.zpowers_le.mpr hψDR))
  haveI : D.Normal := hDnorm
  haveI : (innAut X).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  have hSyl' := isSylowOf_sup_of_outPNice (D := D) (I := innAut X) (R := R) hID hD1 hR hSyl
  have hle := le_pRank_of_isSylowOf hSyl' hQm hQelem hQcard
  have h3 : 3 ≤ CFSG.Open.pRank 3 (fixedSubgroup ψ) := hF3 ψ hψ hψI
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
