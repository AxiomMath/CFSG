module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR865G2Center
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR865G2Outer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63LieOut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Pointwise65
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardG2General
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardTypes
public import CFSG.Quasithin.H13.U3L134K
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSpor)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

@[expose] def G2AutSylowCentralizer : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 3 → (p = 2 → 2 ≤ f) →
    LieModel Y .G2 0 p f → ∀ Q : Subgroup Y, (∃ S : Sylow 3 Y, (S : Subgroup Y) = Q) →
      ∀ φ : MulAut Y, φ ^ 3 = 1 → (∀ q ∈ Q, φ q = q) → ∃ g ∈ Q, φ = MulAut.conj g

private theorem center_eq_bot_of_lieModel_g2
    {Y : Type} [Group Y] {p f : ℕ} (hY : LieModel Y .G2 0 p f) : Subgroup.center Y = ⊥ := by
  obtain ⟨K, hKfield, hKfinite, -, ⟨eY⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup
    (τ := .G2) (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)).2
  rw [eq_bot_iff]
  intro x hx
  have h1 : eY x ∈ Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := eY.surjective y
    rw [← map_mul, ← map_mul, hx]
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact eY.injective (h1.trans (map_one eY).symm)

private theorem g2_exists_conj_of_not_three_dvd
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hY : LieModel Y .G2 0 p f) (hp : p.Prime)
    (h3f : ¬ 3 ∣ f) {φ : MulAut Y} (hφ3 : φ ^ 3 = 1) : ∃ g : Y, φ = MulAut.conj g := by
  classical
  rcases eq_or_ne φ 1 with h1 | h1
  · exact ⟨1, by rw [h1, map_one]⟩
  have hφord : orderOf φ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hφ3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have hc := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨K, _, _, hKcard, ⟨eY⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup
    (τ := .G2) hc.2
  have hdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) ∣ 2 * f :=
    card_outer_adjointGroup_G2_dvd hp hc.1.2.1 hKcard
      (by rw [hKcard]; exact hc.1.2.2.2)
  have hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eY).toEquiv]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (hd.trans hdvd) with h | h
    · omega
    · exact h3f h
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.OddSyl.mem_innAut_of_not_dvd (S := Y) (r := 3)
    (by norm_num) hφord hout
  exact ⟨g, hg.symm⟩

theorem g2AutSylowCentralizer_of_isInner
    : G2AutSylowCentralizer := by
  have h := g2AutCentralizingSylowIsInner_holds
  classical
  intro Y _ _ p f hp hp3 hp2f hY Q hQsyl φ hφ3 hφQ
  obtain ⟨g, hgconj⟩ : ∃ g : Y, φ = MulAut.conj g := by
    by_cases h3f : 3 ∣ f
    · exact h Y p f hp hp3 hp2f h3f hY Q hQsyl φ hφ3 hφQ
    · exact g2_exists_conj_of_not_three_dvd hY hp h3f hφ3
  obtain ⟨S, rfl⟩ := hQsyl
  have hgC : g ∈ Subgroup.centralizer ((S : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 := hφQ q hq
    rw [hgconj, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hg3 : g ^ 3 = 1 := by
    have hconj3 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, ← hgconj, hφ3]
    have hmem : g ^ 3 ∈ Subgroup.center Y := by
      rw [← CFSG.Quasithin.H13.U3.ker_conj_eq_center, MonoidHom.mem_ker]
      exact hconj3
    rwa [center_eq_bot_of_lieModel_g2 hY, Subgroup.mem_bot] at hmem
  have hzg : IsPGroup 3 (Subgroup.zpowers g) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hg3) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hnorm : Subgroup.zpowers g ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) :=
    (Subgroup.zpowers_le.mpr hgC).trans (Subgroup.centralizer_le_normalizer _)
  let H : Subgroup Y := Subgroup.zpowers g ⊔ (S : Subgroup Y)
  have hsup : IsPGroup 3 H := IsPGroup.to_sup_of_normal_right' hzg S.isPGroup' hnorm
  have hPeq : H = (S : Subgroup Y) := S.is_maximal' hsup le_sup_right
  have hgH : g ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  exact ⟨g, hPeq ▸ hgH, hgconj⟩

private theorem card_center_map_sylow_eq_three_of_g2
    {G : Type} [Group G] [Finite G] {L Q : Subgroup G} (hQ : IsSylowOf 3 Q L) {p f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hp2f : p = 2 → 2 ≤ f) (hX : LieModel (Bar2 L) .G2 0 p f) :
    Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3 := by
  classical
  have hQL : Q ≤ L := hQ.le
  have hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (CFSG.Open.pCoreOf 2 L) hQ.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot
  obtain ⟨Pb, hPb⟩ := exists_sylow_map_subgroupOf_mk' hQ.exists_sylow_eq_subgroupOf
  let g : ↥Q →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)
  have hg : Function.Injective g := injective_comp_subgroupOf_mk' hQL hQO2
  have hPbr : (Pb : Subgroup (Bar2 L)) = g.range := hPb.trans (range_comp_subgroupOf_mk' hQL).symm
  have e1 : Nat.card (Subgroup.center ↥Q) = Nat.card (Subgroup.center ↥g.range) :=
    Nat.card_congr (Subgroup.centerCongr (MonoidHom.ofInjective hg)).toEquiv
  have e2 : Nat.card (Subgroup.center ↥(Pb : Subgroup (Bar2 L))) =
      Nat.card (Subgroup.center ↥g.range) :=
    Nat.card_congr (Subgroup.centerCongr (MulEquiv.subgroupCongr hPbr)).toEquiv
  rw [Subgroup.card_map_of_injective Q.subtype_injective, e1, ← e2]
  exact g2SylowCenterCardThree_holds (Bar2 L) p f hp hp3 hp2f hX Pb

private theorem card_range_eq_three_of_lieModel_g2_of_cq
    (hCQ : G2AutSylowCentralizer)
    {G : Type} [Group G] [Finite G] {L X Z Q : Subgroup G} {p f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hp2f : p = 2 → 2 ≤ f)
    (hX : LieModel (Bar2 L) .G2 0 p f)
    (hQL : Q ≤ L)
    (hQsyl : ∃ P : Sylow 3 ↥L, (P : Subgroup ↥L) = Q.subgroupOf L)
    (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hQZ : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    (hXcard : Nat.card X = 3) (hZcard : Nat.card Z = 3) (hXneZ : X ≠ Z)
    (hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x)
    (hEnorm : X ⊔ Z ≤ Subgroup.normalizer (L : Set G))
    (hQE : ⁅Q, X ⊔ Z⁆ = ⊥)
    (hZnotle : ¬ Z ≤ centralizerBar (X ⊔ Z) L) :
    Nat.card (psi hEnorm).range = 3 := by
  classical
  let g : ↥Q →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)
  have hg_inj : Function.Injective g := injective_comp_subgroupOf_mk' hQL hQO2
  have hg_range : g.range = (Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    range_comp_subgroupOf_mk' hQL
  let Qb : Subgroup (Bar2 L) := g.range
  have hQsylb : ∃ Pb : Sylow 3 (Bar2 L), (Pb : Subgroup (Bar2 L)) = Qb := by
    obtain ⟨Pb, hPb⟩ := exists_sylow_map_subgroupOf_mk' hQsyl
    exact ⟨Pb, hPb.trans hg_range.symm⟩
  have hXea : IsElemAbelian 3 X :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime (r := 3) hXcard
  have hZea : IsElemAbelian 3 Z :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime (r := 3) hZcard
  have hEea : IsElemAbelian 3 (X ⊔ Z) := hXea.sup_of_commute hZea hcomm
  have hCentQ : ∀ e : ↥(X ⊔ Z), ∀ q ∈ Qb, psi hEnorm e q = q := by
    intro e q hq
    change q ∈ g.range at hq
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hq
    exact psi_mk'_eq_self_of_commutator_eq_bot hEnorm hQE e y.2
  have hAut : ∀ φ : MulAut (Bar2 L), φ ^ 3 = 1 → (∀ q ∈ Qb, φ q = q) →
      ∃ h ∈ Qb, φ = MulAut.conj h := fun φ hφ3 hφQ =>
    hCQ (Bar2 L) p f hp hp3 hp2f hX Qb hQsylb φ hφ3 hφQ
  have hCQb : ∀ e : ↥(X ⊔ Z),
      ∃ h ∈ (Subgroup.center ↥Qb).map Qb.subtype, psi hEnorm e = MulAut.conj h := by
    intro e
    have he3 : e ^ 3 = 1 := Subtype.ext (hEea.2 (e : G) e.2)
    have hφ3 : (psi hEnorm e) ^ 3 = 1 := by rw [← map_pow, he3, map_one]
    obtain ⟨h, hhQb, hh⟩ := hAut (psi hEnorm e) hφ3 (hCentQ e)
    have hhcent : (⟨h, hhQb⟩ : ↥Qb) ∈ Subgroup.center ↥Qb := by
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have h' := hCentQ e (q : Bar2 L) q.2
      rw [hh, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    exact ⟨h, Subgroup.mem_map.mpr ⟨⟨h, hhQb⟩, hhcent, rfl⟩, hh⟩
  have hCcard : Nat.card ((Subgroup.center ↥Qb).map Qb.subtype) = 3 := by
    have h := card_center_map_eq_of_injective g hg_inj
    rw [Subgroup.card_map_of_injective hg_inj, ← Subgroup.card_subtype] at h
    exact h.trans hQZ
  exact card_range_eq_three_of_conj_mem hEnorm hXcard hZcard hXneZ hcomm hCQb hCcard hZnotle

private theorem eight65_pointwise_false_of_lieModel_g2_of_cq
    (hCQ : G2AutSylowCentralizer)
    {G : Type} [Group G] [Finite G] {D : Data G} {L X P Q Z : Subgroup G} {t : G} {p f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hp2f : p = 2 → 2 ≤ f)
    (hZU : Z ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hPM : P ≤ D.M) (hLMle : L ≤ D.M) (hLM : (L.subgroupOf D.M).Normal)
    (hQP : Q ≤ P) (hZQ : Z ≤ Q)
    (hZcentQ : Z ≤ Subgroup.centralizer (Q : Set G)) (hZcard : Nat.card Z = 3)
    (hQL : Q ≤ L)
    (hQsyl : ∃ S : Sylow 3 ↥L, (S : Subgroup ↥L) = Q.subgroupOf L)
    (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hQZ : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    (hXP : X ≤ P) (hXcard : Nat.card X = 3)
    (h64 : List864 L X P)
    (hXnotM : ¬ Subgroup.normalizer (X : Set G) ≤ D.M)
    (hZbar : Subgroup.center (Bar2 L) = ⊥)
    (hX : LieModel (Bar2 L) .G2 0 p f)
    (htX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (htZ : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹)
    (hnot : ¬ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) : False := by
  classical
  have hZL : Z ≤ L := hZQ.trans hQL
  have hQX : ⁅Q, X⁆ = ⊥ := commutator_eq_bot_of_list864 h64 hnot hQP
  have hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x := by
    intro x hx z hz
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQX (hZQ hz)) x hx
  have hXneZ : X ≠ Z := by
    intro hEq
    apply hXnotM
    rw [hEq]
    exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hZU
  have hQE : ⁅Q, X ⊔ Z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mpr (sup_le
        (Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQX)) hZcentQ))
  have hEnorm : X ⊔ Z ≤ Subgroup.normalizer (L : Set G) := by
    have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLMle).mp hLM
    exact sup_le ((hXP.trans hPM).trans hMN) (hZL.trans Subgroup.le_normalizer)
  have hZnotle : ¬ Z ≤ centralizerBar (X ⊔ Z) L :=
    not_le_centralizerBar_of_center_bar_eq_bot hZbar hZL hZcard
      (le_sup_right : Z ≤ X ⊔ Z)
  have hX0card : Nat.card (centralizerBar (X ⊔ Z) L) = 3 :=
    card_centralizerBar_of_card_range hEnorm
      (card_sup_eq_nine_of_card_three_of_ne hXcard hZcard hXneZ hcomm)
      (card_range_eq_three_of_lieModel_g2_of_cq hCQ hp hp3 hp2f hX hQL hQsyl hQO2 hQZ hXcard
        hZcard hXneZ hcomm hEnorm hQE hZnotle)
  exact eight65_pointwise_false hZU hΓ hLMle hLM hQP hZQ hZcard hXcard h64 hXnotM
    hZbar hZL hX0card htX htZ hnot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
