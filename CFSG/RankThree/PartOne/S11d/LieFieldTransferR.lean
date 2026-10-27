module

public import CFSG.RankThree.PartOne.S11d.LieFieldTransfer
public import CFSG.RankThree.PartOne.S11d.ThreeCompAL

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCX
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

@[expose] def LieFieldOnComponentR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u → 2 ≤ CFSG.pRank p ↥J → ∀ d ∈ J, d ≠ 1 → d ^ p = 1 →
      u * d = d * u →
      ∀ D : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D →
        u ∈ Subgroup.normalizer (D : Set G) →
        FieldLike p u D ∧ ∃ t₁ ∈ D ⊓ Subgroup.centralizer ({u} : Set G),
          ∃ t₂ ∈ D ⊓ Subgroup.centralizer ({u} : Set G), (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
            (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

variable {G : Type} [Group G] [Finite G]

theorem lieFieldOnComponentR_of_tags (hOdd : OddCenterLie)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hHR : ∀ t, HighRankFalse t) (hA : ∀ t, ThreeCompAL t) : LieFieldOnComponentR := by
  intro G _ _ p J u hset hup hrank h2 d hdJ hd1 hdp hud D hD huD
  obtain ⟨hp, hp5, hq, hEven, hrk, hZ, hfa⟩ := hset
  obtain ⟨he, c, hcC, hc1, hcp, huc⟩ := hrank
  have hp2 : p ≠ 2 := by omega
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have huJ : u ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set α := centerQuotientConj J ⟨u, hu⟩ with hα
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := fieldAutT_of_inducesFieldAut hp hZ hu hup hfa
  have hLR2 := localRankLeTwo_of_evenRank he hp hp2 hZ hcC hc1 hcp
  have hLRA := localRankAut_of_evenRank he hp hp2 hZ hu hup huJ hcC hc1 hcp huc
  have hαp : α ^ p = 1 := centerQuotientConj_pow hu hup
  have hαinn : α ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q, hq'⟩
    exact huJ (mem_sup_of_inner hq.1 hu hq'.symm)
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J) :=
    hOdd ↥J hq t n (p * f₀) (by nlinarith) hM
  have hLow : LowRank t n := by
    by_contra hnl
    exact hHR t hGA ↥J p n f₀ hq hp hp5 hf₀ hZ2 hZ ((Sec9A.evenRank_subgroup_le J).trans he) hM hnl
  have h2T : 2 ≤ CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (Subgroup.center ↥J) hZ]
    exact h2
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  have hdJp : dJ ^ p = 1 := Subtype.ext hdp
  have hxp : (dJ : ↥J ⧸ Subgroup.center ↥J) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hdJp]
    rfl
  have hx1 : (dJ : ↥J ⧸ Subgroup.center ↥J) ≠ 1 := by
    intro h1
    apply hd1
    have hc : dJ ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff dJ).mp h1
    have h2' : orderOf (⟨dJ, hc⟩ : Subgroup.center ↥J) ∣ p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hdJp
    have h3 := _root_.orderOf_dvd_natCard (⟨dJ, hc⟩ : Subgroup.center ↥J)
    rcases (Nat.dvd_prime hp).mp h2' with h | h
    · rw [Subgroup.orderOf_mk] at h
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
    · rw [h] at h3
      exact absurd h3 hZ
  have hαx : α (dJ : ↥J ⧸ Subgroup.center ↥J) = (dJ : ↥J ⧸ Subgroup.center ↥J) := by
    rw [hα, centerQuotientConj_mk_apply]
    congr 1
    apply Subtype.ext
    show u * d * u⁻¹ = d
    rw [hud, mul_assoc, mul_inv_cancel, mul_one]
  have hDJ : D ≤ J := hD.1.trans inf_le_left
  have hDbar := isComponentOf_map_centerQuotient hp hZ hdJ hdp hD
  set D' : Subgroup ↥J := D.subgroupOf J with hD'
  set Dbar : Subgroup (↥J ⧸ Subgroup.center ↥J) := D'.map π with hDbardef
  have hstab : ∀ g ∈ Dbar, α g ∈ Dbar := by
    rintro _ ⟨g, hg, rfl⟩
    have hgD : (g : G) ∈ D := Subgroup.mem_subgroupOf.mp hg
    have hugD : u * (g : G) * u⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp huD (g : G)).mp hgD
    exact ⟨⟨u * (g : G) * u⁻¹, hDJ hugD⟩, Subgroup.mem_subgroupOf.mpr hugD,
      (centerQuotientConj_mk_apply hu g).symm⟩
  obtain ⟨hnon, ⟨t', n', f', hf', hmodel'⟩, t₁, ht₁, hα₁, t₂, ht₂, hα₂, ho₁, ho₂, hnc⟩ :=
    hA t _ p hp hp5 hLR2 h2T n f₀ hf₀ hM hLow α hαp hαinn hLRA hX _ hxp hx1 hαx Dbar hDbar hstab
  refine ⟨⟨huD, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro hmem
    obtain ⟨e₀, he₀, c', hc', hu'⟩ := exists_mul_of_mem_sup_centralizer_self D hmem
    refine hnon (π ⟨e₀, hDJ he₀⟩) ⟨⟨e₀, hDJ he₀⟩, Subgroup.mem_subgroupOf.mpr he₀, rfl⟩ ?_
    rintro _ ⟨g, hg, rfl⟩
    have hgD : (g : G) ∈ D := Subgroup.mem_subgroupOf.mp hg
    have hcg : (g : G) * c' = c' * (g : G) := (Subgroup.mem_centralizer_iff.mp hc') g hgD
    change centerQuotientConj J ⟨u, hu⟩ (g : ↥J ⧸ Subgroup.center ↥J) =
      ((⟨e₀, hDJ he₀⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) * (g : ↥J ⧸ Subgroup.center ↥J) *
        ((⟨e₀, hDJ he₀⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)⁻¹
    rw [centerQuotientConj_mk_apply hu g, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show u * (g : G) * u⁻¹ = e₀ * (g : G) * e₀⁻¹
    rw [hu']
    calc e₀ * c' * (g : G) * (e₀ * c')⁻¹ = e₀ * (c' * (g : G)) * c'⁻¹ * e₀⁻¹ := by group
      _ = e₀ * ((g : G) * c') * c'⁻¹ * e₀⁻¹ := by rw [hcg]
      _ = e₀ * (g : G) * e₀⁻¹ := by group
  · rw [hup]
    exact Subgroup.one_mem _
  ·
    have hD'q : CFSG.IsQuasisimple ↥D' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDJ).symm hD.2.1
    let f : ↥D' →* ↥Dbar := (π.comp D'.subtype).codRestrict Dbar fun g => ⟨g, g.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    have hker : f.ker ≤ Subgroup.center ↥D' := by
      intro g hg
      have h1 : π (g : ↥J) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      have h2 : (g : ↥J) ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (Subgroup.mem_center_iff.mp h2 (h : ↥J))
    obtain ⟨e₂⟩ := nonempty_centerQuotientEquiv_of_surjective hD'q.1 f hf hker
    let e₁ : ↥D ≃* ↥D' := (Subgroup.subgroupOfEquivOfLe hDJ).symm
    let e₃ : ↥D ⧸ Subgroup.center ↥D ≃* ↥D' ⧸ Subgroup.center ↥D' :=
      QuotientGroup.congr (Subgroup.center ↥D) (Subgroup.center ↥D') e₁
        (Subgroup.map_center_eq e₁)
    exact ⟨t', n', f', hf', lieModel_of_mulEquiv (e₃.trans e₂).symm hmodel'⟩
  ·
    obtain ⟨g₁, hg₁D, hug₁, hg₁o, hg₁J, hg₁t⟩ :=
      exists_two_element_lift hp hZ hZ2 hu hup ht₁ hα₁ ho₁
    obtain ⟨g₂, hg₂D, hug₂, hg₂o, hg₂J, hg₂t⟩ :=
      exists_two_element_lift hp hZ hZ2 hu hup ht₂ hα₂ ho₂
    refine ⟨g₁, Subgroup.mem_inf.mpr ⟨hg₁D, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, g₂,
      Subgroup.mem_inf.mpr ⟨hg₂D, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hg₁o, hg₂o, ?_⟩
    · calc g₁ * u = u * g₁ * u⁻¹ * u := by rw [hug₁]
        _ = u * g₁ := by group
    · calc g₂ * u = u * g₂ * u⁻¹ * u := by rw [hug₂]
        _ = u * g₂ := by group
    · intro hcomm
      apply hnc
      rw [← hg₁t, ← hg₂t, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hcomm

end CFSG.RankThree.PartOne
