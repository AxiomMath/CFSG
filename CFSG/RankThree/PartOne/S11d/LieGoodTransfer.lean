module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerTags
public import CFSG.RankThree.PartOne.S11d.LieComponentLift
public import CFSG.RankThree.PartOne.S11d.LayerDecomp
public import CFSG.RankThree.PartOne.S11d.FiveClaimAux

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

variable {G : Type} [Group G]

theorem isComponentOf_map_subtype {J : Subgroup G} {d : G} (hdJ : d ∈ J) {Dt : Subgroup ↥J}
    (hq : CFSG.IsQuasisimple ↥Dt)
    (hle : Dt ≤ Subgroup.centralizer ({(⟨d, hdJ⟩ : ↥J)} : Set ↥J))
    (hsub : (Dt.subgroupOf (Subgroup.centralizer ({(⟨d, hdJ⟩ : ↥J)} : Set ↥J))).IsSubnormal) :
    IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) (Dt.map J.subtype) := by
  set Cj : Subgroup ↥J := Subgroup.centralizer ({(⟨d, hdJ⟩ : ↥J)} : Set ↥J) with hCj
  set X : Subgroup G := J ⊓ Subgroup.centralizer ({d} : Set G) with hX
  set D : Subgroup G := Dt.map J.subtype with hD
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hyC := hle hy
    rw [hCj, Subgroup.mem_centralizer_singleton_iff] at hyC
    exact congrArg Subtype.val hyC
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective Dt J.subtype J.subtype_injective) hq
  · have hXCj : ∀ x : ↥X, Subgroup.inclusion (inf_le_left : X ≤ J) x ∈ Cj := by
      intro x
      rw [hCj, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
    let jX : ↥X →* ↥Cj := (Subgroup.inclusion (inf_le_left : X ≤ J)).codRestrict Cj hXCj
    have hH : D.subgroupOf X = (Dt.subgroupOf Cj).comap jX := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hD, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = Subgroup.inclusion (inf_le_left : X ≤ J) x := Subtype.ext hyx
        change Subgroup.inclusion (inf_le_left : X ≤ J) x ∈ Dt
        rw [← this]
        exact hy
      · intro hx
        exact ⟨Subgroup.inclusion (inf_le_left : X ≤ J) x, hx, rfl⟩
    rw [hH]
    exact hsub.comap jX

omit [Group G] in
theorem mem_of_two_power_of_map_mem {Γ Q : Type*} [Group Γ] [Group Q] (π : Γ →* Q)
    (hker : π.ker ≤ Subgroup.center Γ) (hodd : ¬ 2 ∣ Nat.card (Subgroup.center Γ))
    {H : Subgroup Γ} {g : Γ} (hk : ∃ k : ℕ, orderOf g = 2 ^ k) (hg : π g ∈ H.map π) :
    g ∈ H := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨h, hH, hπ⟩ := hg
  have hz : h⁻¹ * g ∈ Subgroup.center Γ :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel])
  set z : Γ := h⁻¹ * g with hzdef
  have hgh : g = h * z := by rw [hzdef, mul_inv_cancel_left]
  have hzord : orderOf z ∣ Nat.card (Subgroup.center Γ) := by
    have := _root_.orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center Γ)
    rwa [Subgroup.orderOf_mk] at this
  have hzcomm : Commute h z := Subgroup.mem_center_iff.mp hz h
  have hZodd : Odd (Nat.card (Subgroup.center Γ)) := Nat.odd_iff.mpr (by omega)
  have hrodd : Odd (orderOf z) := Odd.of_dvd_nat hZodd hzord
  have hr2 : Nat.Coprime (orderOf z) (orderOf g) := by
    rw [hk]
    exact (Odd.coprime_two_right hrodd).pow_right k
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hr2
  have hzr : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have h1 : g ^ orderOf z = h ^ orderOf z := by
    rw [hgh, hzcomm.mul_pow, hzr, mul_one]
  rw [← hm, h1]
  exact H.pow_mem (H.pow_mem hH _) m

variable [Finite G]

theorem fieldLike_pair_of_quotient {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J)) (hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J))
    {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1) {d : G} (hdJ : d ∈ J)
    (hdp : d ^ p = 1) {D : Subgroup G}
    (hD : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D)
    (huD : u ∈ Subgroup.normalizer (D : Set G))
    (hT : ∀ Dbar : Subgroup (↥J ⧸ Subgroup.center ↥J),
      IsComponentOf (Subgroup.centralizer ({((⟨d, hdJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)} :
        Set (↥J ⧸ Subgroup.center ↥J))) Dbar →
      (∀ g ∈ Dbar, centerQuotientConj J ⟨u, hu⟩ g ∈ Dbar) →
        (∀ e ∈ Dbar, ¬ ∀ g ∈ Dbar, centerQuotientConj J ⟨u, hu⟩ g = e * g * e⁻¹) ∧
        (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
          LieModel (↥Dbar ⧸ Subgroup.center ↥Dbar) t' n' 2 (p * f')) ∧
        ∃ t₁ ∈ Dbar, centerQuotientConj J ⟨u, hu⟩ t₁ = t₁ ∧ ∃ t₂ ∈ Dbar,
          centerQuotientConj J ⟨u, hu⟩ t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
          (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) :
    FieldLike p u D ∧ ∃ t₁ ∈ D ⊓ Subgroup.centralizer ({u} : Set G),
      ∃ t₂ ∈ D ⊓ Subgroup.centralizer ({u} : Set G), (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
        (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set α := centerQuotientConj J ⟨u, hu⟩ with hα
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
    hT Dbar hDbar hstab
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

omit [Finite G] in
theorem mem_layer_of_map_mem_layer {J : Subgroup G}
    (hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J))
    {d : G} (hdJ : d ∈ J) {g : G} (hgJ : g ∈ J)
    (hgo : ∃ k : ℕ, orderOf g = 2 ^ k)
    (hg : ((⟨g, hgJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) ∈
      inSubgroup layer (Subgroup.centralizer
        ({((⟨d, hdJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)} : Set (↥J ⧸ Subgroup.center ↥J)))) :
    g ∈ inSubgroup layer (J ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥J := by rw [hπdef, QuotientGroup.ker_mk']
  set M : Subgroup G := inSubgroup layer (J ⊓ Subgroup.centralizer ({d} : Set G)) with hM
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  have hle : inSubgroup layer (Subgroup.centralizer
        ({((⟨d, hdJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)} : Set (↥J ⧸ Subgroup.center ↥J))) ≤
      (M.subgroupOf J).map π := by
    rw [inSubgroup_layer_eq_sSup]
    refine sSup_le fun Ebar hEbar => ?_
    obtain ⟨hq', hcent', hsub', hmapπ⟩ := exists_lift_component (A := dJ) hπ hker hEbar.2.1
      hEbar.1 hEbar.2.2
    have hcomp : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G))
        ((derivedPreimage π Ebar).map J.subtype) := isComponentOf_map_subtype hdJ hq' hcent' hsub'
    have hEM : (derivedPreimage π Ebar).map J.subtype ≤ M := by
      rw [hM, inSubgroup_layer_eq_sSup]
      exact le_sSup hcomp
    have hDt : derivedPreimage π Ebar ≤ M.subgroupOf J := fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hEM ⟨y, hy, rfl⟩)
    rw [← hmapπ]
    exact Subgroup.map_mono hDt
  have hgM : (⟨g, hgJ⟩ : ↥J) ∈ M.subgroupOf J :=
    mem_of_two_power_of_map_mem π hker hZ2 (by
      obtain ⟨k, hk⟩ := hgo
      exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩) (hle hg)
  exact Subgroup.mem_subgroupOf.mp hgM

theorem lieGoodComponent_of_tags (hOdd : OddCenterLie)
    (hT : ∀ t, LieGoodComponentFixT t) : LieGoodComponent := by
  intro G _ _ p J u hset hup hrank hpr d hdJ hd1 hdp hud ⟨s, hsmem, hs2⟩
  obtain ⟨hp, hp5, hq, hEven, hrk, hZ, hfa⟩ := hset
  obtain ⟨he, c, hcC, hc1, hcp, huc⟩ := hrank
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have huJ : u ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥J := by rw [hπdef, QuotientGroup.ker_mk']
  set α := centerQuotientConj J ⟨u, hu⟩ with hα
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := fieldAutT_of_inducesFieldAut hp hZ hu hup hfa
  have hLR2 := localRankLeTwo_of_evenRank he hp hp2 hZ hcC hc1 hcp
  have hLRA := localRankAut_of_evenRank he hp hp2 hZ hu hup huJ hcC hc1 hcp huc
  have hαp : α ^ p = 1 := centerQuotientConj_pow hu hup
  have hαinn : α ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q', hq'⟩
    exact huJ (mem_sup_of_inner hq.1 hu hq'.symm)
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J) :=
    hOdd ↥J hq t n (p * f₀) (by nlinarith) hM
  have hprT : CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) = 1 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (Subgroup.center ↥J) hZ]
    exact hpr
  have hsC : s ∈ J ∧ s ∈ Subgroup.centralizer ({d} : Set G) := Subgroup.mem_inf.mp hsmem
  have hsd : s * d = d * s := Subgroup.mem_centralizer_singleton_iff.mp hsC.2
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  set sJ : ↥J := ⟨s, hsC.1⟩ with hsJdef
  have hdJp : dJ ^ p = 1 := Subtype.ext hdp
  have hsJ2 : orderOf sJ = 2 := by
    rw [← Subgroup.orderOf_coe sJ]
    exact hs2
  have hsJsq : sJ ^ 2 = 1 := by
    have := pow_orderOf_eq_one sJ
    rwa [hsJ2] at this
  have hy1 : π sJ ≠ 1 := by
    intro h1
    have hc : sJ ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff sJ).mp h1
    have h2 := _root_.orderOf_dvd_natCard (⟨sJ, hc⟩ : Subgroup.center ↥J)
    rw [Subgroup.orderOf_mk, hsJ2] at h2
    exact hZ2 h2
  have hxy : π dJ * π sJ = π sJ * π dJ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hsd.symm)
  have hx1 : π dJ ≠ 1 := by
    intro h1
    apply hd1
    have hc : dJ ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff dJ).mp h1
    have h2 : orderOf (⟨dJ, hc⟩ : Subgroup.center ↥J) ∣ p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hdJp
    have h3 := _root_.orderOf_dvd_natCard (⟨dJ, hc⟩ : Subgroup.center ↥J)
    rcases (Nat.dvd_prime hp).mp h2 with h | h
    · rw [Subgroup.orderOf_mk] at h
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
    · rw [h] at h3
      exact absurd h3 hZ
  have hαx : α (π dJ) = π dJ := by
    rw [hα]
    change centerQuotientConj J ⟨u, hu⟩ (dJ : ↥J ⧸ Subgroup.center ↥J) =
      (dJ : ↥J ⧸ Subgroup.center ↥J)
    rw [centerQuotientConj_mk_apply]
    congr 1
    apply Subtype.ext
    show u * d * u⁻¹ = d
    rw [hud, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨hex, hall, hlay⟩ := hT t _ p hp hp5 hLR2 hprT n f₀ hf₀ hM α hαp hαinn hLRA hX
    (π dJ) (by rw [← map_pow, hdJp, map_one]) hx1 hαx (π sJ)
    (by rw [← map_pow, hsJsq, map_one]) hy1 hxy
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨D₀, hcent, hq₀, hsub⟩ := hex
    exact exists_isComponentOf_of_quotient π hπ hker hp hZ hdJ hdp hq₀ hcent hsub
  ·
    intro D hD
    have hYn : u ∈ Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
        Set G) := mem_normalizer_inf_centralizer hu hud
    have hcord : ∃ k : ℕ, orderOf u = p ^ k := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hup) with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    have heC : evenRank ↥((J ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Subgroup.zpowers u) ≤ 3 :=
      (Sec9A.evenRank_subgroup_le _).trans he
    have hDu : u ∈ Subgroup.normalizer (D : Set G) :=
      normalizes_component hp hp3 hYn hcord heC hD
    exact fieldLike_pair_of_quotient hp hZ hZ2 hu hup hdJ hdp hD hDu hall
  ·
    intro g hg hgo
    obtain ⟨hgJu, hgd⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgJ, hgu⟩ := Subgroup.mem_inf.mp hgJu
    have hgd' : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hgd
    have hgu' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgu
    set gJ : ↥J := ⟨g, hgJ⟩ with hgJdef
    have hgC : π gJ ∈ Subgroup.centralizer ({π dJ} : Set (↥J ⧸ Subgroup.center ↥J)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hgd')
    have hgα : α (π gJ) = π gJ := by
      change centerQuotientConj J ⟨u, hu⟩ (gJ : ↥J ⧸ Subgroup.center ↥J) =
        (gJ : ↥J ⧸ Subgroup.center ↥J)
      rw [centerQuotientConj_mk_apply]
      congr 1
      apply Subtype.ext
      show u * g * u⁻¹ = g
      rw [← hgu', mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨k, hk⟩ := hgo
    have hgJo : orderOf gJ = 2 ^ k := by rw [hgJdef, Subgroup.orderOf_mk]; exact hk
    have hg2 : ∃ k : ℕ, orderOf (π gJ) = 2 ^ k := by
      have h1 : orderOf (π gJ) ∣ 2 ^ k := hgJo ▸ orderOf_map_dvd π gJ
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      exact ⟨b, hb⟩
    exact mem_layer_of_map_mem_layer hZ2 hdJ hgJ ⟨k, hk⟩ (hlay (π gJ) hgC hgα hg2)

end CFSG.RankThree.PartOne
