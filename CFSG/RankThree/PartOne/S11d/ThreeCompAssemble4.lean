module

public import CFSG.RankThree.PartOne.S11d.LieFieldTransferR
public import CFSG.RankThree.PartOne.S11d.Facts3
public import CFSG.RankThree.PartOne.S11d.LieGoodTransfer
public import CFSG.RankThree.PartOne.S11d.ThreeCompAssemble
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCX

variable {G : Type} [Group G] [Finite G]

theorem threeSideLR (hOdd : OddCenterLie) (hF : ∀ t, TagFixedFacts t)
    (hBt : ∀ t, ThreeCompBL t) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hHR : ∀ t, HighRankFalse t) (hTE : TwoExcPair) (hLF : LieFieldOnComponentR) {p : ℕ}
    {J : Subgroup G} {u : G}
    (hset : FieldAutSetting p J u) (hup : u ^ p = 1) (hrank : FieldAutRank p J u)
    (h2 : 2 ≤ CFSG.pRank p ↥J) {d : G} (hdJ : d ∈ J) (hd1 : d ≠ 1) (hdp : d ^ p = 1)
    (hud : u * d = d * u)
    (hS : ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      u ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) :
    ∃ K : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) K ∧
      u ∈ Subgroup.normalizer (K : Set G) ∧
      (∀ g ∈ J ⊓ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({d} : Set G),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ K) ∧
      ∃ g₁ ∈ K ⊓ Subgroup.centralizer ({u} : Set G),
        ∃ g₂ ∈ K ⊓ Subgroup.centralizer ({u} : Set G),
          (∃ k : ℕ, orderOf g₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf g₂ = 2 ^ k) ∧ g₁ * g₂ ≠ g₂ * g₁ ∧
          g₁ ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) := by
  classical
  have hset0 := hset
  have hrank0 := hrank
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hset.2.2.2.2.2.2.1
  have hFF := fixedFacts_of_fieldAutSetting hF hset hu hup hrank
  obtain ⟨hp, hp5, hq, hEven, hrk, hZ, hfa⟩ := hset
  obtain ⟨he, c, hcC, hc1, hcp, huc⟩ := hrank
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
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
  have hLow : LowRank t n := by
    by_contra hnl
    exact hHR t hGA ↥J p n f₀ hq hp hp5 hf₀ hZ2 hZ ((Sec9A.evenRank_subgroup_le J).trans he) hM hnl
  have h2T : 2 ≤ CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (Subgroup.center ↥J) hZ]
    exact h2
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  have hdJp : dJ ^ p = 1 := Subtype.ext hdp
  have hxp : (π dJ) ^ p = 1 := by rw [← map_pow, hdJp, map_one]
  have hx1 : π dJ ≠ 1 := by
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
  have hαx : α (π dJ) = π dJ := by
    rw [hα]
    change centerQuotientConj J ⟨u, hu⟩ (dJ : ↥J ⧸ Subgroup.center ↥J) =
      (dJ : ↥J ⧸ Subgroup.center ↥J)
    rw [centerQuotientConj_mk_apply]
    congr 1
    apply Subtype.ext
    show u * d * u⁻¹ = d
    rw [hud, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨S, hSJ, hS1, hS2, hSu, hSd⟩ := hS
  set Sb : Subgroup (↥J ⧸ Subgroup.center ↥J) := (S.subgroupOf J).map π with hSb
  have hSb1 : Sb ≠ ⊥ := by
    obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS1
    let sJ : ↥J := ⟨(s : G), hSJ s.2⟩
    have hsJS : sJ ∈ S.subgroupOf J := s.2
    intro hbot
    have hmem : π sJ ∈ Sb := ⟨sJ, hsJS, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hc : sJ ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff sJ).mp hmem
    obtain ⟨k, hk⟩ := hS2 s
    have hsJk : sJ ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2' : orderOf (⟨sJ, hc⟩ : Subgroup.center ↥J) ∣ 2 ^ k := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hsJk
    have h3 := _root_.orderOf_dvd_natCard (⟨sJ, hc⟩ : Subgroup.center ↥J)
    have hcop : Nat.Coprime (orderOf (⟨sJ, hc⟩ : Subgroup.center ↥J)) 2 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h => hZ2 ?_)
      exact h.trans h3
    have hord1 : orderOf (⟨sJ, hc⟩ : Subgroup.center ↥J) = 1 := by
      have := Nat.Coprime.eq_one_of_dvd (hcop.pow_right k) h2'
      exact this
    have hsJ1 : sJ = 1 := by
      have := orderOf_eq_one_iff.mp hord1
      exact congrArg Subtype.val this
    have hsG : ((sJ : ↥J) : G) = 1 := congrArg Subtype.val hsJ1
    exact hs1 (Subtype.ext hsG)
  have hSb2 : IsPGroup 2 Sb := by
    rintro ⟨y, j, hj, rfl⟩
    obtain ⟨k, hk⟩ := hS2 ⟨(j : G), hj⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hjk : j ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    show (π j) ^ (2 ^ k) = 1
    rw [← map_pow, hjk, map_one]
  have hSbα : ∀ g ∈ Sb, α g ∈ Sb := by
    rintro _ ⟨j, hj, rfl⟩
    have hjS : (j : G) ∈ S := hj
    have hujS : u * (j : G) * u⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hSu (j : G)).mp hjS
    refine ⟨⟨u * (j : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu (j : G)).mp j.2⟩, hujS, ?_⟩
    exact (centerQuotientConj_mk_apply hu j).symm
  have hSbn : π dJ ∈ Subgroup.normalizer (Sb : Set (↥J ⧸ Subgroup.center ↥J)) := by
    refine mem_normalizer_of_conj_mem Sb ?_
    rintro _ ⟨j, hj, rfl⟩
    have hjS : (j : G) ∈ S := hj
    have hdjS : d * (j : G) * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hSd (j : G)).mp hjS
    refine ⟨dJ * j * dJ⁻¹, hdjS, ?_⟩
    simp
  obtain ⟨D, hD, hDα, hDfix⟩ := hBt t _ p hp hp5 hLR2 h2T n f₀ hf₀ hM hLow α hαp hαinn hLRA hX
    (π dJ)
    hxp hx1 hαx Sb hSb1 hSb2 hSbα hSbn
  obtain ⟨hq', hcent', hsub', hmapπ⟩ :=
    exists_lift_component (A := dJ) hπ hker hD.2.1 hD.1 hD.2.2
  set K : Subgroup G := (derivedPreimage π D).map J.subtype with hKdef
  have hKcomp : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) K :=
    isComponentOf_map_subtype hdJ hq' hcent' hsub'
  have hYn : u ∈ Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
      Set G) := mem_normalizer_inf_centralizer hu hud
  have hcord : ∃ k : ℕ, orderOf u = p ^ k := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hup) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have heC : evenRank ↥((J ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Subgroup.zpowers u) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans he
  have hKu : u ∈ Subgroup.normalizer (K : Set G) :=
    normalizes_component hp hp3 hYn hcord heC hKcomp
  have hKJ : K.subgroupOf J = derivedPreimage π D :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have hfixπ : ∀ g : G, ∀ hgJ : g ∈ J, g ∈ Subgroup.centralizer ({u} : Set G) →
      α (π ⟨g, hgJ⟩) = π ⟨g, hgJ⟩ := by
    intro g hgJ hgu
    have hgu' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgu
    change centerQuotientConj J ⟨u, hu⟩ ((⟨g, hgJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) =
      ((⟨g, hgJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)
    rw [centerQuotientConj_mk_apply]
    congr 1
    apply Subtype.ext
    show u * g * u⁻¹ = g
    rw [← hgu', mul_assoc, mul_inv_cancel, mul_one]
  have hπ2 : ∀ (gJ : ↥J), (∃ k : ℕ, orderOf gJ = 2 ^ k) → ∃ k : ℕ, orderOf (π gJ) = 2 ^ k := by
    rintro gJ ⟨k, hk⟩
    have h1 : orderOf (π gJ) ∣ 2 ^ k := hk ▸ orderOf_map_dvd π gJ
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨b, hb⟩
  have hcont : ∀ g ∈ J ⊓ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({d} : Set G),
      (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ K := by
    intro g hg hgo
    obtain ⟨hgJu, hgd⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgJ, hgu⟩ := Subgroup.mem_inf.mp hgJu
    have hgd' : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hgd
    set gJ : ↥J := ⟨g, hgJ⟩ with hgJdef
    have hgC : π gJ ∈ Subgroup.centralizer ({π dJ} : Set (↥J ⧸ Subgroup.center ↥J)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hgd')
    have hgα : α (π gJ) = π gJ := hfixπ g hgJ hgu
    obtain ⟨k, hk⟩ := hgo
    have hgJo : orderOf gJ = 2 ^ k := by rw [hgJdef, Subgroup.orderOf_mk]; exact hk
    have hgD : π gJ ∈ D := hDfix _ hgC hgα (hπ2 gJ ⟨k, hgJo⟩)
    have hgK : gJ ∈ derivedPreimage π D :=
      mem_of_two_power_of_map_mem π hker hZ2 ⟨k, hgJo⟩ (by rw [hmapπ]; exact hgD)
    exact ⟨gJ, hgK, rfl⟩
  have hpairJ : ∃ g₁ ∈ K ⊓ Subgroup.centralizer ({u} : Set G),
      ∃ g₂ ∈ K ⊓ Subgroup.centralizer ({u} : Set G),
        (∃ k : ℕ, orderOf g₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf g₂ = 2 ^ k) ∧ g₁ * g₂ ≠ g₂ * g₁ ∧
        g₁ ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rcases hFF.twoElements with h | hTw
    ·
      obtain ⟨-, g₁, hg₁, g₂, hg₂, ho₁, ho₂, hnc⟩ :=
        hLF G p J u hset0 hup hrank0 h2 d hdJ hd1 hdp hud K hKcomp hKu
      obtain ⟨hg₁K, hg₁C⟩ := Subgroup.mem_inf.mp hg₁
      have hg₁J : g₁ ∈ J := (Subgroup.mem_inf.mp (hKcomp.1 hg₁K)).1
      have hgα : α (π ⟨g₁, hg₁J⟩) = π ⟨g₁, hg₁J⟩ := hfixπ g₁ hg₁J hg₁C
      have hgo : ∃ k : ℕ, orderOf (⟨g₁, hg₁J⟩ : ↥J) = 2 ^ k := by
        obtain ⟨k, hk⟩ := ho₁
        exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
      have hπR : π ⟨g₁, hg₁J⟩ ∈ fixRes α :=
        h _ (mem_fixSub.mpr hgα) (hπ2 _ hgo)
      obtain ⟨e, he', hee⟩ := exists_preimage_of_mem_fixRes hp hZ hu hup hπR
      have hg₁E : g₁ ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) := by
        obtain ⟨k, hk⟩ := hgo
        have hmem : (⟨g₁, hg₁J⟩ : ↥J) ∈ ((inSubgroup perfectResidual
            (J ⊓ Subgroup.centralizer ({u} : Set G))).subgroupOf J) :=
          mem_of_two_power_of_map_mem π hker hZ2 ⟨k, hk⟩
            ⟨⟨e, (Subgroup.mem_inf.mp (inSubgroup_perfectResidual_le_self _ he')).1⟩, he', hee⟩
        exact Subgroup.mem_subgroupOf.mp hmem
      exact ⟨g₁, hg₁, g₂, hg₂, ho₁, ho₂, hnc, hg₁E⟩
    ·
      obtain ⟨t₁, ht₁, hα₁, t₂, ht₂, hα₂, ho₁, ho₂, hnc⟩ :=
        hTE _ p hp hp5 hLR2 h2T hTw α hαp hαinn hLRA hFF.fieldAutT (π dJ) hxp hx1 hαx D hD hDα
      obtain ⟨ht₁D, ht₁R⟩ := Subgroup.mem_inf.mp ht₁
      obtain ⟨ht₂D, -⟩ := Subgroup.mem_inf.mp ht₂
      have ht₁K : t₁ ∈ (K.subgroupOf J).map π := by rw [hKJ, hmapπ]; exact ht₁D
      have ht₂K : t₂ ∈ (K.subgroupOf J).map π := by rw [hKJ, hmapπ]; exact ht₂D
      obtain ⟨g₁, hg₁K, hug₁, hg₁o, hg₁J, hg₁t⟩ :=
        exists_two_element_lift hp hZ hZ2 hu hup ht₁K hα₁ ho₁
      obtain ⟨g₂, hg₂K, hug₂, hg₂o, hg₂J, hg₂t⟩ :=
        exists_two_element_lift hp hZ hZ2 hu hup ht₂K hα₂ ho₂
      obtain ⟨e, he', hee⟩ := exists_preimage_of_mem_fixRes hp hZ hu hup ht₁R
      have hg₁E : g₁ ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) := by
        obtain ⟨k, hk⟩ := hg₁o
        have hgJo : orderOf (⟨g₁, hg₁J⟩ : ↥J) = 2 ^ k := by rw [Subgroup.orderOf_mk]; exact hk
        have hmem : (⟨g₁, hg₁J⟩ : ↥J) ∈ ((inSubgroup perfectResidual
            (J ⊓ Subgroup.centralizer ({u} : Set G))).subgroupOf J) :=
          mem_of_two_power_of_map_mem π hker hZ2 ⟨k, hgJo⟩
            ⟨⟨e, (Subgroup.mem_inf.mp (inSubgroup_perfectResidual_le_self _ he')).1⟩, he',
              hee.trans hg₁t.symm⟩
        exact Subgroup.mem_subgroupOf.mp hmem
      refine ⟨g₁, Subgroup.mem_inf.mpr ⟨hg₁K, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, g₂,
        Subgroup.mem_inf.mpr ⟨hg₂K, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hg₁o, hg₂o,
        ?_, hg₁E⟩
      · calc g₁ * u = u * g₁ * u⁻¹ * u := by rw [hug₁]
          _ = u * g₁ := by group
      · calc g₂ * u = u * g₂ * u⁻¹ * u := by rw [hug₂]
          _ = u * g₂ := by group
      · intro hcomm
        apply hnc
        rw [← hg₁t, ← hg₂t, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hcomm
  exact ⟨K, hKcomp, hKu, hcont, hpairJ⟩

theorem threeComponents_of_tagsLR (hOdd : OddCenterLie) (hF : ∀ t, TagFixedFacts t)
    (hBt : ∀ t, ThreeCompBL t) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hHR : ∀ t, HighRankFalse t) (hTE : TwoExcPair) (hR : FieldFixedRank)
    (hLF : LieFieldOnComponentR) : ThreeComponents := by
  intro G _ _ p J₁ J₂ u₁ u₂ hset₁ hset₂ hr₁ hr₂ hp₁ hp₂ h2 hl₁ hl₂ hE d hd₁ hd₂ hd1 hdp hud₁ hud₂
    hS₁ hS₂
  have hE₁ := hR G p J₁ u₁ hset₁ hp₁ hr₁ h2
  have h2₂ : 2 ≤ CFSG.pRank p ↥J₂ := by
    refine hE₁.trans ?_
    rw [hE]
    exact CFSG.RankThree.PartOne.OddCore37.pRank_le_of_le hset₂.1
      ((inSubgroup_perfectResidual_le_self _).trans inf_le_left)
  obtain ⟨K₁, hK₁, hn₁, hc₁, g₁, hg₁, g₂, hg₂, ho₁, ho₂, hnc, hg₁E⟩ :=
    threeSideLR hOdd hF hBt hGA hHR hTE hLF hset₁ hp₁ hr₁ h2 hd₁ hd1 hdp hud₁ hS₁
  obtain ⟨K₂, hK₂, hn₂, hc₂, -⟩ :=
    threeSideLR hOdd hF hBt hGA hHR hTE hLF hset₂ hp₂ hr₂ h2₂ hd₂ hd1 hdp hud₂ hS₂
  have hg₁K₁ : g₁ ∈ K₁ := (Subgroup.mem_inf.mp hg₁).1
  have hg₂K₁ : g₂ ∈ K₁ := (Subgroup.mem_inf.mp hg₂).1
  have hg₁K₂ : g₁ ∈ K₂ := by
    refine hc₂ g₁ ?_ ho₁
    have hgE₂ : g₁ ∈ inSubgroup perfectResidual (J₂ ⊓ Subgroup.centralizer ({u₂} : Set G)) := by
      rw [← hE]
      exact hg₁E
    have hgJC := inSubgroup_perfectResidual_le_self _ hgE₂
    have hg₁d : g₁ ∈ Subgroup.centralizer ({d} : Set G) :=
      (Subgroup.mem_inf.mp (hK₁.1 hg₁K₁)).2
    exact Subgroup.mem_inf.mpr ⟨hgJC, hg₁d⟩
  have hFL₁ := (hLF G p J₁ u₁ hset₁ hp₁ hr₁ h2 d hd₁ hd1 hdp hud₁ K₁ hK₁ hn₁).1
  have hFL₂ := (hLF G p J₂ u₂ hset₂ hp₂ hr₂ h2₂ d hd₂ hd1 hdp hud₂ K₂ hK₂ hn₂).1
  refine ⟨K₁, K₂, hK₁, hK₂, hn₁, hn₂, hFL₁, hFL₂, g₁, hg₁K₂, hg₁K₁, ?_⟩
  intro hcen
  apply hnc
  have h := Subgroup.mem_center_iff.mp hcen ⟨g₂, hg₂K₁⟩
  exact (congrArg Subtype.val h).symm

end CFSG.RankThree.PartOne
