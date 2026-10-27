module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2ThreeCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_26a_threeCentral_of_K
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h17_20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V)
    (hK3 : Inputs1719.K_J2_threeCentral) (hJ2 : IsSpor (Bar2 L) .J2) :
    ∀ X : Subgroup G, X ≤ H17_25_one D V₀ V L c.hyp125.isElemAbelian →
      Nat.card X = 3 →
        ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L ∧
          X = CFSG.Quasithin.centerOf P := by
  classical
  intro X hXH hXcard
  have hV : IsElemAbelian 2 V := c.hyp125.isElemAbelian
  have hpair := c.hyp125.pairFacts
  obtain ⟨hm3, hN, -⟩ := h17_20 L c
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hnt : ¬ F08.Thin8 L := by
    intro ht
    have hm3' : Open.pRank 3 L = 2 := by
      rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
      exact hm3
    have h3 : Open.pRank 3 L ≤ 1 := ht 3 Nat.prime_three (by norm_num)
    rw [hm3'] at h3
    exact absurd h3 (by norm_num)
  have hL1 : barSub V₀ V hV L ≠ ⊥ :=
    barSub_ne_bot_of_not_thin c.hyp125 hC117 c.mem_calC hnt
  have h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 c.hyp125)
  have hXHle : X ≤ L ⊔ D.T := by
    refine hXH.trans ?_
    change preBarSub (L ⊔ D.T) V₀ V hV _ ≤ L ⊔ D.T
    exact inf_le_left
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) := D.sylowM.le.trans hMnorm
  have hXleL : X ≤ L := by
    intro x hx
    obtain ⟨k, hk⟩ := CFSG.GroupTheory.exists_pow_prime_pow_mem_of_mem_sup (p := 2)
      D.sylowM.isPGroup hTL (x := x) (hXHle hx)
    by_cases hx1 : x = 1
    · simpa [hx1] using L.one_mem
    have hxord3 : orderOf x ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard X hx
      rwa [hXcard] at h
    have hxord : orderOf x = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hxord3 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hpow : x ^ (2 ^ k) = x ^ (2 ^ k % 3) := by
      have h := pow_mod_orderOf x (2 ^ k)
      rw [hxord] at h
      exact h.symm
    rw [hpow] at hk
    have hmodne : 2 ^ k % 3 ≠ 0 := by
      intro h0
      have hdvd : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
      exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
    have hmodlt : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2) with h1 | h2'
    · rw [h1, pow_one] at hk
      exact hk
    · rw [h2'] at hk
      have hx2 : x ^ 2 ∈ L := hk
      have hx3 : x ^ 3 = 1 := by
        rw [← hxord]
        exact pow_orderOf_eq_one x
      have hx22 : (x ^ 2) ^ 2 = x := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, pow_one, one_mul]
      have hx4 : (x ^ 2) ^ 2 ∈ L := L.pow_mem hx2 2
      rw [hx22] at hx4
      exact hx4
  let φL : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLstab)).codRestrict _
      (fun x => actTil_mem_barSub V₀ V hV x.2 (hLstab x.2))
  have hφLsurj : Function.Surjective φL := by
    intro y
    obtain ⟨g, hgL, hgy⟩ :=
      (mem_barSub V₀ V hV L (y : MulAut (Vtil V₀ V hV))).1 y.2
    exact ⟨⟨g, hgL⟩, Subtype.ext hgy⟩
  have hKspor : IsSpor ↥(barSub V₀ V hV L) .J2 := by
    obtain ⟨e⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV hLstab h2 hL1 hsimple
    obtain ⟨eJ⟩ := hJ2
    exact ⟨e.symm.trans eJ⟩
  let S : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  let K : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (L ⊔ D.T)
  let SK : Subgroup (MulAut (Vtil V₀ V hV)) := S ⊓ K
  have hKY : K ≤ Y := barSub_mono V₀ V hV le_sup_left
  have hSY : S ≤ Y := barSub_mono V₀ V hV le_sup_right
  have hTstab : D.T ≤ stabTil V₀ V :=
    D.sylowM.le.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  have hYsup : Y = K ⊔ S := by
    change barSub V₀ V hV (L ⊔ D.T) = barSub V₀ V hV L ⊔ barSub V₀ V hV D.T
    exact s16c7_barSub_sup V₀ V hV hLstab hTstab
  have hKnormal : (K.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 ?_
    have hKMbar : K ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hLM
    have hSMbar : S ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV D.sylowM.le
    have hMbarN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (K : Set _) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKMbar).1
        (barSub_subgroupOf_mbar_normal hV hLM hMnorm)
    rw [hYsup]
    exact sup_le Subgroup.le_normalizer (hSMbar.trans hMbarN)
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 S Y := isSylowIn_barSub_T_sup c.hyp125 hLM
  have hSKsyl : CFSG.QuasithinUnique.IsSylowTwoOf SK K :=
    CFSG.Quasithin.E1.isSylowIn_two_iff.mp (hTsyl.inf_normal hKY hKnormal)
  have hcardK : Nat.card ↥K = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 :=
    CFSG.GH74.card_of_isSporadic_J2 hKspor
  have hSKne : SK ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card SK = 1 := (Subgroup.eq_bot_iff_card (H := SK)).mp hbot
    have hcardsub : Nat.card (SK.subgroupOf K) = Nat.card SK :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (show SK ≤ K from inf_le_right)).toEquiv
    have hmul := Subgroup.index_mul_card (H := SK.subgroupOf K)
    rw [hcardsub, hcard1, mul_one] at hmul
    exact hSKsyl.2.2 (by rw [hmul, hcardK]; norm_num)
  have hSKnormal : (SK.subgroupOf S).Normal := by
    have hSleN : S ≤ Subgroup.normalizer (SK : Set _) := by
      have h1 : S ≤ Subgroup.normalizer (K : Set _) :=
        hSY.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKY).1 hKnormal)
      have h2 : S ≤ Subgroup.normalizer (S : Set _) := Subgroup.le_normalizer
      have hSKcomm : SK = K ⊓ S := by
        rw [show SK = S ⊓ K from rfl, inf_comm]
      rw [hSKcomm]
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show SK ≤ S from inf_le_left)).2 hSleN
  have hS2 : IsPGroup 2 S := hTsyl.isPGroup
  have hSKsubne : SK.subgroupOf S ≠ ⊥ := by
    intro h
    apply hSKne
    have hmap := congrArg (Subgroup.map S.subtype) h
    rwa [Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le
      (show SK ≤ S from inf_le_left)] at hmap
  have hinf : (SK.subgroupOf S) ⊓ Subgroup.center ↥S ≠ ⊥ := by
    exact @Group.IsNilpotent.inf_center_ne_bot_of_normal ↥S _ hS2.isNilpotent
      (SK.subgroupOf S) hSKnormal hSKsubne
  obtain ⟨w, hw, hw1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hinf
  let c₀ : MulAut (Vtil V₀ V hV) := (w : ↥S)
  have hc₀SK : c₀ ∈ SK := Subgroup.mem_subgroupOf.mp hw.1
  have hc₀S : c₀ ∈ S := (show S ⊓ K ≤ S from inf_le_left) hc₀SK
  have hc₀cent : ∀ s ∈ S, c₀ * s = s * c₀ := by
    intro s hs
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw.2 ⟨s, hs⟩)).symm
  have hc₀ne : c₀ ≠ 1 := by
    intro h
    exact hw1 (Subtype.ext h)
  have hzpS : Subgroup.zpowers c₀ ≤ S := Subgroup.zpowers_le.mpr hc₀S
  have hzp2 : IsPGroup 2 (Subgroup.zpowers c₀) := hS2.to_le hzpS
  have hzpne : Subgroup.zpowers c₀ ≠ ⊥ := by
    intro h
    apply hc₀ne
    have : c₀ ∈ Subgroup.zpowers c₀ := Subgroup.mem_zpowers c₀
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have h2dvd : 2 ∣ Nat.card (Subgroup.zpowers c₀) := by
    rcases hzp2.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.eq_bot_iff_card _).2 h) hzpne
    · exact h
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers c₀)) 2 h2dvd
  let z : MulAut (Vtil V₀ V hV) := (u : MulAut (Vtil V₀ V hV))
  have hzS : z ∈ S := hzpS u.2
  have hzSK : z ∈ SK := Subgroup.zpowers_le.mpr hc₀SK u.2
  have hzK : z ∈ K := (show S ⊓ K ≤ K from inf_le_right) hzSK
  have hzcent : ∀ s ∈ S, z * s = s * z := by
    have hzp_cent : Subgroup.zpowers c₀ ≤ Subgroup.centralizer (S : Set _) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr (fun s hs => (hc₀cent s hs).symm)
    have hz_cent : z ∈ Subgroup.centralizer (S : Set _) := hzp_cent u.2
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp hz_cent s hs).symm
  have hzord : orderOf z = 2 := by
    rw [Subgroup.orderOf_coe]
    exact huord
  have hzordK : orderOf (⟨z, hzK⟩ : ↥K) = 2 := by
    simpa using hzord
  let gX : ↥X →* ↥K :=
    { toFun := fun x => φL ⟨x.1, hXleL x.2⟩
      map_one' := map_one φL
      map_mul' := by
        intro a b
        simpa using map_mul φL ⟨a.1, hXleL a.2⟩ ⟨b.1, hXleL b.2⟩ }
  let YX : Subgroup ↥K := (⊤ : Subgroup ↥X).map gX
  have hgXker : gX.ker = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hact1 : actTil V₀ V hV ⟨(x : G), hLstab (hXleL x.2)⟩ = 1 := by
        have h := congrArg Subtype.val hx
        dsimp only [gX, φL] at h
        exact h
      have hxP : (x : G) ∈ pCoreOf 2 L :=
        mem_pCoreOf_of_actTil_eq_one c.hyp125 c.mem_calC.1 hsimple hL1 (hXleL x.2)
          (hLstab (hXleL x.2)) hact1
      have hxord3 : orderOf (x : G) ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard X x.2
        rwa [hXcard] at h
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
      have hxord2 : orderOf (x : G) ∣ 2 ^ n := by
        rw [← hn]
        exact Subgroup.orderOf_dvd_natCard _ hxP
      have hgcd : Nat.gcd 3 (2 ^ n) = 1 := by
        have hcop : Nat.Coprime 3 (2 ^ n) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by
            intro hdvd
            exact (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdvd))
        exact hcop.gcd_eq_one
      have hdvd1 : orderOf (x : G) ∣ 1 := by
        rw [← hgcd]
        exact Nat.dvd_gcd hxord3 hxord2
      exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact map_one gX
  have hgXinj : Function.Injective gX := (MonoidHom.ker_eq_bot_iff gX).1 hgXker
  have hYXcard : Nat.card YX = 3 := by
    rw [Subgroup.card_map_of_injective hgXinj, Subgroup.card_top]
    exact hXcard
  have hYXle : YX ≤ Subgroup.centralizer
      ({(⟨z, hzK⟩ : ↥K)} : Set ↥K) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    obtain ⟨-, hxstab, hxact⟩ := (mem_preBarSub (L ⊔ D.T) V₀ V hV _).1 (hXH x.2)
    have hz_centS : z ∈ Subgroup.centralizer (S : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (hzcent s hs).symm
    have hz_center : (⟨z, hzS⟩ : ↥S) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext ((hzcent s s.2).symm)
    have hz_map : z ∈ (Subgroup.center S).map S.subtype :=
      ⟨⟨z, hzS⟩, hz_center, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hxact z hz_map
    have hφval : ((gX x : ↥K) : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV ⟨(x : G), hLstab (hXleL x.2)⟩ := rfl
    have hxval : actTil V₀ V hV ⟨(x : G), hxstab⟩ =
        actTil V₀ V hV ⟨(x : G), hLstab (hXleL x.2)⟩ :=
      congrArg (actTil V₀ V hV) (Subtype.ext rfl)
    simpa [hφval, hxval] using hcomm.symm
  have hSKsubsyl : CFSG.Quasithin.IsSylowIn 2 (SK.subgroupOf K) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hSKsyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    · rw [Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex] using hSKsyl.2.2
  have hzSKsub : (⟨z, hzK⟩ : ↥K) ∈ SK.subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr hzSK
  have hzcentK : ∀ y ∈ SK.subgroupOf K, (⟨z, hzK⟩ : ↥K) * y = y * ⟨z, hzK⟩ := by
    intro y hy
    apply Subtype.ext
    exact hzcent (y : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp hy).1
  have hK3app : ∃ P : Subgroup ↥K, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧
      YX = CFSG.Quasithin.centerOf P :=
    hK3 (X := ↥K) hKspor (SK.subgroupOf K) hSKsubsyl (⟨z, hzK⟩ : ↥K)
      hzSKsub hzcentK hzordK YX hYXle hYXcard
  obtain ⟨Q, hQsyl, hYXQ⟩ := hK3app
  let N : Subgroup ↥L := Q.comap φL
  have hXN : (X.subgroupOf L) ≤ N := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxQ : gX ⟨x, hx⟩ ∈ Q := by
      have hxY : gX ⟨x, hx⟩ ∈ YX := Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
      rw [hYXQ] at hxY
      exact hxY.1
    simpa [gX] using hxQ
  let XN : Subgroup ↥N := (X.subgroupOf L).subgroupOf N
  have hXNp : IsPGroup 3 XN := by
    have hcardXN : Nat.card XN = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleL).toEquiv]
      exact hXcard
    exact IsPGroup.of_card (n := 1) (by rw [hcardXN]; norm_num)
  obtain ⟨QN, hXNQN⟩ := hXNp.exists_le_sylow
  obtain ⟨QL, hQL⟩ := Sylow.exists_comap_subtype_eq QN
  let P : Subgroup G := (QL : Subgroup ↥L).map L.subtype
  refine ⟨P, ⟨QL, rfl⟩, ?_⟩
  let ψ : ↥N →* ↥Q :=
    { toFun := fun n => ⟨φL n.1, (Subgroup.mem_comap.mp n.2)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨l, hl⟩ := hφLsurj q.1
    refine ⟨⟨l, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap]
      rw [hl]
      exact q.2
    · apply Subtype.ext
      exact hl
  have hQNmap_top : (QN : Subgroup ↥N).map ψ = ⊤ := by
    have hdiv : ((QN : Subgroup ↥N).map ψ).index ∣ (QN : Subgroup ↥N).index :=
      Subgroup.index_map_dvd (QN : Subgroup ↥N) hψsurj
    have hnot : ¬ 3 ∣ ((QN : Subgroup ↥N).map ψ).index :=
      fun h => QN.not_dvd_index (h.trans hdiv)
    obtain ⟨n, hn⟩ := hQsyl.isPGroup.index ((QN : Subgroup ↥N).map ψ)
    have hn0 : n = 0 := by
      by_contra hn0
      exact hnot (by rw [hn]; exact dvd_pow_self 3 hn0)
    have hidx1 : ((QN : Subgroup ↥N).map ψ).index = 1 := by
      rw [hn, hn0, pow_zero]
    exact Subgroup.index_eq_one.mp hidx1
  have hQ_le : Q ≤ (QL : Subgroup ↥L).map φL := by
    intro q hq
    let qQ : ↥Q := ⟨q, hq⟩
    have hqtop : qQ ∈ (QN : Subgroup ↥N).map ψ := by
      rw [hQNmap_top]
      exact Subgroup.mem_top qQ
    obtain ⟨n, hnQN, hqn⟩ := Subgroup.mem_map.mp hqtop
    have hnQL : N.subtype n ∈ (QL : Subgroup ↥L) := by
      have := hnQN
      rw [← hQL] at this
      exact this
    refine Subgroup.mem_map.mpr ⟨N.subtype n, hnQL, ?_⟩
    have hqval : (ψ n : ↥Q).1 = qQ.1 := congrArg Subtype.val hqn
    exact hqval
  have hφQL : (QL : Subgroup ↥L).map φL = Q := by
    have hP3 : IsPGroup 3 ((QL : Subgroup ↥L).map φL) := QL.isPGroup'.map φL
    exact hQsyl.eq_of_le hQ_le le_top hP3
  have hφQL_mem : ∀ y : ↥L, y ∈ (QL : Subgroup ↥L) → φL y ∈ Q := by
    intro y hy
    have hy' : φL y ∈ (QL : Subgroup ↥L).map φL := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rwa [hφQL] at hy'
  have hXleP : X ≤ P := by
    intro x hx
    have hxL : (⟨x, hXleL hx⟩ : ↥L) ∈ N :=
      hXN (Subgroup.mem_subgroupOf.mpr hx)
    have hxN : (⟨⟨x, hXleL hx⟩, hxL⟩ : ↥N) ∈ (QN : Subgroup ↥N) :=
      hXNQN (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx))
    have hxQL : (⟨x, hXleL hx⟩ : ↥L) ∈ (QL : Subgroup ↥L) := by
      have h := hxN
      rw [← hQL] at h
      exact Subgroup.mem_comap.mp h
    exact Subgroup.mem_map.mpr ⟨⟨x, hXleL hx⟩, hxQL, rfl⟩
  have hxcentQ : ∀ (x : G) (hx : x ∈ X) (q : ↥K), q ∈ Q →
      gX ⟨x, hx⟩ * q = q * gX ⟨x, hx⟩ := by
    intro x hx q hq
    have hxY : gX ⟨x, hx⟩ ∈ YX :=
      Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    rw [hYXQ] at hxY
    obtain ⟨-, hxcentral⟩ := Subgroup.mem_inf.mp hxY
    exact (Subgroup.mem_centralizer_iff.mp hxcentral q hq).symm
  have hXleCenter : X ≤ CFSG.Quasithin.centerOf P := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hXleP hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨y, hyQL, rfl⟩ := Subgroup.mem_map.mp hp
    have hyQ : φL y ∈ Q := hφQL_mem y hyQL
    have hcommK : gX ⟨x, hx⟩ * φL y = φL y * gX ⟨x, hx⟩ :=
      hxcentQ x hx (φL y) hyQ
    have hxP : x ∈ P := hXleP hx
    have hyP : (y : G) ∈ P := Subgroup.mem_map.mpr ⟨y, hyQL, rfl⟩
    have hcommL : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (hXleL hx) y.2) (L.inv_mem (hXleL hx)))
        (L.inv_mem y.2)
    have hφcomm : φL ⟨x * (y : G) * x⁻¹ * (y : G)⁻¹, hcommL⟩ = 1 := by
      have hprod : (⟨x * (y : G) * x⁻¹ * (y : G)⁻¹, hcommL⟩ : ↥L) =
          (⟨x, hXleL hx⟩ : ↥L) * ⟨y, y.2⟩ * (⟨x, hXleL hx⟩ : ↥L)⁻¹ * ⟨y, y.2⟩⁻¹ := by
        ext
        simp [mul_assoc]
      rw [hprod, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h := hcommK
      rw [show gX ⟨x, hx⟩ = φL ⟨x, hXleL hx⟩ from rfl] at h
      rw [h]
      group
    have hact : actTil V₀ V hV ⟨x * (y : G) * x⁻¹ * (y : G)⁻¹, hLstab hcommL⟩ = 1 :=
      congrArg Subtype.val hφcomm
    have hcommO2 : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_actTil_eq_one c.hyp125 c.mem_calC.1 hsimple hL1 hcommL
        (hLstab hcommL) hact
    have hcommP : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem hxP)) (P.inv_mem hyP)
    have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P L := ⟨QL, rfl⟩
    have hP3 : IsPGroup 3 P := hPsyl.isPGroup
    have hO2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    have hdisj : Disjoint P (pCoreOf 2 L) :=
      IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP3 hO2
    have hbot : P ⊓ pCoreOf 2 L = ⊥ := hdisj.eq_bot
    have hmem : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ P ⊓ pCoreOf 2 L :=
      Subgroup.mem_inf.mpr ⟨hcommP, hcommO2⟩
    rw [hbot] at hmem
    have hcomm : x * (y : G) = (y : G) * x := by
      have h1 : x * (y : G) * x⁻¹ * (y : G)⁻¹ = 1 := Subgroup.mem_bot.mp hmem
      calc x * (y : G) = (x * (y : G) * x⁻¹ * (y : G)⁻¹) * ((y : G) * x) := by group
        _ = (y : G) * x := by rw [h1, one_mul]
    exact hcomm.symm
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P L := ⟨QL, rfl⟩
  have hP3 : IsPGroup 3 P := hPsyl.isPGroup
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hdisj : Disjoint P (pCoreOf 2 L) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP3 hO2
  have hbot : P ⊓ pCoreOf 2 L = ⊥ := hdisj.eq_bot
  have hφP_inj : ∀ a b : ↥P, φL ⟨a.1, hPsyl.le a.2⟩ = φL ⟨b.1, hPsyl.le b.2⟩ → a = b := by
    intro a b hab
    have hcommL : a.1 * b.1⁻¹ ∈ L :=
      L.mul_mem (hPsyl.le a.2) (L.inv_mem (hPsyl.le b.2))
    have hprod : (⟨a.1 * b.1⁻¹, hcommL⟩ : ↥L) =
        (⟨a.1, hPsyl.le a.2⟩ : ↥L) * (⟨b.1, hPsyl.le b.2⟩ : ↥L)⁻¹ := by
      ext
      simp
    have hφ1 : φL ⟨a.1 * b.1⁻¹, hcommL⟩ = 1 := by
      rw [hprod, map_mul, map_inv, hab, mul_inv_cancel]
    have hact : actTil V₀ V hV ⟨a.1 * b.1⁻¹, hLstab hcommL⟩ = 1 :=
      congrArg Subtype.val hφ1
    have hcommO2 : a.1 * b.1⁻¹ ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_actTil_eq_one c.hyp125 c.mem_calC.1 hsimple hL1 hcommL
        (hLstab hcommL) hact
    have hcommP : a.1 * b.1⁻¹ ∈ P := P.mul_mem a.2 (P.inv_mem b.2)
    have hmem : a.1 * b.1⁻¹ ∈ P ⊓ pCoreOf 2 L := Subgroup.mem_inf.mpr ⟨hcommP, hcommO2⟩
    rw [hbot] at hmem
    have h1 : a.1 * b.1⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    exact Subtype.ext (by
      have h := congrArg (fun z => z * b.1) h1
      simpa using h)
  have hcenterCard : Nat.card (CFSG.Quasithin.centerOf P) ≤ 3 := by
    let fC : ↥(CFSG.Quasithin.centerOf P) → ↥YX := fun z =>
      ⟨φL ⟨z.1, hPsyl.le (Subgroup.mem_inf.mp z.2).1⟩, by
        have hzP : z.1 ∈ P := (Subgroup.mem_inf.mp z.2).1
        have hzcent : z.1 ∈ Subgroup.centralizer (P : Set _) :=
          (Subgroup.mem_inf.mp z.2).2
        obtain ⟨y, hyQL, hyz⟩ := Subgroup.mem_map.mp hzP
        have hzQ : φL ⟨z.1, hPsyl.le hzP⟩ ∈ Q := by
          have hzL : (⟨z.1, hPsyl.le hzP⟩ : ↥L) = y := by
            ext
            exact hyz.symm
          rw [hzL]
          exact hφQL_mem y hyQL
        have hzcentQ : φL ⟨z.1, hPsyl.le hzP⟩ ∈
            Subgroup.centralizer (Q : Set _) := by
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          have hq' : q ∈ (QL : Subgroup ↥L).map φL := by
            rw [hφQL]
            exact hq
          obtain ⟨y', hyQL', hyq⟩ := Subgroup.mem_map.mp hq'
          have hy'P : (y' : G) ∈ P := Subgroup.mem_map.mpr ⟨y', hyQL', rfl⟩
          have hcommP := Subgroup.mem_centralizer_iff.mp hzcent (y' : G) hy'P
          have hcommL' : (⟨z.1, hPsyl.le hzP⟩ : ↥L) * y' =
              y' * ⟨z.1, hPsyl.le hzP⟩ := by
            apply Subtype.ext
            exact hcommP.symm
          have hcommK : φL ⟨z.1, hPsyl.le hzP⟩ * φL y' =
              φL y' * φL ⟨z.1, hPsyl.le hzP⟩ := by
            have h := congrArg φL hcommL'
            simpa [map_mul] using h
          rw [hyq] at hcommK
          exact hcommK.symm
        rw [hYXQ]
        exact Subgroup.mem_inf.mpr ⟨hzQ, hzcentQ⟩⟩
    have hinj : Function.Injective fC := by
      intro z₁ z₂ hz
      have hz' : φL ⟨z₁.1, hPsyl.le (Subgroup.mem_inf.mp z₁.2).1⟩ =
          φL ⟨z₂.1, hPsyl.le (Subgroup.mem_inf.mp z₂.2).1⟩ :=
        congrArg (fun w : ↥YX => (w : ↥K)) hz
      have hP := hφP_inj ⟨z₁.1, (Subgroup.mem_inf.mp z₁.2).1⟩
        ⟨z₂.1, (Subgroup.mem_inf.mp z₂.2).1⟩ hz'
      have hval : z₁.1 = z₂.1 := congrArg (fun w : ↥P => (w : G)) hP
      exact Subtype.ext hval
    have h := Nat.card_le_card_of_injective fC hinj
    simpa [hYXcard] using h
  exact Subgroup.eq_of_le_of_card_ge hXleCenter (by
    calc Nat.card (CFSG.Quasithin.centerOf P) ≤ 3 := hcenterCard
      _ = Nat.card X := hXcard.symm)


theorem gap17_26a_U_holds
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h17_20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V)
    (hK2 : K_J2_centralizer_shape) (hK3 : Inputs1719.K_J2_threeCentral) :
    Gap17_26a_U D V₀ V L c := by
  intro hm hJ2 hN h242 hfus X hXH hXp
  classical
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁def
  have hH1M : H₁ ≤ D.M := H17_25_one_le_M c.hyp125 c.mem_calC.1.le
  have hXH₁ : X ≤ H₁ := hXH
  have hshape := gap17_25_H1_shape_of D V₀ V h17_20 hC117 hK2 L c hJ2
  obtain ⟨p, hpp, hp2, hp5, hXcard⟩ := hXp
  have hpdvdH : p ∣ Nat.card ↥H₁ := hXcard ▸ Subgroup.card_dvd_of_le hXH₁
  have hcardH : Nat.card ↥H₁ = Nat.card (Bar2 H₁) * Nat.card (CFSG.pCore 2 ↥H₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H₁)
  have hbar : Nat.card (Bar2 H₁) = 60 ∨ Nat.card (Bar2 H₁) = 120 := by
    rcases hshape with h | h
    · obtain ⟨e⟩ := h
      left
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    · obtain ⟨e⟩ := h
      right
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
  have hpBar : p ∣ Nat.card (Bar2 H₁) := by
    rw [hcardH] at hpdvdH
    rcases hpp.dvd_mul.mp hpdvdH with h | h
    · exact h
    · exfalso
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥H₁))
      have hdvd : p ∣ 2 ^ n := by rw [← hn]; exact h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
        (hpp.dvd_of_dvd_pow hdvd))
  have hp3 : p = 3 := by
    have hdvd : p ∣ 60 ∨ p ∣ 120 := by
      rcases hbar with h | h
      · exact Or.inl (h ▸ hpBar)
      · exact Or.inr (h ▸ hpBar)
    rcases hdvd with h | h
    · have h' : p ∣ 4 * 15 := by rw [show (4 : ℕ) * 15 = 60 by norm_num]; exact h
      rcases hpp.dvd_mul.mp h' with h4 | h15
      · have h4' : p ∣ 2 ^ 2 := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4
        exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
          (hpp.dvd_of_dvd_pow h4')) hp2
      · have h15' : p ∣ 3 * 5 := by rw [show (3 : ℕ) * 5 = 15 by norm_num]; exact h15
        rcases hpp.dvd_mul.mp h15' with h3 | h5
        · exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1 h5) hp5
    · have h' : p ∣ 8 * 15 := by rw [show (8 : ℕ) * 15 = 120 by norm_num]; exact h
      rcases hpp.dvd_mul.mp h' with h8 | h15
      · have h8' : p ∣ 2 ^ 3 := by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h8
        exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
          (hpp.dvd_of_dvd_pow h8')) hp2
      · have h15' : p ∣ 3 * 5 := by rw [show (3 : ℕ) * 5 = 15 by norm_num]; exact h15
        rcases hpp.dvd_mul.mp h15' with h3 | h5
        · exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1 h5) hp5
  have hX3 : Nat.card X = 3 := by rw [hXcard, hp3]
  obtain ⟨P, hP, hXP⟩ :=
    gap17_26a_threeCentral_of_K c h17_20 hC117 hK3 hJ2 X hXH hX3
  rw [hXP]
  obtain ⟨hNZ, hF⟩ := hfus P hP
  refine CFSG.LocalAnalysis.UniquenessCase.UC6.inU_of_normalizer_le_of_fusion
    (CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) ?_ hNZ ?_
  · exact Subgroup.le_normalizer.trans hNZ
  · intro g hg
    have hmem1 : CFSG.Open.uniqueFourConj g (CFSG.Quasithin.centerOf P) ∈
        CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf (⊤ : Subgroup G)
          (CFSG.Quasithin.centerOf P) := by
      refine ⟨g⁻¹, Subgroup.mem_top g⁻¹, ?_⟩
      rfl
    have hmem : CFSG.Open.uniqueFourConj g (CFSG.Quasithin.centerOf P) ∈
        CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf (⊤ : Subgroup G)
            (CFSG.Quasithin.centerOf P) ∩ {A : Subgroup G | A ≤ D.M} :=
      Set.mem_inter hmem1 hg
    rw [hF] at hmem
    obtain ⟨m, hmM, hmeq⟩ := hmem
    refine ⟨m⁻¹, D.M.inv_mem hmM, ?_⟩
    rw [hmeq]
    simp [CFSG.Open.uniqueFourConj]

theorem seventeen_twentysix_a_reduction_of_U
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    {D : Data G} {V₀ V : Subgroup G} (h20 : R17_20At D V₀ V) (h22 : R17_22At D V₀ V)
    (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V) (hSg : UC6S846.SigmaStd D)
    (h880 : F08.R880 D) (hJ2aut : K_J2_aut_five_rank) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h88 : W3Thm88 G) (h126 : R126 D) (h861 : W3Lem86_1 G)
    (h93 : ∀ L, Ctx17_17 D V₀ V L → CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (hNE : ∀ H₀, Gap17_26_NE D V₀ V H₀)
    (hJ2center : K_J2_center_five) (hC117 : C117 D V₀ V) (hK2 : K_J2_centralizer_shape)
    (hK3 : Inputs1719.K_J2_threeCentral)
    (hAlt : Gap17_26a_Alt D V₀ V) (hFirst : Gap17_26a_First D V₀ V) :
    R17_26aAt D V₀ V ∨ Config17_26a_II D V₀ V :=
  seventeen_twentysix_a_reduction hTim hcat D V₀ V h20 h22 h23 h25 hSg h880 hJ2aut h61 h66 h88
    h126 h861 h93 hNE hJ2center (fun L c => gap17_26a_U_holds c h20 hC117 hK2 hK3) hAlt
    hFirst

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
