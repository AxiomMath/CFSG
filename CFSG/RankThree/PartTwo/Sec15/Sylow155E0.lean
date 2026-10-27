module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Core
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xQ
public import CFSG.RankThree.PartTwo.Sec15.Sylow155StepDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155E0

private theorem odd_orderOf_of_coprime' {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : Nat.Coprime 2 (Nat.card K)) {k : X} (hk : k ∈ K) : Odd (orderOf k) := by
  have h1 : orderOf k ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  exact Nat.coprime_two_left.mp (hK.coprime_dvd_right h1)

private theorem eq_one_of_odd_of_isPGroup' {X : Type} [Group X] {T : Subgroup X}
    (hT : IsPGroup 2 T) {t : X} (ht : t ∈ T) (hto : Odd (orderOf t)) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT ⟨t, ht⟩
  rw [Subgroup.orderOf_mk] at hn
  have hcop : Nat.Coprime (orderOf t) (2 ^ n) := (Nat.coprime_two_right.mpr hto).pow_right n
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (hn ▸ dvd_refl _))

private theorem fusionIsSylowIn_sup_of_coprime {X : Type} [Group X] [Finite X]
    {T K : Subgroup X} [K.Normal] (hT : IsPGroup 2 T) (hK : Nat.Coprime 2 (Nat.card K)) :
    CFSG.Open.fusionIsSylowIn 2 T (T ⊔ K) := by
  refine ⟨le_sup_left, hT, fun S hS hS2 hTS => le_antisymm (fun s hs => ?_) hTS⟩
  have hsTK : s ∈ ((T ⊔ K : Subgroup X) : Set X) := hS hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T K
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)] at hsTK
  obtain ⟨t, ht, k, hk, rfl⟩ := hsTK
  have hkS : k ∈ S := by
    have := S.mul_mem (S.inv_mem (hTS ht)) hs
    simpa using this
  show t * k ∈ T
  rw [eq_one_of_odd_of_isPGroup' hS2 hkS (odd_orderOf_of_coprime' hK hk), mul_one]
  exact ht

theorem le_layerOddPreimage_sup (hst : StellmacherKP) (hT4 : TheoremFourHyp G)
    {R V : Subgroup G} (hR2 : IsPGroup 2 R) (hsyl : CFSG.Open.fusionIsSylowIn 2 R V)
    (hV3 : ¬ 3 ∣ Nat.card V) :
    V ≤ layerOddPreimage V ⊔
      (V ⊓ Subgroup.normalizer (Sec16.Proof165.stellmacherSub R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRV : R ≤ V := hsyl.1
  set O : Subgroup ↥V := pPrimeCore 2 ↥V with hOdef
  have hOc : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  set π : ↥V →* ↥V ⧸ O := QuotientGroup.mk' O with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  obtain ⟨PV, hPV⟩ := Sec16.Proof165.sylow_of_fusionIsSylowIn hsyl
  set Sb : Sylow 2 (↥V ⧸ O) := PV.mapSurjective hπs with hSbdef
  have hSb : (Sb : Subgroup (↥V ⧸ O)) = (R.subgroupOf V).map π := by
    rw [hSbdef, Sylow.coe_mapSurjective, hPV]
  set Nb : Subgroup (↥V ⧸ O) :=
    Subgroup.normalizer
      (((Sb : Subgroup (↥V ⧸ O)) ⊓ layer (↥V ⧸ O) : Subgroup (↥V ⧸ O)) : Set (↥V ⧸ O))
    with hNbdef
  have hSz : S4Free.SzSections (↥V ⧸ O) := (hT4.szSections hst.2 hV3).quotient O
  have hchar : IsCharacteristicP 2 ↥Nb :=
    isCharacteristicP_normalizer_inf_layer_of_szSections
      (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two) hSz Sb
  have hSbN : (Sb : Subgroup (↥V ⧸ O)) ≤ Nb := sylow_le_normalizer_inf Sb
  have hmemS : ∀ r : ↥R, π (Subgroup.inclusion hRV r) ∈ (Sb : Subgroup (↥V ⧸ O)) := fun r => by
    rw [hSb]
    exact Subgroup.mem_map_of_mem π (show Subgroup.inclusion hRV r ∈ R.subgroupOf V from r.2)
  let ι : ↥R →* ↥Nb :=
    (π.comp (Subgroup.inclusion hRV)).codRestrict Nb fun r => hSbN (hmemS r)
  have hι : ∀ r : ↥R, ((ι r : ↥Nb) : ↥V ⧸ O) = π (Subgroup.inclusion hRV r) := fun _ => rfl
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).mpr fun r hr => ?_
    have hm : Subgroup.inclusion hRV r ∈ O := by
      rw [← hker, MonoidHom.mem_ker, ← hι, hr]
      rfl
    have ho : Odd (orderOf (r : G)) := by
      have h1 := odd_orderOf_of_coprime' hOc hm
      rw [← Subgroup.orderOf_coe, Subgroup.coe_inclusion] at h1
      exact h1
    exact Subtype.ext (eq_one_of_odd_of_isPGroup' hR2 r.2 ho)
  have hrange : ι.range = (Sb : Subgroup (↥V ⧸ O)).subgroupOf Nb := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf, hSb, Subgroup.mem_map]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨Subgroup.inclusion hRV r, r.2, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨⟨(v : G), hv⟩, Subtype.ext ?_⟩
      have hv' : Subgroup.inclusion hRV (⟨(v : G), hv⟩ : ↥R) = v := Subtype.ext rfl
      rw [hι, hv', hvx]
  have h3 : ¬ 3 ∣ Nat.card ↥Nb := fun h3 =>
    hV3 (h3.trans ((Subgroup.card_subgroup_dvd_card Nb).trans (Subgroup.card_quotient_dvd_card O)))
  have hCO : Subgroup.centralizer (S4Free.oTwo ↥Nb : Set ↥Nb) ≤ S4Free.oTwo ↥Nb := by
    rw [oTwo_eq_pCore]
    exact hchar
  have hadm : S4Free.IsAdmissibleHost ι :=
    S4Free.isAdmissibleHost_of_not_three_dvd h3 hinj
      ⟨Sb.subtype hSbN, by rw [Sylow.coe_subtype, hrange]⟩ hCO
  have hWN : ((S4Free.stellmacherWSz.{0, 0} ↥R).map ι).Normal :=
    S4Free.stellmacherWSz_normal hadm (hSz.subgroup Nb)
  have hWR : Sec16.Proof165.stellmacherSub R ≤ R := Subgroup.map_subtype_le _
  have hWV : Sec16.Proof165.stellmacherSub R ≤ V := hWR.trans hRV
  set W' : Subgroup ↥V := (Sec16.Proof165.stellmacherSub R).subgroupOf V with hW'def
  set Wb : Subgroup (↥V ⧸ O) := W'.map π with hWbdef
  have hWbN : Wb ≤ Nb := by
    refine le_trans ?_ hSbN
    rw [hSb, hWbdef, hW'def]
    exact Subgroup.map_mono (Subgroup.comap_mono hWR)
  have heq : (S4Free.stellmacherWSz.{0, 0} ↥R).map ι = Wb.subgroupOf Nb := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, hWbdef, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Subgroup.inclusion hRV s, ⟨s, hs, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨s, hs, hsv⟩, hvx⟩
      refine ⟨s, hs, Subtype.ext ?_⟩
      have hv' : Subgroup.inclusion hRV s = v := Subtype.ext hsv
      rw [hι, hv', hvx]
  have hNbW : Nb ≤ Subgroup.normalizer (Wb : Set (↥V ⧸ O)) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hWbN, ← heq]
    exact hWN
  set H1 : Subgroup ↥V := Nb.comap π with hH1def
  set E0' : Subgroup ↥V := (layer (↥V ⧸ O)).comap π with hE0'def
  have hOle : ∀ K : Subgroup (↥V ⧸ O), O ≤ K.comap π := fun K x hx => by
    have hx' : x ∈ π.ker := by rw [hker]; exact hx
    exact MonoidHom.ker_le_comap π K hx'
  have hH1D : H1 ≤ Subgroup.normalizer ((W' ⊔ O : Subgroup ↥V) : Set ↥V) := by
    have h1 : H1 ≤ (Subgroup.normalizer (Wb : Set (↥V ⧸ O))).comap π := Subgroup.comap_mono hNbW
    rwa [Subgroup.comap_normalizer_eq_of_surjective Wb hπs, hWbdef, Subgroup.comap_map_eq,
      hker] at h1
  have hDH1 : W' ⊔ O ≤ H1 := sup_le (Subgroup.map_le_iff_le_comap.mp hWbN) (hOle Nb)
  have hW'2 : IsPGroup 2 W' :=
    (hR2.to_le hWR).comap_of_injective V.subtype V.subtype_injective
  have hsylW : CFSG.Open.fusionIsSylowIn 2 W' (W' ⊔ O) := fusionIsSylowIn_sup_of_coprime hW'2 hOc
  have hfr1 : H1 ≤ (W' ⊔ O) ⊔ (H1 ⊓ Subgroup.normalizer (W' : Set ↥V)) :=
    Sylow155F.le_sup_inf_normalizer hsylW hDH1 hH1D
  have hEn : (layer (↥V ⧸ O)).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := ↥V ⧸ O)
    infer_instance
  obtain ⟨P0, hP0⟩ :=
    CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal Sb (layer (↥V ⧸ O))
  have hfr2 : Nb ⊔ layer (↥V ⧸ O) = ⊤ := by
    have := Sylow.normalizer_sup_eq_top P0
    rwa [hP0, Subgroup.subgroupOf_map_subtype] at this
  have htop' : H1 ⊔ E0' = ⊤ := by
    rw [hH1def, hE0'def, Subgroup.comap_sup_eq π Nb (layer (↥V ⧸ O)) hπs, hfr2,
      Subgroup.comap_top]
  have htop : (⊤ : Subgroup ↥V) ≤ H1 ⊔ E0' := htop'.ge
  have htop2 : (⊤ : Subgroup ↥V) ≤ E0' ⊔ Subgroup.normalizer (W' : Set ↥V) := by
    refine htop.trans (sup_le (hfr1.trans (sup_le (sup_le ?_ ?_) ?_)) le_sup_left)
    · exact le_sup_of_le_right Subgroup.le_normalizer
    · exact le_sup_of_le_left (hOle _)
    · exact le_sup_of_le_right inf_le_right
  have hmap : V ≤ (E0' ⊔ Subgroup.normalizer (W' : Set ↥V)).map V.subtype := fun v hv =>
    ⟨⟨v, hv⟩, htop2 (Subgroup.mem_top _), rfl⟩
  rw [Subgroup.map_sup] at hmap
  refine hmap.trans (sup_le_sup (le_of_eq rfl) (le_inf (Subgroup.map_subtype_le _) ?_))
  have h1 := Subgroup.le_normalizer_map (H := W') V.subtype
  rwa [hW'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWV] at h1

theorem layerOddPreimage_eq_bot_of_isCharacteristicP {V : Subgroup G}
    (hV : IsCharacteristicP 2 ↥V) : layerOddPreimage V = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 ↥V = ⊥ := pPrimeCore_eq_bot_of_isCharacteristicP _ 2 hV
  have hE : layer ↥V = ⊥ := layer_eq_bot_of_isCharacteristicP _ 2 hV
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 ↥V)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  let e : ↥V ≃* ↥V ⧸ pPrimeCore 2 ↥V :=
    MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 ↥V))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have hEq : layer (↥V ⧸ pPrimeCore 2 ↥V) = ⊥ := by
    have hmap := CFSG.WholeGroup.layer_map_mulEquiv e
    rw [hE, Subgroup.map_bot] at hmap
    exact hmap.symm
  rw [layerOddPreimage, hEq, MonoidHom.comap_bot, QuotientGroup.ker_mk', hO, Subgroup.map_bot]

theorem le_n155_of_layerOddPreimage_le (hst : StellmacherKP) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {X K Y M T P V : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P) (hV : V ∈ scriptQ A (lB A))
    (hsyl : CFSG.Open.fusionIsSylowIn 2 (CFSG.Open.pCoreOf 2 Y) V)
    (hE0 : layerOddPreimage V ≤ n155 A K) : V ≤ n155 A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hV3 : ¬ 3 ∣ Nat.card V := (isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.1.2.1
  obtain ⟨hCR, hCne, hNC, -⟩ := Sec16.Proof165.stellmacherSub_spec hst h.toTheoremFourHyp hR2
    (by rw [hRdef]; exact hC.isY.1.1.2)
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hC.isY.1.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hVW : V ⊓ Subgroup.normalizer (Sec16.Proof165.stellmacherSub R : Set G) ∈
      scriptQ A (lB A) :=
    mem_scriptQ_of_le hV inf_le_left
      (Late.le_normalizer_inf hV.1.2.2 ((hAR.trans hNC).trans Subgroup.le_normalizer))
  have hVWN : V ⊓ Subgroup.normalizer (Sec16.Proof165.stellmacherSub R : Set G) ≤ n155 A K :=
    (le_delta hVW inf_le_right).trans (hE.claim _ hCne hCR
      (Proof155Wx.stellmacherSub_subgroupOf_characteristic R))
  exact (le_layerOddPreimage_sup hst h.toTheoremFourHyp hR2 hsyl hV3).trans (sup_le hE0 hVWN)

theorem delta_sup_le_n155_of_e0 (hst : StellmacherKP)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hE0 : layerOddPreimage
      (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K) :
    delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤ n155 A K := by
  obtain ⟨hDH, -, -, hsyl⟩ := Sylow155B1.delta_host_facts h h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  exact le_n155_of_layerOddPreimage_le hst h hC hE hDH hsyl hE0

end Sylow155E0

theorem step155HostE0W_of_hostCharSup {A : Subgroup G} {c : G} {L : Subgroup G}
    (hHC : Step155HostCharSupW A c L) : Step155HostE0W A c L :=
  fun h X K Y M T P hC hmax hab hE h146 hRP hIX =>
    (Sylow155E0.layerOddPreimage_eq_bot_of_isCharacteristicP
      (hHC h X K Y M T P hC hmax hab hE h146 hRP hIX)).le.trans bot_le

end CFSG.RankThree.PartTwo.Sec15
