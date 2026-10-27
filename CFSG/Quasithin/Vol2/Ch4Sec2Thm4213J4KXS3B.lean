module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXS3A
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXSN
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXJ3
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXOT
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXS2

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open
open scoped CFSG.ASVolI.ChIJK

theorem exists_noncomm_of_quasisimple {K : Type} [Group K] (hK : CFSG.IsQuasisimple K) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hK.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem inspBM_le_centralizer {Γ : Type} [Group Γ] [Finite Γ]
    (hBM : CFSG.Quasithin.H13.Ch4.InspBM22Cover)
    (hQT : ∀ (X : Type) [Group X] [Finite X] (f : X →* Γ), Function.Injective f →
      CFSG.Quasithin.IsQuasithin X)
    (hKG : ∀ (X : Type) [Group X] [Finite X] (f : X →* Γ), Function.Injective f →
      CFSG.SectionRank.IsKGroupCat X)
    {KΓ Jc : Subgroup Γ} {r : Γ} (hr2 : r * r = 1) (hrN : r ∈ Subgroup.normalizer (Jc : Set Γ))
    (hJq : CFSG.IsQuasisimple ↥Jc) (hKJ : KΓ ≤ Jc)
    (hKq : CFSG.IsQuasisimple ↥KΓ)
    (hKr : KΓ ≤ Subgroup.centralizer ({r} : Set Γ))
    (hNr : Subgroup.centralizer ({r} : Set Γ) ≤ Subgroup.normalizer (KΓ : Set Γ))
    (hM22 : CFSG.Quasithin.IsSporadic .M22 (↥KΓ ⧸ Subgroup.center ↥KΓ)) :
    Jc ≤ Subgroup.centralizer ({r} : Set Γ) := by
  by_contra hnot
  set N : Subgroup Γ := Subgroup.normalizer (Jc : Set Γ) with hNdef
  have hJN : Jc ≤ N := Subgroup.le_normalizer
  have hKN : KΓ ≤ N := hKJ.trans hJN
  have hrN' : r ∈ N := hrN
  let rN : N := ⟨r, hrN'⟩
  have hrN2 : rN ^ 2 = 1 := by
    apply Subtype.ext
    simp only [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact hr2
  have hYnorm : (Jc.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).mpr le_rfl
  have hYq : CFSG.IsQuasisimple ↥(Jc.subgroupOf N) := isQuasisimple_subgroupOf hJN hJq
  have hinjY : Function.Injective ((N.subtype).comp (Jc.subgroupOf N).subtype) :=
    N.subtype_injective.comp (Jc.subgroupOf N).subtype_injective
  have hYqt : CFSG.Quasithin.IsQuasithin ↥(Jc.subgroupOf N) :=
    hQT _ ((N.subtype).comp (Jc.subgroupOf N).subtype) hinjY
  have hYk : CFSG.SectionRank.IsKGroupCat ↥(Jc.subgroupOf N) :=
    hKG _ ((N.subtype).comp (Jc.subgroupOf N).subtype) hinjY
  have hYr : ¬ Jc.subgroupOf N ≤ Subgroup.centralizer ({rN} : Set N) := by
    intro h
    apply hnot
    intro j hj
    have hjN : (⟨j, hJN hj⟩ : N) ∈ Jc.subgroupOf N := Subgroup.mem_subgroupOf.mpr hj
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hjN)
    have h2 := congrArg Subtype.val h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using h2)
  have hC : KΓ.subgroupOf N ≤ Jc.subgroupOf N ⊓ Subgroup.centralizer ({rN} : Set N) := by
    intro k hk
    have hkK : (k : Γ) ∈ KΓ := Subgroup.mem_subgroupOf.mp hk
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (hKJ hkK), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKr hkK)
  have hCsn : ((KΓ.subgroupOf N).subgroupOf
      (Jc.subgroupOf N ⊓ Subgroup.centralizer ({rN} : Set N))).IsSubnormal := by
    have hnorm : ((KΓ.subgroupOf N).subgroupOf
        (Jc.subgroupOf N ⊓ Subgroup.centralizer ({rN} : Set N))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC]
      intro y hy
      obtain ⟨_, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyr : (y : Γ) ∈ Subgroup.centralizer ({r} : Set Γ) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC)
        simpa using h2
      have hyK : (y : Γ) ∈ Subgroup.normalizer (KΓ : Set Γ) := hNr hyr
      rw [Subgroup.mem_normalizer_iff] at hyK
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hh := hyK (h : Γ)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hh
    exact Subgroup.Normal.isSubnormal hnorm
  have hCq : CFSG.IsQuasisimple ↥(KΓ.subgroupOf N) := isQuasisimple_subgroupOf hKN hKq
  have hM : CFSG.Quasithin.IsSporadic .M22
      (↥(KΓ.subgroupOf N) ⧸ Subgroup.center ↥(KΓ.subgroupOf N)) :=
    isSporadic_M22_subgroupOf hKN hM22
  exact hBM ↥N (Jc.subgroupOf N) rN hYnorm hYq hYqt hYk hrN2 hYr (KΓ.subgroupOf N) hC hCsn hCq hM

theorem step3_component {Γ : Type} [Group Γ] [Finite Γ] {KΓ : Subgroup Γ} {r z : Γ}
    (hKq : CFSG.IsQuasisimple ↥KΓ) (hKz : Nat.card ↥(Subgroup.center ↥KΓ) = 6)
    (E0 : Subgroup (↥KΓ ⧸ Subgroup.center ↥KΓ)) (hE0 : IsElemAbelian 3 E0)
    (hE0c : Nat.card E0 = 9)
    (hM22 : CFSG.Quasithin.IsSporadic .M22 (↥KΓ ⧸ Subgroup.center ↥KΓ))
    (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrK : ∀ k ∈ KΓ, r * k = k * r)
    (hNr : Subgroup.centralizer ({r} : Set Γ) ≤ Subgroup.normalizer (KΓ : Set Γ))
    (hOcen : ∀ o ∈ CFSG.oddCore Γ, ∀ k ∈ KΓ, o * k = k * o)
    (hzKX : z ∈ KΓ) (hzc : ∀ k ∈ KΓ, z * k = k * z)
    (hpz : CFSG.Open.pRank 3 (Subgroup.centralizer ({z} : Set Γ)) ≤ 2)
    (hBM : CFSG.Quasithin.H13.Ch4.InspBM22Cover)
    (hQT : ∀ (X : Type) [Group X] [Finite X] (f : X →* Γ), Function.Injective f →
      CFSG.Quasithin.IsQuasithin X)
    (hKG : ∀ (X : Type) [Group X] [Finite X] (f : X →* Γ), Function.Injective f →
      CFSG.SectionRank.IsKGroupCat X) :
    CFSG.Open.IsComponentOf KΓ ⊤ := by
  classical
  have hKr : KΓ ≤ Subgroup.centralizer ({r} : Set Γ) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hrK k hk).symm
  have hev : 2 ∣ Nat.card ↥KΓ := by
    have h6 : Nat.card ↥(Subgroup.center ↥KΓ) ∣ Nat.card ↥KΓ := Subgroup.card_subgroup_dvd_card _
    rw [hKz] at h6
    exact (by norm_num : 2 ∣ 6).trans h6
  have hOZ : CFSG.oddCore ↥KΓ ≤ Subgroup.center ↥KΓ := oddCore_le_center_of_even hKq hev
  have hKq' : CFSG.IsQuasisimple (↥KΓ ⧸ CFSG.oddCore ↥KΓ) :=
    isQuasisimple_quot_of_le_center hKq _ hOZ
  have hKnormal : (KΓ.subgroupOf (Subgroup.centralizer ({r} : Set Γ))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKr).mpr hNr
  have hcomp : CFSG.ASVolI.ChIJK.IsTwoComponentIn KΓ (Subgroup.centralizer ({r} : Set Γ)) :=
    ⟨CFSG.ASVolI.burnsideI31_mem_cComp_iff.mp (quasithinIsCComponent_of_normal hKq hKr hKnormal),
      hKq'⟩
  have hKGΓ : CFSG.SectionRank.IsKGroupCat Γ := hKG Γ (MonoidHom.id Γ) Function.injective_id
  have hr2sq : r ^ 2 = 1 := by rw [pow_two]; exact hr2
  have hI := CFSG.ASVolI.as_I_3_2 Γ hKGΓ r hr2sq hr1 KΓ hcomp
  have hK1 : KΓ ≤ CFSG.conjugate KΓ 1 := fun k hk => ⟨k, hk, by simp [MulAut.conj_apply]⟩
  have hJcle : CFSG.ASVolI.ChIJK.conjClosure KΓ (CFSG.ASVolI.ChIJK.oddCoreE Γ) ≤
      ⨆ g : Γ, CFSG.conjugate KΓ g := by
    unfold CFSG.ASVolI.ChIJK.conjClosure
    exact iSup₂_le fun y _ => le_iSup (fun g : Γ => CFSG.conjugate KΓ g) y
  have hKJc : KΓ ≤ CFSG.ASVolI.ChIJK.conjClosure KΓ (CFSG.ASVolI.ChIJK.oddCoreE Γ) := by
    unfold CFSG.ASVolI.ChIJK.conjClosure
    exact le_iSup₂_of_le (f := fun y _ => CFSG.conjugate KΓ y) 1 (Subgroup.one_mem _) hK1
  rcases hI with ⟨hJT, hJr⟩ | ⟨J, hJ2, hJne, hJeq, ⟨e⟩⟩
  ·
    set Jc := CFSG.ASVolI.ChIJK.conjClosure KΓ (CFSG.ASVolI.ChIJK.oddCoreE Γ) with hJcdef
    have hcenJ : ∀ o ∈ CFSG.oddCore Γ, ∀ j ∈ Jc, o * j = j * o :=
      fun o ho j hj => oddCore_centralizes_iSup hOcen o ho j (hJcle hj)
    have hJq : CFSG.IsQuasisimple ↥Jc := (twoComp_quasisimple hJT hcenJ).1
    have hsnJ : Jc.IsSubnormal := (isCComponent_of_twoComp_top hJT).2.2.1
    have hr2' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
    have hrN : r ∈ Subgroup.normalizer (Jc : Set Γ) := by
      apply normalizer_of_map_eq
      have h := hJr
      unfold CFSG.conjugate at h
      rw [hr2'] at h
      exact h
    have hJrC : Jc ≤ Subgroup.centralizer ({r} : Set Γ) :=
      inspBM_le_centralizer hBM hQT hKG hr2 hrN hJq hKJc hKq hKr hNr hM22
    have hKJ : KΓ = Jc := by
      have hnorm : (KΓ.subgroupOf Jc).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKJc).mpr (hJrC.trans hNr)
      rcases normal_le_center_or_top hJq (KΓ.subgroupOf Jc) with hc | htop
      · exfalso
        obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple hKq
        have hua : (⟨(a : Γ), hKJc a.2⟩ : ↥Jc) ∈ KΓ.subgroupOf Jc :=
          Subgroup.mem_subgroupOf.mpr a.2
        have h1 := Subgroup.mem_center_iff.mp (hc hua) ⟨(b : Γ), hKJc b.2⟩
        have h2 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul] at h2
        exact hab (Subtype.ext h2.symm)
      · exact le_antisymm hKJc (Subgroup.subgroupOf_eq_top.mp htop)
    rw [hKJ]
    exact isComponentOf_top_of_quasisimple hsnJ hJq
  ·
    have hJc2 : J ≤ CFSG.ASVolI.ChIJK.conjClosure KΓ (CFSG.ASVolI.ChIJK.oddCoreE Γ) := by
      rw [hJeq]
      exact le_sup_left
    have hJ'c2 : CFSG.conjugate J r ≤
        CFSG.ASVolI.ChIJK.conjClosure KΓ (CFSG.ASVolI.ChIJK.oddCoreE Γ) := by
      rw [hJeq]
      exact le_sup_right
    have hKJJ' : KΓ ≤ J ⊔ CFSG.conjugate J r := by
      rw [← hJeq]
      exact hKJc
    have hJle : J ≤ ⨆ g : Γ, CFSG.conjugate KΓ g := hJc2.trans hJcle
    have hcenJ : ∀ o ∈ CFSG.oddCore Γ, ∀ j ∈ J, o * j = j * o :=
      fun o ho j hj => oddCore_centralizes_iSup hOcen o ho j (hJle hj)
    obtain ⟨hJq, hOJ⟩ := twoComp_quasisimple hJ2 hcenJ
    have hsnJ : J.IsSubnormal := (isCComponent_of_twoComp_top hJ2).2.2.1
    have hr2' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
    have hJ'q : CFSG.IsQuasisimple ↥(CFSG.conjugate J r) :=
      CFSG.IsQuasisimple.of_mulEquiv
        (J.equivMapOfInjective (MulAut.conj r⁻¹).toMonoidHom (MulAut.conj r⁻¹).injective).symm hJq
    have hJ'sn : (CFSG.conjugate J r).IsSubnormal :=
      hsnJ.map (f := (MulAut.conj r⁻¹).toMonoidHom) (MulAut.conj r⁻¹).surjective
    have hJcomp : CFSG.Open.IsComponentOf J ⊤ := isComponentOf_top_of_quasisimple hsnJ hJq
    have hJ'comp : CFSG.Open.IsComponentOf (CFSG.conjugate J r) ⊤ :=
      isComponentOf_top_of_quasisimple hJ'sn hJ'q
    have hcomm0 := CFSG.ComponentClassification.LocalComponents.commute_of_ne J
      (CFSG.conjugate J r) hJcomp hJ'comp hJne.symm
    have hcomm : ∀ j ∈ J, ∀ j' ∈ CFSG.conjugate J r, j * j' = j' * j := by
      intro j hj j' hj'
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm0 hj
      exact (Subgroup.mem_centralizer_iff.mp hle j' hj').symm
    have hJ'conj : ∀ j ∈ J, r * j * r⁻¹ ∈ CFSG.conjugate J r := by
      intro j hj
      refine Subgroup.mem_map.mpr ⟨j, hj, ?_⟩
      show r⁻¹ * j * r⁻¹⁻¹ = r * j * r⁻¹
      rw [inv_inv, hr2']
    have hJ'conj' : ∀ j' ∈ CFSG.conjugate J r, r⁻¹ * j' * r ∈ J := by
      rintro _ ⟨j, hj, rfl⟩
      have e' : r⁻¹ * (MulAut.conj r⁻¹).toMonoidHom j * r = j := by
        show r⁻¹ * (r⁻¹ * j * r⁻¹⁻¹) * r = j
        rw [inv_inv, hr2']
        calc r * (r * j * r) * r = (r * r) * j * (r * r) := by group
          _ = j := by rw [hr2, one_mul, mul_one]
      rw [e']
      exact hj
    have hoT : CFSG.ASVolI.ChIJK.oddTwoCore ↥KΓ = Subgroup.center ↥KΓ :=
      oddTwoCore_eq_center hKq hKz E0 hE0 hE0c
    have hZne : Subgroup.center ↥KΓ ≠ ⊤ := by
      intro htop'
      obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple hKq
      apply hab
      have ha : a ∈ Subgroup.center ↥KΓ := by
        rw [htop']
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    have hidx : (CFSG.ASVolI.ChIJK.oddTwoCore ↥J).index = (Subgroup.center ↥KΓ).index := by
      have h1 : Nat.card (↥J ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥J) =
          Nat.card (↥KΓ ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥KΓ) := Nat.card_congr e.toEquiv
      rw [hoT] at h1
      exact h1
    have hO22ne : CFSG.ASVolI.ChIJK.oddTwoCore ↥J ≠ ⊤ := by
      intro htop
      have h1 : (CFSG.ASVolI.ChIJK.oddTwoCore ↥J).index = 1 := Subgroup.index_eq_one.mpr htop
      have h2 : (Subgroup.center ↥KΓ).index = 1 := by rw [← hidx]; exact h1
      exact hZne (Subgroup.index_eq_one.mp h2)
    have hO22J : CFSG.ASVolI.ChIJK.oddTwoCore ↥J ≤ Subgroup.center ↥J :=
      twoComp_oddTwoCore_le_center hJ2 hOJ hO22ne
    have hJZ : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card (↥KΓ ⧸ Subgroup.center ↥KΓ) := by
      have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤
          Nat.card (↥J ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥J) := Subgroup.index_antitone hO22J
      have h2 : Nat.card (↥J ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥J) =
          Nat.card (↥KΓ ⧸ Subgroup.center ↥KΓ) := by
        have h3 : Nat.card (↥J ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥J) =
            Nat.card (↥KΓ ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥KΓ) := Nat.card_congr e.toEquiv
        rw [h3, hoT]
      exact h1.trans h2.le
    exact (alt2_impossible hKq hKz E0 hE0 hE0c hrK hzKX hzc hcomm hKJJ' hJ'conj hJ'conj' hJZ e
      hoT hpz).elim

end CFSG.Quasithin.H13.Ch4.J4KX

end
