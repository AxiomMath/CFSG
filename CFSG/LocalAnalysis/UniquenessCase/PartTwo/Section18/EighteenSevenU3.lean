module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Setting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem imageBar2_isPGroup_quotient {X : Type} [Group X] [Finite X]
    {K T H : Subgroup X} (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hT : IsPGroup 2 T) (hsup : K ⊔ T = H) :
    IsPGroup 2 (Bar2 H ⧸ S18.imageBar2 H K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hsup ▸ le_sup_right
  have hCnormal : (S18.imageBar2 H K).Normal :=
    Subgroup.Normal.map hKn (S18.piBar2 H) (QuotientGroup.mk'_surjective _)
  haveI : (S18.imageBar2 H K).Normal := hCnormal
  have hTbar : IsPGroup 2 (S18.imageBar2 H T) := by
    have h1 : IsPGroup 2 (T.subgroupOf H) :=
      hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact h1.map (S18.piBar2 H)
  have hsupC : S18.imageBar2 H K ⊔ S18.imageBar2 H T = ⊤ := by
    have h1 : S18.imageBar2 H (K ⊔ T) =
        S18.imageBar2 H K ⊔ S18.imageBar2 H T := by
      rw [S18.imageBar2, S18.imageBar2, S18.imageBar2, ← Subgroup.map_sup,
        ← Subgroup.subgroupOf_sup hKH hTH]
    rw [← h1, hsup]
    simp [S18.imageBar2, S18.piBar2, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  haveI : ((S18.imageBar2 H K).subgroupOf (⊤ : Subgroup (Bar2 H))).Normal :=
    hCnormal.subgroupOf ⊤
  have hquotTop : IsPGroup 2 ((⊤ : Subgroup (Bar2 H)) ⧸
      (S18.imageBar2 H K).subgroupOf ⊤) :=
    CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Bar2 H)
      (L := S18.imageBar2 H K) (Q := S18.imageBar2 H T) (K := ⊤) hTbar le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hCnormal]; exact le_top) hsupC
  have he : ((S18.imageBar2 H K).subgroupOf (⊤ : Subgroup (Bar2 H))).map
      (Subgroup.topEquiv (G := Bar2 H)).toMonoidHom = S18.imageBar2 H K := by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  exact IsPGroup.of_equiv hquotTop
    (QuotientGroup.congr ((S18.imageBar2 H K).subgroupOf ⊤)
      (S18.imageBar2 H K) Subgroup.topEquiv he)

private theorem odd_card_centralizer_of_two_quotient {Q : Type} [Group Q] [Finite Q]
    {C : Subgroup Q} (hCn : C.Normal) (hquot : IsPGroup 2 (Q ⧸ C))
    (hO2 : CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q) = ⊥) :
    Odd (Nat.card (Subgroup.centralizer (C : Set Q))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal := hCn
  let D := Subgroup.centralizer (C : Set Q)
  have hDn : D.Normal := Subgroup.normal_centralizer
  haveI : D.Normal := hDn
  let f : ↥D →* Q ⧸ C := (QuotientGroup.mk' C).comp D.subtype
  have hker : f.ker ≤ Subgroup.center ↥D := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxC : (x : Q) ∈ C := by
      have hx1 : (QuotientGroup.mk' C) (x : Q) = 1 := hx
      exact (QuotientGroup.eq_one_iff (x : Q)).mp hx1
    exact (Subgroup.mem_centralizer_iff.mp y.2 (x : Q) hxC).symm
  have hnil : Group.IsNilpotent ↥D := by
    haveI : Group.IsNilpotent (Q ⧸ C) := hquot.isNilpotent
    exact Subgroup.isNilpotent_of_ker_le_center f hker
  have hbot_of_sylow : ∀ P : Sylow 2 ↥D,
      ((P : Subgroup ↥D).map D.subtype) = ⊥ := by
    intro P
    have hPchar : (P : Subgroup ↥D).Characteristic :=
      Sylow.characteristic_of_normal P (Group.IsNilpotent.sylow_normal hnil 2 P)
    haveI : (P : Subgroup ↥D).Characteristic := hPchar
    have hPq_norm : ((P : Subgroup ↥D).map D.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hPq_p : IsPGroup 2 ((P : Subgroup ↥D).map D.subtype) :=
      P.isPGroup'.map D.subtype
    have hPq_le : ((P : Subgroup ↥D).map D.subtype) ≤
        CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q) := by
      refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf le_top ?_ hPq_p
      intro x _ y hy
      exact hPq_norm.conj_mem y hy x
    rw [hO2] at hPq_le
    exact le_bot_iff.mp hPq_le
  rw [Nat.odd_iff]
  by_contra hodd
  have heven : 2 ∣ Nat.card ↥D := (Nat.not_odd_iff_even.mp (by rwa [Nat.odd_iff])).two_dvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 heven
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, ht, pow_one]⟩
  obtain ⟨P, hP⟩ := hzp2.exists_le_sylow
  have htP : t ∈ (P : Subgroup ↥D) := hP (Subgroup.mem_zpowers t)
  have htmap : (t : Q) ∈ (P : Subgroup ↥D).map D.subtype := ⟨t, htP, rfl⟩
  rw [hbot_of_sylow P] at htmap
  have ht1 : (t : Q) = 1 := Subgroup.mem_bot.mp htmap
  have htord : orderOf (t : Q) = 2 := (Subgroup.orderOf_coe t).trans ht
  rw [ht1, orderOf_one] at htord
  omega

private theorem centralizer_le_of_two_quotient {Q : Type} [Group Q] [Finite Q]
    {C : Subgroup Q} (hCn : C.Normal) (hquot : IsPGroup 2 (Q ⧸ C))
    (hDodd : Odd (Nat.card (Subgroup.centralizer (C : Set Q)))) :
    Subgroup.centralizer (C : Set Q) ≤ C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal := hCn
  intro d hd
  have hodd : Odd (orderOf d) :=
    hDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd)
  obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk' C d)
  have hdvd : orderOf ((QuotientGroup.mk' C) d) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have hdvd' : orderOf ((QuotientGroup.mk' C) d) ∣ orderOf d := orderOf_map_dvd _ d
  have hcop : Nat.Coprime (orderOf ((QuotientGroup.mk' C) d)) (orderOf d) :=
    Nat.Coprime.coprime_dvd_left hdvd
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
  have hone : orderOf ((QuotientGroup.mk' C) d) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd'
  exact (QuotientGroup.eq_one_iff d).mp (orderOf_eq_one_iff.mp hone)

private theorem odd_center_of_centralizer_le {Q : Type} [Group Q] [Finite Q]
    {C : Subgroup Q} (hDleC : Subgroup.centralizer (C : Set Q) ≤ C)
    (hDodd : Odd (Nat.card (Subgroup.centralizer (C : Set Q)))) :
    Odd (Nat.card (Subgroup.center ↥C)) := by
  let D := Subgroup.centralizer (C : Set Q)
  have hcenter : (Subgroup.center ↥C).map C.subtype = D := by
    rw [← CFSG.centerIn_eq_map_center C]
    change C ⊓ D = D
    exact inf_eq_right.mpr hDleC
  have hcard : Nat.card (Subgroup.center ↥C) = Nat.card D := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, hcenter]
  rw [hcard]
  exact hDodd

theorem inFGroupU3Setting_imageBar2 {X : Type} [Group X] [Finite X] {K T H : Subgroup X}
    {n : ℕ} (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hU : IsSU3 (Bar2 K) n)
    (hT : IsPGroup 2 T) (hsup : K ⊔ T = H) :
    WeakClosure81.InFGroupU3.Setting (S18.imageBar2 H K) n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : H ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  have hpCore : CFSG.Open.pCoreOf 2 K = K ⊓ CFSG.Open.pCoreOf 2 H :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hKH hKN
  let Q := Bar2 H
  let C : Subgroup Q := S18.imageBar2 H K
  have hCnormal : C.Normal :=
    Subgroup.Normal.map hKn (S18.piBar2 H) (QuotientGroup.mk'_surjective _)
  haveI : C.Normal := hCnormal
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec18.Claim184LcProof.quotient_mulEquiv_map hKH
      (hpCore.le.trans inf_le_right)
  have hquot : IsPGroup 2 (Q ⧸ C) := imageBar2_isPGroup_quotient hKH hKn hT hsup
  have hO2 : CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq]
    exact CFSG.LocalAnalysis.WeakClosure81.pCore_two_bar2_eq_bot H
  have hDodd : Odd (Nat.card (Subgroup.centralizer (C : Set Q))) :=
    odd_card_centralizer_of_two_quotient hCnormal hquot hO2
  have hDleC : Subgroup.centralizer (C : Set Q) ≤ C :=
    centralizer_le_of_two_quotient hCnormal hquot hDodd
  refine ⟨hCnormal, ?_, ?_, hDleC, ?_, ?_⟩
  · exact hU.1.of_mulEquiv e.symm
  · exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hU.2
  · exact odd_center_of_centralizer_le hDleC hDodd
  · intro x
    obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk' C x)
    refine ⟨k, ?_⟩
    have hk' : (QuotientGroup.mk' C) (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact hk
    exact (QuotientGroup.eq_one_iff (x ^ 2 ^ k)).mp hk'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
