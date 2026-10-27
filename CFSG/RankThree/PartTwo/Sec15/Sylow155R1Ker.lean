module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofCS
import CFSG.RankThree.PartTwo.Sec4.T444.Step450
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

theorem eq_one_of_coprime_of_mem_centralizer_layer {Q : Type*} [Group Q] [Finite Q]
    (hcore : CFSG.pPrimeCore 3 Q = ⊥) {r : Q} (hr : Nat.Coprime (orderOf r) 3)
    (hrE : r ∈ Subgroup.centralizer (CFSG.layer Q : Set Q))
    (hrP : r ∈ Subgroup.centralizer (CFSG.pCore 3 Q : Set Q)) : r = 1 := by
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers r) := by
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hr.symm
  have hE : ∀ J : Subgroup Q, IsComponent J →
      Subgroup.zpowers r ≤ Subgroup.centralizer (J : Set Q) := by
    intro J hJ
    have hJle : J ≤ CFSG.layer Q := by
      rw [CFSG.layer.eq_sSup]
      exact le_sSup hJ
    exact Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJle) hrE)
  exact Subgroup.zpowers_eq_bot.mp (Sec4.eq_bot_of_le_centralizer_of_pPrimeCore_eq_bot hcore h3
    (Subgroup.zpowers_le.mpr hrP) hE)

variable {G : Type} [Group G] [Finite G]

private theorem res1_le_C {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (L : Subgroup G) : A ≤ Res1C A L := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, (Subgroup.mem_inf.mp hb).1⟩ ⟨a, ha⟩)

private theorem res1_le_sup_zpowers {A B : Subgroup G} (hB : IsHyperplane A B) {d : G}
    (hdA : d ∈ A) (hdB : d ∉ B) : A ≤ B ⊔ Subgroup.zpowers d := by
  set H := B ⊔ Subgroup.zpowers d
  have hHA : H ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr hdA)
  have hBH : B ≤ H := le_sup_left
  have hdH : d ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBH
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hHA
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hkj : k * j = 3 := by
    have h1 : Nat.card B * (k * j) = Nat.card B * 3 := by
      rw [← mul_assoc, ← hk, ← hj, hB.2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hBpos h1
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hBeq : B = H := Subgroup.eq_of_le_of_card_ge hBH (by rw [hk, mul_one])
    exact hdB (hBeq ▸ hdH)
  have hj1 : j = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp ⟨j, hkj.symm⟩ with h1 | h3
    · exact absurd h1 hk1
    · subst h3
      omega
  exact (Subgroup.eq_of_le_of_card_ge hHA (by rw [hj, hj1, mul_one])).ge

private theorem res1_c_not_mem {A : Subgroup G} {c : G} {L : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hcomp : Res1Comp A c L Yc) : c ∉ L := by
  intro hcL
  obtain ⟨-, ⟨c', hc'Y, hc'⟩, hbot⟩ := hcomp
  obtain ⟨hcA, hcard, -⟩ := zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcard
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈
      ((A ⊓ L).subgroupOf (Res1C A L)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))) := by
    refine ⟨c', ?_, rfl⟩
    show c' ∈ (A ⊓ L).subgroupOf (Res1C A L)
    rw [Subgroup.mem_subgroupOf]
    have : (c' : G) = c := hc'
    rw [this]
    exact ⟨hcA, hcL⟩
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' = 1 := by
    have h := Subgroup.mem_inf.mpr ⟨hmem, hc'Y⟩
    rw [hbot] at h
    exact h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hord : orderOf c' = 3 := by
    rw [← hc3, ← hc']
    exact (Subgroup.orderOf_coe c').symm
  have hdvd : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Res1C A L)) := by
    have h := orderOf_dvd_natCard (⟨c', h1⟩ : CFSG.pPrimeCore 3 ↥(Res1C A L))
    rwa [Subgroup.orderOf_mk, hord] at h
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card) hdvd

private theorem res1_comm_map {A : Subgroup G} {c : G} {L : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (hAeq : A ≤ (A ⊓ L) ⊔ Subgroup.zpowers c)
    (hcY : c ∈ (Yc.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)))).map
      (Res1C A L).subtype) {z : Res1Q A L} (hz : ∀ y ∈ Yc, z * y = y * z) :
    ∀ ab ∈ (A.subgroupOf (Res1C A L)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))),
      z * ab = ab * z := by
  classical
  have hAC : A ≤ Res1C A L := res1_le_C hAab L
  set C : Subgroup G := Res1C A L
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)
  set S : Subgroup G :=
    ((Subgroup.centralizer ({z} : Set (Res1Q A L))).comap π).map C.subtype
  have hcentral : ∀ e ∈ A ⊓ L, ∀ (heC : e ∈ C) (w : ↥C), (⟨e, heC⟩ : ↥C) * w = w * ⟨e, heC⟩ := by
    intro e he heC w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp w.2 e he)
  have hBS : A ⊓ L ≤ S := by
    intro e he
    have heC : e ∈ C := hAC (Subgroup.mem_inf.mp he).1
    refine ⟨⟨e, heC⟩, ?_, rfl⟩
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C) z
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
      ← map_mul, hcentral e he heC w]
  have hcS : c ∈ S := by
    obtain ⟨c', hc'Y, hc'⟩ := hcY
    refine ⟨c', ?_, hc'⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (hz _ (Subgroup.mem_comap.mp hc'Y)).symm
  have hAS : A ≤ S := hAeq.trans (sup_le hBS (Subgroup.zpowers_le.mpr hcS))
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨a', ha', ha'eq⟩ := hAS (Subgroup.mem_subgroupOf.mp ha)
  have : a' = a := Subtype.ext ha'eq
  subst this
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp ha')).symm

theorem res1_eq_one_of_centralizes {A : Subgroup G} {c : G} {L : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L))
    (hcomp : Res1Comp A c L Yc) (hsimple : IsSimpleGroup ↥Yc) {x : Res1Q A L}
    (hx : Nat.Coprime (orderOf x) 3) (hxY : ∀ y ∈ Yc, x * y = y * x) : x = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hS.mem_partTwoF.1
  have hAC : A ≤ Res1C A L := res1_le_C hAab L
  have hAmax : ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A := by
    intro y hy3 hya
    refine mem_of_mem_partTwoF hS.mem_partTwoF hy3 fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hya a ha
  have hcL : c ∉ L := res1_c_not_mem hS hcomp
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).1
  have hAeq : A ≤ (A ⊓ L) ⊔ Subgroup.zpowers c :=
    res1_le_sup_zpowers hhyp hcA fun h => hcL (Subgroup.mem_inf.mp h).2
  obtain ⟨hYcomp, hcY, -⟩ := hcomp
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  have hlayer : CFSG.layer (Res1Q A L) ≤ Yc :=
    sSup_le fun _ hK => (res1_isComponent_unique hS hhyp hK hYcomp).le
  set P : Subgroup (Res1Q A L) := CFSG.pCore 3 (Res1Q A L)
  have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup
  have hinf : ∀ z ∈ P, z ∈ Yc → z = 1 := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (P.subgroupOf Yc) with hbot | htop
    · intro z hzP hzY
      have hz : (⟨z, hzY⟩ : ↥Yc) ∈ P.subgroupOf Yc := Subgroup.mem_subgroupOf.mpr hzP
      rw [hbot, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    · exfalso
      have hYP : Yc ≤ P := fun y hy => by
        have hy' : (⟨y, hy⟩ : ↥Yc) ∈ P.subgroupOf Yc := by
          rw [htop]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hy'
      haveI : Group.IsNilpotent ↥Yc := (hP3.to_le hYP).isNilpotent
      haveI : Group.IsPerfect ↥Yc := hYcomp.1.1
      exact Group.IsPerfect.not_isNilpotent ↥Yc ‹_›
  have hPY : ∀ u ∈ P, ∀ y ∈ Yc, u * y = y * u := by
    intro u hu y hy
    have h1 : u * y * u⁻¹ * y⁻¹ ∈ Yc := Yc.mul_mem (hYn.conj_mem y hy u) (Yc.inv_mem hy)
    have h2 : u * y * u⁻¹ * y⁻¹ ∈ P := by
      have h : y * u⁻¹ * y⁻¹ ∈ P := (CFSG.pCore_normal (p := 3)).conj_mem u⁻¹ (P.inv_mem hu) y
      rw [show u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹ * y⁻¹) by group]
      exact P.mul_mem hu h
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    rw [commutatorElement_def]
    exact hinf _ h2 h1
  have hΩ : ∀ u ∈ P, u ^ 3 = 1 →
      u ∈ (A.subgroupOf (Res1C A L)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))) := by
    intro u hu hu3
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(Res1C A L)) u
    exact Proof1418Res3.mem_map_of_commute hAC hAab.2 hAmax hu3
      (res1_comm_map hAab hAeq hcY (hPY _ hu))
  have hxP : x ∈ Subgroup.centralizer (P : Set (Res1Q A L)) := by
    let α : MulAut ↥P := MulAut.conjNormal x
    have hα : Nat.Coprime (orderOf α) 3 :=
      Nat.Coprime.coprime_dvd_left (orderOf_map_dvd MulAut.conjNormal x) hx
    have hfix : ∀ u : ↥P, u ^ 3 = 1 → α u = u := by
      intro u hu3
      have hu3' : (u : Res1Q A L) ^ 3 = 1 := by simpa using congrArg Subtype.val hu3
      have hcomm := res1_comm_map hAab hAeq hcY hxY _ (hΩ u u.2 hu3')
      apply Subtype.ext
      show x * u * x⁻¹ = u
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm
    have hα1 : α = 1 :=
      HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
        (by norm_num) hP3 hα hfix
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h : α ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hα1]; rfl
    have h2 := congrArg Subtype.val h
    simp only [α, MulAut.conjNormal_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hxE : x ∈ Subgroup.centralizer (CFSG.layer (Res1Q A L) : Set (Res1Q A L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hxY e (hlayer he)).symm
  exact eq_one_of_coprime_of_mem_centralizer_layer (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3)
    hx hxE hxP

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
