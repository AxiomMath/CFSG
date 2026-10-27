module

public import CFSG.RankThree.PartTwo.Sec15.Item15Type
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
import CFSG.Sporadic.J2
import CFSG.Sporadic.ON
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped Pointwise

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem card_alternatingGroup_ten : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem card_of_isTripleCover {X Y : Type*} [Group X] [Group Y] [Finite X]
    (h : Sec4.IsTripleCover X Y) : Nat.card X = 3 * Nat.card Y := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  rw [← Nat.card_congr e.toEquiv, ← h3, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)

theorem checkSL_60 : ∀ q < 4, 2 ≤ q → q ^ 3 ∣ 60 →
    60 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide

theorem checkSU_60 : ∀ q < 4, 2 ≤ q → q ^ 3 ∣ 60 →
    60 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide

theorem checkSL_1080 : ∀ q < 11, 2 ≤ q → q ^ 3 ∣ 1080 →
    1080 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_1080 : ∀ q < 11, 2 ≤ q → q ^ 3 ∣ 1080 →
    1080 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem not_isLThreeEpsAt_of_card_small {X : Type} [Group X]
    (hX : Nat.card X = 60 ∨ Nat.card X = 1080) (p f : ℕ) [Fact p.Prime] :
    ¬ IsLThreeEpsAt X p f := by
  rcases hX with h | h
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_60)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_60) p f
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_1080)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_1080) p f

theorem not_isoLThreePi_of_card_small {X : Type} [Group X]
    (hX : Nat.card X = 60 ∨ Nat.card X = 1080) (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi X p e := by
  rcases hX with h | h
  · exact KFacts.KS14.not_isoLThreePi_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_60)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_60) p e
  · exact KFacts.KS14.not_isoLThreePi_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_1080)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_1080) p e

theorem not_mem_list136_of_card_small {X : Type} [Group X]
    (hX : Nat.card X = 60 ∨ Nat.card X = 1080) :
    ¬ (Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12)) := by
  rintro (he | ⟨p, f, hp, -, hL⟩ | he | he | he)
  · obtain ⟨e⟩ := he
    have h := Nat.card_congr e.toEquiv
    rw [CFSG.Sporadic.J2.card_J2] at h
    omega
  · exact not_isoLThreePi_of_card_small hX p f hL
  · obtain ⟨e⟩ := he
    have h := Nat.card_congr e.toEquiv
    rw [card_alternatingGroup_seven] at h
    omega
  · obtain ⟨e⟩ := he
    have h := Nat.card_congr e.toEquiv
    rw [KFacts.KS14.card_nativeM22] at h
    omega
  · obtain ⟨e⟩ := he
    have h := Nat.card_congr e.toEquiv
    rw [KFacts.KS14.card_nativeM12] at h
    omega

theorem eq_bot_or_eq_bot_of_isQuasisimple {X : Type*} [Group X] (hq : IsQuasisimple X)
    {U V : Subgroup X} (hU : U.Normal) (hV : V.Normal) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    U = ⊥ ∨ V = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hU with hUt | hUc
  · right
    rw [hUt, top_inf_eq] at hinf
    exact hinf
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hV with hVt | hVc
  · left
    rw [hVt, inf_top_eq] at hinf
    exact hinf
  exfalso
  have hcen : Subgroup.center X = ⊤ := top_le_iff.mp (hsup ▸ sup_le hUc hVc)
  obtain ⟨-, hs, -⟩ := hq
  have hnt := hs.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff y).mpr (hcen ▸ Subgroup.mem_top y))

theorem pPrimeCore_three_eq_bot_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hq : IsQuasisimple Q) (h3 : 3 ∣ Nat.card Q) (hZ : IsPGroup 3 (Subgroup.center Q)) :
    CFSG.pPrimeCore 3 Q = ⊥ := by
  have hcop := CFSG.pPrimeCore_coprime_card (p := 3) (G := Q)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.pPrimeCore_normal (p := 3) (G := Q)) with htop | hcen
  · exfalso
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3
  · have hp : IsPGroup 3 (CFSG.pPrimeCore 3 Q) := hZ.to_le hcen
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hk] at hcop
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exfalso
      have := Nat.Coprime.coprime_dvd_right (dvd_pow_self 3 (Nat.succ_ne_zero k)) hcop
      norm_num at this

section Case148

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem exists_hj_of_img148
    (h148 : Item148 A LB) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hAab : IsMulCommutative A)
    (hch : Chosen136 A)
    (hq : letI := ker148_normal hY.2
      IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)))
    (hcard : letI := ker148_normal hY.2
      Nat.card ↥(img148 A Y (deltaZero A LB Y)) = 60 ∨
        Nat.card ↥(img148 A Y (deltaZero A LB Y)) = 1080) :
    ∃ c : G, Subgroup.zpowers c ∈ omegaA A ∧
      deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
        deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
      ∃ L ∈ lA A c,
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  let := ker148_normal hY.2
  have h148Y := (h148 Y hY).2
  have hq' : IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)) := hq
  have hcard2 : Nat.card ↥(img148 A Y (deltaZero A LB Y)) = 60 ∨
      Nat.card ↥(img148 A Y (deltaZero A LB Y)) = 1080 := hcard
  set X := img148 A Y (deltaZero A LB Y) with hX
  have hXnt : Nontrivial ↥X := CFSG.LocalCores.isQuasisimple_nontrivial hq'
  have hcard' : Nat.card ↥X ≤ 1080 := by omega
  rcases h148Y with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    have hX1 : X = ⊥ := img148_eq_bot_of_le h1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥X)
    exact hx (Subtype.ext ((Subgroup.mem_bot).mp (hX1 ▸ x.2)))
  ·
    obtain ⟨c', hc', hdec, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p, f, e', hp, -, -, -, hL3'⟩ | ⟨hJ, -⟩
    ·
      exfalso
      obtain ⟨φ⟩ := hφ
      have hcL : Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 60 ∨
          Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 1080 := by
        rw [← Nat.card_congr φ.toEquiv]
        exact hcard2
      exact not_mem_list136_of_card_small hcL (hch.2 c' hc' L' hL').1
    ·
      exfalso
      obtain ⟨φ⟩ := hφ
      have h := Nat.card_congr φ.toEquiv
      rw [card_alternatingGroup_seven] at h
      omega
    ·
      exact (not_isLThreeEpsAt_of_card_small hcard2 p f hL3').elim
    ·
      exact ⟨c', hc', hdec, L', hL', hJ⟩
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := h3
    rcases h with hON | ⟨U, V, hU, hV, hUV, -, hUV3, hU6, hV6⟩ |
        ⟨U, V, hU, hV, hUV, -, hU6, heV⟩ | hφ | hφ | ⟨_, hφ⟩
    · have h := card_of_isTripleCover hON
      rw [CFSG.Sporadic.ON.card_ON] at h
      omega
    ·
      have hU1 : Nat.card ↥U = 1080 := by
        rw [card_of_isTripleCover hU6, card_alternatingGroup_six]
      have hV1 : Nat.card ↥V = 1080 := by
        rw [card_of_isTripleCover hV6, card_alternatingGroup_six]
      have hUle := Subgroup.card_le_card_group U
      have hUt : U = ⊤ := Subgroup.eq_top_of_card_eq U (by omega)
      have hVt : V = ⊤ := Subgroup.eq_top_of_card_eq V (by omega)
      rw [hUt, hVt, inf_top_eq, Subgroup.card_top] at hUV3
      omega
    ·
      have hU1 : Nat.card ↥U = 1080 := by
        rw [card_of_isTripleCover hU6, card_alternatingGroup_six]
      have hUle := Subgroup.card_le_card_group U
      have hUt : U = ⊤ := Subgroup.eq_top_of_card_eq U (by omega)
      rw [hUt, top_inf_eq] at hUV
      obtain ⟨eV⟩ := heV
      have h := Nat.card_congr eV.toEquiv
      rw [hUV, Subgroup.card_bot, card_alternatingGroup_five] at h
      omega
    ·
      obtain ⟨φ⟩ := hφ
      have h := Nat.card_congr φ.toEquiv
      rw [Nat.card_prod, card_alternatingGroup_five] at h
      omega
    ·
      obtain ⟨φ⟩ := hφ
      have h := Nat.card_congr φ.toEquiv
      rw [card_alternatingGroup_seven] at h
      omega
    ·
      exact not_isLThreeEpsAt_of_card_small hcard2 7 1 (Or.inl hφ)
  ·
    exfalso
    obtain ⟨hφ, -⟩ := h4
    obtain ⟨φ⟩ := hφ
    have h := Nat.card_congr φ.toEquiv
    rw [card_alternatingGroup_ten] at h
    omega
  ·
    exfalso
    obtain ⟨-, -, -, n, -, -, -, -, -, hiso, -⟩ := h5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact not_isoLThreePi_of_card_small hcard2 2 (3 * n) hiso
  ·
    exfalso
    obtain ⟨hφ, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    have h := Nat.card_congr φ.toEquiv
    rw [Nat.card_prod, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h
    omega
  ·
    exfalso
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hC₁ : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    have hC₂ : img148 A Y J₁ ≤ Subgroup.centralizer (img148 A Y J₂ : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hN₁ : ((img148 A Y J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
    have hN₂ : ((img148 A Y J₂).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂le).mpr ?_
      rw [← hsup]
      exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    have hsup' : (img148 A Y J₁).subgroupOf X ⊔ (img148 A Y J₂).subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJ₁le hJ₂le, hsup, Subgroup.subgroupOf_self]
    have hinf' : (img148 A Y J₁).subgroupOf X ⊓ (img148 A Y J₂).subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J₁ ⊓ img148 A Y J₂ := ⟨hx.1, hx.2⟩
      rw [hinf] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
    have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
      rcases eq_bot_or_eq_bot_of_isQuasisimple hq' hN₁ hN₂ hsup' hinf' with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₂le)
    have hAle : A ≤ Y ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
      intro J hJY hJ p f hZ
      rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
      obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
      exact hab (img148_comm hAab a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂

end Case148

theorem mem_sectionCentralizer_of_eq_sup {G : Type} [Group G] [Finite G] {A Y : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA : Late.IsE27 A) {c : G} (hc : c ∈ A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYΔ : Y = deltaZero A LB Y)
    (hdec : deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
      deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hO : pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y) :
    c ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) := by
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set D := deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hD
  have hDc : D ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sSup_le fun Q hQ => ?_
    exact le_centralizer_of_le_normalizer_zpowers hA hc hQ.1.1 (hQ.2.trans inf_le_right)
  have hDY : D ≤ Y := (deltaZero_le _).trans inf_le_left
  have hYN : Y ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hcO : c ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y (hAY hc)
  have hYeq : Y = O ⊔ D := by
    conv_lhs => rw [hYΔ, hdec, ← hYΔ]
    rw [hO]
  refine ⟨hc, fun y hy => ?_⟩
  have hy' : y ∈ ((O : Set G) * (D : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O D (hDY.trans hYN), ← hYeq]
    exact hy
  obtain ⟨o, ho, z, hz, rfl⟩ := hy'
  have hcz : c * z = z * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hDc hz)).symm
  have h1 : c * o * c⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hcO o).mp ho
  have hzc : z * c⁻¹ = c⁻¹ * z := by
    calc z * c⁻¹ = c⁻¹ * (c * z) * c⁻¹ := by group
      _ = c⁻¹ * (z * c) * c⁻¹ := by rw [hcz]
      _ = c⁻¹ * z := by group
  have h2 : c * (o * z) * c⁻¹ * (o * z)⁻¹ = (c * o * c⁻¹) * o⁻¹ := by
    calc c * (o * z) * c⁻¹ * (o * z)⁻¹ = c * o * (z * c⁻¹) * z⁻¹ * o⁻¹ := by group
      _ = c * o * (c⁻¹ * z) * z⁻¹ * o⁻¹ := by rw [hzc]
      _ = (c * o * c⁻¹) * o⁻¹ := by group
  rw [h2]
  exact O.mul_mem h1 (O.inv_mem ho)

end CFSG.RankThree.PartTwo.Sec15
