module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
import CFSG.RankThree.PartTwo.Sec15.Gagen1511WStar
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec14.Concrete

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Abstract

private theorem res1B203_eq_one_of_commute {D : Type*} [Group D] [IsSimpleGroup D]
    {V : Subgroup D} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V) {e : D}
    (hcomm : ∀ v ∈ V, v * e = e * v) : e = 1 := by
  have hne : V ≠ ⊥ := by
    rintro rfl
    obtain ⟨-, -, a, b, hab⟩ := hVq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim x y])
  have htop : V = ⊤ := (hV.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left hne
  have hec : e ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g (htop ▸ Subgroup.mem_top g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D) with hc | hc
  · rw [hc] at hec
    exact Subgroup.mem_bot.mp hec
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hVq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : (x : D) ∈ Subgroup.center D := hc ▸ Subgroup.mem_top _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx (y : D)).symm

private theorem res1B203_nontrivial {D : Type*} [Group D] {V : Subgroup D}
    (hVq : CFSG.IsQuasisimple ↥V) : Nontrivial D := by
  by_contra hD
  rw [not_nontrivial_iff_subsingleton] at hD
  obtain ⟨-, -, a, b, hab⟩ := hVq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [Subsingleton.elim x y])

end Abstract

section Types

private theorem res1B203_isSimpleGroup {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) : IsSimpleGroup X := by
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact e.isSimpleGroup

private theorem res1B203_card {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Nat.card X = 2520 ∨ Nat.card X = 443520 := by
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  · right
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_nativeM22

private theorem res1B203_not_isoLThreePi {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi X p e := by
  rcases res1B203_card hQ with h | h
  · exact Proof1514.not_isoLThreePi_of_card_2520 h p e
  · exact KFacts.KS14.not_isoLThreePi_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22) p e

private theorem res1B203_not_isLThreeEpsAt {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) (p f : ℕ) [Fact p.Prime] :
    ¬ IsLThreeEpsAt X p f := by
  rcases res1B203_card hQ with h | h
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) Proof1514.checkSL_a7)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) Proof1514.checkSU_a7) p f
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22) p f

private theorem res1B203_not_j2 {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    ¬ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [KFacts.KS14.card_nativeJ2] at h
  rcases res1B203_card hQ with h' | h' <;> omega

end Types

theorem res1_b155_eq_bot
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hQ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P' : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P')
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hMX : M = Subgroup.normalizer (X : Set G)) : b155 A M X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hR.toSec14Std
  have hD0 := hR.toSec13Data
  have h3L : 3 ∣ Nat.card L := by
    refine Proof1515.three_dvd_card_of_thetaQuot ?_
    rcases res1B203_card hQ with hc | hc <;> rw [hc] <;> norm_num
  have hQ' : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact Set.mem_singleton_iff.mp hc'
    have hLL : L' = L := Proof1515.eq_of_mem_lA_of_zpowers_eq h h3L hcc hL'
    rw [hLL]
    exact hQ
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXY : X ≤ Y := hC.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hMXm : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G) := by
    refine ⟨hC.mem_m.1, ?_⟩
    have hAY : (A ⊔ Y : Subgroup G) ≤ M := hC.mem_m.2
    exact fun z hz => (sup_le (hXY.trans (le_sup_right.trans hAY))
      (le_sup_left.trans hAY)) hz
  obtain ⟨hXM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hMXm
  let : (ker148 A M).Normal := ker148_normal hM2.1.2
  obtain ⟨heq149, -, -⟩ := h149 M hM2.1
  have hI₀Δ : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M := by
    rw [heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hXI₀ : X ≤ oPrimeResidualOf 3 (delta A (lB A) M) := le_oPrimeResidualOf_delta hX4 hXM
  have hI₀M : oPrimeResidualOf 3 (delta A (lB A) M) ≤ M :=
    (Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le M)
  have hBI₀ : b155 A M X ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
    oPrimeResidualOf_mono (p := 3) (K := u155 A M X) inf_le_left
  have hXD : X ≤ deltaZero A (lB A) M := hXI₀.trans hI₀Δ
  set D := img148 A M (deltaZero A (lB A) M) with hD
  set V := (img148 A M X).subgroupOf D with hV
  have hVsub : V.IsSubnormal := by
    rw [hV, hD]
    exact Proof153Twin3.isSubnormal_img_subgroupOf hAM hE.mem_x
  obtain ⟨eY⟩ := Proof155INorm.nonempty_quot_equiv_img hAM hE.mem_x hXD
  have hVq : CFSG.IsQuasisimple ↥V := CFSG.LocalCores.isQuasisimple_of_mulEquiv eY
    (Proof1515.isQuasisimple_quot_pPrimeCore hX4)
  have hDs : IsSimpleGroup ↥D := by
    rcases (h148 M hM2.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
    ·
      exfalso
      have hD1 : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
      have hsub : Subsingleton ↥D := by
        rw [hD, hD1]
        exact inferInstance
      exact (not_nontrivial_iff_subsingleton.mpr hsub) (res1B203_nontrivial hVq)
    ·
      obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
      have := res1B203_isSimpleGroup (hQ' hc' hL')
      have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by simp)
      rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, -⟩ | ⟨⟨φ⟩, -⟩
      · exact φ.isSimpleGroup
      · exact φ.isSimpleGroup
      · have := hp
        exact (res1B203_not_isoLThreePi (hQ' hc' hL') p (f * e') hiso).elim
      · exact (res1B203_not_j2 (hQ' hc' hL') ⟨φ⟩).elim
    ·
      obtain ⟨c', d, L', hc', hL', ⟨φ⟩, -⟩ := h3
      exact (res1B203_not_j2 (hQ' hc' hL') ⟨φ⟩).elim
    ·
      obtain ⟨-, -, hW⟩ := h4
      exact (Proof1511Point.not_wStarS4_of_le_normalizer hR.isE27 hD0.mem_A hD0.ne_one hN
        hW).elim
    ·
      obtain ⟨c', hcA, L', n, m, hc', hL', -, -, -, -, -, -, hε, -⟩ := h5
      exact (res1B203_not_isLThreeEpsAt (hQ' hc' hL') 2 (n * m) hε).elim
    ·
      obtain ⟨-, ⟨c', L', hc', hL', ⟨φ⟩⟩, -⟩ := h6
      exact (res1B203_not_j2 (hQ' hc' hL') ⟨φ⟩).elim
    ·
      obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, hΩ₁, -, hL₁, -, -, -, -,
        -, -, -, -, -, -, -, -, hiso, -⟩ := h7
      have := hp₁
      exact (res1B203_not_isoLThreePi (hQ' hΩ₁ hL₁) p₁ (f₁ * e₁) hiso).elim
  have hO2M : CFSG.Open.pCoreOf 2 X ≤ pPrimeCoreOf 3 M := by
    refine Sec14.le_pPrimeCoreOf ?_ ?_ ?_
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXM
    · rw [hMX]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
  have hBle : b155 A M X ≤ pPrimeCoreOf 3 M := by
    intro b hb
    have hbU : b ∈ u155 A M X := Sec14.oPrimeResidualOf_le_self 3 _ hb
    have hbM : b ∈ M := hI₀M (hBI₀ hb)
    have hbMA : b ∈ M ⊔ A := Subgroup.mem_sup_left hbM
    have hbD : b ∈ deltaZero A (lB A) M := hI₀Δ (hBI₀ hb)
    have heD : QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩ ∈ D :=
      mem_img148_iff.mpr ⟨b, hbMA, hbD, rfl⟩
    have hone : (⟨QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩, heD⟩ : ↥D) = 1 := by
      refine res1B203_eq_one_of_commute hVsub hVq ?_
      intro v hv
      obtain ⟨x, hxMA, hxX, hxv⟩ := mem_img148_iff.mp (Subgroup.mem_subgroupOf.mp hv)
      have hcomm : ⁅x, b⁆ ∈ pPrimeCoreOf 3 M := hO2M (hbU.2.2.2 x hxX)
      have hmemMA : ⁅x, b⁆ ∈ M ⊔ A := Subgroup.mem_sup_left (Sec14.pPrimeCoreOf_le 3 M hcomm)
      have hz : QuotientGroup.mk' (ker148 A M) ⟨⁅x, b⁆, hmemMA⟩ = 1 :=
        mk'_ker148_eq_one_iff.mpr hcomm
      have heq : (⟨⁅x, b⁆, hmemMA⟩ : ↥(M ⊔ A)) =
          ⁅(⟨x, hxMA⟩ : ↥(M ⊔ A)), (⟨b, hbMA⟩ : ↥(M ⊔ A))⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [heq, map_commutatorElement] at hz
      have hcm := commutatorElement_eq_one_iff_mul_comm.mp hz
      apply Subtype.ext
      change (v : ↥(M ⊔ A) ⧸ ker148 A M) * QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩ =
        QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩ * (v : ↥(M ⊔ A) ⧸ ker148 A M)
      rw [← hxv]
      exact hcm
    exact mk'_ker148_eq_one_iff.mp (congrArg Subtype.val hone)
  have hB3 : ¬ 3 ∣ Nat.card (b155 A M X) := by
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Sec14.coprime_card_pPrimeCoreOf 3 M) (h3.trans (Subgroup.card_dvd_of_le hBle))
  have hB1 : oPrimeResidualOf 3 (b155 A M X) = ⊥ :=
    Sec16.oPrimeResidualOf_three_eq_bot_of_not_dvd hB3
  have hBB : oPrimeResidualOf 3 (b155 A M X) = b155 A M X :=
    Sec14.oPrimeResidualOf_eq_of_le (Sec14.oPrimeResidualOf_le_self 3 _) fun x hx k hk => by
      show x ∈ oPrimeResidualOf 3 (u155 A M X)
      rw [Sec14.oPrimeResidualOf_eq_closure]
      exact Subgroup.subset_closure ⟨hx, k, hk⟩
  exact hBB.symm.trans hB1

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
