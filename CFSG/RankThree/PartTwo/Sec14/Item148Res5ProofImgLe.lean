module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofComp
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofA10
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec5.Items52

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Item148Res5

section Quot

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem eq_bot_of_le_img148_of_coprime {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hPY : P ≤ img148 A Y Y)
    (hPN : img148 A Y Y ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hP3 : ¬ 3 ∣ Nat.card P) : P = ⊥ := by
  set P₀ : Subgroup G := (P.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype ⊓ Y
    with hP₀
  have hP₀Y : P₀ ≤ Y := inf_le_right
  have key : ∀ y ∈ Y, ∀ g ∈ P₀, y * g * y⁻¹ ∈ P₀ := by
    intro y hy g hg
    obtain ⟨⟨m, hm, rfl⟩, hgY⟩ := hg
    have hyM : y ∈ Y ⊔ A := Subgroup.mem_sup_left hy
    refine ⟨⟨⟨y, hyM⟩ * m * (⟨y, hyM⟩ : ↥(Y ⊔ A))⁻¹, ?_, rfl⟩,
      Y.mul_mem (Y.mul_mem hy hgY) (Y.inv_mem hy)⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hyα : QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ ∈ img148 A Y Y :=
      mem_img148_iff.mpr ⟨y, hyM, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPN hyα) _).mp hm
  have hnorm : Y ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key y hy g, fun h => ?_⟩
    have h1 := key y⁻¹ (Y.inv_mem hy) _ h
    rwa [show y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g by group] at h1
  have hcop : Nat.Coprime 3 (Nat.card P₀) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨⟨m, hm, hmg⟩, -⟩ := g.2
    have hmg' : (m : G) = (g : G) := hmg
    have hm3 : m ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hmg', Subgroup.coe_one, ← Subgroup.coe_pow, ← hg,
        pow_orderOf_eq_one, Subgroup.coe_one]
    have hmα3 : (QuotientGroup.mk' (ker148 A Y) m) ^ 3 = 1 := by rw [← map_pow, hm3, map_one]
    have h1 : QuotientGroup.mk' (ker148 A Y) m = 1 :=
      Res2LBal.eq_one_of_mem_of_pow hP3 hm (m := 1) (by rw [pow_one]; exact hmα3)
    rw [mk'_ker148_eq_one_iff] at h1
    have h2 : (m : G) = 1 := eq_one_of_pow_three_pow_eq_one148
      (coprime_card_pPrimeCoreOf 3 Y) h1 (k := 1) (by
        rw [pow_one, ← Subgroup.coe_pow, hm3, Subgroup.coe_one])
    have h3' : (g : G) = 1 := hmg' ▸ h2
    have : g = 1 := Subtype.ext h3'
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hle := le_pPrimeCoreOf hP₀Y hnorm hcop
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, hgM, hgY, rfl⟩ := mem_img148_iff.mp (hPY hx)
  rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
  exact hle ⟨⟨⟨g, hgM⟩, hx, rfl⟩, hgY⟩

theorem exists_lift_centralizer148 (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {B H : Subgroup G} (hBA : B ≤ A)
    (hBH : B ≤ Subgroup.normalizer (H : Set G))
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hxH : x ∈ img148 A Y H)
    (hxB : x ∈ Subgroup.centralizer (img148 A Y B : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ∃ (g : G) (hg : g ∈ Y ⊔ A), g ∈ H ∧ g ∈ Subgroup.centralizer (B : Set G) ∧
      QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ = x := by
  obtain ⟨k, hkM, hkH, rfl⟩ := mem_img148_iff.mp hxH
  have hB3 : IsPGroup 3 B := isPGroup_three_of_pow148 fun b hb => hA3 b (hBA hb)
  have hN3 : Nat.Coprime 3 (Nat.card (H ⊓ pPrimeCoreOf 3 Y : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_pPrimeCoreOf 3 Y)
  have hBN : B ≤ Subgroup.normalizer ((H ⊓ pPrimeCoreOf 3 Y : Subgroup G) : Set G) :=
    le_trans (le_inf hBH (hBA.trans (hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y))))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hk : ∀ b ∈ B, k⁻¹ * (b * k * b⁻¹) ∈ H ⊓ pPrimeCoreOf 3 Y := by
    intro b hb
    refine ⟨H.mul_mem (H.inv_mem hkH) ((Subgroup.mem_normalizer_iff.mp (hBH hb) k).mp hkH), ?_⟩
    have hbM : b ∈ Y ⊔ A := Subgroup.mem_sup_right (hBA hb)
    have hbα : QuotientGroup.mk' (ker148 A Y) ⟨b, hbM⟩ ∈ img148 A Y B :=
      mem_img148_iff.mpr ⟨b, hbM, hb, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hxB _ hbα
    have e1 : QuotientGroup.mk' (ker148 A Y) ⟨k, hkM⟩ =
        QuotientGroup.mk' (ker148 A Y) (⟨b, hbM⟩ * ⟨k, hkM⟩ * (⟨b, hbM⟩ : ↥(Y ⊔ A))⁻¹) := by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    have h1 := mk'_ker148_eq_iff.mp e1
    simpa using h1
  obtain ⟨y, hy, hyc⟩ := exists_commute_mem_coset148 hB3 hN3 hBN hk
  have hyeq : y = k * (k⁻¹ * y) := by group
  have hyM : y ∈ Y ⊔ A := by
    rw [hyeq]
    exact (Y ⊔ A).mul_mem hkM (Subgroup.mem_sup_left ((pPrimeCoreOf_le 3 Y) hy.2))
  refine ⟨y, hyM, ?_, ?_, ?_⟩
  · rw [hyeq]
    exact H.mul_mem hkH hy.1
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hyc b hb
  · rw [mk'_ker148_eq_iff]
    have h1 := (pPrimeCoreOf 3 Y).inv_mem hy.2
    simpa using h1

omit [Finite G] in
theorem img148_normal (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    (img148 A Y Y).Normal := by
  have hN : img148 A Y (Y ⊔ A) ≤
      Subgroup.normalizer (img148 A Y Y : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (sup_le Subgroup.le_normalizer hAY)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) g
  have hm : QuotientGroup.mk' (ker148 A Y) m ∈ img148 A Y (Y ⊔ A) :=
    mem_img148_iff.mpr ⟨m, m.2, m.2, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hN hm) n).mp hn

omit [Finite G] in
theorem isComponent_img148 (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hJs : IsSimpleGroup ↥(img148 A Y J)) :
    IsComponent (img148 A Y J) ∧ Subgroup.center ↥(img148 A Y J) = ⊥ := by
  obtain ⟨hJY, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hnc : ∃ a b : ↥(img148 A Y J), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥(img148 A Y J) := ⟨⟨fun a b => hcon a b⟩⟩
    have : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
    exact Group.IsPerfect.not_isMulCommutative ↥(img148 A Y J) hcomm
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
  have hsub : ((img148 A Y J).subgroupOf (img148 A Y Y)).IsSubnormal :=
    Main148.isSubnormal_img148 hJY le_sup_left hJ'.2.1
  have hYsn : (img148 A Y Y).IsSubnormal := (img148_normal hAY).isSubnormal
  exact ⟨⟨hq, Subgroup.IsSubnormal.trans (img148_mono hJY) hsub hYsn⟩, hZ⟩

end Quot

end Item148Res5

open Item148Res5

section Steps


theorem step148RankImgLeEq_holds :
    Step148RankImgLeEq := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hA
  let := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have h27 : Nat.card A = 27 := hstd.toSec13Data.card_eq
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h := isSimpleGroup_img148_of_kType148 hstd hkt
    rw [hJeq] at h
    exact h
  obtain ⟨hJc, hJZ⟩ := isComponent_img148 hAY hJ hJs
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have heJ : alpha148 A Y e he ∈
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have : alpha148 A Y e he ∈ img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [hAJc]
      exact Subgroup.mem_zpowers _
    exact this.2
  have he3 : alpha148 A Y e he ^ 3 = 1 := alpha148_pow_three hA3 he
  have hZJ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have heJn : e ∉ J := by
    intro heJ'
    have h1 : alpha148 A Y e he ∈ img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      ⟨mem_img148_iff.mpr ⟨e, Subgroup.mem_sup_right he, heJ', rfl⟩, heJ⟩
    rw [hZJ, Subgroup.mem_bot] at h1
    apply he1
    refine alpha148_injective (Y := Y) hA3 he A.one_mem ?_
    rw [h1, alpha148_eq_mk']
    exact (map_one _).symm
  have hB0 : IsHyperplane A (A ⊓ J) := by
    refine ⟨inf_le_left, ?_⟩
    have hN : A ⊓ J ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
      intro a ha
      refine Subgroup.centralizer_le_normalizer (Subgroup.zpowers e : Set G) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hAc e he a ha.1) k).eq
    have hdvd := Item148Res4.card_sup_dvd_of_le_normalizer (Subgroup.zpowers e) (A ⊓ J) hN
    rw [← hA, h27] at hdvd
    have he3' : Nat.card (Subgroup.zpowers e) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 e he))
    have hle27 := Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) hdvd
    have hdiv : Nat.card ↥(A ⊓ J) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
    have hne : Nat.card ↥(A ⊓ J) ≠ 27 := by
      intro h
      apply heJn
      have hAJ' : A ⊓ J = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h27])
      exact (hAJ' ▸ (inf_le_right : A ⊓ J ≤ J)) he
    interval_cases k
    · rw [hk] at hle27
      nlinarith
    · rw [hk] at hle27
      nlinarith
    · rw [hk, h27]
      norm_num
    · exact absurd hk hne
  have hAeq : img148 A Y A = Subgroup.zpowers (alpha148 A Y e he) ⊔ img148 A Y (A ⊓ J) := by
    have h0 : img148 A Y (Subgroup.zpowers e ⊔ (A ⊓ J)) = img148 A Y A := by rw [← hA]
    rw [← h0, img148_sup ((Subgroup.zpowers_le.mpr he).trans le_sup_right)
      ((inf_le_left.trans le_sup_right))]
    congr 1
    refine le_antisymm (img148_zpowers_le he) ?_
    rw [Subgroup.zpowers_le]
    exact mem_img148_iff.mpr ⟨e, Subgroup.mem_sup_right he, Subgroup.mem_zpowers e, rfl⟩
  have hB0J : img148 A Y (A ⊓ J) ≤ img148 A Y J := img148_mono inf_le_right
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        w ^ 3 = 1 → w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hAF hAY hw hw3
  have hAJle : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
        Subgroup.zpowers (alpha148 A Y e he) := hAJc.le
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ := Item148Res4.exists_ne_one_mem_inf148 (hA3 e he) h27 hA
    have hb3 : alpha148 A Y b hbA ^ 3 = 1 := alpha148_pow_three hA3 hbA
    have hb1' : alpha148 A Y b hbA ≠ 1 := by
      intro h
      apply hb1
      refine alpha148_injective (Y := Y) hA3 hbA A.one_mem ?_
      rw [h, alpha148_eq_mk']
      exact (map_one _).symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (alpha148 A Y b hbA) = 3 := orderOf_eq_prime hb3 hb1'
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _
      (mem_img148_iff.mpr ⟨b, Subgroup.mem_sup_right hbA, hbJ, rfl⟩)
  have hAJC : img148 A Y A ≤ img148 A Y J ⊔
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hAeq]
    refine sup_le ?_ (hB0J.trans le_sup_left)
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right heJ
  have hJYb : img148 A Y J ≤ img148 A Y Y := img148_mono hJY
  have hO3 : ∀ P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), P ≤ img148 A Y Y →
      img148 A Y Y ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ¬ 3 ∣ Nat.card P → P = ⊥ := fun P h1 h2 h3 => eq_bot_of_le_img148_of_coprime h1 h2 h3
  set OB := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ((A ⊓ J : Subgroup G) : Set G)) with hOB
  have hOBM : OB ≤ Y ⊔ A := (pPrimeCoreOf_le 3 _).trans (inf_le_left.trans le_sup_left)
  have hOB3 : ¬ 3 ∣ Nat.card (img148 A Y OB) := by
    refine Item148PtRes.not_three_dvd_card_img148 ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hOBN : img148 A Y Y ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
        Subgroup.normalizer (img148 A Y OB : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx
    have hxB : x ∈ Subgroup.centralizer (img148 A Y (A ⊓ J) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      Subgroup.centralizer_le hB0J hx.2
    obtain ⟨g, hg, hgY, hgB, rfl⟩ := exists_lift_centralizer148 hA3 hAY inf_le_left
      (inf_le_left.trans hAY) hx.1 hxB
    exact img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 _)
      (mem_img148_iff.mpr ⟨g, hg, ⟨hgY, hgB⟩, rfl⟩)
  refine Item148Res4.img148_deltaZero_le fun R hR => ?_
  have hRY : R ≤ Y := hR.2
  have hRM : R ≤ Y ⊔ A := hRY.trans le_sup_left
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := (mem_scriptQ_iff.mp hR.1.1).2.1
  have hR3 : ¬ 3 ∣ Nat.card R :=
    (isPiSubgroup_piCompl_iff Nat.prime_three R).mp (mem_scriptQ_iff.mp hR.1.1).1
  have hRcomm : img148 A Y R ≤ ⁅img148 A Y R, img148 A Y A⁆ := by
    conv_lhs => rw [hR.1.2]
    rw [Item148PtRes.img148_commutator hRM le_sup_right]
  have hRN : img148 A Y R ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_normalizer_of_component hJc h3J he3 heJ hB0J hAeq hF3 hAJle hRcomm
  have hRJC : img148 A Y R ≤ img148 A Y J ⊔
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_sup_centralizer_of_le_commutator hAJC hRN hRcomm
  have hARb : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y R : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAR
  have hkey : ∀ y ∈ img148 A Y R,
      y ∈ Subgroup.centralizer (img148 A Y (A ⊓ J) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ⁅y, alpha148 A Y e he⁆ ∈ img148 A Y J := by
    intro y hyR hyB
    obtain ⟨g, hgM, hgR, hgB, rfl⟩ := exists_lift_centralizer148 hA3 hAY inf_le_left
      ((inf_le_left : A ⊓ J ≤ A).trans hAR) hyR hyB
    set R₀ := R ⊓ Subgroup.centralizer ((A ⊓ J : Subgroup G) : Set G) with hR₀
    have hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G) := by
      refine le_trans (le_inf hAR ?_) Subgroup.inf_normalizer_le_normalizer_inf
      have hAB : A ≤ Subgroup.normalizer ((A ⊓ J : Subgroup G) : Set G) :=
        le_trans (le_inf Subgroup.le_normalizer hAJ) Subgroup.inf_normalizer_le_normalizer_inf
      exact hAB.trans (Sec5.normalizer_le_normalizer_centralizer _)
    have hR₀3 : Nat.Coprime 3 (Nat.card R₀) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
        hR3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hAp : IsPGroup 3 A := isPGroup_three_of_pow148 hA3
    have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3
      Nat.prime_three A R₀ hAp hAR₀ hR₀3
    have hcomR₀ : ⁅R₀, A⁆ ≤ R₀ := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      rw [commutatorElement_def, show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
      exact R₀.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hAR₀ ha) _).mp (R₀.inv_mem hx))
    have hAN₀ : A ≤ Subgroup.normalizer ((⁅R₀, A⁆ : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
      have h1 : R₀.map (MulAut.conj a) = R₀ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAR₀ ha)
      have h2 : A.map (MulAut.conj a) = A :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
      rw [h1, h2]
    have hQ0 : ⁅R₀, A⁆ ∈ collectionIn (scriptQZero A (lB A))
        (Y ⊓ Subgroup.centralizer ((A ⊓ J : Subgroup G) : Set G)) :=
      ⟨⟨mem_scriptQ_of_le hR.1.1 (hcomR₀.trans inf_le_left) hAN₀, hidem.symm⟩,
        hcomR₀.trans (inf_le_inf_right _ hRY)⟩
    have hle : ⁅R₀, A⁆ ≤ OB := (le_sSup hQ0).trans (hYB (A ⊓ J) hB0)
    have hge : ⁅g, e⁆ ∈ OB := hle (Subgroup.commutator_mem_commutator ⟨hgR, hgB⟩ he)
    have heM : e ∈ Y ⊔ A := Subgroup.mem_sup_right he
    have hgeM : ⁅g, e⁆ ∈ Y ⊔ A := by
      rw [commutatorElement_def]
      exact (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hgM heM) ((Y ⊔ A).inv_mem hgM))
        ((Y ⊔ A).inv_mem heM)
    have himg : ⁅QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩, alpha148 A Y e he⁆ ∈ img148 A Y OB := by
      refine mem_img148_iff.mpr ⟨⁅g, e⁆, hgeM, hge, ?_⟩
      rw [alpha148_eq_mk', ← map_commutatorElement]
      rfl
    have hyR' : QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩ ∈ img148 A Y R :=
      mem_img148_iff.mpr ⟨g, hgM, hgR, rfl⟩
    have hzR : ⁅QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩, alpha148 A Y e he⁆ ∈ img148 A Y R := by
      have h1 : alpha148 A Y e he * (QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩)⁻¹ *
          (alpha148 A Y e he)⁻¹ ∈ img148 A Y R :=
        (Subgroup.mem_normalizer_iff.mp (hARb (alpha148_mem_img148 he)) _).mp (inv_mem hyR')
      have e2 : ⁅QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩, alpha148 A Y e he⁆ =
          QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩ * (alpha148 A Y e he *
            (QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩)⁻¹ * (alpha148 A Y e he)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e2]
      exact mul_mem hyR' h1
    exact mem_of_mem_sup_centralizer hJc h3J hJYb hO3 hZJ hOB3 hOBN himg
      ((img148_mono hRY) hzR) (hRJC hzR)
  have hxe : ∀ x ∈ img148 A Y R, ⁅x, alpha148 A Y e he⁆ ∈ img148 A Y J := by
    intro x hx
    have hB3 : IsPGroup 3 (img148 A Y (A ⊓ J)) := by
      refine isPGroup_three_of_pow148 fun b hb => ?_
      obtain ⟨a, ha, haA, rfl⟩ := mem_img148_iff.mp hb
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 a haA.1)
      rw [this, map_one]
    have hN3 : Nat.Coprime 3 (Nat.card ↥(img148 A Y R ⊓ img148 A Y J)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
        Item148PtRes.not_three_dvd_card_img148 hR3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hBN : img148 A Y (A ⊓ J) ≤ Subgroup.normalizer
        ((img148 A Y R ⊓ img148 A Y J : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) :
          Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      le_trans (le_inf ((img148_mono inf_le_left).trans hARb) (hB0J.trans Subgroup.le_normalizer))
        Subgroup.inf_normalizer_le_normalizer_inf
    have hk : ∀ b ∈ img148 A Y (A ⊓ J), x⁻¹ * (b * x * b⁻¹) ∈ img148 A Y R ⊓ img148 A Y J := by
      intro b hb
      refine Subgroup.mem_inf.mpr ⟨(img148 A Y R).mul_mem ((img148 A Y R).inv_mem hx)
        ((Subgroup.mem_normalizer_iff.mp (hARb (img148_mono inf_le_left hb)) x).mp hx), ?_⟩
      have h1 : x⁻¹ * b * x⁻¹⁻¹ ∈ img148 A Y J :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem (hRN hx)) b).mp (hB0J hb)
      rw [inv_inv] at h1
      rw [show x⁻¹ * (b * x * b⁻¹) = x⁻¹ * b * x * b⁻¹ by group]
      exact (img148 A Y J).mul_mem h1 ((img148 A Y J).inv_mem (hB0J hb))
    obtain ⟨y, hy, hyc⟩ := exists_commute_mem_coset148 hB3 hN3 hBN hk
    have hyR : y ∈ img148 A Y R := by
      rw [show y = x * (x⁻¹ * y) by group]
      exact mul_mem hx hy.1
    have hyB : y ∈ Subgroup.centralizer
        (img148 A Y (A ⊓ J) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb => hyc b hb
    have h1 := hkey y hyR hyB
    have hj : x⁻¹ * y ∈ img148 A Y J := hy.2
    have hjc : (x⁻¹ * y)⁻¹ * alpha148 A Y e he = alpha148 A Y e he * (x⁻¹ * y)⁻¹ :=
      Subgroup.mem_centralizer_iff.mp heJ _ (inv_mem hj)
    have e1 : ⁅x, alpha148 A Y e he⁆ = ⁅y, alpha148 A Y e he⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc x * alpha148 A Y e he * x⁻¹ * (alpha148 A Y e he)⁻¹ =
          y * ((x⁻¹ * y)⁻¹ * alpha148 A Y e he) * (x⁻¹ * y) * y⁻¹ *
            (alpha148 A Y e he)⁻¹ := by group
        _ = y * (alpha148 A Y e he * (x⁻¹ * y)⁻¹) * (x⁻¹ * y) * y⁻¹ *
            (alpha148 A Y e he)⁻¹ := by rw [hjc]
        _ = y * alpha148 A Y e he * y⁻¹ * (alpha148 A Y e he)⁻¹ := by group
    rw [e1]
    exact h1
  let T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) :=
    { carrier := {a | a ∈ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
        ∀ x ∈ img148 A Y R, ⁅x, a⁆ ∈ img148 A Y J}
      mul_mem' := by
        rintro a₁ a₂ ⟨h₁N, h₁⟩ ⟨h₂N, h₂⟩
        refine ⟨mul_mem h₁N h₂N, fun x hx => ?_⟩
        have e : ⁅x, a₁ * a₂⁆ = ⁅x, a₁⁆ * (a₁ * ⁅x, a₂⁆ * a₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (h₁ x hx) ((Subgroup.mem_normalizer_iff.mp h₁N _).mp (h₂ x hx))
      one_mem' := ⟨one_mem _, fun x _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨hN, h⟩
        refine ⟨inv_mem hN, fun x hx => ?_⟩
        have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem hN) _).mp (inv_mem (h x hx)) }
  have hAT : img148 A Y A ≤ T := by
    rw [hAeq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨Subgroup.centralizer_le_normalizer _ heJ, hxe⟩
    · intro b hb
      refine ⟨Subgroup.le_normalizer (hB0J hb), fun x hx => ?_⟩
      rw [commutatorElement_def]
      have h1 : x * b * x⁻¹ ∈ img148 A Y J :=
        (Subgroup.mem_normalizer_iff.mp (hRN hx) b).mp (hB0J hb)
      exact mul_mem h1 (inv_mem (hB0J hb))
  refine hRcomm.trans ?_
  rw [Subgroup.commutator_le]
  intro x hx a ha
  exact (hAT ha).2 x hx

end Steps

end CFSG.RankThree.PartTwo.Sec14
