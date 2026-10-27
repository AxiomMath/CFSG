module

import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofA10Gen
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
public import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofImg
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Item148Res4

namespace Item148Res6

section Steps

theorem step148RankImgGeField_of_ne :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) → J ≠ Y →
        letI := ker148_normal hY.2
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hJYeq
  let := ker148_normal hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1).trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hJ' : J ∈ scriptY A := ⟨fun h => hY.1 (top_le_iff.mp (h ▸ hJY)), hAJ⟩
  have hcard : Nat.card J < Nat.card Y := Subgroup.card_lt_of_lt (lt_of_le_of_ne hJY hJYeq)
  have hnorm := (ih J hJ' hcard).1
  obtain ⟨n, hn, hKn, hJn, -⟩ := hF
  have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJs : IsSimpleGroup ↥(img148 A Y J) :=
    (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega) hJn).1
  have hJ3 : 3 ∣ Nat.card ↥(img148 A Y J) :=
    Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi (by omega) hJn
  have hK3 : 3 ∣ Nat.card ↥(img148 A Y K) :=
    Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hKn
  set φ : ↥J →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hJM) with hφ
  have hrange : φ.range = img148 A Y J := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hRs : IsSimpleGroup ↥φ.range := by
    rw [hrange]
    exact hJs
  have hker : CFSG.pPrimeCore 3 ↥J ≤ φ.rangeRestrict.ker := by
    set P := (CFSG.pPrimeCore 3 ↥J).map φ.rangeRestrict with hPdef
    have hPn : P.Normal :=
      (inferInstance : (CFSG.pPrimeCore 3 ↥J).Normal).map _ φ.rangeRestrict_surjective
    have hP3 : ¬ 3 ∣ Nat.card P := by
      intro h3
      have h1 := h3.trans (Subgroup.card_map_dvd _ _)
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)) h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
    · intro x hx
      rw [MonoidHom.mem_ker]
      have : φ.rangeRestrict x ∈ P := Subgroup.mem_map_of_mem _ hx
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hP3
      rw [ht, Subgroup.card_top, Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv]
      exact hJ3
  set φ' := QuotientGroup.lift (CFSG.pPrimeCore 3 ↥J) φ.rangeRestrict hker with hφ'
  have hφ's : Function.Surjective φ' := by
    intro y
    obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective y
    exact ⟨(x : ↥J ⧸ CFSG.pPrimeCore 3 ↥J), rfl⟩
  set D := (((deltaZero A (lB A) J).subgroupOf J).map
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))).map φ' with hD
  have hDn : D.Normal := hnorm.map _ hφ's
  have hDmem : ∀ g : G, g ∈ deltaZero A (lB A) J → (hg : g ∈ J) →
      φ.rangeRestrict ⟨g, hg⟩ ∈ D := by
    intro g hgX hg
    exact ⟨_, ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩, rfl⟩
  have hKX : K ≤ deltaZero A (lB A) J :=
    hP.2.2.2.2.2.2.1.le.trans (deltaZero_mono148 hKJ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with hb | ht
  · exfalso
    have hK1 : img148 A Y K = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨g, hgM, hgK, rfl⟩ := mem_img148_iff.mp hz
      have h1 := hDmem g (hKX hgK) (hKJ hgK)
      rw [hb, Subgroup.mem_bot] at h1
      have h2 : (φ.rangeRestrict ⟨g, hKJ hgK⟩ : ↥(Y ⊔ A) ⧸ ker148 A Y) = 1 := by
        rw [h1]
        rfl
      rw [Subgroup.mem_bot]
      exact h2
    rw [hK1, Subgroup.card_bot] at hK3
    norm_num at hK3
  · intro z hz
    have hzR : z ∈ φ.range := hrange ▸ hz
    have : (⟨z, hzR⟩ : ↥φ.range) ∈ D := ht ▸ Subgroup.mem_top _
    obtain ⟨w, ⟨x, hx, rfl⟩, hwz⟩ := this
    have hx' : (x : G) ∈ deltaZero A (lB A) J := Subgroup.mem_subgroupOf.mp hx
    have h1 : z = ((φ' (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x) : ↥φ.range) :
        ↥(Y ⊔ A) ⧸ ker148 A Y) := (congrArg Subtype.val hwz).symm
    rw [h1]
    exact mem_img148_iff.mpr ⟨x, hJM x.2, deltaZero_mono148 hJY hx', rfl⟩

theorem step148RankImgGe_ten :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Ten A Y K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        letI := ker148_normal hY.2
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hTen hA
  have := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hstd.toSec13Data.mem_partTwoE
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) := hP.2.2.2.2.2.1
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) := hKYC.trans inf_le_right
  have hKX : K ≤ deltaZero A (lB A) Y :=
    hP.2.2.2.2.2.2.1.le.trans (deltaZero_mono148 (hKYC.trans inf_le_left))
  have hle : img148 A Y A ≤ img148 A Y J :=
    Item148Rank.img148_le_of_lift148Ten148 hAF hAY he hK hKJ hJY hAJ hkt.1 hTen
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  obtain ⟨⟨φK⟩, ⟨φJ⟩⟩ := hTen
  set Q' := ↥(Y ⊔ A) ⧸ ker148 A Y
  set Jb := img148 A Y J with hJb
  set Kb := img148 A Y K with hKb
  set Ab := img148 A Y A with hAb
  set Xb := img148 A Y (deltaZero A (lB A) Y) with hXb
  have hKJb : Kb ≤ Jb := img148_mono hKJ
  set E := Ab.subgroupOf Jb with hE
  set K' := Kb.subgroupOf Jb with hK'
  set M := Xb.subgroupOf Jb with hM
  obtain ⟨hAbE, hAb27⟩ := img148_isE27 (Y := Y) hA27
  have hE27 : Nat.card E = 27 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hAb27]
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h := congrArg Subtype.val (hAbE.1.is_comm.comm
        ⟨((x : ↥Jb) : Q'), Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨((y : ↥Jb) : Q'), Subgroup.mem_subgroupOf.mp y.2⟩)
      simpa using h
    · apply Subtype.ext
      have h := hAbE.2 ((x : ↥Jb) : Q') (Subgroup.mem_subgroupOf.mp hx)
      simpa using h
  have heJ : alpha148 A Y e he ∈ Jb := hle (alpha148_mem_img148 he)
  set x : ↥Jb := ⟨alpha148 A Y e he, heJ⟩ with hx
  have hxE : x ∈ E := Subgroup.mem_subgroupOf.mpr (alpha148_mem_img148 he)
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : alpha148 A Y e he = alpha148 A Y 1 A.one_mem := by
      have h3 : alpha148 A Y e he = 1 := congrArg Subtype.val h1
      rw [h3, alpha148_eq_mk']
      exact (map_one _).symm
    exact he1 (alpha148_injective hA3 he A.one_mem h2)
  have hK'x : K' ≤ Subgroup.centralizer ({x} : Set ↥Jb) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨g, hg, hgK, hgz⟩ := mem_img148_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (z : Q') * alpha148 A Y e he = alpha148 A Y e he * (z : Q')
    rw [← hgz, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKC hgK))
  have hK'7 : Nonempty (↥K' ≃* alternatingGroup (Fin 7)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKJb).trans φK⟩
  have hK'M : K' ≤ M := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (img148_mono hKX (Subgroup.mem_subgroupOf.mp hz))
  have hNM : Subgroup.normalizer (E : Set ↥Jb) ≤ Subgroup.normalizer (M : Set ↥Jb) := by
    intro n hn
    have hnQ : (n : Q') ∈ Subgroup.normalizer (Ab : Set Q') := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hle hy⟩).mp
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hy
        have hy' : y ∈ Jb := by
          have h2 : (n : Q')⁻¹ * ((n : Q') * y * (n : Q')⁻¹) * (n : Q') ∈ Jb :=
            Jb.mul_mem (Jb.mul_mem (Jb.inv_mem n.2) (hle hy)) n.2
          rwa [show (n : Q')⁻¹ * ((n : Q') * y * (n : Q')⁻¹) * (n : Q') = y by group] at h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hy'⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
    have hnX := mem_normalizer_img148_deltaZero hA3 hAY hnQ
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hnX z
  have hMtop := kf148A10Gen_holds ↥Jb ⟨φJ⟩ E K' M x hEab hE27 hxE hx1 hK'x hK'7 hK'M hNM
  intro z hz
  have : (⟨z, hz⟩ : ↥Jb) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end Steps

end Item148Res6

end CFSG.RankThree.PartTwo.Sec14
