module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofImg
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Steps

@[expose] def Step148RankImgGeFieldTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) → J = Y →
        letI := ker148_normal hY.2
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y)

theorem step148RankImgGeField_of_top (hTop : Step148RankImgGeFieldTop) :
    Step148RankImgGeField := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA
  by_cases hJYeq : J = Y
  · exact hTop G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hJYeq
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

end Steps

end CFSG.RankThree.PartTwo.Sec14
