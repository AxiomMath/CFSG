module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJA6
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelveImg

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148

section Certificates


@[expose] def Step148NormalHJA6One2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
        img148 A Y (deltaZero A (lB A) Y) = img148 A Y J →
        (omegaA A).ncard ≠ 12 →
        ∀ (y : G) (hy : y ∈ Y),
          QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) ∈
            Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))


theorem step148NormalHJA6One_of_two (h134 : Item134) (h48 : Sec4.Item4_8)
    (hTwo : Step148NormalHJA6One2) : Step148NormalHJA6One := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ
  by_cases h12 : (omegaA A).ncard = 12
  swap
  · exact hTwo G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
      hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ h12
  intro y hy
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨η⟩ := hη
  have hYd6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr η.symm hJ6
  obtain ⟨-, hdYB, -⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hYd6
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hJcard : Nat.card ↥(img148 A Y J) = 1080 :=
    Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hJ6
  have h3J' : 3 ∣ Nat.card ↥(img148 A Y J) := by rw [hJcard]; norm_num
  have h3J : 3 ∣ Nat.card J := h3J'.trans (card_img148_dvd hJM)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  set dα := alpha148 A Y d hdA with hdαdef
  have hdJ : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ (hYBYd hdYB), rfl⟩
  have hdC : img148 A Y J ≤ Subgroup.centralizer {dα} :=
    HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  by_contra hN
  set x := QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) with hx
  have hne : (img148 A Y J).map (MulAut.conj x).toMonoidHom ≠ img148 A Y J := by
    intro heq'
    apply hN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq'
  set K := (img148 A Y J).map (MulAut.conj x).toMonoidHom with hK
  have hKc : IsComponent K := Res2LBal.isComponent_conj hJc x
  have hKJ : img148 A Y J ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun z hz => Res2LBal.mem_centralizer_of_mem_of_ne hKc hJc hne hz
  have eK : ↥(img148 A Y J) ≃* ↥K :=
    (img148 A Y J).equivMapOfInjective _ (MulAut.conj x).injective
  have hK6 : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr eK hJ6
  have hdZ : dα ∈ K ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [center_eq_of_tripleCover_A6148 hS hJc hJ6 x hne]
    refine Subgroup.mem_inf.mpr ⟨hdJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hdC hz))
  have hKd : K ≤ Subgroup.centralizer {dα} := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdZ.2 z hz
  have hxY : x ∈ img148 A Y Y := mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_left hy, hy, rfl⟩
  have hKY : K ≤ img148 A Y Y := by
    rintro _ ⟨z, hz, rfl⟩
    exact (img148 A Y Y).mul_mem ((img148 A Y Y).mul_mem hxY (img148_mono hJY hz))
      ((img148 A Y Y).inv_mem hxY)
  exact false_of_ncard_twelve_img148' h134 h48 hS hY hB hc h12 hdA _ _ (img148_mono hJY) hKY
    hdC hKd hKJ (isTwelveType_of_tripleCover_A6 hJ6 hJc.1.1)
    (isTwelveType_of_tripleCover_A6 hK6 hKc.1.1)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
