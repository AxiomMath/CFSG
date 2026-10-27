module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofEps
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Res148

theorem exists_lift148 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) {e : G} (he : e ∈ A)
    (he1 : e ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer {e})) :
    ∃ J ∈ thetaComponentsIn Y, K ≤ J ∧ A ≤ Subgroup.normalizer (J : Set G) := by
  have hA : Late.IsE27 A := h.isE27
  have hAc : IsMulCommutative A := hA.1.1
  have hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n := ⟨3, le_rfl, by rw [hA.2]; norm_num⟩
  have hKYC := le_of_mem_thetaComponentsIn hK
  have hKY : K ≤ Y := hKYC.trans inf_le_left
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hK1 : K ≠ ⊥ := by
    have : Nontrivial (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have : Nontrivial ↥K := (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this
  have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hY1 | hYt
    · exact hK1 (le_bot_iff.mp (hY1 ▸ hKY))
    · exact hY.1 hYt
  have hM4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  have hYCM : Y ⊓ Subgroup.centralizer ({e} : Set G) ≤
      (Y ⊔ A) ⊓ Subgroup.centralizer ({e} : Set G) := inf_le_inf_right _ le_sup_left
  have hKM : K ∈ thetaComponentsIn ((Y ⊔ A) ⊓ Subgroup.centralizer ({e} : Set G)) := by
    have hnorm : ((Y ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf
        ((Y ⊔ A) ⊓ Subgroup.centralizer ({e} : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYCM]
      intro m hm
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMN (Subgroup.mem_inf.mp hm).1, Subgroup.le_normalizer (Subgroup.mem_inf.mp hm).2⟩
    refine Sec6.mem_thetaComponentsIn_of (hKYC.trans hYCM) hKp ?_ hKq
    exact isSubnormal_subgroupOf_trans148 hKYC hYCM
      (mem_thetaComponentsIn_iff.mp hK).2.2.1 hnorm.isSubnormal
  obtain ⟨J, hJM, hKJ⟩ := Sec6.exists_le_mem_thetaComponentsIn h48 hM4
    (le_sup_right : A ≤ Y ⊔ A) hA.1 hAn he he1 hKM
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM4 le_sup_right hA.1 hAn J hJM
  have hJY : J ≤ Y := le_of_isPerfect_of_le_sup hAc hY.2
    (isPerfect_of_mem_thetaComponentsIn hJM) (le_of_mem_thetaComponentsIn hJM)
  have hJ : J ∈ thetaComponentsIn Y := mem_thetaComponentsIn_iff.mpr
    ⟨hJY, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hJY le_sup_left
      (mem_thetaComponentsIn_iff.mp hJM).2⟩
  exact ⟨J, hJ, hKJ, hAJ⟩

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem theta_le_of_img148_eq {K J : Subgroup G} (hKM : K ≤ Y ⊔ A)
    (hKJ : img148 A Y K = img148 A Y J)
    (hJθ : aschbacherSolvableCore 3 ↥(img148 A Y J) = ⊥) :
    inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y := by
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) K with hT
  obtain ⟨hθs, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hTK : T ≤ K := Subgroup.map_subtype_le _
  have hTM : T ≤ Y ⊔ A := hTK.trans hKM
  have hTn : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T := by
    intro k hk t ht
    obtain ⟨t', ht', rfl⟩ := ht
    have : (aschbacherSolvableCore 3 ↥K).Normal := Subgroup.normal_of_characteristic _
    exact ⟨⟨k, hk⟩ * t' * ⟨k, hk⟩⁻¹, this.conj_mem t' ht' ⟨k, hk⟩, rfl⟩
  set Tα := img148 A Y T with hTα
  have hTαJ : Tα ≤ img148 A Y J := hKJ ▸ img148_mono hTK
  set N : Subgroup ↥(img148 A Y J) := Tα.subgroupOf (img148 A Y J) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨t, htM, htT, hteq⟩ := mem_img148_iff.mp hn
    have hx : ((x : ↥(img148 A Y J)) : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y K := by
      rw [hKJ]
      exact x.2
    obtain ⟨k, hkM, hkK, hkeq⟩ := mem_img148_iff.mp hx
    refine mem_img148_iff.mpr ⟨k * t * k⁻¹, (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hkM htM)
      ((Y ⊔ A).inv_mem hkM), hTn k hkK t htT, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hkeq, ← hteq, ← map_inv, ← map_mul]
    rfl
  have hTs : Group.IsSolvable ↥T := by
    have e : ↥(aschbacherSolvableCore 3 ↥K) ≃* ↥T :=
      (aschbacherSolvableCore 3 ↥K).equivMapOfInjective K.subtype K.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hNs : Group.IsSolvable ↥N := by
    have hTαs : Group.IsSolvable ↥Tα := by
      set f : ↥(T.subgroupOf (Y ⊔ A)) →* ↥Tα :=
        (QuotientGroup.mk' (ker148 A Y)).subgroupMap (T.subgroupOf (Y ⊔ A)) with hf
      have : Group.IsSolvable ↥(T.subgroupOf (Y ⊔ A)) := by
        have e := Subgroup.subgroupOfEquivOfLe hTM
        exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact Group.isSolvable_of_surjective (f := f) (MonoidHom.subgroupMap_surjective _ _)
    have e := Subgroup.subgroupOfEquivOfLe hTαJ
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hN3 : ¬ 3 ∣ Nat.card ↥N := by
    intro h3
    have hcard : Nat.card ↥N = Nat.card ↥Tα :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTαJ).toEquiv
    have h1 : Nat.card ↥Tα ∣ Nat.card ↥T := Main148.card_img148_dvd hTM
    have h2 : Nat.card ↥T = Nat.card ↥(aschbacherSolvableCore 3 ↥K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [hcard] at h3
    exact hθ3 (h2 ▸ h3.trans h1)
  have hNle := (solvable_prime_complement_core_characterization (H := ↥(img148 A Y J))
    Nat.prime_three).2.2.2.1 N hNn hNs hN3
  rw [hJθ, le_bot_iff] at hNle
  intro t ht
  have htM : t ∈ Y ⊔ A := hTM ht
  have htα : QuotientGroup.mk' (ker148 A Y) ⟨t, htM⟩ ∈ Tα := mem_img148_iff.mpr ⟨t, htM, ht, rfl⟩
  have hmem : (⟨_, hTαJ htα⟩ : ↥(img148 A Y J)) ∈ N := by
    rw [hN, Subgroup.mem_subgroupOf]
    exact htα
  rw [hNle, Subgroup.mem_bot] at hmem
  exact (mk'_ker148_eq_one_iff (g := ⟨t, htM⟩)).mp (congrArg Subtype.val hmem)

end Quot

end Res148

open Res148

@[expose] def Step148KThetaOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      ∀ J ∈ thetaComponentsIn Y, K ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        3 ∣ Nat.card J → e ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y

theorem step148KTheta_of_outer (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hO : Step148KThetaOuter) : Step148KTheta := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP
  let := ker148_normal hY.2
  have hB : IsHyperplane A B := hP.1
  have heB : e ∈ B := hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK := hP.2.2.2.2.2.1
  have he : e ∈ A := hB.1 heB
  obtain ⟨J, hJ, hKJ, hAJ⟩ := exists_lift148 h45 h48 h hY he he1 hK
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A := hKJ.trans hJM
  have hθK : inSubgroup (aschbacherSolvableCore 3) K ≤ K := Subgroup.map_subtype_le _
  by_cases h3J : 3 ∣ Nat.card J
  swap
  ·
    have hJs : (J.subgroupOf Y).IsSubnormal := (mem_thetaComponentsIn_iff.mp hJ).2.2.1
    have h3J' : ¬ 3 ∣ Nat.card ↥(J.subgroupOf Y) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv]
    have hle := Sec4.le_pPrimeCore_of_isSubnormal hJs h3J'
    have hJle : J ≤ pPrimeCoreOf 3 Y := by
      intro x hx
      exact ⟨⟨x, hJY hx⟩, hle hx, rfl⟩
    exact hθK.trans (hKJ.trans hJle)
  by_cases hc : e ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)
  swap
  · exact hO G A c L h Y hY hs hYB B Q e K Le hP J hJ hKJ hAJ h3J hc
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hKYe : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hKe : K ≤ Subgroup.centralizer {e} := hKYe.trans inf_le_right
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  obtain ⟨hJq, hJθ⟩ := Main148.img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hJc : img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y e he} := by
    intro x hx
    obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hc.2 j hjJ
    have heM : e ∈ Y ⊔ A := Subgroup.mem_sup_right he
    have hmem : e * j * e⁻¹ * j⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem heM hjM) ((Y ⊔ A).inv_mem heM))
        ((Y ⊔ A).inv_mem hjM)
    have h2 := (mk'_ker148_eq_one_iff (A := A) (Y := Y) (g := ⟨_, hmem⟩)).mpr h1
    have h3 : alpha148 A Y e he * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
        (alpha148 A Y e he)⁻¹ * (QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩)⁻¹ = 1 := by
      rw [alpha148_eq_mk', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hCJ := Main148.img148_inf_centralizer_alpha148 hY.2 hJM hAJ he (hA3 e he)
  rw [inf_eq_left.mpr hJc] at hCJ
  have hKsubJ : (K.subgroupOf (J ⊓ Subgroup.centralizer {e})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hK).2.2.1
    have hle : J ⊓ Subgroup.centralizer {e} ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle)
    have heq : (K.subgroupOf (Y ⊓ Subgroup.centralizer ({e} : Set G))).comap
        (Subgroup.inclusion hle) = K.subgroupOf (J ⊓ Subgroup.centralizer {e}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hKsub : ((img148 A Y K).subgroupOf (img148 A Y J)).IsSubnormal := by
    rw [hCJ]
    exact Main148.isSubnormal_img148 (le_inf hKJ hKe) (inf_le_left.trans hJM) hKsubJ
  by_cases hK1 : Nontrivial ↥(img148 A Y K)
  · have hKJα : img148 A Y K = img148 A Y J :=
      Main148.eq_of_le_of_isSubnormal_of_isQuasisimple (img148_mono hKJ) hJq hKαp hK1 hKsub
    exact theta_le_of_img148_eq hKM hKJα hJθ
  ·
    rw [not_nontrivial_iff_subsingleton] at hK1
    refine hθK.trans fun k hk => ?_
    have h1 : QuotientGroup.mk' (ker148 A Y) ⟨k, hKM hk⟩ = 1 := by
      have hm : QuotientGroup.mk' (ker148 A Y) ⟨k, hKM hk⟩ ∈ img148 A Y K :=
        mem_img148_iff.mpr ⟨k, hKM hk, hk, rfl⟩
      have := Subsingleton.elim (⟨_, hm⟩ : ↥(img148 A Y K)) 1
      exact congrArg Subtype.val this
    exact (mk'_ker148_eq_one_iff (g := ⟨k, hKM hk⟩)).mp h1

end CFSG.RankThree.PartTwo.Sec14
