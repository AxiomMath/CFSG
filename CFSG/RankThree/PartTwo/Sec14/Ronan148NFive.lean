module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148MFive
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148N

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_three_pow_eq_one148 {J R : Subgroup G}
    (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hR : Nat.Coprime 3 (Nat.card R)) {z j : G}
    (hj : j ∈ J) (hr : j⁻¹ * z ∈ R) {k : ℕ} (hz : z ^ (3 ^ k) = 1) : z ∈ J := by
  set NJ := Subgroup.normalizer (J : Set G) with hNJ
  have hJN : J ≤ NJ := Subgroup.le_normalizer
  haveI : (J.subgroupOf NJ).Normal := Subgroup.normal_in_normalizer
  set π := QuotientGroup.mk' (J.subgroupOf NJ) with hπ
  have hjN : j ∈ NJ := hJN hj
  have hrN : j⁻¹ * z ∈ NJ := hRJ hr
  have hzN : z ∈ NJ := by
    have hzjr : z = j * (j⁻¹ * z) := by group
    rw [hzjr]
    exact NJ.mul_mem hjN hrN
  have hπj : π ⟨j, hjN⟩ = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hj
  have hπz : π ⟨z, hzN⟩ = π ⟨j⁻¹ * z, hrN⟩ := by
    have hprod : (⟨z, hzN⟩ : NJ) = ⟨j, hjN⟩ * ⟨j⁻¹ * z, hrN⟩ := by
      apply Subtype.ext
      simp
    rw [hprod, map_mul, hπj, one_mul]
  have h1 : orderOf (π ⟨z, hzN⟩) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have hpow : (⟨z, hzN⟩ : NJ) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hz)
    rw [← map_pow, hpow, map_one]
  have h2 : orderOf (π ⟨z, hzN⟩) ∣ Nat.card R := by
    rw [hπz]
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard R hr
  have h3 : orderOf (π ⟨z, hzN⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k hR)) h2
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact Subgroup.mem_subgroupOf.mp h3

theorem inf_pPrimeCoreOf_le_theta148 {Y J : Subgroup G} (hJY : J ≤ Y)
    (hJq : IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J)) (hJ3 : 3 ∣ Nat.card J) :
    J ⊓ pPrimeCoreOf 3 Y ≤ inSubgroup (aschbacherSolvableCore 3) J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θJ := aschbacherSolvableCore 3 ↥J with hθJ
  set R := pPrimeCoreOf 3 Y with hR
  have hθn : θJ.Normal := by
    have := (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).2.1
    exact Subgroup.normal_of_characteristic θJ
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  set N : Subgroup ↥J := R.subgroupOf J with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (R : Set G) := hYR (hJY g.2)
    simpa using (Subgroup.mem_normalizer_iff.mp hg (n : G)).mp hn
  have hNc : ¬ 3 ∣ Nat.card N := by
    intro h3
    have hle : N.map J.subtype ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hx
    rw [← Subgroup.card_map_of_injective J.subtype_injective] at h3
    have := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (coprime_card_pPrimeCoreOf 3 Y)
    exact absurd (Nat.Coprime.eq_one_of_dvd this h3) (by norm_num)
  set T := N.map (QuotientGroup.mk' θJ) with hT
  have hTn : T.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hT3 : ¬ 3 ∣ Nat.card ↥T := fun h3 => hNc (h3.trans (Subgroup.card_map_dvd _ _))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq hTn with htop | hcen
  · exfalso
    have hθ3 : ¬ 3 ∣ Nat.card θJ :=
      (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).2.2.1
    have hQ3 : ¬ 3 ∣ Nat.card (↥J ⧸ θJ) := by
      intro h3
      apply hT3
      rw [htop, Subgroup.card_top]
      exact h3
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θJ] at hJ3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hJ3 with h | h
    · exact hQ3 h
    · exact hθ3 h
  · have hTs : Group.IsSolvable ↥T := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
      exact (Subgroup.mem_center_iff.mp (hcen b.2) a)
    have hle := (solvable_prime_complement_core_characterization (H := ↥J ⧸ θJ)
      Nat.prime_three).2.2.2.1 T hTn hTs hT3
    rw [(theta_quotient_core_and_ranks (G := ↥J)).1, le_bot_iff, hT, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hle
    intro x hx
    obtain ⟨hxJ, hxR⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxJ⟩, hle ?_, rfl⟩
    rw [hN, Subgroup.mem_subgroupOf]
    exact hxR

theorem isSolvable_inSubgroup_theta148 (J : Subgroup G) :
    Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) J) := by
  have hs := (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).1
  exact Group.isSolvable_of_surjective
    (f := ((aschbacherSolvableCore 3 ↥J).equivMapOfInjective J.subtype
      J.subtype_injective).toMonoidHom) (MulEquiv.surjective _)

section Five


theorem step148RankFiveSol_holds : Ronan148M.Step148RankFiveSol := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hXJ
  letI := ker148_normal hY.2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := pPrimeCoreOf 3 Y with hRdef
  set X := deltaZero A (lB A) Y with hXdef
  set C := X ⊓ Subgroup.centralizer ({e} : Set G) with hCdef
  have hXY : X ≤ Y := deltaZero_le Y
  obtain ⟨hJY, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨n, hn, -, hJn, -⟩ := hF
  have hJ3 : 3 ∣ Nat.card J :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi (by omega) hJn).trans
      (Main148.card_img148_dvd hJM)
  have hRc : Nat.Coprime 3 (Nat.card R) := coprime_card_pPrimeCoreOf 3 Y
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := by
    have hUs : (CFSG.pPrimeCore 3 ↥Y).IsSubnormal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := ↥Y)).isSubnormal
    rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hJ' hUs with
      hle | ⟨hle, -⟩
    · exfalso
      have hJle : J ≤ R := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hJY]
        exact Subgroup.map_mono hle
      have := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJle) hRc
      exact absurd (Nat.Coprime.eq_one_of_dvd this hJ3) (by norm_num)
    · have h1 := (Subgroup.map_mono (f := Y.subtype) hle).trans
        (Subgroup.le_normalizer_map Y.subtype)
      rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at h1
  have hcovX : ∀ x ∈ X, ∃ j ∈ J, j⁻¹ * x ∈ R := by
    intro x hx
    have hxM : x ∈ Y ⊔ A := (le_sup_left : Y ≤ Y ⊔ A) (hXY hx)
    have hmem : QuotientGroup.mk' (ker148 A Y) ⟨x, hxM⟩ ∈ img148 A Y J := by
      rw [← hXJ]
      exact mem_img148_iff.mpr ⟨x, hxM, hx, rfl⟩
    obtain ⟨j, hjM, hjJ, hjeq⟩ := mem_img148_iff.mp hmem
    exact ⟨j, hjJ, mk'_ker148_eq_iff.mp hjeq⟩
  have hOJ : oPrimeResidualOf 3 C ≤ J := by
    rw [oPrimeResidualOf, Subgroup.map_le_iff_le_comap, oPrimeResidual, Subgroup.closure_le]
    rintro z ⟨k, hk⟩
    obtain ⟨j, hj, hjz⟩ := hcovX z (Subgroup.mem_inf.mp z.2).1
    exact mem_of_pow_three_pow_eq_one148 hRJ hRc hj hjz (by simpa using congrArg Subtype.val hk)
  have hMJ : inSubgroup perfectResidual (oPrimeResidualOf 3 C) ≤ J :=
    (Ronan148M.inSubgroup_perfectResidual_le _).trans hOJ
  have hJq : IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
    set ε := Subgroup.subgroupOfEquivOfLe hJY
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ ε (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three ε)) hJ'.2.2
  have hle : inSubgroup perfectResidual (oPrimeResidualOf 3 C) ⊓ R ≤
      inSubgroup (aschbacherSolvableCore 3) J :=
    (inf_le_inf_right R hMJ).trans (inf_pPrimeCoreOf_le_theta148 hJY hJq hJ3)
  have hθs := isSolvable_inSubgroup_theta148 J
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem step148RankFive_holds :
    Step148RankFive :=
  Ronan148M.step148RankFive_of_sol step148RankFiveSol_holds

end Five

end CFSG.RankThree.PartTwo.Sec14.Ronan148N
