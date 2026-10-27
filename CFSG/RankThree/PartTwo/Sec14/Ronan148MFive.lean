module

import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfield
import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailBalance
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.PartTwo.Sec14.Ronan148MInd
import CFSG.RankThree.PartTwo.Sec14.Ronan148MLemTheta
import CFSG.RankThree.PartTwo.Sec14.Ronan148MLemSol
import CFSG.RankThree.PartTwo.Sec14.Ronan148MLemIdx

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_mono {p : ℕ} {K H : Subgroup G} (h : K ≤ H) :
    oPrimeResidualOf p K ≤ oPrimeResidualOf p H := by
  rintro _ ⟨x, hx, rfl⟩
  have key : ∀ y : ↥K, y ∈ oPrimeResidual p ↥K → (y : G) ∈ oPrimeResidualOf p H := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨k, hk⟩ := hz
      refine ⟨⟨z, h z.2⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    | one => exact Subgroup.one_mem _
    | mul y z _ _ hy hz => simpa using (oPrimeResidualOf p H).mul_mem hy hz
    | inv y _ hy => simpa using (oPrimeResidualOf p H).inv_mem hy
  exact key x hx

omit [Finite G] in
theorem oPrimeResidualOf_le' {p : ℕ} (X : Subgroup G) : oPrimeResidualOf p X ≤ X :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem inSubgroup_perfectResidual_le (X : Subgroup G) : inSubgroup perfectResidual X ≤ X :=
  Subgroup.map_subtype_le _

theorem isPerfect_inSubgroup_perfectResidual148 (X : Subgroup G) :
    Group.IsPerfect ↥(inSubgroup perfectResidual X) := by
  have := (perfect_residual_characterization (G := ↥X)).2.2.1
  exact Group.IsPerfect.map X.subtype

section Five


@[expose] def Step148RankFiveSol : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        (letI := ker148_normal hY.2; img148 A Y (deltaZero A (lB A) Y) = img148 A Y J) →
        Group.IsSolvable ↥(inSubgroup perfectResidual
            (oPrimeResidualOf 3 (deltaZero A (lB A) Y ⊓ Subgroup.centralizer ({e} : Set G))) ⊓
          pPrimeCoreOf 3 Y)

theorem step148RankFive_of_sol
    (hsol : Step148RankFiveSol) : Step148RankFive := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hXJ
  letI := ker148_normal hY.2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := hsol G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hXJ
  set X := deltaZero A (lB A) Y with hXdef
  set C := X ⊓ Subgroup.centralizer ({e} : Set G) with hCdef
  set M := inSubgroup perfectResidual (oPrimeResidualOf 3 C) with hMdef
  have hMC : M ≤ C := (inSubgroup_perfectResidual_le _).trans (oPrimeResidualOf_le' C)
  have hMX : M ≤ X := hMC.trans inf_le_left
  have hMe : M ≤ Subgroup.centralizer ({e} : Set G) := hMC.trans inf_le_right
  have hXY : X ≤ Y := deltaZero_le Y
  have hMY : M ≤ Y := hMX.trans hXY
  have hMM : M ≤ Y ⊔ A := hMY.trans le_sup_left
  have hMperf : Group.IsPerfect ↥M := isPerfect_inSubgroup_perfectResidual148 _
  have hKmem := hP.2.2.2.2.2.1
  have hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hKmem
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hKX : K ≤ X := by
    rw [hKΔ]
    exact deltaZero_mono148 (hKY.trans inf_le_left)
  have hKC : K ≤ C := le_inf hKX (hKY.trans inf_le_right)
  have hKM' : K ≤ Y ⊔ A := (hKY.trans inf_le_left).trans le_sup_left
  have hKperf : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hKmem
  have hKs : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 h hkt
  have hK3 : 3 ∣ Nat.card ↥(img148 A Y K) := Main148.three_dvd_card_img148_of_types h hkt.2
  have hKne : img148 A Y K ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hK3
    omega
  have hKp' : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM'
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := exists_ne_comm_of_isPerfect hKp' hKne
  have hnc : ∃ a b : ↥(img148 A Y K), a * b ≠ b * a :=
    ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, fun hc => hxy₀ (congrArg Subtype.val hc)⟩
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    obtain ⟨hKH, hK'⟩ := mem_thetaComponentsIn_iff.mp hKmem
    set ε := Subgroup.subgroupOfEquivOfLe hKH
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ ε (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three ε)) hK'.2.2
  obtain ⟨-, ⟨φK⟩⟩ := Main148.theta_le_of_isSimpleGroup_img148 hKM' hKq hKs hnc
  have hKs' : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := MulEquiv.isSimpleGroup φK.symm
  have hK3' : 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    rwa [← Nat.card_congr φK.toEquiv]
  have hKO : K ≤ oPrimeResidualOf 3 C := by
    have h1 := oPrimeResidualOf_mono (p := 3) hKC
    rwa [oPrimeResidualOf_eq_self_of_simple_theta hKperf hKs' hK3'] at h1
  have hKM : K ≤ M := Item134Arg128Fail.le_inSubgroup_perfectResidual hKperf hKO
  obtain ⟨n, hn, hKn, hJn, hkind⟩ := hF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.isE27.1.2
  set σ := alpha148 A Y e he with hσ
  have hσ3 : σ ^ 3 = 1 := alpha148_pow_three hA3 he
  have hσN : σ ∈ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ (alpha148_mem_img148 he)
  have hcentK : ∀ {Z : Subgroup G}, Z ≤ Y ⊔ A → Z ≤ Subgroup.centralizer ({e} : Set G) →
      img148 A Y Z ≤ Subgroup.centralizer ({σ} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro Z hZ hZe z hz
    obtain ⟨g, hgM, hgZ, rfl⟩ := mem_img148_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff, hσ, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hZe hgZ))
  have hMKimg : img148 A Y M = img148 A Y K := by
    have hKsub : img148 A Y K ≤ img148 A Y J := img148_mono hKJ
    have hMsub : img148 A Y M ≤ img148 A Y J := by
      rw [← hXJ]
      exact img148_mono hMX
    rcases Item148Res8.kf148SubfieldOver_holds _ (img148 A Y J) (img148 A Y K) (img148 A Y M) σ
        n hn hJn hkind hσ3 hσN hKsub (hcentK hKM' (hKY.trans inf_le_right)) hKs hKn
        (img148_mono hKM) hMsub with hEq | ⟨hN, hcard⟩
    ·
      exfalso
      have hJc : img148 A Y J ≤ Subgroup.centralizer ({σ} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
        hEq ▸ hcentK hMM hMe
      apply not_isInnerAut_of_inducesStdKind_field148 hkind hσN
      have hker : (⟨σ, hσN⟩ : Subgroup.normalizer
          (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ∈
          (img148 A Y J).normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
          Subgroup.mem_centralizer_iff]
        intro z hz
        exact Subgroup.mem_centralizer_singleton_iff.mp (hJc hz)
      rw [MonoidHom.mem_ker] at hker
      rw [hker]
      exact Subgroup.one_mem _
    · have hMp : Group.IsPerfect ↥(img148 A Y M) := isPerfect_img148 hMM
      exact le_antisymm (le_of_isPerfect_of_card_dvd_three_mul (img148_mono hKM) hN hcard hMp)
        (img148_mono hKM)
  have hcov : ∀ m ∈ M, ∃ k ∈ K, k⁻¹ * m ∈ M ⊓ pPrimeCoreOf 3 Y := by
    intro m hm
    have hmimg : QuotientGroup.mk' (ker148 A Y) ⟨m, hMM hm⟩ ∈ img148 A Y K := by
      rw [← hMKimg]
      exact mem_img148_iff.mpr ⟨m, hMM hm, hm, rfl⟩
    obtain ⟨k, hkM, hkK, hkeq⟩ := mem_img148_iff.mp hmimg
    refine ⟨k, hkK, M.mul_mem (M.inv_mem (hKM hkK)) hm, ?_⟩
    exact mk'_ker148_eq_iff.mp hkeq
  set H₀ := Y ⊓ Subgroup.centralizer ({e} : Set G) with hH₀
  have hON : pPrimeCoreOf 3 H₀ ≤ Subgroup.normalizer (K : Set G) := by
    obtain ⟨hKH, hK'⟩ := mem_thetaComponentsIn_iff.mp hKmem
    have hUs : (CFSG.pPrimeCore 3 ↥H₀).IsSubnormal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := ↥H₀)).isSubnormal
    rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hK' hUs with
      hle | ⟨hle, -⟩
    · exfalso
      have hKle : K ≤ pPrimeCoreOf 3 H₀ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
        exact Subgroup.map_mono hle
      have h3K : 3 ∣ Nat.card K := hK3.trans (Main148.card_img148_dvd hKM')
      have := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKle)
        (coprime_card_pPrimeCoreOf 3 H₀)
      exact absurd (Nat.Coprime.eq_one_of_dvd this h3K) (by norm_num)
    · have h1 := (Subgroup.map_mono (f := H₀.subtype) hle).trans
        (Subgroup.le_normalizer_map H₀.subtype)
      rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h1
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := by
    intro m hm
    obtain ⟨k, hkK, ho⟩ := hcov m hm
    have hoC : k⁻¹ * m ∈ pPrimeCoreOf 3 H₀ := by
      refine inf_le_pPrimeCoreOf148 (N := pPrimeCoreOf 3 Y) (X := H₀)
        (inf_le_left.trans (le_normalizer_pPrimeCoreOf 3 Y)) (coprime_card_pPrimeCoreOf 3 Y) ?_
      refine ⟨ho.2, ?_, ?_⟩
      · exact hMY ho.1
      · exact hMe ho.1
    have hm' : m = k * (k⁻¹ * m) := by group
    rw [hm']
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hkK) (hON hoC)
  have hMK : M ≤ K := le_of_isPerfect_of_cover_solvable hKM hMN hcov hR hMperf
  have hMeq : M = K := le_antisymm hMK hKM
  rw [hMeq]
  exact hKΔ

end Five

end CFSG.RankThree.PartTwo.Sec14.Ronan148M
