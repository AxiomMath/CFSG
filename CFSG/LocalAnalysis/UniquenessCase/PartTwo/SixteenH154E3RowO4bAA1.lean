module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAD
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Matrix Pointwise

private theorem s16h_e3_centralizer_le_scalars {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
          Set (MulAut (StdMod s16h_H5E3RkιA K))) ≤
      natImage (StatedScalars s16h_H5E3RkιA K) := by
  intro g hg
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) :=
    S18.hasScalarCommutant_statedOmegaMinus2 hirr
  let f : (s16h_H5E3RkιA → K) →+ (s16h_H5E3RkιA → K) :=
    AddMonoidHom.mk' (toAddMap g) (fun v w => toAddMap_add g v w)
  have hcomm : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v : s16h_H5E3RkιA → K,
      f ((γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v) =
        (γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ f v := by
    intro γ hγ v
    have hmem : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ ∈
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) := ⟨_, rfl⟩
    have hc : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g =
        g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    change toAddMap g ((γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v) =
        (γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ toAddMap g v
    calc toAddMap g ((γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v)
        = toAddMap (g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩) v := by
          rw [toAddMap_mul, toAddMap_natAut]
      _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g) v := by
          rw [← hc]
      _ = (γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ toAddMap g v := by
          rw [toAddMap_mul, toAddMap_natAut]
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hsingle : (Pi.single (Sum.inl (0 : Fin 1)) (1 : K) : s16h_H5E3RkιA → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 1))
      simpa using this
    refine hsingle ((toAddMap_eq_zero_iff g).mp ?_)
    have h1 : f (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0 := by
      rw [hμ, h0, zero_smul]
    change toAddMap g (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0
    exact h1
  let u : Kˣ := Units.mk0 μ hμ0
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar s16h_H5E3RkιA u, ⟨u, rfl⟩⟩, ?_⟩
  apply toAddMap_injective
  intro v
  rw [toAddMap_natAut]
  change ((Matrix.GeneralLinearGroup.scalar s16h_H5E3RkιA u :
      GL s16h_H5E3RkιA K) : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v =
    toAddMap g v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  rw [Matrix.mulVec_diagonal]
  exact congrFun (hμ v).symm x

private theorem s16h_e3_card_statedScalars_natImage {K : Type} [Field K] [Finite K] :
    Nat.card (natImage (StatedScalars s16h_H5E3RkιA K)) = Nat.card K - 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16h_H5E3RkιA K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16h_H5E3RkιA K))
  calc Nat.card (natImage (StatedScalars s16h_H5E3RkιA K))
      = Nat.card ↥(StatedScalars s16h_H5E3RkιA K) :=
        (Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv).symm
    _ = Nat.card Kˣ :=
        (Nat.card_congr (MonoidHom.ofInjective
          (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective
            (ι := s16h_H5E3RkιA) (R := K))).toEquiv).symm
    _ = Nat.card K - 1 := Nat.card_units K

private theorem s16h_e3_scalars_commute_natImage {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {mu g : MulAut (StdMod ι K)}
    (hmu : mu ∈ natImage (StatedScalars ι K)) (hg : g ∈ natImage Γ) : mu * g = g * mu := by
  obtain ⟨u, rfl⟩ := hmu
  obtain ⟨γ, rfl⟩ := hg
  obtain ⟨s, hs⟩ := u.2
  change matHom u.1 * matHom γ.1 = matHom γ.1 * matHom u.1
  rw [← map_mul, ← map_mul]
  congr 1
  rw [← hs]
  exact Matrix.GeneralLinearGroup.scalar_commute s γ.1

private theorem s16h_e3_normalizerMonoidHom_conj {G : Type} [Group G] (Ω : Subgroup G)
    (y : ↥Ω) :
    Ω.normalizerMonoidHom ⟨y.1, Subgroup.le_normalizer y.2⟩ = MulAut.conj y := by
  ext z
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  rfl

theorem s16h_H5_omegaMinusFour_q_sq_order_meet {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {q : ℕ} (hq : q = 3 ∨ q = 7)
    {D : Subgroup (MulAut (StdMod s16h_H5E3RkιA K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian q D) (hDcard : Nat.card ↥D = q ^ 2) :
    Nat.card ↥(D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c))) = q := by
  classical
  let G := MulAut (StdMod s16h_H5E3RkιA K)
  let Γ : Subgroup (GL s16h_H5E3RkιA K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup G := natImage Γ
  change Nat.card ↥(D ⊓ Ω) = q
  have hqprime : q.Prime := by rcases hq with h | h <;> subst h <;> norm_num
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hq2 : q ≠ 2 := by rcases hq with h | h <;> omega
  have hDN' : D ≤ Subgroup.normalizer (Ω : Set G) := hDN
  have hInjNatAut : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInjNatAut
  have hL2 : IsL2 ↥Ω (2 * 3) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  have hm : CFSG.Open.StatedClassicalModel ↥Ω .PSL 2 2 (2 * 3) :=
    hL2.statedClassicalModel (by decide)
  have hΩrank : CFSG.Open.pRank q Ω ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ω]
    exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hm hqprime hq2
  have hmeet_le : Nat.card ↥(D ⊓ Ω) ≤ q := by
    have hEab : IsElemAbelian q (D ⊓ Ω) := hDab.mono inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEab.isPGroup
    have hk1 : k ≤ CFSG.Open.pRank q Ω :=
      CFSG.SectionRank.le_pRank hqprime.one_lt inf_le_right hEab hk
    calc Nat.card ↥(D ⊓ Ω) = q ^ k := hk
      _ ≤ q ^ 1 := Nat.pow_le_pow_right hqprime.pos (hk1.trans hΩrank)
      _ = q := pow_one q
  have hmeet_ne : D ⊓ Ω ≠ ⊥ := by
    intro hbot
    let C : Subgroup G := Subgroup.centralizer (Ω : Set G)
    have hCleScal : C ≤ natImage (StatedScalars s16h_H5E3RkιA K) :=
      s16h_e3_centralizer_le_scalars (K := K) hirr
    have hScalLeC : natImage (StatedScalars s16h_H5E3RkιA K) ≤ C := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (s16h_e3_scalars_commute_natImage (Γ := Γ) hg hh).symm
    have hCcard : Nat.card ↥C = 7 := by
      have hCeq : C = natImage (StatedScalars s16h_H5E3RkιA K) :=
        le_antisymm hCleScal hScalLeC
      rw [hCeq, s16h_e3_card_statedScalars_natImage (K := K), hK]
      norm_num
    have hCnorm : C ≤ Subgroup.normalizer (Ω : Set G) :=
      Subgroup.centralizer_le_normalizer (Ω : Set G)
    haveI hnC : (Ω.subgroupOf C).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hCnorm
    haveI hnSup : (Ω.subgroupOf (C ⊔ Ω)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hCnorm
    have hKdvd7 : Nat.card ↥(D ⊓ (C ⊔ Ω)) ∣ 7 := by
      let Ksub : Subgroup G := D ⊓ (C ⊔ Ω)
      have hKinf : Ksub ⊓ Ω = ⊥ := by
        have h1 : (C ⊔ Ω) ⊓ Ω = Ω := inf_eq_right.mpr le_sup_right
        dsimp [Ksub]
        rw [inf_assoc, h1, hbot]
      let π : ↥Ksub →* ((C ⊔ Ω : Subgroup G) ⧸ Ω.subgroupOf (C ⊔ Ω)) :=
        (QuotientGroup.mk' (Ω.subgroupOf (C ⊔ Ω))).comp
          (Subgroup.inclusion (inf_le_right : Ksub ≤ C ⊔ Ω))
      have hπinj : Function.Injective π := by
        rw [← MonoidHom.ker_eq_bot_iff π, Subgroup.eq_bot_iff_forall]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hxΩ : ((x : ↥Ksub) : G) ∈ Ω := by
          have hq1 : (Subgroup.inclusion (inf_le_right : Ksub ≤ C ⊔ Ω) x :
              (C ⊔ Ω : Subgroup G) ⧸ Ω.subgroupOf (C ⊔ Ω)) = 1 := hx
          rw [QuotientGroup.eq_one_iff] at hq1
          simpa using (Subgroup.mem_subgroupOf.mp hq1)
        have hxbot : ((x : ↥Ksub) : G) ∈ Ksub ⊓ Ω :=
          Subgroup.mem_inf.mpr ⟨x.2, hxΩ⟩
        rw [hKinf, Subgroup.mem_bot] at hxbot
        exact Subtype.ext hxbot
      have hcardK : Nat.card ↥Ksub = Nat.card ↥π.range :=
        Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv
      have hquotdvd : Nat.card ((C ⊔ Ω : Subgroup G) ⧸ Ω.subgroupOf (C ⊔ Ω)) ∣ 7 := by
        have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient C Ω hCnorm
        rw [← Nat.card_congr hiso.toEquiv,
          ← Subgroup.index_eq_card (H := Ω.subgroupOf C)]
        have h := Subgroup.index_dvd_card (H := Ω.subgroupOf C)
        rwa [hCcard] at h
      change Nat.card ↥Ksub ∣ 7
      rw [hcardK]
      exact (Subgroup.card_subgroup_dvd_card π.range).trans hquotdvd
    let ψ : ↥D →* MulAut ↥Ω :=
      (Subgroup.normalizerMonoidHom Ω).comp (Subgroup.inclusion hDN')
    let φ : ↥D →* Outer ↥Ω :=
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Ω)).comp ψ
    have hker_le : (φ.ker).map (Subgroup.subtype D) ≤ D ⊓ (C ⊔ Ω) := by
      rintro x ⟨d, hd, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨d.2, ?_⟩
      have hdmem : ψ d ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Ω := by
        have h1 : φ d = 1 := MonoidHom.mem_ker.mp hd
        exact (QuotientGroup.eq_one_iff (ψ d)).mp h1
      rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hdmem
      obtain ⟨ω, hω⟩ := hdmem
      have hψω : ψ d = Ω.normalizerMonoidHom ⟨ω.1, Subgroup.le_normalizer ω.2⟩ := by
        rw [s16h_e3_normalizerMonoidHom_conj Ω ω, hω]
      have hmemC : (d : ↥D) * ω.1⁻¹ ∈ C := by
        have hker : Subgroup.inclusion hDN' d *
            (⟨ω.1, Subgroup.le_normalizer ω.2⟩ :
              ↥(Subgroup.normalizer (Ω : Set G)))⁻¹ ∈
            C.subgroupOf (Subgroup.normalizer (Ω : Set G)) := by
          rw [← Subgroup.normalizerMonoidHom_ker, MonoidHom.mem_ker, map_mul, map_inv]
          rw [show Ω.normalizerMonoidHom (Subgroup.inclusion hDN' d) =
              Ω.normalizerMonoidHom ⟨ω.1, Subgroup.le_normalizer ω.2⟩ from hψω,
            mul_inv_cancel]
        simpa using Subgroup.mem_subgroupOf.mp hker
      simpa [mul_assoc] using Subgroup.mul_mem_sup hmemC ω.2
    have hker_dvd7 : Nat.card ↥φ.ker ∣ 7 := by
      have h1 : Nat.card ↥φ.ker ∣ Nat.card ↥(D ⊓ (C ⊔ Ω)) := by
        rw [← Subgroup.card_map_of_injective (K := φ.ker) (Subgroup.subtype_injective D)]
        exact Subgroup.card_dvd_of_le hker_le
      exact h1.trans hKdvd7
    have hOut_le : Nat.card (Outer ↥Ω) ≤ 6 := by
      obtain ⟨⟨-, -, -⟩, L', hL'f, hL'fin, hL'card, ⟨ePSL⟩⟩ := hm
      letI : Field L' := hL'f
      letI : Finite L' := hL'fin
      let e' : ↥Ω ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) L' :=
        ePSL.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 L').symm
      have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
        Nat.prime_two L' hL'card).2 ↥Ω ⟨e'⟩
      have hdvd6 : Nat.card (Outer ↥Ω) ∣ 6 := by
        have h6 : (2 * 3) * Nat.gcd 2 (2 ^ (2 * 3) - 1) = 6 := by norm_num
        rwa [h6] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd6
    have hDvd : φ.ker.index * Nat.card ↥φ.ker = Nat.card ↥D := by
      rw [mul_comm, Subgroup.card_mul_index]
    have hIndexLe : φ.ker.index ≤ 6 := by
      rw [Subgroup.index_ker]
      simpa using (Subgroup.card_le_card_group φ.range).trans hOut_le
    rcases hq with rfl | rfl
    · have hdiv9 : Nat.card ↥φ.ker ∣ 9 := by
        have h := Subgroup.card_subgroup_dvd_card φ.ker
        rw [hDcard] at h
        norm_num at h
        exact h
      have hg : Nat.card ↥φ.ker ∣ Nat.gcd 7 9 := Nat.dvd_gcd hker_dvd7 hdiv9
      have hker1 : Nat.card ↥φ.ker = 1 := by
        rw [show Nat.gcd 7 9 = 1 by norm_num] at hg
        exact Nat.dvd_one.mp hg
      rw [hker1, mul_one, hDcard] at hDvd
      norm_num at hDvd
      rw [hDvd] at hIndexLe
      norm_num at hIndexLe
    · have hdiv49 : Nat.card ↥φ.ker ∣ 49 := by
        have h := Subgroup.card_subgroup_dvd_card φ.ker
        rw [hDcard] at h
        norm_num at h
        exact h
      have hg : Nat.card ↥φ.ker ∣ Nat.gcd 7 49 := Nat.dvd_gcd hker_dvd7 hdiv49
      have hg7 : Nat.card ↥φ.ker ∣ 7 := by
        rwa [show Nat.gcd 7 49 = 7 by norm_num] at hg
      rcases Nat.prime_seven.eq_one_or_self_of_dvd (Nat.card ↥φ.ker) hg7 with hk | hk
      · rw [hk, mul_one, hDcard] at hDvd
        norm_num at hDvd
        rw [hDvd] at hIndexLe
        norm_num at hIndexLe
      · rw [hk, hDcard] at hDvd
        norm_num at hDvd
        have hidx : φ.ker.index = 7 := by omega
        rw [hidx] at hIndexLe
        norm_num at hIndexLe
  have hdvd : Nat.card ↥(D ⊓ Ω) ∣ q ^ 2 := by
    rw [← hDcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hgt : 1 < Nat.card ↥(D ⊓ Ω) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet_ne
    exact ⟨⟨a, 1, ha⟩⟩
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hqprime).mp hdvd
  have hj1 : j = 1 := by
    rcases Nat.lt_or_ge j 1 with h | h
    · have hj0 : j = 0 := by omega
      rw [hj0, pow_zero] at hj
      omega
    · rcases Nat.lt_or_ge j 2 with h2 | h2
      · omega
      · have hj2 : j = 2 := by omega
        rw [hj2, pow_two] at hj
        nlinarith [hqprime.two_le, hmeet_le]
  rw [hj, hj1, pow_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
