module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2121d
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.GroupTheory.PRankBound
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma415Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PRankSurvivor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UCKPAutQuot
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S151YC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.SzN17Abs
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31HSCases
public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31Hat
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

private abbrev s16hι : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem s16h_centralizer_natImage_le_statedScalars {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) : Set (MulAut (StdMod s16hι K))) ≤
      natImage (StatedScalars s16hι K) := by
  intro g hg
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) :=
    S18.hasScalarCommutant_statedOmegaMinus2 hirr
  let f : (s16hι → K) →+ (s16hι → K) :=
    AddMonoidHom.mk' (toAddMap g) (fun v w => toAddMap_add g v w)
  have hcomm : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v : s16hι → K,
      f ((γ : Matrix s16hι s16hι K) *ᵥ v) =
        (γ : Matrix s16hι s16hι K) *ᵥ f v := by
    intro γ hγ v
    have hmem : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ ∈
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) := ⟨_, rfl⟩
    have hc : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g =
        g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    change toAddMap g ((γ : Matrix s16hι s16hι K) *ᵥ v) =
        (γ : Matrix s16hι s16hι K) *ᵥ toAddMap g v
    calc toAddMap g ((γ : Matrix s16hι s16hι K) *ᵥ v)
        = toAddMap (g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩) v := by
          rw [toAddMap_mul, toAddMap_natAut]
      _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g) v := by
          rw [← hc]
      _ = (γ : Matrix s16hι s16hι K) *ᵥ toAddMap g v := by
          rw [toAddMap_mul, toAddMap_natAut]
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hsingle : (Pi.single (Sum.inl (0 : Fin 1)) (1 : K) : s16hι → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 1))
      simpa using this
    refine hsingle ((toAddMap_eq_zero_iff g).mp ?_)
    have h1 : f (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0 := by
      rw [hμ, h0, zero_smul]
    change toAddMap g (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0
    exact h1
  let u : Kˣ := Units.mk0 μ hμ0
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar s16hι u, ⟨u, rfl⟩⟩, ?_⟩
  apply toAddMap_injective
  intro v
  rw [toAddMap_natAut]
  change ((Matrix.GeneralLinearGroup.scalar s16hι u : GL s16hι K) :
      Matrix s16hι s16hι K) *ᵥ v = toAddMap g v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  rw [Matrix.mulVec_diagonal]
  exact congrFun (hμ v).symm x

private theorem s16h_card_statedScalars_natImage {K : Type} [Field K] [Finite K] :
    Nat.card (natImage (StatedScalars s16hι K)) = Nat.card K - 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16hι K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16hι K))
  calc Nat.card (natImage (StatedScalars s16hι K))
      = Nat.card ↥(StatedScalars s16hι K) :=
        (Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv).symm
    _ = Nat.card Kˣ :=
        (Nat.card_congr (MonoidHom.ofInjective
          (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := s16hι)
            (R := K))).toEquiv).symm
    _ = Nat.card K - 1 := Nat.card_units K

private theorem s16h_pRank_statedScalars_natImage_le_one {K : Type} [Field K] [Finite K]
    {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q (natImage (StatedScalars s16hι K)) ≤ 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16hι K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16hι K))
  let eScal : ↥(natImage (StatedScalars s16hι K)) ≃* Kˣ :=
    (MonoidHom.ofInjective hInj).symm.trans
      (MonoidHom.ofInjective
        (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective
          (ι := s16hι) (R := K))).symm
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (natImage (StatedScalars s16hι K)),
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt eScal]
  exact CFSG.SectionRank.pRank_le_one_of_isCyclic hq
    (inferInstance : IsCyclic (⊤ : Subgroup Kˣ))

theorem s16h_natNorm_elemAbelian_le_omegaMinus4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {a : ℕ} (ha : 1 ≤ a ∧ a ≤ 3) (hK : Nat.card K = 2 ^ a) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {A' : Subgroup (MulAut (StdMod _ K))}
    (hA : A' ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hE : IsElemAbelian q A') : Nat.card ↥A' ≤ q ^ 2 := by
  let Γ : Subgroup (GL s16hι K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16hι K)) := natImage Γ
  have hAleN : A' ≤ Subgroup.normalizer (Ω : Set (MulAut (StdMod s16hι K))) := hA
  let ψ : ↥A' →* MulAut ↥Ω :=
    (Subgroup.normalizerMonoidHom Ω).comp (Subgroup.inclusion hAleN)
  have hInjNatAut : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInjNatAut
  have hL2 : IsL2 ↥Ω (2 * a) :=
    uc22p22d_isL2_of_omegaMinus4 ha.1 hK b c hirr eImg.symm
  have hAutRank := uc22p2121d_pRank_mulAut_l2 hL2 hq hq2
  have hEtop : IsElemAbelian q (⊤ : Subgroup ↥A') := by
    rw [← Subgroup.subgroupOf_self]
    exact hE.subgroupOf A'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    (show IsPGroup q ↥A' from fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩)
  have hrank := CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank
    q hq ψ hEtop k (by rw [Subgroup.card_top]; exact hk)
  have hker_map_le : ψ.ker.map (Subgroup.subtype A') ≤
      A' ⊓ Subgroup.centralizer (Ω : Set (MulAut (StdMod s16hι K))) := by
    rintro x ⟨y, hy, rfl⟩
    have hyker : ψ y = 1 := (MonoidHom.mem_ker).mp hy
    have hmem : Subgroup.inclusion hAleN y ∈ (Subgroup.normalizerMonoidHom Ω).ker := by
      rw [MonoidHom.mem_ker]
      exact hyker
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact ⟨y.2, (Subgroup.mem_subgroupOf.mp hmem)⟩
  have hker_le_scal : CFSG.Open.pRank q ψ.ker ≤
      CFSG.Open.pRank q (natImage (StatedScalars s16hι K)) :=
    (CFSG.SectionRank.pRank_le_map hq.one_lt (Subgroup.subtype A')
        (Subgroup.subtype_injective A') ψ.ker).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt
        (hker_map_le.trans (inf_le_right.trans
          (s16h_centralizer_natImage_le_statedScalars (K := K) hirr))))
  have hker1 : CFSG.Open.pRank q ψ.ker ≤ 1 :=
    hker_le_scal.trans (s16h_pRank_statedScalars_natImage_le_one (K := K) hq)
  have hker0 : q ∣ a → CFSG.Open.pRank q ψ.ker ≤ 0 := by
    intro hqa
    refine hker_le_scal.trans ?_
    have hcard : Nat.card (natImage (StatedScalars s16hι K)) = 2 ^ a - 1 := by
      rw [s16h_card_statedScalars_natImage (K := K), hK]
    refine (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hq (H :=
      natImage (StatedScalars s16hι K)) (k := 0) ?_)
    rw [pow_one, hcard]
    have hqle : q ≤ 3 := by
      have := Nat.le_of_dvd (by omega : 0 < a) hqa
      omega
    have hq2le : 2 ≤ q := hq.two_le
    have ha1 : 1 ≤ a := ha.1
    have ha3 : a ≤ 3 := ha.2
    interval_cases q
    · exact absurd rfl hq2
    · interval_cases a
      · exact absurd hqa (by norm_num)
      · exact absurd hqa (by norm_num)
      · norm_num
  have himg_le : CFSG.Open.pRank q ψ.range ≤
      CFSG.Open.pRank q (⊤ : Subgroup (MulAut ↥Ω)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  have hrank' : k ≤ CFSG.Open.pRank q ψ.ker + CFSG.Open.pRank q ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact hrank
  have hk2 : k ≤ 2 := by
    by_cases hqa : q ∣ a
    · have h0 := hker0 hqa
      have h2 := hAutRank.1
      omega
    · have hna2 : ¬ q ∣ 2 * a := by
        intro hd
        have hqa' : q ∣ a := by
          rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
          · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h
            exact absurd this hq2
          · exact h
        exact hqa hqa'
      have h1 := hAutRank.2 hna2
      omega
  calc Nat.card ↥A' = q ^ k := hk
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq.pos hk2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
