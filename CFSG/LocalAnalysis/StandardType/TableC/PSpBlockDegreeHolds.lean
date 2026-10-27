module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.TableC.PSpLeafDefs
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSp
public import CFSG.LocalAnalysis.StandardType.TableC.PSpNoFieldExt
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.LocalAnalysis.ComponentClassification.EvenLieFieldExponent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.RankThree.PartOne.TCP.AlModel
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp
public import CFSG.LocalAnalysis.StandardType.TableC.PSpBlockRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutA6
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerTransport
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cClause
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015U6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Cat
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd
public import CFSG.RankThree.PartOne.TCP.AlSL2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section
namespace CFSG.StandardType.TableC
open CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.StandardType
open CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Assembly.LowTwoRank CFSG.StandardType.RCKRP
open scoped Matrix


theorem not_fieldExtCase_of_selfDual_degree_one
    {n f : ℕ} (hf : 1 ≤ f)
    {X : Type} [Group X] [Finite X]
    {ψ : ↥(StatedSp n (GaloisField 2 f)) →* X}
    (hψker : ψ.ker ≤ Subgroup.center ↥(StatedSp n (GaloisField 2 f)))
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (hJe : CFSG.Assembly.IsComponentOf J'
      ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S e,
        glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    ¬ GGSixLSevenFieldExtCase (J'.map ψ) .PSp f := by
  intro hFE
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    haveI : Subsingleton ↥(StatedSp 0 (GaloisField 2 f)) :=
      CFSG.ClassicalInvolution.ModelFacts.subsingleton_statedSp_zero
    exact (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton ↥J'))
      (CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2)
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  have hcenter : Subgroup.center ↥(StatedSp n (GaloisField 2 f)) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := GaloisField 2 f) hn
  have hψ : Function.Injective ψ := by
    have hker : ψ.ker = ⊥ :=
      le_bot_iff.mp (by simpa [hcenter] using hψker)
    exact (MonoidHom.ker_eq_bot_iff ψ).mp hker
  obtain ⟨m, ι, _E, _W, hm1, hsmall, hinj, hrange, _hE, _hform, _hact,
    _hWfix, _hspan, _horth⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_linearBlockModel_selfDual_PSp
      n f S hS he hadj hdeg hJe hA6
  have hθinj : Function.Injective (ψ.comp ι) := hψ.comp hinj
  have hθrange : (ψ.comp ι).range = J'.map ψ := by
    simpa [MonoidHom.range_comp, hrange]
  by_cases hm2 : 2 ≤ m
  · let eJ : ↥(J'.map ψ) ≃* ↥(StatedSp m (GaloisField 2 f)) :=
      ((MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hθrange)).symm
    have hmf : (m, f) ≠ (2, 1) := by
      intro h
      have hm : m = 2 := (Prod.mk.inj h).1
      have hf1 : f = 1 := (Prod.mk.inj h).2
      subst hm
      subst hf1
      rcases hsmall with h4 | h3
      · rw [hcF] at h4
        norm_num at h4
      · omega
    exact CFSG.StandardType.TableC.not_fieldExtCase_of_mulEquiv_statedSp
      (F := GaloisField 2 f) (J := J'.map ψ) (m := m) (f := f)
      hcF hm2 hmf eJ hFE
  · have hm1' : m = 1 := by omega
    subst m
    let eJ : ↥(J'.map ψ) ≃* ↥(StatedSp 1 (GaloisField 2 f)) :=
      ((MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hθrange)).symm
    have h4 : 4 ≤ 2 ^ f := by
      rcases hsmall with h4 | h3
      · rwa [hcF] at h4
      · omega
    let eSL : ↥(J'.map ψ) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
      eJ.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
        (K := GaloisField 2 f)).symm
    have hL : CFSG.Blueprint.LieModel
        (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL 2 2 f :=
      CFSG.RankThree.PartOne.TCP.lieModel_of_equiv_SL2
        (F := GaloisField 2 f) h4 hcF eSL
    obtain ⟨t', m', f', hff, hmod', -⟩ := hFE
    have hshape : CFSG.ComponentClassification.CatLeafProof.IsChar2LieShape .PSL 2 :=
      Or.inl ⟨rfl, rfl⟩
    have hfeq : f' = f :=
      CFSG.ComponentClassification.CatLeafProof.fieldExponent_eq_of_isChar2LieShape
        hL hshape hmod'
    omega


theorem not_fieldExtCase_of_selfDual_degree_two
    {n f : ℕ} (hf : 1 ≤ f)
    {X : Type} [Group X] [Finite X]
    (ψ : ↥(StatedSp n (GaloisField 2 f)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(StatedSp n (GaloisField 2 f)))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (hJε : CFSG.Assembly.IsComponentOf J'
      ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε,
        glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (heε : e * ε = e) (hself : e = ε)
    (hdeg₁ : 2 ≤ blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    ¬ GGSixLSevenFieldExtCase (J'.map ψ) .PSp f := by
  subst e
  have hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ε = ε :=
    hε.2.2.2.1
  obtain ⟨r, ι, β₀, hdim, hlong, hcen, hrange, a₁, a₂, b₁, b₂, h₁, h₂, h₃,
    himg₁, himg₂⟩ :=
    exists_blockModel_selfDualTwo_PSp_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJε
  have hker : ι.ker ≤ Subgroup.center (ggU .PSU r (max f 1)).K := by
    intro y hy
    apply hcen y
    rw [MonoidHom.mem_ker.mp hy]
    exact Subgroup.one_mem _
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJε.2.2
  rcases rckRP_admissible_PSU_of_quasisimple_range (g := max f 1)
      (le_max_right f 1) ι hq with hadm | ⟨hr2, hg2⟩
  ·
    have hρrange : (ψ.comp ι).range = J'.map ψ := by
      rw [MonoidHom.range_comp, hrange]
    have hρker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (max f 1)).K := by
      intro y hy
      apply hcen y
      exact hψ (MonoidHom.mem_ker.mpr (by
        simpa only [MonoidHom.comp_apply] using MonoidHom.mem_ker.mp hy))
    have hmodelJ : LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ))
        .PSU r 2 (max f 1) :=
      irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm (ψ.comp ι) hρrange hρker
    have hmodelJf : LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ))
        .PSU r 2 f := by
      simpa [max_eq_left hf] using hmodelJ
    have hr3 : 3 ≤ r := hadm.2.2.1
    intro hFE
    obtain ⟨t', m', f', hff, hmod', -⟩ := hFE
    have hdet : CFSG.SeitzReduction.UnitaryPilot.SUmEvenTypeDetAt r := by
      rcases Nat.lt_or_ge r 4 with hr | hr
      · obtain rfl : r = 3 := by omega
        exact CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet
      · exact CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt hr
    have hEq := hdet (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) f t' m' f'
      hmodelJf hmod'.admissible hmod'
    omega
  ·
    obtain rfl : r = 2 := hr2
    have hg2' : 2 ≤ max f 1 := hg2
    obtain ⟨ePSU⟩ :=
      rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := max f 1) (le_max_right f 1)
    let κ : (ggU .PSL 2 (max f 1)).K →* ↥(StatedSp n (GaloisField 2 f)) :=
      ι.comp ePSU.toMonoidHom
    have hκrange : κ.range = J' := by
      rw [← hrange]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨ePSU y, rfl⟩
      · rintro ⟨z, rfl⟩
        exact ⟨ePSU.symm z, by simp [κ]⟩
    have hρκrange : (ψ.comp κ).range = J'.map ψ := by
      rw [MonoidHom.range_comp, hκrange]
    have hρκker : (ψ.comp κ).ker ≤ Subgroup.center (ggU .PSL 2 (max f 1)).K := by
      intro y hy
      have hy' : ePSU y ∈ Subgroup.center (ggU .PSU 2 (max f 1)).K := by
        apply hcen (ePSU y)
        apply hψ
        exact MonoidHom.mem_ker.mpr (by
          simpa [κ] using MonoidHom.mem_ker.mp hy)
      rw [Subgroup.mem_center_iff] at hy' ⊢
      intro w
      apply ePSU.injective
      simpa only [map_mul] using hy' (ePSU w)
    have hadmPSL : StatedLieAdmissible .PSL 2 2 (max f 1) := by
      have h4 : 4 ≤ 2 ^ max f 1 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ max f 1 := Nat.pow_le_pow_right (by norm_num) hg2'
      unfold CFSG.Open.StatedLieAdmissible
      refine ⟨Nat.prime_two, le_max_right f 1, le_rfl, ?_, ?_⟩
      · intro h
        have h2 : 2 ^ max f 1 = 2 := (Prod.mk.inj h).2
        omega
      · intro h
        have h3 : 2 ^ max f 1 = 3 := (Prod.mk.inj h).2
        omega
    have hmodelJ : LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ))
        .PSL 2 2 (max f 1) :=
      irg_lieModel_quot (Or.inl rfl) hadmPSL (ψ.comp κ) hρκrange hρκker
    have hmodelJf : LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ))
        .PSL 2 2 f := by
      simpa [max_eq_left hf] using hmodelJ
    intro hFE
    obtain ⟨t', m', f', hff, hmod', -⟩ := hFE
    have hEq := CFSG.SeitzReduction.RankOne.sl2EvenTypeDet
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) f t' m' f'
      hmodelJf hmod'.admissible hmod'
    omega


theorem not_fieldExtCase_of_dualPair_degree_one
    {n f : ℕ} (hf : 1 ≤ f)
    {X : Type} [Group X] [Finite X]
    {ψ : ↥(StatedSp n (GaloisField 2 f)) →* X}
    (hψker : ψ.ker ≤ Subgroup.center ↥(StatedSp n (GaloisField 2 f)))
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hSU : ∀ s ∈ S, s ∈ StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (hJe : CFSG.Assembly.IsComponentOf J'
      ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S
        (e + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e),
        glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S
          (e + formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e)⁆) :
    ¬ GGSixLSevenFieldExtCase (J'.map ψ) .PSp f := by
  intro hFE
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    haveI : Subsingleton ↥(StatedSp 0 (GaloisField 2 f)) :=
      CFSG.ClassicalInvolution.ModelFacts.subsingleton_statedSp_zero
    exact (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton ↥J'))
      (CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2)
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  have hcenter : Subgroup.center ↥(StatedSp n (GaloisField 2 f)) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := GaloisField 2 f) hn
  have hψ : Function.Injective ψ := by
    have hker : ψ.ker = ⊥ :=
      le_bot_iff.mp (by simpa [hcenter] using hψker)
    exact (MonoidHom.ker_eq_bot_iff ψ).mp hker
  obtain ⟨k, ι, _β₀, _hrank, _hlong, hιcent, hιrange, _a₁, _a₂, _b₁, _b₂,
    _h1, _h2, _h34, _hAl, _hAl'⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_blockModel_dualPair_PSp_explicit
      n f S hSU hS he hpair hdeg hJe
  have hθr : (ψ.comp ι).range = J'.map ψ := by
    simpa [MonoidHom.range_comp, hιrange]
  have hθker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    exact hιcent y (hψker (by rw [MonoidHom.mem_ker]; exact hy))
  let eJ'J : ↥J' ≃* ↥(J'.map ψ) := Subgroup.equivMapOfInjective J' ψ hψ
  have hJq : CFSG.Assembly.IsQuasisimple ↥(J'.map ψ) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv eJ'J.symm hJe.2.2
  have hJq_range : CFSG.Assembly.IsQuasisimple ↥((ψ.comp ι).range) := by
    rw [hθr]
    exact hJq
  obtain ⟨h2k, h22, hqSL⟩ :=
    CFSG.StandardType.isQuasisimple_specialLinear_of_quasisimple_range
      (ψ.comp ι) hJq_range
  have h2k' : 2 ≤ k + 1 := by simpa using h2k
  have h22' : (k + 1 ≠ 2) ∨ (Nat.card (GaloisField 2 f) ≠ 2) := by
    simpa using h22
  have hf0 : f ≠ 0 := by omega
  have hpow2 : ∀ {q : ℕ}, 2 ^ q = 2 → q = 1 := by
    intro q hq
    have h' : 2 ^ q = 2 ^ 1 := by rw [hq, pow_one]
    exact Nat.pow_right_injective (le_refl 2) h'
  have hadm : CFSG.Open.StatedLieAdmissible .PSL (k + 1) 2 f := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨Nat.prime_two, hf, h2k', ?_, ?_⟩
    · intro heq
      have hk2 : k + 1 = 2 := (Prod.mk.inj heq).1
      have hpow : 2 ^ f = 2 := (Prod.mk.inj heq).2
      have hcard : Nat.card (GaloisField 2 f) = 2 := by rw [hcF, hpow]
      rcases h22' with hne | hne
      · exact hne hk2
      · exact hne hcard
    · intro heq
      have h2 : 2 ^ f = 3 := (Prod.mk.inj heq).2
      have hdvd : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
      rw [h2] at hdvd
      norm_num at hdvd
  haveI : Group.IsPerfect (ggU .PSL (k + 1) f).K := ⟨hqSL.1⟩
  obtain ⟨eJcent⟩ :=
    CFSG.StandardType.TableCRes.quotCenter_mulEquiv_of_perfect
      (ψ.comp ι) hθker (J'.map ψ) hθr
  have hPSL : Nonempty (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL (k + 1) (GaloisField 2 f))) :=
    ⟨eJcent.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (k + 1) (GaloisField 2 f))⟩
  have hX : CFSG.Blueprint.LieModel
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL (k + 1) 2 f := by
    refine Or.inl ⟨by decide, ?_⟩
    unfold CFSG.Open.StatedClassicalModel
    exact ⟨hadm, GaloisField 2 f, inferInstance, inferInstance, hcF, hPSL⟩
  obtain ⟨t', m', f', hff, hmod', -⟩ := hFE
  rcases Nat.lt_or_ge (k + 1) 3 with h3 | h3
  · have hk2 : k + 1 = 2 := by omega
    have hX2 : CFSG.Blueprint.LieModel
        (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL 2 2 f := by
      simpa [hk2] using hX
    have hfeq : f' = f :=
      (CFSG.SeitzReduction.RankOne.lieModel_PSL_two_two_unique_of_card_eq
        hX2 hmod' rfl).2.2
    omega
  · obtain ⟨-, -, hfeq⟩ :=
      CFSG.SeitzReduction.LinearPilot.slmEvenTypeDetAt h3
        (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) f t' m' f' hX
        (CFSG.Blueprint.LieModel.admissible hmod') hmod'
    omega

theorem isEmpty_altSix_of_fieldExtCase {X : Type} [Group X] {J : Subgroup X}
    {t : StatedLieTag} {f : ℕ} (hFE : GGSixLSevenFieldExtCase J t f) :
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  have hZ : Subgroup.center ↥J = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    have hez : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨v, rfl⟩ := e.surjective w
      simpa only [map_mul] using congrArg e (hz v)
    have hez1 : e z = 1 := by
      simpa only [CFSG.HardMathSupport.Solomon.Coordinator.center_alt_six,
        Subgroup.mem_bot] using hez
    apply e.injective
    simpa only [map_one] using hez1
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  obtain ⟨t', n', f', hff, hmodel, hnot⟩ := hFE
  apply CFSG.LocalAnalysis.GLTheoremA.H1431c.not_lieModel_two_of_isA6 ?_ hmodel
  refine ⟨TauCeti.CFSGIndex.alternating 6 (by norm_num), Or.inl rfl, ⟨?_⟩⟩
  exact eQ.trans (MulEquiv.refl _)


theorem ggSixTCBlockDegPSp_holds : GGSixTCBlockDegPSp := by
  intro n f hn hf X _ _ ψ hψker S hSU hS hodd J' ε e hε hJε he heε hFE
  have hψinj : Function.Injective ψ := by
    have hZ : Subgroup.center ↥(StatedSp n (GaloisField 2 f)) = ⊥ :=
      CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot hn
    exact (MonoidHom.ker_eq_bot_iff ψ).mp
      (le_bot_iff.mp (by simpa only [hZ] using hψker))
  have hA6Image := isEmpty_altSix_of_fieldExtCase hFE
  have hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) := by
    refine ⟨fun eA => ?_⟩
    exact hA6Image.false
      ((Subgroup.equivMapOfInjective J' ψ hψinj).symm.trans eA)
  by_cases hself : e = ε
  · left
    refine ⟨hself, ?_⟩
    by_contra hfour
    have hlt4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4 :=
      Nat.lt_of_not_ge hfour
    have hadj : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e = e := by
      simpa only [hself] using hε.2.2.2.1
    have hJe : CFSG.Assembly.IsComponentOf J'
        ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S e,
          glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S e⁆ := by
      simpa only [hself] using hJε
    by_cases hlt2 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2
    · exact (not_fieldExtCase_of_selfDual_degree_one hf hψker hS he hadj hlt2 hJe hA6) hFE
    · exact (not_fieldExtCase_of_selfDual_degree_two hf ψ hψker S hSU hS hodd hε hJε he
        heε hself (Nat.le_of_not_gt hlt2) hlt4) hFE
  · right
    refine ⟨hself, ?_⟩
    by_contra htwo
    have hlt2 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2 :=
      Nat.lt_of_not_ge htwo
    obtain hsame | ⟨hsum, hzero⟩ :=
      CFSG.StandardType.TableC.isPrimIdemIn_eq_or_add_formAdj_statedSp n (GaloisField 2 f)
        hS hSU hε he heε
    · exact hself hsame.symm
    · have hpair : formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e ≠ e := by
        intro h
        rw [h] at hzero
        exact he.2.2.1 (he.2.1.symm.trans hzero)
      have hJsum : CFSG.Assembly.IsComponentOf J'
          ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S
              (e + formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e),
            glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S
              (e + formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e)⁆ := by
        simpa only [hsum] using hJε
      exact (not_fieldExtCase_of_dualPair_degree_one hf hψker hSU hS he hpair hlt2 hJsum) hFE

end CFSG.StandardType.TableC
