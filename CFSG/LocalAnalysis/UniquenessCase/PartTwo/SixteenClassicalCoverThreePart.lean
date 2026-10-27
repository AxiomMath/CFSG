module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductLayer
import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
import CFSG.LieType.Steinberg.Classical.SpinPlus
import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGK1ScLin
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.Quasithin.Background.B69SL2
public import CFSG.Quasithin.Vol2.Ch12Sec5Pb
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.LieType.SteinbergBRParabolicResidualImage
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F1Weak
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.HSL3S77Case
public import CFSG.Quasithin.Background.HSL3S77SD
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec4L5B42
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Cx
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Wedge
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma7
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma8
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Para
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Walter.J1
public import Certificates.Kernel.SporSch.J4S.NoCP
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.StandardType CFSG.SectionRank CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

private theorem s16lc_sl2_lift {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Type} [Group E] [Finite E] {Y : Type} [Group Y]
    {π : E →* Y} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ 2 ∣ Nat.card π.ker)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* Y) :
    ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) F →* E, ∀ g, π (ρ' g) = ρ g := by
  let P := CFSG.SectionRank.EvenCover.pullback π ρ
  have hsurj : Function.Surjective (CFSG.SectionRank.EvenCover.pullbackFst π ρ) :=
    CFSG.SectionRank.EvenCover.pullbackFst_surjective hπ ρ
  have hker : (CFSG.SectionRank.EvenCover.pullbackFst π ρ).ker ≤ Subgroup.center P :=
    CFSG.SectionRank.EvenCover.pullbackFst_ker_le_center hcen ρ
  have hCpb : ¬ 2 ∣ Nat.card (CFSG.SectionRank.EvenCover.pullbackFst π ρ).ker := fun h2 =>
    hC (h2.trans (CFSG.SectionRank.EvenCover.card_pullbackFst_ker_dvd π ρ))
  obtain ⟨σ, hσ⟩ := ProductLayerAux.exists_sl2_section hsurj hker hCpb
  exact ⟨(MonoidHom.snd _ E).comp (P.subtype.comp σ), fun g =>
    DFunLike.congr_fun (CFSG.SectionRank.EvenCover.comp_snd_section σ hσ) g⟩

private theorem s16lc_sp_split {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    {E : Type} [Group E] [Finite E] {π : E →* StatedSp m F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : Nat.Coprime 2 (Nat.card π.ker)) :
    ∃ σ : StatedSp m F →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' : ¬ 2 ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hC
  exact (sp_existsUnique_section_of_sl2_lift (p := 2) m hπ hcen hC'
    fun ρ => s16lc_sl2_lift hπ hcen hC' ρ).exists

private theorem s16lc_spinPlus_split {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : 3 ≤ m) {E : Type} [Group E] [Finite E]
    {π : E →* spinGroup (quadPlus m F)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : Nat.Coprime 2 (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadPlus m F) →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' : ¬ 2 ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hC
  exact (existsUnique_section_of_sl2_lift (p := 2) (SpinPlus.isCTGroupDatum hm)
    (plusDatum_steinbergExtras hm) (SpinPlus.isParametrization hm) (SpinPlus.rankOne hm)
    hπ hcen hC' fun ρ => s16lc_sl2_lift hπ hcen hC' ρ).exists

private theorem s16lc_spinMinus_split {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : 4 ≤ m) {b d : F} (hirr : ∀ s : F, s ^ 2 + b * s + d ≠ 0)
    {E : Type} [Group E] [Finite E] {π : E →* spinGroup (quadMinus m F b d)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : Nat.Coprime 2 (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadMinus m F b d) →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' : ¬ 2 ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hC
  haveI : Fact (∀ r : F, r ^ 2 ≠ -d + b * r) := fact_shortField hirr
  haveI : Finite (ShortField b d) := finite_shortField (b := b) (c := d)
  haveI : CharP (ShortField b d) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b d)).injective 2
  exact (existsUnique_section_of_rankOne_lift (p := 2) (minusDatum_isCTGroupDatum m hirr hm)
    (minusDatum_steinbergExtras m hirr) (fun _ hγ => isPGroup_minusRootGroup hirr hγ)
    hπ hcen hC' fun i => by
      by_cases hi : i.val + 1 < m - 1
      · obtain ⟨ρ', hρ'⟩ := s16lc_sl2_lift (π := π) hπ hcen hC'
          ((minusFrame m b d).longSL2 (succ_ne_of_lt m hi) true false)
        exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
          (rankOne_minusRootGroup_of_lt m hirr hi).le hρ'
      · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras m hirr) i
          (shortRels m hirr i) (mem_minusRootGroup_single_iff hirr hi)
          (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
          (fun t ht h1 =>
            CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.shortRels_h_eq_one' hirr i ht h1)
          hπ hcen hC').exists

theorem s16lc_center_three_free_of_ggCenterPrime
    {R Q : Type} [Group R] [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hcp : GGCenterPrime 3 R) (e : (Q ⧸ Subgroup.center Q) ≃* R) :
    ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  let ψ : Q →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hψ : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center Q := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hx1 : QuotientGroup.mk' (Subgroup.center Q) x = 1 :=
      e.injective (by simpa using hx)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact hx1
  exact hcp Q ψ hψ hker (Group.IsPerfect.commutator_eq_top (G := Q))

theorem s16lc_sp_center_three_free
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 3 ≤ m)
    {Q : Type} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (e : (Q ⧸ Subgroup.center Q) ≃* ↥(StatedSp m F)) :
    ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(StatedSp m F)),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
      Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : ↥(StatedSp m F) →* E, ∀ h, π (s h) = h :=
    fun _ _ _ π hπ hcen hC => s16lc_sp_split hπ hcen hC
  have hcp : GGCenterPrime 3 (StatedSp m F) :=
    (OrthRest.center_data (H := ↥(StatedSp m F)) (R := StatedSp m F) (MulEquiv.refl _)
      (CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two
        (m := m) (F := F) (by omega)) hsplit Nat.prime_three (by norm_num)).2
  exact s16lc_center_three_free_of_ggCenterPrime hcp e

theorem s16lc_omegaPlus_center_three_free
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 3 ≤ m)
    {Q : Type} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (e : (Q ⧸ Subgroup.center Q) ≃*
      StatedProj (StatedOmega (StatedQuadPlus m F))) :
    ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Finite (spinGroup (quadPlus m F)) :=
    finite_spinGroup_of_ker (quadPlus m F) (coe_ker_spinMatrix_quadPlus (K := F) (n := m))
  obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := F) (n := m) hm
  let eH : spinGroup (quadPlus m F) ≃*
      StatedProj (StatedOmega (StatedQuadPlus m F)) :=
    MulEquiv.ofBijective
      (spinToStatedProj (quadPlus m F) (range_spinMatrix_quadPlus (K := F) (n := m) hm)) hbij
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* spinGroup (quadPlus m F)),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
      Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : spinGroup (quadPlus m F) →* E, ∀ h, π (s h) = h :=
    fun _ _ _ π hπ hcen hC => s16lc_spinPlus_split hm hπ hcen hC
  have hcp : GGCenterPrime 3
      (StatedProj (StatedOmega (StatedQuadPlus m F))) :=
    (OrthRest.center_data (H := spinGroup (quadPlus m F))
      (R := StatedProj (StatedOmega (StatedQuadPlus m F))) eH hZ hsplit
      Nat.prime_three (by norm_num)).2
  exact s16lc_center_three_free_of_ggCenterPrime hcp e

theorem s16lc_omegaMinus_center_three_free
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 4 ≤ m)
    {b d : F} (hirr : ∀ s : F, s ^ 2 + b * s + d ≠ 0)
    {Q : Type} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (e : (Q ⧸ Subgroup.center Q) ≃*
      StatedProj (StatedOmega (StatedQuadMinus m F b d))) :
    ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  haveI : Finite (spinGroup (quadMinus m F b d)) :=
    finite_spinGroup_of_ker (quadMinus m F b d) (coe_ker_spinMatrix_quadMinus hirr)
  obtain ⟨hbij, hZ⟩ := OrthRest.spinMinus_bij (K := F) (n := m) hm hirr
  let eH : spinGroup (quadMinus m F b d) ≃*
      StatedProj (StatedOmega (StatedQuadMinus m F b d)) :=
    MulEquiv.ofBijective
      (spinToStatedProj (quadMinus m F b d)
        (range_spinMatrix_quadMinus (K := F) (n := m) hm hirr)) hbij
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* spinGroup (quadMinus m F b d)),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
      Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : spinGroup (quadMinus m F b d) →* E, ∀ h, π (s h) = h :=
    fun _ _ _ π hπ hcen hC => s16lc_spinMinus_split hm hirr hπ hcen hC
  have hcp : GGCenterPrime 3
      (StatedProj (StatedOmega (StatedQuadMinus m F b d))) :=
    (OrthRest.center_data (H := spinGroup (quadMinus m F b d))
      (R := StatedProj (StatedOmega (StatedQuadMinus m F b d))) eH hZ hsplit
      Nat.prime_three (by norm_num)).2
  exact s16lc_center_three_free_of_ggCenterPrime hcp e



theorem ggCenterPrime_statedSL_zmod_two
    {n : ℕ} (hn : n = 3 ∨ n = 4) :
    GGCenterPrime 3 (CFSG.Open.StatedSL n (ZMod 2)) := by
  have hpd : ¬ (3 ∣ n ∧ 3 ∣ Nat.card (ZMod 2) - 1) := by
    rw [Nat.card_zmod]
    omega
  have hLarge : GGCenterPrime 3
      (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin n) (ZMod 2))) :=
    ggCenterPrime_linear_gcd (K := ZMod 2) (d := n)
      (by omega) Nat.prime_three (by norm_num) hpd
  have hProj : GGCenterPrime 3
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n (ZMod 2)) :=
    ggCenterPrime_of_mulEquiv (TypeA.recipeEquiv n (ZMod 2)).symm hLarge
  have hStatedProj : GGCenterPrime 3
      (CFSG.Open.StatedProj (CFSG.Open.StatedSL n (ZMod 2))) :=
    ggCenterPrime_of_mulEquiv
      (CFSG.Quasithin.B69.statedProjEquivProjectiveSL n (ZMod 2)) hProj
  exact ggCenterPrime_of_mulEquiv
    (CFSG.Quasithin.B69.statedSLEquivStatedProj (Nat.card_zmod 2) n) hStatedProj

theorem ggCenterPrime_gl_three_zmod_two :
    GGCenterPrime 3 (GL (Fin 3) (ZMod 2)) := by
  have hSL : GGCenterPrime 3 (CFSG.Open.StatedSL 3 (ZMod 2)) :=
    ggCenterPrime_statedSL_zmod_two (Or.inl rfl)
  exact ggCenterPrime_of_mulEquiv
    ((CFSG.Quasithin.H13.S125Pb.glEquivSL (a := Fin 3)).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2))) hSL

theorem ggCenterPrime_of_isSLn
    {X : Type} [Group X] {n : ℕ} (h : IsSLn X n 1) (hn : n = 3 ∨ n = 4) :
    GGCenterPrime 3 X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eX⟩⟩ := h
  let : Field K := hKf
  let : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hSL : GGCenterPrime 3 (CFSG.Open.StatedSL n (ZMod 2)) :=
    ggCenterPrime_statedSL_zmod_two hn
  have hSpecial : GGCenterPrime 3 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    ggCenterPrime_of_mulEquiv
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)) hSL
  have hK : GGCenterPrime 3 (CFSG.Open.StatedSL n K) :=
    ggCenterPrime_of_mulEquiv (CFSG.Quasithin.H13.statedSLEquivZModTwo hK2) hSpecial
  exact ggCenterPrime_of_mulEquiv eX hK

theorem cover_center_three_free_of_isSLn_three_or_four
    {X : Type} [Group X] {n : ℕ} (h : IsSLn X n 1) (hn : n = 3 ∨ n = 4) :
    ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* X) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  intro Q _ _ hQ ⟨eQ⟩
  have : Group.IsPerfect Q := ⟨hQ.1⟩
  exact s16lc_center_three_free_of_ggCenterPrime (ggCenterPrime_of_isSLn h hn) eQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
