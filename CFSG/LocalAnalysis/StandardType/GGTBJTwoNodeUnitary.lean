module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.RankThree.PartOne.KF.R9Levi
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepair
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.RankThree.PartOne.KF.R9Model
public import CFSG.RankThree.PartOne.KF.R9Plane

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.StandardType.TableBUE

variable {G : Type} [Group G] [Finite G]

theorem exists_diagonal_cover_of_large_unitary_side_of_cfg_of_rank
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 4 ≤ r)
    (hr5 : r ≠ 5 ∨ f ≠ 1 ∧
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ 4 ≤ Nat.card (ggGamma X hN).range)
    (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hInn : GGInnerDiagOn Bs X := by
    rcases hside with rfl | ⟨z, hz⟩
    · exact hIDA.1
    · exact hIDA.2 z X hz
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF : Nat.card F = (2 ^ f) ^ 2 := by simpa [pow_two] using hFK
  have hF2 : Nat.card F = 2 ^ (2 * f) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hF
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm]
  have : CharP F 2 := charP_two_of_card hF2
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hBsI' : ∀ b (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) F (2 ^ f)))
        (LargeEvenGUSet (Fin (r + 1)) F (2 ^ f)) := by
    intro b hb
    exact ggLAut_mem_of_induces X θ hN hBsI hb
  have hf1 : 1 ≤ f := hΛ.1
  have hd : 5 ≤ r + 1 := by omega
  have hdnd : (r + 1, f) ≠ (6, 1) := by
    intro h
    have hd6 := congrArg Prod.fst h
    have hf6 := congrArg Prod.snd h
    rcases hr5 with hr5 | ⟨hf5, -⟩
    · exact hr5 (by omega)
    · exact hf5 (by simpa using hf6)
  have hdq32 : (r + 1, 2 ^ f) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hlift : GGTorusLift p (r - 2)
      (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) F (2 ^ f))) := by
    have hrank : ggUnitaryTorusRank p (r + 1) = r - 2 := by
      rw [ggUnitaryTorusRank]
      simp only [if_pos hpd]
      omega
    rw [← hrank]
    exact ggTorusLift_unitary (K := F) (n := f) (d := r + 1) (p := p)
      hF hf1 (by omega) hdq32 hp hpq
  have hTB : GGTorusTBGroup p (r - 2)
      (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) F (2 ^ f)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) F (2 ^ f)))
        (LargeEvenGUSet (Fin (r + 1)) F (2 ^ f)))
      X (ggQuotHom θ) (ggGamma X hN).range := by
    rcases hside with rfl | ⟨z, hz⟩
    · exact ggTorusTBGroup_of_L hcfg hXperf θ hN hBsI' hlift
    · exact ggTorusTBGroup_of_nbr hcfg hz hXperf θ hN hBsI' hlift
  obtain ⟨hψs, hψker, -, hAe, hAI, hr2, hr3, -⟩ := hTB
  have hd3 : 3 ≤ r + 1 := by omega
  have hcov : LineU.UnitaryCoverAt f (r + 1) F :=
    LineU.unitaryUniversalCover_holds f (r + 1) F hF hd hdnd
  have hcard : p ^ ((r + 1) / p + 2) ≤ Nat.card (ggGamma X hN).range := by
    by_cases hr5' : r = 5
    · obtain ⟨-, hrk⟩ := hr5.resolve_left (not_not.mpr hr5')
      have hp3 : p = 3 := by
        have hdvd : p ∣ 6 := by simpa only [hr5'] using hpd
        have h23 : p ∣ 2 * 3 := hdvd
        rcases (Nat.Prime.dvd_mul hp).mp h23 with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
        · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
      have h4 : (r + 1) / p + 2 = 4 := by simp [hr5', hp3]
      rw [h4]
      exact hrk hN
    by_cases hr4 : r = 4
    · have hp5 : p = 5 := by
        have hdvd : p ∣ 5 := by simpa only [hr4] using hpd
        exact ((Nat.dvd_prime Nat.prime_five).mp hdvd).resolve_left hp.ne_one
      simpa only [hr4, hp5] using hr3
    · have hdiv : (r + 1) / p + 2 ≤ r - 2 := by
        by_cases hr6 : r = 6
        · have hp7 : p = 7 := by
            have hdvd : p ∣ 7 := by simpa only [hr6] using hpd
            exact ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdvd).resolve_left hp.ne_one
          subst r
          subst p
          norm_num
        · have hp3 : 3 ≤ p := by have := hp.two_le; omega
          have hbase : r + 1 ≤ 3 * (r - 4) := by omega
          have hmul : r + 1 ≤ p * (r - 4) := by
            calc r + 1 ≤ 3 * (r - 4) := hbase
              _ ≤ p * (r - 4) := Nat.mul_le_mul_right _ hp3
          have hquot : (r + 1) / p ≤ r - 4 := Nat.div_le_of_le_mul hmul
          omega
      exact (Nat.pow_le_pow_right hp.pos hdiv).trans hr2
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel (L' := X) (K := F) (n := f) (d := r + 1) (p := p) hF hf1 hd hp hpq
      hpd hcov hψs hψker hXperf hAe hAI hcard
  exact ⟨F, hField, hFinite, inferInstance, hN, φ,
    ⟨hF, ⟨TableBU.unitaryFieldData_of_card hF hf1, hφs, hφker⟩, hdiag⟩⟩

theorem exists_diagonal_cover_of_large_unitary_side_of_cfg
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t :=
  exists_diagonal_cover_of_large_unitary_side_of_cfg_of_rank hRig hcfg hIDA hside hr (Or.inl hr5)
    hpq hpd hLab hΛ

theorem exists_diagonal_cover_of_large_unitary_side
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t :=
  exists_diagonal_cover_of_large_unitary_side_of_cfg hRig hH.1 hH.2.2.1 hside hr hr5 hpq hpd
    hLab hΛ

theorem exists_diagonal_cover_of_large_unitary_coprime_of_inner
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hInn : GGInnerDiagOn Bs X)
    {r f : ℕ} (hr : 4 ≤ r) (hr5f : r ≠ 5 ∨ f ≠ 1) (hpq : p ∣ 2 ^ f + 1)
    (hpd : ¬ p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t := by
  classical
  have hp : p.Prime := Fact.out
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF : Nat.card F = (2 ^ f) ^ 2 := by simpa [pow_two] using hFK
  have hF2 : Nat.card F = 2 ^ (2 * f) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hF
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm]
  have : CharP F 2 := charP_two_of_card hF2
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hBsI' : ∀ b (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) F (2 ^ f)))
        (LargeEvenGUSet (Fin (r + 1)) F (2 ^ f)) := by
    intro b hb
    exact ggLAut_mem_of_induces X θ hN hBsI hb
  have hf1 : 1 ≤ f := hΛ.1
  have hd : 5 ≤ r + 1 := by omega
  have hdnd : (r + 1, f) ≠ (6, 1) := by
    intro h
    have hd6 := congrArg Prod.fst h
    have hf1' := congrArg Prod.snd h
    rcases hr5f with hr5 | hf
    · exact hr5 (by omega)
    · exact hf hf1'
  have hd3 : 3 ≤ r + 1 := by omega
  have hcov : LineU.UnitaryCoverAt f (r + 1) F :=
    LineU.unitaryUniversalCover_holds f (r + 1) F hF hd hdnd
  have hAe : IsElemAbelian p (ggGamma X hN).range :=
    isElemAbelian_range
      (fun a b : Bs => Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2))
      (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2))
      (ggGamma X hN)
  have hAI : ∀ a ∈ (ggGamma X hN).range,
      ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) F (2 ^ f)))
        (LargeEvenGUSet (Fin (r + 1)) F (2 ^ f)),
        ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hN b, hBsI' b b.2,
      fun l => ggBeta_ggQuotHom X hN θ b l⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime (L' := X) (K := F) (n := f) (d := r + 1) (p := p)
      hF hf1 hd3 hp hpq hpd hcov (ggQuotHom_surjective θ)
      (ker_ggQuotHom θ).le hXperf hAe hAI
  exact ⟨F, hField, hFinite, inferInstance, hN, φ,
    ⟨hF, ⟨TableBU.unitaryFieldData_of_card hF hf1, hφs, hφker⟩, hdiag⟩⟩

theorem exists_diagonal_cover_of_large_unitary_side_coprime
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 4 ≤ r) (hr5f : r ≠ 5 ∨ f ≠ 1) (hpq : p ∣ 2 ^ f + 1)
    (hpd : ¬ p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t := by
  refine exists_diagonal_cover_of_large_unitary_coprime_of_inner hRig hH.1.tableB_facts.2.1 ?_
    hr hr5f hpq hpd hLab hΛ
  rcases hside with rfl | ⟨z, hz⟩
  · exact hH.2.2.1.1
  · exact hH.2.2.1.2 z X hz

theorem exists_diagonal_cover_of_large_unitary_L_coprime
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5f : r ≠ 5 ∨ f ≠ 1) (hpq : p ∣ 2 ^ f + 1)
    (hpd : ¬ p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t := by
  exact exists_diagonal_cover_of_large_unitary_side_coprime hRig hH (Or.inl rfl)
    hr hr5f hpq hpd hLab hΛ

theorem exists_diagonal_cover_of_large_unitary_L
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t := by
  exact exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inl rfl) hr hr5 hpq hpd hLab hΛ

omit [Finite G] in
theorem ggFrameDiagU_of_ggGamma_actsDiagU
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n p : ℕ}
    (hKd : UnitaryFieldData 2 f F) (hn : 3 ≤ n)
    {Bs : Subgroup G} {L : Subgroup G} {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {φ : ↥(unitarySU 2 f F n) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 f F n), φ g = 1 →
      ∃ c : F, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal (fun _ => c))
    {b : G} (hb : b ∈ Bs) {t : Fin n → F}
    (ht : LineU.ActsDiagU φ (ggGamma L hN ⟨b, hb⟩) t)
    (hpow : (ggGamma L hN ⟨b, hb⟩) ^ p = 1) (hpq : p ∣ 2 ^ f + 1) :
    SURep.GGFrameDiagU (L.subtype.comp φ) b := by
  classical
  have ht0 : LineU.ActsDiagU φ (ggGamma L hN ⟨b, hb⟩) t := ht
  obtain ⟨D, hD, hDt, hact⟩ := ht
  have hne : ∀ i, t i ≠ 0 := fun i => LineU.diag_ne_zero_of_eq hDt i
  let i0 : Fin n := ⟨0, by omega⟩
  let τ : Fin n → Fˣ := fun i =>
    Units.mk0 (t i / t i0) (div_ne_zero (hne i) (hne i0))
  have hτnorm : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1 := by
    intro i
    have hratio : (t i / t i0) ^ p = 1 := by
      have h := LineU.ActsDiagU.ratio_pow hKd hn hφker ht0 hpow i i0
      simpa [div_eq_mul_inv] using h
    obtain ⟨k, hk⟩ := hpq
    have h1 : (t i / t i0) ^ (2 ^ f + 1) = 1 := by
      rw [hk, pow_mul, hratio, one_pow]
    simpa [τ] using h1
  have hD_eq : D = Matrix.GeneralLinearGroup.scalar (Fin n)
      (Units.mk0 (t i0) (hne i0)) * diagHom n τ := by
    apply Units.ext
    ext i j
    rw [hDt, Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst j
      simp only [τ, Matrix.scalar_apply, Matrix.diagonal_apply_eq, if_true, Units.val_mk0]
      field_simp [hne i0]
    · simp only [Matrix.scalar_apply, hij, if_false, zero_mul,
        Matrix.diagonal_apply_ne _ hij]
  refine ⟨τ, hτnorm, ?_⟩
  intro s s' hs'
  have hconj : D * (s : GL (Fin n) F) * D⁻¹ =
      diagHom n τ * (s : GL (Fin n) F) * (diagHom n τ)⁻¹ := by
    rw [hD_eq]
    set c := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 (t i0) (hne i0))
    have hc : c ∈ Subgroup.center (GL (Fin n) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hcomm := Subgroup.mem_center_iff.mp hc
      (diagHom n τ * (s : GL (Fin n) F) * (diagHom n τ)⁻¹)
    calc (c * diagHom n τ) * s * (c * diagHom n τ)⁻¹ =
        c * (diagHom n τ * s * (diagHom n τ)⁻¹) * c⁻¹ := by group
      _ = (diagHom n τ * s * (diagHom n τ)⁻¹) * c * c⁻¹ := by rw [hcomm]
      _ = diagHom n τ * s * (diagHom n τ)⁻¹ := by group
  have hconj_s : LineU.conjN D hD s = s' := by
    apply Subtype.ext
    rw [LineU.coe_conjN, hconj, hs']
  calc b * (L.subtype.comp φ) s * b⁻¹
      = L.subtype (ggGamma L hN ⟨b, hb⟩ (φ s)) := (ggGamma_coe L hN ⟨b, hb⟩ (φ s)).symm
    _ = L.subtype (φ (LineU.conjN D hD s)) := by rw [hact]
    _ = (L.subtype.comp φ) s' := congrArg (fun u => L.subtype (φ u)) hconj_s


omit [Finite G] in
lemma UnitTB.ker_comp_subtype_le_center
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    {L : Subgroup G} {φ : ↥(unitarySU 2 f F n) →* L} (hM : UnitTB.Model φ) :
    (L.subtype.comp φ).ker ≤ Subgroup.center ↥(unitarySU 2 f F n) := by
  intro g hg
  have hgφ : φ g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
  obtain ⟨c, hc⟩ := hM.ker g hgφ
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hc, ← Matrix.scalar_apply]
  exact (Matrix.scalar_comm c (fun r' => mul_comm c r')
    (((y : ↥(unitarySU 2 f F n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F)).symm

theorem exists_block_of_diagonal_unitary_component
    {F : Type} [Field F] [Finite F] [CharP F 2] {p r f : ℕ}
    (hr : 2 ≤ r) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {φ : ↥(unitarySU 2 f F (r + 1)) →* X}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      LineU.ActsDiagU φ a t)
    {C : Set G} (hCB : C ⊆ Bs)
    (hJ : Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer C)) :
    ∃ S : Finset (Fin (r + 1)),
      J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp φ) ∧ 2 ≤ S.card := by
  classical
  let hKd : UnitaryFieldData 2 f F := hM.field
  have hqne : 2 ^ f + 1 ≠ 1 := by
    have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hqne
  obtain ⟨ζ, hζo, hζpow⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hKd hq hqdvd
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hq.ne_one hζo.symm
  have hζpow' : (ζ : F) ^ (2 ^ f + 1) = 1 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hζpow
  have hζσ : (unitaryInvolution F 2 f) (ζ : F) * ζ = 1 :=
    UFusion.norm_one_of_pow hζpow'
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF (r + 1)
  have hQ : UFusion.IsUFrame (unitaryInvolution F 2 f) P := hP
  let E := SURep.ggFrameEquiv hF P hP
  let ψ : SU (unitaryInvolution F 2 f) (r + 1) →* G :=
    (X.subtype.comp φ).comp E.toMonoidHom
  have hggframe : SURep.ggFrameU hF ψ P hP = X.subtype.comp φ := by
    ext s
    simp [SURep.ggFrameU_apply, ψ, E]
  have hkerφ : (X.subtype.comp φ).ker ≤ Subgroup.center (unitarySU 2 f F (r + 1)) :=
    UnitTB.ker_comp_subtype_le_center hM
  have hkerψ : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (r + 1)) := by
    intro x hx
    have hxE : E x ∈ (X.subtype.comp φ).ker := by
      rw [MonoidHom.mem_ker]
      have hx' := MonoidHom.mem_ker.mp hx
      have hx'' : ((φ (E x) : X) : G) = 1 := by
        simpa [ψ, MonoidHom.comp_apply] using hx'
      exact hx''
    exact (MulEquivClass.apply_mem_center_iff E).1 (hkerφ hxE)
  have hψrange : ψ.range = X := by
    change ((X.subtype.comp φ).comp E.toMonoidHom).range = X
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr E.surjective, Subgroup.map_top,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hM.surj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hL : Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer C) := by
    rw [hψrange]
    exact hJ
  have hAe : IsElemAbelian p (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hS : C ⊆ UFusion.uFrameTorus ψ P := by
    intro b hbC
    have hbB : b ∈ Bs := hCB hbC
    have hmem : ggGamma X hN ⟨b, hbB⟩ ∈ (ggGamma X hN).range := ⟨⟨b, hbB⟩, rfl⟩
    obtain ⟨t, ht⟩ := hdiag _ hmem
    have hpow : (ggGamma X hN ⟨b, hbB⟩) ^ p = 1 := hAe.2 _ hmem
    have hn : 3 ≤ r + 1 := by omega
    have hframe : SURep.GGFrameDiagU (X.subtype.comp φ) b :=
      ggFrameDiagU_of_ggGamma_actsDiagU hKd hn hM.ker hbB ht hpow hpq
    have hframe' : SURep.GGFrameDiagU (SURep.ggFrameU hF ψ P hP) b := by
      rw [hggframe]
      exact hframe
    exact UFusion.mem_uFrameTorus_of_frameDiagU hF hQ hframe'
  obtain ⟨a, hEq, -⟩ :=
    UFusion.exists_eq_uFrameBlock_of_isComponentOf hf1 hF hkerψ hQ hζ1 hζσ hS hL
  have hS2 : 2 ≤ (UFusion.uClass ψ P C a).card := by
    by_contra h
    have hle : (UFusion.uClass ψ P C a).card ≤ 1 := by omega
    have hbot := UFusion.uFrameBlock_eq_bot_of_card_le_one ψ P hle
    have hJbot : J = ⊥ := hEq.trans hbot
    have hJsol : Group.IsSolvable ↥J := by
      rw [hJbot]
      infer_instance
    have hJqNat : CFSG.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL.2.2
    exact (not_isSolvable_of_isQuasisimple hJqNat hJsol).elim
  refine ⟨UFusion.uClass ψ P C a, ?_, hS2⟩
  rw [hEq, UFusion.uFrameBlock_eq_map_blockSU hF hQ, hggframe]

theorem exists_block_of_large_unitary_L_of_cfg
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (L.subtype.comp φ) ∧
        2 ≤ S.card ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side_of_cfg hRig hcfg hIDA (Or.inl rfl) hr hr5 hpq hpd
      hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hDB : D ≤ Bs := hcfg.2.2.1.1.trans hcfg.2.1.1
  obtain ⟨S, hJ, hS⟩ := exists_block_of_diagonal_unitary_component (by omega : 2 ≤ r)
    hΛ.1 hpq hcfg.tableB_facts.2.1 hN hF hM hdiag hDB
      hcfg.2.2.1.2.2.2.2.2.1
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJ, hS, hdiag⟩

theorem exists_block_of_large_unitary_L
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (L.subtype.comp φ) ∧
        2 ≤ S.card ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) :=
  exists_block_of_large_unitary_L_of_cfg hRig hH.1 hH.2.2.1 hr hr5 hpq hpd hLab hΛ

omit [Finite G] in
theorem card_eq_of_blockSU_label
    (hRig : GGLabelRigidInput) {F : Type} [Field F] [Finite F] [CharP F 2]
    {r f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf1 : 1 ≤ f)
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f F (r + 1)))
    {S : Finset (Fin (r + 1))} (hS2 : 2 ≤ S.card)
    (hBq : Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := F) (n := f) S).map ψ))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r - 2, f⟩)
    (hLab : GGHasLabel ⟨.twA, r - 2, f⟩
      (↥((TableBUE.blockSU (K := F) (n := f) S).map ψ) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := F) (n := f) S).map ψ))) :
    S.card = r - 1 := by
  classical
  set B := (TableBUE.blockSU (K := F) (n := f) S).map ψ with hB
  have hKd : UnitaryFieldData 2 f F := TableBU.unitaryFieldData_of_card hF hf1
  have hBqNat : CFSG.IsQuasisimple ↥B :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hBq
  by_cases hsmall : f = 1 ∧ S.card ≤ 3
  · obtain ⟨hf_eq, hScard⟩ := hsmall
    subst f
    have hsol : Group.IsSolvable ↥B := by
      rw [hB]
      exact WitSU.isSolvable_map_blockSU_two_one hKd ψ (by omega : 1 ≤ S.card) hScard
    exact (not_isSolvable_of_isQuasisimple hBqNat hsol).elim
  by_cases hcard2 : S.card = 2
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact hsmall ⟨by omega, by omega⟩
    have hmod : LieModel (↥B ⧸ Subgroup.center ↥B) .PSL 2 2 f := by
      rw [hB]
      exact LinTypeAk.lieModel_map_blockSU_of_card_two hKd hf2 hker hcard2
    have hcls : StatedClassicalModel (↥B ⧸ Subgroup.center ↥B) .PSL 2 2 f :=
      hmod.statedClassicalModel (by decide)
    have hΛA : LargeEvenInLambda2 ⟨.A, 1, f⟩ := largeEvenInLambda2_typeA hcls
    have hLabA : GGHasLabel ⟨.A, 1, f⟩
        (↥B ⧸ Subgroup.center ↥B) := ggHasLabel_typeA hcls
    have hiso := hRig _ _ _ hΛ hΛA hLab hLabA
    simp only [GGLabelIso, LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false,
      or_false] at hiso
  · have hS3 : 3 ≤ S.card := by omega
    have hVq : (S.card, 2 ^ f) ≠ (3, 2) := by
      intro h
      have h3 : S.card = 3 := congrArg Prod.fst h
      have h2pow : 2 ^ f = 2 := congrArg Prod.snd h
      have h4 : 4 ≤ 2 ^ f := by
        have h2 : 2 ≤ f := by
          by_contra hf
          exact hsmall ⟨by omega, by omega⟩
        exact Nat.pow_le_pow_right (n := 2) (by norm_num) h2
      omega
    have hmod : LieModel (↥B ⧸ Subgroup.center ↥B) .PSU S.card 2 f := by
      rw [hB]
      exact SUTorus.lieModel_map_blockSU hKd hker hS3 hVq
    have hcls : StatedClassicalModel (↥B ⧸ Subgroup.center ↥B) .PSU S.card 2 f :=
      hmod.statedClassicalModel (by decide)
    obtain ⟨e⟩ := SUTorus.nonempty_mulEquiv_quotient_center_blockSU hKd hker hS3 hVq
    have hLabB : GGHasLabel ⟨.twA, S.card - 1, f⟩ (↥B ⧸ Subgroup.center ↥B) := by
      rw [hB]
      have hsc : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
      exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA hF (hsc.symm ▸ e)
    have hΛB : LargeEvenInLambda2 ⟨.twA, S.card - 1, f⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA hf1
        (by omega) (by
          intro hb
          by_contra hf2
          exact hsmall ⟨by omega, by omega⟩)
    have hiso := hRig _ _ _ hΛ hΛB hLab hLabB
    simp only [GGLabelIso, LargeEvenLabel.mk.injEq] at hiso
    omega

theorem exists_corank_two_block_of_large_unitary_L_of_cfg
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (L.subtype.comp φ) ∧
        S.card = r - 1 ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJblock, hS2, hdiag⟩ :=
    exists_block_of_large_unitary_L_of_cfg hRig hcfg hIDA hr hr5 hpq hpd hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hΛ.1
  have hkerφ : (L.subtype.comp φ).ker ≤ Subgroup.center (unitarySU 2 f F (r + 1)) :=
    UnitTB.ker_comp_subtype_le_center hM
  have hJq : Assembly.IsQuasisimple
      ((TableBUE.blockSU (K := F) (n := f) S).map (L.subtype.comp φ)) := by
    rw [← hJblock]
    exact hcfg.2.2.1.2.2.2.2.2.1.2.2
  have hJLabBlock : GGHasLabel ⟨.twA, r - 2, f⟩
      ((↥((TableBUE.blockSU (K := F) (n := f) S).map (L.subtype.comp φ)) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := F) (n := f) S).map
          (L.subtype.comp φ)))) := by
    rw [← hJblock]
    exact hJLab
  have hΛJ : LargeEvenInLambda2 ⟨.twA, r - 2, f⟩ := by
    change 1 ≤ f ∧ 2 ≤ r - 2 ∧ (r - 2 = 2 → 2 ≤ f)
    refine ⟨hf1, by omega, ?_⟩
    intro ha
    have hr4 : r = 4 := by omega
    have hp5 : p = 5 := by
      have hdvd : p ∣ 5 := by simpa only [hr4] using hpd
      exact ((Nat.dvd_prime Nat.prime_five).mp hdvd).resolve_left (Fact.out : p.Prime).ne_one
    by_contra hf2
    have hf : f = 1 := by omega
    have : 5 ∣ 3 := by simpa only [hp5, hf, pow_one] using hpq
    norm_num at this
  have hcard := card_eq_of_blockSU_label hRig hF hf1 hkerφ hS2 hJq hΛJ hJLabBlock
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJblock, hcard, hdiag⟩

theorem exists_corank_two_block_of_large_unitary_L
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (L.subtype.comp φ) ∧
        S.card = r - 1 ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) :=
  exists_corank_two_block_of_large_unitary_L_of_cfg hRig hH.1 hH.2.2.1 hr hr5 hpq hpd hLab hΛ
    hJLab

theorem GGResHyp.not_unitaryModel_J_degree_three_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    {F : Type} [Field F] [Finite F] {f : ℕ} (hf2 : 2 ≤ f)
    (hpq : 3 ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f F 3) →* ↥J} (hM : UnitTB.Model ψ) : False := by
  classical
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let K0 := ↥(unitarySU 2 f F 3)
  have hKq : CFSG.IsQuasisimple K0 :=
    (CFSG.RankThree.PartOne.KFU.isQuasisimple_unitarySU_three hM.field hf2).1
  have hker : ψ.ker ≤ Subgroup.center K0 := by
    intro g hg
    obtain ⟨c, hc⟩ := hM.ker g hg
    exact SmallU.mem_center_of_scalar hc
  let e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hKq hM.surj hker
  obtain ⟨E, hEelem, hEcard⟩ := GGResHyp.exists_coroot_quotient_of_A3 hH hD
  let E₁ : Subgroup (K0 ⧸ Subgroup.center K0) := E.map e.symm.toMonoidHom
  have hE₁elem : IsElemAbelian 3 E₁ := hEelem.map e.symm.toMonoidHom
  have hE₁card : Nat.card E₁ = 27 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]
  let e₂ := CFSG.RankThree.PartTwo.KFacts.suCenterEquiv hM.field hq2
  let E₂ : Subgroup (unitaryPSU hM.field 3) :=
    E₁.map e₂.toMonoidHom
  have hE₂elem : IsElemAbelian 3 E₂ := by
    dsimp only [E₂]
    exact hE₁elem.map e₂.toMonoidHom
  have hE₂card : Nat.card E₂ = 27 := by
    dsimp only [E₂]
    rw [Subgroup.card_map_of_injective e₂.injective, hE₁card]
  have hZ : Subgroup.center (unitaryPSU hM.field 3) = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.center_unitaryPSU_three_eq_bot hM.field hq2
  have hconj_inj : Function.Injective
      (MulAut.conj : unitaryPSU hM.field 3 →*
        MulAut (unitaryPSU hM.field 3)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  let B : Subgroup (MulAut (unitaryPSU hM.field 3)) :=
    E₂.map (MulAut.conj : unitaryPSU hM.field 3 →*
      MulAut (unitaryPSU hM.field 3))
  have hBcard : Nat.card B = 27 := by
    rw [Subgroup.card_map_of_injective hconj_inj, hE₂card]
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE₂elem.1.is_comm.comm ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩)
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, hE₂elem.2 y hy, map_one]
  have hBle : B ≤ (CFSG.RankThree.PartTwo.KFacts.psuConj hM.field).range := by
    rintro x ⟨y, -, rfl⟩
    exact CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.mem_psuConj_range_of_isInnerAut
      (CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj y)
  have hF : Nat.card F = (2 ^ f) ^ 2 := by
    calc Nat.card F = 2 ^ (2 * f) := hM.field.card
      _ = (2 ^ f) ^ 2 := by rw [show 2 * f = f * 2 by omega, pow_mul]
  have h3dvd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h2 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      rwa [one_pow] at this
    rw [h2]
    exact dvd_mul_of_dvd_left hpq _
  have hle := CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.card_le_nine_of_le_psuConj_range
    (h := hM.field) h3dvd B hBle hBab hB3
  rw [hBcard] at hle
  norm_num at hle


theorem GGResHyp.unitaryModel_J_degree_ge_four_of_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    {F : Type} [Field F] [Finite F] {f m : ℕ} (hf1 : 1 ≤ f)
    (hpq : 3 ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f F m) →* ↥J} (hM : UnitTB.Model ψ) (hm : 2 ≤ m)
    (hdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin m → F, LineU.ActsDiagU ψ a t) : 4 ≤ m := by
  by_contra hm4
  have hm3 : m = 3 := by
    have h3 := hH.unitaryModel_J_degree_ge_three hm hM hdiag
    omega
  subst hm3
  by_cases hf : f = 1
  · subst hf
    have h43 := hH.unitaryModel_J_degree_ge_four_qTwo hm hM
    omega
  · have hf2 : 2 ≤ f := by omega
    exact (hH.not_unitaryModel_J_degree_three_A3 hD hf2 hpq hM).elim

theorem GGResHyp.exists_twA3_label_of_unitaryModel_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    {F : Type} [Field F] [Finite F] {r f : ℕ}
    (hpq : 3 ∣ 2 ^ f + 1)
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    {φ : ↥(unitarySU 2 f F (r + 1)) →* ↥L}
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .A3 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  obtain ⟨m, hm, ψ, hψM, hψdiag⟩ := hH.exists_unitaryModel_J_of_L hM hdiag
  have hm4 : 4 ≤ m := hH.unitaryModel_J_degree_ge_four_of_A3 hD hΛ.1 hpq hψM hm hψdiag
  have hcard := card_ggAutomizer_eq_factorial_of_unitaryModel
    (p := 3) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hψM
    hψM.field.card_eq_sq (by norm_num : (3 : ℕ) ≠ 2) hpq hm4 hψdiag
  have h24 := ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  have hmfact : m.factorial = 24 := by rw [← hcard, h24]
  have hm4eq : m = 4 := by
    have h4 : m.factorial = Nat.factorial 4 := by
      rw [hmfact]
      norm_num
    exact (Nat.factorial_inj (by omega : 1 < m)).mp h4
  have hm1 : m - 1 = 3 := by omega
  have hJlab : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J) := by
    have h := ggHasLabel_of_unitaryModel hψM (by omega : 3 ≤ m) (by
      intro hdm
      have := congrArg Prod.fst hdm
      omega)
    simpa [hm1] using h
  refine ⟨⟨.twA, 3, f⟩, ?_, ?_, hJlab⟩
  · exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA
      hΛ.1 (by omega) (by omega)
  · unfold ggResLineJLabel
    exact Or.inr ⟨Or.inl rfl, rfl, hpq⟩

theorem GGResHyp.exists_twA3_label_of_large_unitary_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5)
    (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .A3 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  by_cases hpd : 3 ∣ r + 1
  · obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
      exists_diagonal_cover_of_large_unitary_L (p := 3) hRig hH hr hr5 hpq hpd hLab hΛ
    let : Field F := hField
    let : Finite F := hFinite
    let : CharP F 2 := hChar
    exact hH.exists_twA3_label_of_unitaryModel_L hD hpq hΛ hM hdiag
  · obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
      exists_diagonal_cover_of_large_unitary_L_coprime (p := 3) hRig hH hr (Or.inl hr5) hpq hpd
        hLab hΛ
    let : Field F := hField
    let : Finite F := hFinite
    let : CharP F 2 := hChar
    exact hH.exists_twA3_label_of_unitaryModel_L hD hpq hΛ hM hdiag

end CFSG.StandardType

end
