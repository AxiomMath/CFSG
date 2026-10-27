module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
import CFSG.RankThree.PartTwo.Sec4.Census.Witness46
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU localRank)
open CFSG.Assembly.LowTwoRank
open Matrix

theorem isoLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    [Fact p.Prime] (h : IsoLThreePi Y p f) : IsoLThreePi X p f := by
  rcases h with ⟨h1, ⟨e'⟩⟩ | ⟨h1, ⟨e'⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h1, ⟨e.trans e'⟩⟩

section Models

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem isoLThreePi_projImage_slPi [Fact p.Prime] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) : IsoLThreePi (projImage (slPi π 3 (p ^ f) K)) p f := by
  have := hK.finite
  have hf := hK.one_le
  cases π
  · right
    refine ⟨hq, ?_⟩
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hK.card]
      simp only [Sec4.piCard, Bool.cond_false]
      rw [← pow_mul, mul_comm]
    let φ : K ≃+* GaloisField p (2 * f) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) (by omega) hcard
    rw [Sec13.projSU_eq]
    exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
      (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ f))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩
  · left
    refine ⟨hq, ?_⟩
    have hcard : Nat.card K = p ^ f := hK.card
    let φ : K ≃+* GaloisField p f :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hcard
    rw [Sec13.projSL_eq]
    exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
      (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSL φ 3)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩

theorem nonempty_quotient_center_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nonempty (slPi π 3 (p ^ f) K ⧸ Subgroup.center (slPi π 3 (p ^ f) K) ≃*
      projImage (slPi π 3 (p ^ f) K)) := by
  set H := slPi π 3 (p ^ f) K with hH
  have hker : (Sec4.projOf H).ker = Subgroup.center H := by
    ext s
    rw [Sec4.mem_ker_projOf]
    constructor
    · intro hs
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨c, hc⟩ := hs
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hc]
      exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (t : GL (Fin 3) K)).eq
    · intro hs
      exact Sec13.mem_statedScalars_of_mem_center hK hq hs
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (Sec4.projOf_surjective H))⟩

end Models

theorem isoLThreePi_quotient_center_of_isSLThreePiAt {X : Type} [Group X] {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (h : IsSLThreePiAt X (p ^ e)) :
    IsoLThreePi (X ⧸ Subgroup.center X) p e := by
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK⟩ := h
  have key : ∀ (π : Bool), PiField π p e K → ModThree π (p ^ e) →
      Nonempty (X ≃* slPi π 3 (p ^ e) K) → IsoLThreePi (X ⧸ Subgroup.center X) p e := by
    rintro π hPi hq ⟨φ⟩
    obtain ⟨ψ⟩ := nonempty_quotient_center_slPi hPi hq
    have φc : X ⧸ Subgroup.center X ≃* slPi π 3 (p ^ e) K ⧸
        Subgroup.center (slPi π 3 (p ^ e) K) :=
      QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
    exact isoLThreePi_of_mulEquiv (φc.trans ψ)
      (isoLThreePi_projImage_slPi hPi hq)
  rcases hK with ⟨hcard, hq, ⟨φ⟩⟩ | ⟨hcard, hq, ⟨φ⟩⟩
  · exact key true ⟨hp, he, hcard⟩ hq ⟨φ⟩
  · exact key false ⟨hp, he, hcard⟩ hq ⟨φ⟩

section Radical

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem center_eq_bot_of_isoLThreePi (hL : L ∈ thetaComponents 3 G) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he h
  have hq2 : 2 < p ^ e := by
    by_contra h2
    have hp : p.Prime := Fact.out
    have h1 : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
    have h22 : p ^ e = 2 := by omega
    cases π
    · have hsolv := Sec13.isSolvable_projImage_slPi_two hK h22
      have hsL : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have hq' := hL.2.2
      have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hq'.1
      have := CFSG.LocalCores.isQuasisimple_nontrivial hq'
      exact Group.IsPerfect.not_isSolvable (L ⧸ aschbacherSolvableCore 3 L) hsL
    · change p ^ e % 3 = 1 at hq
      omega
  have hZ := Sec13.center_projImage_slPi hK hq hq2
  rw [← Subgroup.map_center_eq φ.symm, hZ, Subgroup.map_bot]

theorem isoLThreePi_solvableRadical (hL : L ∈ thetaComponents 3 G) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) :
    haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
    IsoLThreePi (L ⧸ solvableRadical L) p e := by
  have : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨eR⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := L) hL.2.2
  rcases h with hSL | hPSL
  · exact isoLThreePi_of_mulEquiv eR.symm
      (isoLThreePi_quotient_center_of_isSLThreePiAt he hSL)
  · have hZ := center_eq_bot_of_isoLThreePi hL he hPSL
    have e0 : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)
        ≃* L ⧸ aschbacherSolvableCore 3 L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact isoLThreePi_of_mulEquiv (eR.symm.trans e0) hPSL

theorem localRank_solvableRadical_lt (h41 : Item4_1LargePrime) (hG : SectionFourHyp G)
    (hL : L ∈ thetaComponents 3 G) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
    localRank p (L ⧸ solvableRadical L) < 3 := by
  have : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨eR⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := L) hL.2.2
  have hS := Item41Narrow.sectionFourHyp_thetaQuotient h41 hG hL
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv eR hp]
  exact (Item41Narrow.localRank_quotient_center_le
    (Census.isPGroup_center_thetaQuotient L) hp hp3).trans_lt (hS.localRank_lt p hp hp3)

end Radical

theorem le_two_of_isoLThreePi {S : Type} [Group S] [Finite S] {p e : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (he : 1 ≤ e) (hS : localRank p S < 3) (h : IsoLThreePi S p e) : e ≤ 2 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have : Finite (projSL 3 (GaloisField p e)) := Finite.of_equiv S φ.toEquiv
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv φ hp] at hS
    have := Census.le_localRank_projSL_three hp2 he
    omega
  · have : Finite (projSU 3 p e) := Finite.of_equiv S φ.toEquiv
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv φ hp] at hS
    have := Census.le_localRank_projSU_three hp2 he
    omega

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
