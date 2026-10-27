module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Objects
public import Certificates.Certificate17280
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixC
public import CFSG.CGT.PushingUpLit.BHS.FourOne
public import CFSG.CGT.PushingUpLit.BHS.FourOneD
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GF2Type.Smith1979.GammaU.Sigma
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.Timmesfeld.Moufang.Cases
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8026Base

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GammaU.Native
open HJBridge (RowsOf rowsOf_mul rowsOf_one rowsOf_hjWord rowsOf_unique)
open HJ12 (wordR)

local notation "hjW1" => (HJ12.hj_eWords.headD [])
local notation "hjW2" => (HJ12.hj_eWords.getD 1 [])
local notation "hjE1" => hjWord hjW1
local notation "hjE2" => hjWord hjW2
local notation "hjR1" => wordR hjW1
local notation "hjR2" => wordR hjW2

noncomputable def hjA : Subgroup (MulAut W12) :=
  Subgroup.zpowers hjE1 ⊔ Subgroup.zpowers hjE2

theorem mem_fixCodes_of_mem_fixV {x : MulAut W12} {r : Array ℕ}
    (hx : HJBridge.RowsOf x r) (hr : ∀ y ∈ r, y < 4096) {v : W12}
    (hv : v ∈ fixV (Subgroup.zpowers x)) :
    CFSG.GF2Type.Smith1979.GammaU.codeOf (Multiplicative.toAdd v) ∈ HJ12.fixCodes r := by
  have hv' : x v = v := (HJBridge.mem_fixV_zpowers_iff x v).1 hv
  have h := hx (Multiplicative.toAdd v)
  rw [ofAdd_toAdd, hv'] at h
  have hlin : CFSG.GF2Type.Smith1979.GammaU.linOfRows r (Multiplicative.toAdd v) =
      Multiplicative.toAdd v := (congrArg Multiplicative.toAdd h).symm
  have hcode : CFSG.GF2Type.Smith1979.GammaU.appN r
      (CFSG.GF2Type.Smith1979.GammaU.codeOf (Multiplicative.toAdd v)) =
      CFSG.GF2Type.Smith1979.GammaU.codeOf (Multiplicative.toAdd v) := by
    apply CFSG.GF2Type.Smith1979.GammaU.vecOf_inj
      (CFSG.GF2Type.Smith1979.GammaU.StepA.appN_lt hr _)
      (CFSG.GF2Type.Smith1979.GammaU.codeOf_lt _)
    rw [CFSG.GF2Type.Smith1979.GammaU.vecOf_appN,
      CFSG.GF2Type.Smith1979.GammaU.vecOf_codeOf, hlin]
  simp only [HJ12.fixCodes, List.mem_filter, List.mem_range, beq_iff_eq]
  exact ⟨CFSG.GF2Type.Smith1979.GammaU.codeOf_lt _, by
    simpa only [CFSG.GF2Type.Smith1979.GammaU.native_appN] using hcode⟩

theorem fixV_eq_of_fixCodes_eq {x y : MulAut W12} {r s : Array ℕ}
    (hx : HJBridge.RowsOf x r) (hy : HJBridge.RowsOf y s)
    (hr : ∀ z ∈ r, z < 4096) (hs : ∀ z ∈ s, z < 4096)
    (h : HJ12.fixCodes r = HJ12.fixCodes s) :
    fixV (Subgroup.zpowers x) = fixV (Subgroup.zpowers y) := by
  have hcode : ∀ {v : W12}, v ∈ fixV (Subgroup.zpowers x) →
      CFSG.GF2Type.Smith1979.GammaU.codeOf (Multiplicative.toAdd v) ∈
        HJ12.fixCodes s := by
    intro v hv
    rw [← h]
    exact mem_fixCodes_of_mem_fixV hx hr hv
  apply le_antisymm
  · intro v hv
    have h' := mem_fixV_of_mem_fixCodes hy (hcode hv)
    have hv' : v = Multiplicative.ofAdd (CFSG.GF2Type.Smith1979.GammaU.vecOf
        (CFSG.GF2Type.Smith1979.GammaU.codeOf (Multiplicative.toAdd v))) := by
      rw [CFSG.GF2Type.Smith1979.GammaU.vecOf_codeOf, ofAdd_toAdd]
    rw [hv']
    exact h'
  · intro v hv
    have h' := mem_fixV_of_mem_fixCodes hx (by
      rw [h]
      exact mem_fixCodes_of_mem_fixV hy hs hv)
    have hv' : v = Multiplicative.ofAdd (CFSG.GF2Type.Smith1979.GammaU.vecOf
        (CFSG.GF2Type.Smith1979.GammaU.codeOf (Multiplicative.toAdd v))) := by
      rw [CFSG.GF2Type.Smith1979.GammaU.vecOf_codeOf, ofAdd_toAdd]
    rw [hv']
    exact h'

theorem hjQuad_A_basic :
    hjA ≤ hjL0 ∧ hjA ≠ ⊥ ∧ IsElemAbelian2 hjA := by
  classical
  have hc : HJ12.hjQuadFourCheck = true := Certificates.certificate17280
  simp only [HJ12.hjQuadFourCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨⟨⟨hinv1, hinv2⟩, hcomm⟩, hne⟩, hfix2⟩, hfix12⟩ := hc
  have hinv1' : hjR1 ≠ CFSG.GammaU.Native.idR ∧
      CFSG.GammaU.Native.mulR hjR1 hjR1 = CFSG.GammaU.Native.idR := by
    simpa [HJ12.isInvol, beq_iff_eq, bne_iff_ne] using hinv1
  have hinv2' : hjR2 ≠ CFSG.GammaU.Native.idR ∧
      CFSG.GammaU.Native.mulR hjR2 hjR2 = CFSG.GammaU.Native.idR := by
    simpa [HJ12.isInvol, beq_iff_eq, bne_iff_ne] using hinv2
  have he1_sq : hjE1 ^ 2 = 1 := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW1) (HJBridge.rowsOf_hjWord hjW1)
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR hjR1 hjR1 =
      CFSG.GammaU.Native.mulR hjR1 hjR1 from rfl, hinv1'.2] at h
    have h1 := HJBridge.rowsOf_unique h HJBridge.rowsOf_one
    simpa [pow_two] using h1
  have he2_sq : hjE2 ^ 2 = 1 := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW2) (HJBridge.rowsOf_hjWord hjW2)
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR hjR2 hjR2 =
      CFSG.GammaU.Native.mulR hjR2 hjR2 from rfl, hinv2'.2] at h
    have h1 := HJBridge.rowsOf_unique h HJBridge.rowsOf_one
    simpa [pow_two] using h1
  have hcomm' : CFSG.GammaU.Native.mulR hjR1 hjR2 =
      CFSG.GammaU.Native.mulR hjR2 hjR1 := by
    simpa [HJ12.commR, beq_iff_eq] using hcomm
  have he12 : hjE1 * hjE2 = hjE2 * hjE1 := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW1) (HJBridge.rowsOf_hjWord hjW2)
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR hjR1 hjR2 =
      CFSG.GammaU.Native.mulR hjR1 hjR2 from rfl, hcomm'] at h
    exact HJBridge.rowsOf_unique h
      (HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW2) (HJBridge.rowsOf_hjWord hjW1))
  have he1_ne_one : hjE1 ≠ 1 :=
    hjWord_ne_one (by
      simpa only [CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] using hinv1'.1)
  have he2_ne_one : hjE2 ≠ 1 :=
    hjWord_ne_one (by
      simpa only [CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] using hinv2'.1)
  have he_ne : hjE1 ≠ hjE2 := by
    intro h
    have h1 : HJBridge.RowsOf hjE2 hjR1 := by
      rw [← h]
      exact HJBridge.rowsOf_hjWord hjW1
    have hrows := rows_eq_of_rowsOf h1 (HJBridge.rowsOf_hjWord hjW2)
      (by simpa using HJBridge.wordR_canon hjW1)
      (by simpa using HJBridge.wordR_canon hjW2)
    exact hne hrows
  have hzp : ∀ {x y : MulAut W12}, x ^ 2 = 1 → y ∈ Subgroup.zpowers x → y = 1 ∨ y = x := by
    intro x y hx2 hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases Int.even_or_odd' n with ⟨m, hm | hm⟩
    · left
      rw [hm, zpow_mul, zpow_two, ← sq, hx2, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_two, ← sq, hx2, one_zpow, one_mul, zpow_one]
  have hcomm_e : ∀ a ∈ Subgroup.zpowers hjE1, ∀ b ∈ Subgroup.zpowers hjE2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_zpow he12 m n)).eq
  have hAelems : ∀ a ∈ hjA, a = 1 ∨ a = hjE1 ∨ a = hjE2 ∨ a = hjE1 * hjE2 := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_e ha
    rcases hzp he1_sq hx with rfl | rfl
    · rcases hzp he2_sq hy with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inr (Or.inl (by simp)))
    · rcases hzp he2_sq hy with rfl | rfl
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have hcardz1 : Nat.card ↥(Subgroup.zpowers hjE1) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime he1_sq he1_ne_one]
  have hcardz2 : Nat.card ↥(Subgroup.zpowers hjE2) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime he2_sq he2_ne_one]
  have hcard_inter : Nat.card ↥(Subgroup.zpowers hjE1 ⊓ Subgroup.zpowers hjE2) = 1 := by
    have hbot : Subgroup.zpowers hjE1 ⊓ Subgroup.zpowers hjE2 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases hzp he1_sq hx.1 with rfl | rfl
      · exact Subgroup.one_mem ⊥
      · rcases hzp he2_sq hx.2 with h | h
        · exact absurd h he1_ne_one
        · exact absurd h he_ne
    rw [hbot]
    simp
  have hcardA : Nat.card ↥hjA = 4 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers hjE1) (Subgroup.zpowers hjE2) hcomm_e).1
    rw [hcardz1, hcardz2, hcard_inter] at h
    change Nat.card ↥(Subgroup.zpowers hjE1 ⊔ Subgroup.zpowers hjE2) = 4
    omega
  have hAel : IsElemAbelian2 hjA :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian2_sup
      (CFSG.Quasithin.StabLat.isElemAbelian2_zpowers he1_sq)
      (CFSG.Quasithin.StabLat.isElemAbelian2_zpowers he2_sq) hcomm_e
  refine ⟨?_, ?_, hAel⟩
  · exact sup_le (Subgroup.zpowers_le.2 (hjWord_mem hjW1))
      (Subgroup.zpowers_le.2 (hjWord_mem hjW2))
  · intro hbot
    have hmem : hjE1 ∈ hjA := Subgroup.mem_sup_left (Subgroup.mem_zpowers hjE1)
    rw [hbot] at hmem
    exact he1_ne_one (Subgroup.mem_bot.mp hmem)

theorem hjQuad_A_fixed :
    ∀ B : Subgroup (MulAut W12), B ≤ hjA → E3.mQuot hjA B < 2 → fixV B = fixV hjA := by

  classical
  have hc : HJ12.hjQuadFourCheck = true := Certificates.certificate17280
  simp only [HJ12.hjQuadFourCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨⟨⟨hinv1, hinv2⟩, hcomm⟩, hne⟩, hfix2⟩, hfix12⟩ := hc
  have hinv1' : hjR1 ≠ CFSG.GammaU.Native.idR ∧
      CFSG.GammaU.Native.mulR hjR1 hjR1 = CFSG.GammaU.Native.idR := by
    simpa [HJ12.isInvol, beq_iff_eq, bne_iff_ne] using hinv1
  have hinv2' : hjR2 ≠ CFSG.GammaU.Native.idR ∧
      CFSG.GammaU.Native.mulR hjR2 hjR2 = CFSG.GammaU.Native.idR := by
    simpa [HJ12.isInvol, beq_iff_eq, bne_iff_ne] using hinv2
  have he1_sq : hjE1 ^ 2 = 1 := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW1) (HJBridge.rowsOf_hjWord hjW1)
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR hjR1 hjR1 =
      CFSG.GammaU.Native.mulR hjR1 hjR1 from rfl, hinv1'.2] at h
    have h1 := HJBridge.rowsOf_unique h HJBridge.rowsOf_one
    simpa [pow_two] using h1
  have he2_sq : hjE2 ^ 2 = 1 := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW2) (HJBridge.rowsOf_hjWord hjW2)
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR hjR2 hjR2 =
      CFSG.GammaU.Native.mulR hjR2 hjR2 from rfl, hinv2'.2] at h
    have h1 := HJBridge.rowsOf_unique h HJBridge.rowsOf_one
    simpa [pow_two] using h1
  have hcomm' : CFSG.GammaU.Native.mulR hjR1 hjR2 =
      CFSG.GammaU.Native.mulR hjR2 hjR1 := by
    simpa [HJ12.commR, beq_iff_eq] using hcomm
  have he12 : hjE1 * hjE2 = hjE2 * hjE1 := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW1) (HJBridge.rowsOf_hjWord hjW2)
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR hjR1 hjR2 =
      CFSG.GammaU.Native.mulR hjR1 hjR2 from rfl, hcomm'] at h
    exact HJBridge.rowsOf_unique h
      (HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW2) (HJBridge.rowsOf_hjWord hjW1))
  have he1_ne_one : hjE1 ≠ 1 :=
    hjWord_ne_one (by
      simpa only [CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] using hinv1'.1)
  have he2_ne_one : hjE2 ≠ 1 :=
    hjWord_ne_one (by
      simpa only [CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] using hinv2'.1)
  have he_ne : hjE1 ≠ hjE2 := by
    intro h
    have h1 : HJBridge.RowsOf hjE2 hjR1 := by
      rw [← h]
      exact HJBridge.rowsOf_hjWord hjW1
    have hrows := rows_eq_of_rowsOf h1 (HJBridge.rowsOf_hjWord hjW2)
      (by simpa using HJBridge.wordR_canon hjW1)
      (by simpa using HJBridge.wordR_canon hjW2)
    exact hne hrows
  have hzp : ∀ {x y : MulAut W12}, x ^ 2 = 1 → y ∈ Subgroup.zpowers x → y = 1 ∨ y = x := by
    intro x y hx2 hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases Int.even_or_odd' n with ⟨m, hm | hm⟩
    · left
      rw [hm, zpow_mul, zpow_two, ← sq, hx2, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_two, ← sq, hx2, one_zpow, one_mul, zpow_one]
  have hcomm_e : ∀ a ∈ Subgroup.zpowers hjE1, ∀ b ∈ Subgroup.zpowers hjE2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_zpow he12 m n)).eq
  have hAelems : ∀ a ∈ hjA, a = 1 ∨ a = hjE1 ∨ a = hjE2 ∨ a = hjE1 * hjE2 := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_e ha
    rcases hzp he1_sq hx with rfl | rfl
    · rcases hzp he2_sq hy with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inr (Or.inl (by simp)))
    · rcases hzp he2_sq hy with rfl | rfl
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have hcardz1 : Nat.card ↥(Subgroup.zpowers hjE1) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime he1_sq he1_ne_one]
  have hcardz2 : Nat.card ↥(Subgroup.zpowers hjE2) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime he2_sq he2_ne_one]
  have hcard_inter : Nat.card ↥(Subgroup.zpowers hjE1 ⊓ Subgroup.zpowers hjE2) = 1 := by
    have hbot : Subgroup.zpowers hjE1 ⊓ Subgroup.zpowers hjE2 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases hzp he1_sq hx.1 with rfl | rfl
      · exact Subgroup.one_mem ⊥
      · rcases hzp he2_sq hx.2 with h | h
        · exact absurd h he1_ne_one
        · exact absurd h he_ne
    rw [hbot]
    simp
  have hcardA : Nat.card ↥hjA = 4 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers hjE1) (Subgroup.zpowers hjE2) hcomm_e).1
    rw [hcardz1, hcardz2, hcard_inter] at h
    change Nat.card ↥(Subgroup.zpowers hjE1 ⊔ Subgroup.zpowers hjE2) = 4
    omega
  have hAel : IsElemAbelian2 hjA :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian2_sup
      (CFSG.Quasithin.StabLat.isElemAbelian2_zpowers he1_sq)
      (CFSG.Quasithin.StabLat.isElemAbelian2_zpowers he2_sq) hcomm_e
  have hfix_e : fixV (Subgroup.zpowers hjE1) = fixV (Subgroup.zpowers hjE2) :=
    fixV_eq_of_fixCodes_eq (HJBridge.rowsOf_hjWord hjW1) (HJBridge.rowsOf_hjWord hjW2)
      (HJBridge.wordR_canon hjW1).2 (HJBridge.wordR_canon hjW2).2 hfix2.symm
  have hfix_12 : fixV (Subgroup.zpowers (hjE1 * hjE2)) = fixV (Subgroup.zpowers hjE1) :=
    fixV_eq_of_fixCodes_eq
      (HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord hjW1) (HJBridge.rowsOf_hjWord hjW2))
      (HJBridge.rowsOf_hjWord hjW1)
      (mulR_lt (HJBridge.wordR_canon hjW1).2)
      (HJBridge.wordR_canon hjW1).2 hfix12
  have hfixA : fixV hjA = fixV (Subgroup.zpowers hjE1) := by
    apply le_antisymm
    · intro v hv
      exact fun x hx => hv x (Subgroup.mem_sup_left hx)
    · intro v hv
      have hv2 : v ∈ fixV (Subgroup.zpowers hjE2) := by rw [← hfix_e]; exact hv
      exact CFSG.Quasithin.FixVLat.mem_fixV_sup hv hv2
  intro B hB hm
  have hA2 : IsPGroup 2 ↥hjA := CFSG.Quasithin.E3.isPGroup_of_isElemAbelian2 hAel
  have hrel : B.relIndex hjA = 2 ^ E3.mQuot hjA B := E3.relIndex_eq_two_pow hA2 B
  set m := E3.mQuot hjA B with hmdef
  have hm01 : E3.mQuot hjA B = 0 ∨ E3.mQuot hjA B = 1 := by
    have hm' : m < 2 := hm
    interval_cases m
    · exact Or.inl hmdef.symm
    · exact Or.inr hmdef.symm
  rcases hm01 with hm0 | hm1
  · have hm0' : m = 0 := by rw [hmdef]; exact hm0
    have hrel1 : B.relIndex hjA = 1 := by rw [hrel, hm0', pow_zero]
    have hBA : hjA ≤ B := Subgroup.relIndex_eq_one.1 hrel1
    have hBeq : B = hjA := le_antisymm hB hBA
    rw [hBeq]
  · have hm1' : m = 1 := by rw [hmdef]; exact hm1
    have hrel2 : B.relIndex hjA = 2 := by rw [hrel, hm1']; norm_num
    have hcardB : Nat.card ↥B = 2 := by
      have hmul := Subgroup.relIndex_mul_card B hjA
      rw [inf_eq_left.2 hB, hrel2] at hmul
      have hmul' : 2 * Nat.card ↥B = 4 := hmul.trans hcardA
      omega
    have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot] at hcardB
      simp at hcardB
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbord : orderOf b = 2 := by
      have hdvd : orderOf b ∣ Nat.card ↥B := Subgroup.orderOf_dvd_natCard B hbB
      rw [hcardB] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hb1'
      · exact h
    have hBz : B = Subgroup.zpowers b := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbB) ?_
      rw [Nat.card_zpowers, hbord, hcardB]
    rw [hBz]
    rcases hAelems b (hB hbB) with rfl | rfl | rfl | rfl
    · exact absurd rfl hb1'
    · exact hfixA.symm
    · exact hfix_e.symm.trans hfixA.symm
    · exact hfix_12.trans hfixA.symm
theorem hjQuad_mem_aSet : hjA ∈ E3.aSet 2 hjL0 :=
  ⟨hjQuad_A_basic.1, hjQuad_A_basic.2.1, hjQuad_A_basic.2.2, hjQuad_A_fixed⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
