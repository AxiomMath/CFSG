module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryCfg
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryPGL2
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace HeringUnitary

section Lin


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
  {haN : a ∈ Subgroup.normalizer (L : Set G)} {m : ℕ}

theorem chevTwo_projSL_two (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {n : ℕ} (hn : 1 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 n)) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  let e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 F := φ.trans (Sec4.projSLEquivPSLn 2 F)
  have h3 : (3 : F) ≠ 0 :=
    Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) (GaloisField.card 2 n (by omega))
  have hbd : ∀ F' : Subgroup (MulAut (PSL2 F)), CFSG.Assembly.IsElemAbelian 3 F' →
      F' ≤ (pglAction F).range → Nat.card F' ≤ 9 := fun F' hF' hFN => by
    have := card_inf_pglAction_le_nine h3 F' hF'
    rwa [inf_eq_left.mpr hFN] at this
  have hinn : ∀ x, (MulAut.congr e).toMonoidHom (MulAut.conj x) ∈ (pglAction F).range :=
    fun x => by
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact KFacts.innAut_le_range_pglAction F ⟨e x, rfl⟩
  by_cases hout : InducesOuterTheta a L
  · rcases KFacts.inducesKindPSL2_diagonal_or_field (L := L) ha3 hout e with ⟨hx, hd⟩ | hf
    · exfalso
      exact c.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _ hinn hd.1 hbd
    · exact Or.inl (InducesStdKind.psl2 F ⟨e, hf⟩)
  · exfalso
    have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
        (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
      by_contra h
      exact hout ⟨haN, h⟩
    obtain ⟨y, hy⟩ := hin
    refine c.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _ hinn ?_ hbd
    rw [← hy]
    exact hinn y

theorem chevTwo_projSL_three (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {n : ℕ} (hn : 1 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  let e : L ⧸ aschbacherSolvableCore 3 L ≃*
      LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
  have h3 : (3 : F) ≠ 0 :=
    Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) (GaloisField.card 2 n (by omega))
  have hbd : ∀ F' : Subgroup (MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)),
      CFSG.Assembly.IsElemAbelian 3 F' →
      F' ≤ LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F → Nat.card F' ≤ 9 :=
    fun F' hF' hFN => by
      have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
      rwa [inf_eq_left.mpr hFN] at this
  have hinn : ∀ x, (MulAut.congr e).toMonoidHom (MulAut.conj x) ∈
      LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F := fun x => by
    rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
    exact KFacts.innAut_le_linearAutGroup 3 F ⟨e x, rfl⟩
  by_cases hout : InducesOuterTheta a L
  · rcases KFacts.inducesKindPSL_diagonal_or_field (L := L) (by norm_num) ha3 hout e with
      ⟨hx, hd⟩ | hf
    · exfalso
      exact c.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _ hinn hd.1 hbd
    · exact Or.inl (InducesStdKind.psl 3 F (by norm_num) ⟨e, hf⟩)
  · exfalso
    have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
        (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
      by_contra h
      exact hout ⟨haN, h⟩
    obtain ⟨y, hy⟩ := hin
    refine c.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _ hinn ?_ hbd
    rw [← hy]
    exact hinn y

theorem chevTwo_projSU_three (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {n : ℕ} (hn : 1 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 n) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · exfalso
    obtain rfl : n = 1 := by omega
    have hcard : Nat.card (projSU 3 2 1) = 72 := Sec4.Item419ThetaProof.card_projSU_three_two_one
    have hdvd : Nat.card (projSU 3 2 m) ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) :=
      Subgroup.card_dvd_of_injective c.ι c.ι_inj
    rw [Nat.card_congr φ.toEquiv, hcard] at hdvd
    have h2 := Item419Res3.two_pow_dvd_card_projSU_three_two c.odd
    have h9 : 2 ^ 9 ∣ 72 := (pow_dvd_pow 2 (by have := c.three_le; omega)).trans (h2.trans hdvd)
    norm_num at h9
  · have hU := Sec4.unitaryFieldData_galoisField 2 n hn
    haveI := hU.finite
    have hq : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    let e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
      φ.trans (Sec4.projSUEquivUnitaryPSU 2 n hU)
    have h3 : (3 : GaloisField 2 (2 * n)) ≠ 0 :=
      Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num)
        (GaloisField.card 2 (2 * n) (by omega))
    have hbd : ∀ F' : Subgroup (MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3)),
        CFSG.Assembly.IsElemAbelian 3 F' →
        F' ≤ (KFacts.psuConj hU).range → Nat.card F' ≤ 9 :=
      fun F' hF' hFN => Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 F' hF' hFN
    have hinn : ∀ x, (MulAut.congr e).toMonoidHom (MulAut.conj x) ∈
        (KFacts.psuConj hU).range := fun x => by
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨e x, rfl⟩
    by_cases hout : InducesOuterTheta a L
    · rcases KFacts.inducesKindPSU3_diagonal_or_field (L := L) (h := hU) hq ha3 hout e with
        ⟨hx, hd⟩ | hf
      · exfalso
        exact c.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _ hinn hd.1
          hbd
      · exact Or.inl (InducesStdKind.psu3 hU hq ⟨e, hf⟩)
    · exfalso
      have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
          (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
        by_contra h
        exact hout ⟨haN, h⟩
      obtain ⟨y, hy⟩ := hin
      refine c.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _ hinn ?_ hbd
      rw [← hy]
      exact hinn y

theorem chevTwo_statedSL_three (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  have h3 : (3 : K) ≠ 0 := Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hK
  let e : L ⧸ aschbacherSolvableCore 3 L ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  let φ' : MulAut (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) :=
    (LocalAnalysis.ComponentInitial.LinearFlag.descendAut 3 K).comp (MulAut.congr e).toMonoidHom
  have hφ' : Function.Injective φ' :=
    Sec4.descendAut_three_injective.comp (MulAut.congr e).injective
  have hbd : ∀ F' : Subgroup (MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K)),
      CFSG.Assembly.IsElemAbelian 3 F' →
      F' ≤ LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 K → Nat.card F' ≤ 9 :=
    fun F' hF' hFN => by
      have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
      rwa [inf_eq_left.mpr hFN] at this
  have hinn : ∀ x, φ' (MulAut.conj x) ∈
      LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 K := fun x => by
    simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [KFacts.congr_mulAutConj, KFacts.descendAut_conj]
    exact KFacts.innAut_le_linearAutGroup 3 K ⟨_, rfl⟩
  rcases KFacts.inducesKindSL_inner_or_diagonal_or_field (L := L) (by norm_num) haN ha3 e with
    hi | hd | hf
  · exfalso
    exact c.false_of_hom φ' hφ' _ hinn (KFacts.innAut_le_linearAutGroup 3 K hi) hbd
  · exfalso
    exact c.false_of_hom φ' hφ' _ hinn hd.1 hbd
  · exact Or.inl (InducesStdKind.sl 3 K (by norm_num) ⟨e, haN, hf⟩)

theorem chevTwo_statedSU_three (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · exfalso
    obtain rfl : n = 1 := by omega
    have hdvd : Nat.card (projSU 3 2 m) ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) :=
      Subgroup.card_dvd_of_injective c.ι c.ι_inj
    have hX : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ Nat.card (GL (Fin 3) K) := by
      rw [Nat.card_congr φ.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hGL : Nat.card (GL (Fin 3) K) = 181440 := by
      haveI : Fintype K := Fintype.ofFinite K
      have hq4 : Fintype.card K = 4 := by
        rw [← Nat.card_eq_fintype_card, hK]; norm_num
      rw [Matrix.card_GL_field, hq4]
      decide
    have h2 := Item419Res3.two_pow_dvd_card_projSU_three_two c.odd
    have h9 : 2 ^ 9 ∣ 181440 :=
      (pow_dvd_pow 2 (by have := c.three_le; omega)).trans (h2.trans (hdvd.trans (hGL ▸ hX)))
    norm_num at h9
  · have hU : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
      ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have h3 : (3 : K) ≠ 0 := Sec4.three_ne_zero_of_card (p := 2) (f := 2 * n) Nat.prime_two
      (by norm_num) (by rw [hK, ← pow_mul, mul_comm])
    let φ' : MulAut (L ⧸ aschbacherSolvableCore 3 L) →*
        MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3) :=
      (MulAut.congr (KFacts.suCenterEquiv hU hq)).toMonoidHom.comp
        ((KFacts.centerDescend (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 3)).comp
          (MulAut.congr φ).toMonoidHom)
    have hφ' : Function.Injective φ' :=
      (MulAut.congr (KFacts.suCenterEquiv hU hq)).injective.comp
        ((Sec21.Item223CensusProof.centerDescend_injective_unitarySU hU hq).comp
          (MulAut.congr φ).injective)
    have hbd : ∀ F' : Subgroup (MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3)),
        CFSG.Assembly.IsElemAbelian 3 F' →
        F' ≤ (KFacts.psuConj hU).range → Nat.card F' ≤ 9 :=
      fun F' hF' hFN => Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 F' hF' hFN
    have hinn : ∀ x, φ' (MulAut.conj x) ∈ (KFacts.psuConj hU).range := fun x => by
      simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [KFacts.congr_mulAutConj, KFacts.centerDescend_conj, KFacts.congr_mulAutConj]
      exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨_, rfl⟩
    rcases KFacts.inducesKindSU3_inner_or_diagonal_or_field (L := L) (h := hU) hq haN ha3 φ with
      hi | hd | hf
    · exfalso
      exact c.false_of_hom φ' hφ' _ hinn ((KFacts.stdPinnedPSU3 hU).inn_le hi) hbd
    · exfalso
      exact c.false_of_hom φ' hφ' _ hinn hd.1 hbd
    · exact Or.inl (InducesStdKind.su3 hU hq ⟨φ, haN, hf⟩)

end Lin

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
