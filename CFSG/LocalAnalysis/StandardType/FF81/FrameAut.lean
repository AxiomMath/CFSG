module

public import CFSG.LocalAnalysis.StandardType.FF81.FrameMat
import CFSG.RankThree.PartOne.TAIL.LSideOutAut
import CFSG.LargeExtraspecial.DW37Input
import CFSG.ClassicalInvolution.Phan.BlockSingle
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSLAux
import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.TAIL.KSideCen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.FF81

open scoped MatrixGroups

open CFSG.ClassicalInvolution.Phan in
private lemma coe_jBlock_transvection {n : ℕ} [NeZero n] {a b : ℕ} (ha : a < n - 1)
    (hb : b < n - 1) (hab : a ≠ b) :
    (jBlock n
        (Matrix.SpecialLinearGroup.transvection (i := (⟨a, ha⟩ : Fin (n - 1)))
          (j := (⟨b, hb⟩ : Fin (n - 1))) (by simpa [Fin.ext_iff] using hab) (1 : ZMod 2)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) =
      1 + Matrix.single (⟨2 + a, by omega⟩ : Fin (n + 1)) ⟨2 + b, by omega⟩ (1 : ZMod 2) := by
  have hblock : (jBlock n
      (Matrix.SpecialLinearGroup.transvection (i := (⟨a, ha⟩ : Fin (n - 1)))
        (j := (⟨b, hb⟩ : Fin (n - 1))) (by simpa [Fin.ext_iff] using hab) (1 : ZMod 2)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) =
      blockMat (F := ZMod 2) (n + 1) 2
        ((Matrix.SpecialLinearGroup.transvection (i := (⟨a, ha⟩ : Fin (n - 1)))
          (j := (⟨b, hb⟩ : Fin (n - 1))) (by simpa [Fin.ext_iff] using hab) (1 : ZMod 2)) :
          Matrix (Fin (n - 1)) (Fin (n - 1)) (ZMod 2)) := rfl
  rw [hblock, Matrix.SpecialLinearGroup.transvection_coe]
  exact blockMat_one_add_single (by have := NeZero.pos n; omega)
    (⟨a, ha⟩ : Fin (n - 1)) ⟨b, hb⟩ (1 : ZMod 2)

open CFSG.ComponentClassification.CatalogueBGraphForm in
private lemma coe_slGraphAut_transvection {m : ℕ} (p q : Fin (m + 1)) (hpq : p ≠ q) :
    (slGraphAut (m + 1) (ZMod 2) (Matrix.SpecialLinearGroup.transvection hpq (1 : ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = 1 + Matrix.single q p (1 : ZMod 2) := by
  have h : slGraphAut (m + 1) (ZMod 2) (Matrix.SpecialLinearGroup.transvection hpq 1) =
      Matrix.SpecialLinearGroup.transvection hpq.symm 1 :=
    (CFSG.StandardType.RCKRP.irgL_slGraphAut_transvection hpq (1 : ZMod 2)).trans
      (congrArg (Matrix.SpecialLinearGroup.transvection hpq.symm)
        (show (-1 : ZMod 2) = 1 by decide))
  rw [h, Matrix.SpecialLinearGroup.transvection_coe]

private lemma mul_single_of_fixes_jBlock {n : ℕ} [NeZero n] (g : SL(n + 1, ZMod 2))
    (hfix : ∀ B : SL(n - 1, ZMod 2),
      (MulAut.conj g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (n + 1)
        (ZMod 2)) (jBlock n B) = jBlock n B)
    {a b : ℕ} (ha : a < n - 1) (hb : b < n - 1) (hab : a ≠ b) :
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) *
        Matrix.single (⟨2 + b, by omega⟩ : Fin (n + 1)) ⟨2 + a, by omega⟩ (1 : ZMod 2) =
      Matrix.single (⟨2 + a, by omega⟩ : Fin (n + 1)) ⟨2 + b, by omega⟩ (1 : ZMod 2) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) := by
  let B : SL(n - 1, ZMod 2) :=
    Matrix.SpecialLinearGroup.transvection (i := (⟨a, ha⟩ : Fin (n - 1)))
      (j := (⟨b, hb⟩ : Fin (n - 1))) (by simpa [Fin.ext_iff] using hab) (1 : ZMod 2)
  have hne : (⟨2 + a, by omega⟩ : Fin (n + 1)) ≠ ⟨2 + b, by omega⟩ := by
    intro h
    apply hab
    have h' : 2 + a = 2 + b := by simpa using congrArg Fin.val h
    omega
  have hB : (jBlock n B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) =
      1 + Matrix.single (⟨2 + a, by omega⟩ : Fin (n + 1)) ⟨2 + b, by omega⟩ (1 : ZMod 2) :=
    coe_jBlock_transvection ha hb hab
  have hB' : jBlock n B =
      Matrix.SpecialLinearGroup.transvection (i := (⟨2 + a, by omega⟩ : Fin (n + 1)))
        (j := (⟨2 + b, by omega⟩ : Fin (n + 1))) hne (1 : ZMod 2) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.transvection_coe]
    exact hB
  have h0 := hfix B
  rw [MulAut.mul_apply, MulAut.conj_apply] at h0
  have h1 : g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (n + 1) (ZMod 2)
      (jBlock n B) = jBlock n B * g := by
    have := congrArg (fun z : SL(n + 1, ZMod 2) => z * g) h0
    simpa [mul_assoc] using this
  have h2 := congrArg (fun z : SL(n + 1, ZMod 2) =>
    (z : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))) h1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
  rw [hB', coe_slGraphAut_transvection (p := (⟨2 + a, by omega⟩ : Fin (n + 1)))
    (q := (⟨2 + b, by omega⟩ : Fin (n + 1))) hne,
    Matrix.SpecialLinearGroup.transvection_coe] at h2
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h2
  exact add_left_cancel h2

private lemma not_conj_mul_slGraphAut_fixes_jBlock {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    (g : SL(n + 1, ZMod 2))
    (hfix : ∀ B : SL(n - 1, ZMod 2),
      (MulAut.conj g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (n + 1)
        (ZMod 2)) (jBlock n B) = jBlock n B) :
    False := by
  have h0 := mul_single_of_fixes_jBlock (n := n) g hfix (a := 0) (b := 1)
    (by omega) (by omega) (by decide)
  have h1 := mul_single_of_fixes_jBlock (n := n) g hfix (a := 1) (b := 2)
    (by omega) (by omega) (by decide)
  have hR : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) *
      (Matrix.single (⟨3, by omega⟩ : Fin (n + 1)) ⟨2, by omega⟩ (1 : ZMod 2) *
        Matrix.single (⟨4, by omega⟩ : Fin (n + 1)) ⟨3, by omega⟩ (1 : ZMod 2)) =
      Matrix.single (⟨2, by omega⟩ : Fin (n + 1)) ⟨4, by omega⟩ (1 : ZMod 2) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) := by
    rw [← Matrix.mul_assoc, h0, Matrix.mul_assoc, h1, ← Matrix.mul_assoc]
    simp
  have hzero : (Matrix.single (⟨2, by omega⟩ : Fin (n + 1)) ⟨4, by omega⟩ (1 : ZMod 2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = 0 := by
    rw [← hR]
    have h32 : (Matrix.single (⟨3, by omega⟩ : Fin (n + 1)) ⟨2, by omega⟩ (1 : ZMod 2) *
        Matrix.single (⟨4, by omega⟩ : Fin (n + 1)) ⟨3, by omega⟩ (1 : ZMod 2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = 0 := by
      simp [Matrix.single_mul_single_of_ne]
    rw [h32, Matrix.mul_zero]
  have hsingle : (Matrix.single (⟨2, by omega⟩ : Fin (n + 1)) ⟨4, by omega⟩ (1 : ZMod 2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = 0 := by
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) =>
      M * ((g⁻¹ : SL(n + 1, ZMod 2)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))) hzero
    rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.zero_mul] at h
    exact h
  have hcontra := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) =>
    M (⟨2, by omega⟩ : Fin (n + 1)) ⟨4, by omega⟩) hsingle
  simp only [Matrix.single_apply_same, Matrix.zero_apply] at hcontra
  exact absurd hcontra (by decide)

private lemma exists_conj_eq_of_fixes_tOne_jBlock {n : ℕ} [NeZero n] (g : SL(n + 1, ZMod 2))
    (h1 : MulAut.conj g (tOne n) = tOne n)
    (h2 : ∀ B : SL(n - 1, ZMod 2), MulAut.conj g (jBlock n B) = jBlock n B) :
    ∃ a : ℕ, MulAut.conj g = MulAut.conj (tOne n ^ a) := by
  have hcomm : g * tOne n = tOne n * g := by
    rw [MulAut.conj_apply] at h1
    have h := congrArg (fun z : SL(n + 1, ZMod 2) => z * g) h1
    simpa [mul_assoc] using h
  obtain ⟨a, B, hg⟩ := mem_centralizer_tOne_iff.mp hcomm
  have hconj : MulAut.conj g = MulAut.conj (tOne n ^ a) * MulAut.conj (jBlock n B) := by
    rw [hg, map_mul]
  have hBC : ∀ C : SL(n - 1, ZMod 2), B * C = C * B := by
    intro C
    have hfix : MulAut.conj (jBlock n B) (jBlock n C) = jBlock n C := by
      have h := h2 C
      rw [hconj, MulAut.mul_apply] at h
      have hx : Commute (tOne n ^ a) (MulAut.conj (jBlock n B) (jBlock n C)) := by
        rw [MulAut.conj_apply]
        have hB : Commute (tOne n ^ a) (jBlock n B) := by
          rw [tOne, ← map_pow]
          exact blockSL2_zero_mul_jBlock n (rhoTwo ^ a) B
        have hC : Commute (tOne n ^ a) (jBlock n C) := by
          rw [tOne, ← map_pow]
          exact blockSL2_zero_mul_jBlock n (rhoTwo ^ a) C
        exact (hB.mul_right hC).mul_right hB.inv_right
      have hx' : MulAut.conj (tOne n ^ a) (MulAut.conj (jBlock n B) (jBlock n C)) =
          MulAut.conj (jBlock n B) (jBlock n C) := by
        rw [MulAut.conj_apply]
        exact hx.mul_inv_cancel
      rwa [hx'] at h
    have hbc : jBlock n B * jBlock n C = jBlock n C * jBlock n B := by
      have := congrArg (fun z : SL(n + 1, ZMod 2) => z * jBlock n B) hfix
      rw [MulAut.conj_apply] at this
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
    exact jBlock_injective n (by rw [map_mul, map_mul]; exact hbc)
  have hB1 : B = 1 := by
    have hmem : B ∈ Subgroup.center (SL(n - 1, ZMod 2)) :=
      Subgroup.mem_center_iff.mpr (fun C => (hBC C).symm)
    rw [CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot (n - 1)] at hmem
    exact Subgroup.mem_bot.mp hmem
  refine ⟨a, ?_⟩
  rw [hg, hB1, map_one (jBlock n), mul_one]

theorem exists_eq_conj_tOne_pow {n : ℕ} [NeZero n] (hn : 4 ≤ n) (β : MulAut SL(n + 1, ZMod 2))
    (h1 : β (tOne n) = tOne n) (h2 : ∀ B : SL(n - 1, ZMod 2), β (jBlock n B) = jBlock n B) :
    ∃ a : ℕ, β = MulAut.conj (tOne n ^ a) := by
  obtain ⟨g, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two (n := n + 1) (by omega) β
  interval_cases ε
  · rw [hβ, pow_zero, mul_one] at h1
    obtain ⟨a, ha⟩ := exists_conj_eq_of_fixes_tOne_jBlock g h1 (by
      intro B
      have h := h2 B
      rw [hβ, pow_zero, mul_one] at h
      exact h)
    exact ⟨a, by rw [hβ, pow_zero, mul_one, ha]⟩
  · exfalso
    rw [pow_one] at hβ
    exact not_conj_mul_slGraphAut_fixes_jBlock hn g (by
      intro B
      have h := h2 B
      rwa [hβ] at h)

private lemma eq_one_of_commute {G : Type} [Group G] {n : ℕ} {L : Subgroup G}
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) {z : ↥L}
    (hz : ∀ y : ↥L, z * y = y * z) : z = 1 := by
  have hmem : φ z ∈ Subgroup.center (SL(n + 1, ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro A
    calc A * φ z = φ (φ.symm A) * φ z := by
          conv_lhs => rw [← MulEquiv.apply_symm_apply φ A]
      _ = φ (φ.symm A * z) := by rw [← MulEquiv.map_mul]
      _ = φ (z * φ.symm A) := by rw [← hz (φ.symm A)]
      _ = φ z * φ (φ.symm A) := by rw [MulEquiv.map_mul]
      _ = φ z * A := by rw [MulEquiv.apply_symm_apply φ A]
  have hcenter := CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot (n + 1)
  rw [hcenter, Subgroup.mem_bot] at hmem
  apply φ.injective
  rw [hmem, MulEquiv.map_one]

private lemma pow_eq_one_of_conj_eq {G : Type} [Group G] {n : ℕ} {L : Subgroup G}
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) {w : ↥L} {x : G} {a : ℕ}
    (hwo : orderOf w = 3) (hcop : Nat.Coprime (orderOf x) 3)
    (hxy : ∀ y : ↥L, x * (y : G) * x⁻¹ =
      ((w ^ a : ↥L) : G) * (y : G) * (((w ^ a : ↥L) : G))⁻¹) :
    w ^ a = 1 := by
  let wG : G := ((w ^ a : ↥L) : G)
  let c : G := wG⁻¹ * x
  have hc : ∀ y : ↥L, c * (y : G) = (y : G) * c := by
    intro y
    have h := congrArg (fun t => wG⁻¹ * t * x) (hxy y)
    calc c * (y : G) = wG⁻¹ * (x * (y : G) * x⁻¹) * x := by
          dsimp only [c]
          group
      _ = wG⁻¹ * (wG * (y : G) * wG⁻¹) * x := by rw [h]
      _ = (y : G) * c := by
          dsimp only [c]
          group
  have hcw : Commute wG c :=
    (commute_iff_eq wG c).mpr (by simpa [wG] using (hc (w ^ a)).symm)
  have hxeq : x = wG * c := by
    dsimp only [c]
    group
  let k : ℕ := orderOf x
  have hpow : wG ^ k * c ^ k = 1 := by
    calc wG ^ k * c ^ k = (wG * c) ^ k := (hcw.mul_pow k).symm
      _ = x ^ k := by rw [← hxeq]
      _ = 1 := by simp [k]
  have hwGk : wG ^ k = (c ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hz_comm : ∀ y : ↥L, ((w ^ a) ^ k) * y = y * ((w ^ a) ^ k) := by
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hcoe : (((w ^ a) ^ k : ↥L) : G) = wG ^ k := by
      simp [wG]
    rw [hcoe, hwGk]
    have hcy : Commute c (y : G) := (commute_iff_eq c (y : G)).mpr (hc y)
    exact ((hcy.pow_left k).inv_left).eq
  have hz_one : ((w ^ a) ^ k : ↥L) = 1 := eq_one_of_commute φ hz_comm
  have hwpow : w ^ (a * k) = 1 := by
    rw [pow_mul]
    exact hz_one
  have h3dvd : 3 ∣ a * k := by
    rw [← hwo]
    exact orderOf_dvd_of_pow_eq_one hwpow
  have h3a : 3 ∣ a := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right h3dvd
  rw [← orderOf_dvd_iff_pow_eq_one]
  rw [hwo]
  exact h3a

private lemma exists_pow_conj_eq_of_normalizer {G : Type} [Group G] {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) {L : Subgroup G} (φ : ↥L ≃* SL(n + 1, ZMod 2)) {w : ↥L}
    (hw : φ w = tOne n) {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hxw : x * (w : G) = w * x)
    (hxJ : ∀ B : SL(n - 1, ZMod 2),
      x * (φ.symm (jBlock n B) : G) = φ.symm (jBlock n B) * x) :
    ∃ a : ℕ, ∀ y : ↥L, x * (y : G) * x⁻¹ =
      ((w ^ a : ↥L) : G) * (y : G) * (((w ^ a : ↥L) : G))⁻¹ := by
  let ψ : ↥L ≃* ↥L := L.normalizerMonoidHom ⟨x, hxN⟩
  have hψapply : ∀ y : ↥L, ((ψ y : ↥L) : G) = x * (y : G) * x⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hxN⟩ y
  let β : MulAut SL(n + 1, ZMod 2) := φ.symm.trans (ψ.trans φ)
  have hβ : ∀ A, β A = φ (ψ (φ.symm A)) := by
    intro A
    simp [β, MulEquiv.trans_apply]
  have h1 : β (tOne n) = tOne n := by
    have hφw : φ.symm (tOne n) = w := by
      rw [← hw, MulEquiv.symm_apply_apply]
    have hψw : ψ w = w := by
      apply Subtype.ext
      rw [hψapply w, hxw, mul_assoc, mul_inv_cancel, mul_one]
    rw [hβ, hφw, hψw, hw]
  have h2 : ∀ B : SL(n - 1, ZMod 2), β (jBlock n B) = jBlock n B := by
    intro B
    have hψJ : ψ (φ.symm (jBlock n B)) = φ.symm (jBlock n B) := by
      apply Subtype.ext
      rw [hψapply (φ.symm (jBlock n B)), hxJ B, mul_assoc, mul_inv_cancel, mul_one]
    rw [hβ, hψJ, MulEquiv.apply_symm_apply]
  obtain ⟨a, ha⟩ := exists_eq_conj_tOne_pow hn β h1 h2
  refine ⟨a, fun y => ?_⟩
  have hψeq : ψ y = w ^ a * y * (w ^ a)⁻¹ := by
    apply φ.injective
    have hβeval : φ (ψ y) = β (φ y) := by
      rw [hβ, MulEquiv.symm_apply_apply]
    rw [hβeval, ha, MulAut.conj_apply, map_mul, map_mul, map_inv, map_pow, hw]
  have h := congrArg (fun t : ↥L => (t : G)) hψeq
  rw [hψapply y] at h
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h

theorem commute_of_commute_centralizer {G : Type} [Group G] {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    {L : Subgroup G} (φ : ↥L ≃* SL(n + 1, ZMod 2)) {w : ↥L} (hw : φ w = tOne n) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : Nat.Coprime (orderOf x) 3)
    (hxw : x * (w : G) = w * x)
    (hxJ : ∀ B : SL(n - 1, ZMod 2), x * (φ.symm (jBlock n B) : G) = φ.symm (jBlock n B) * x) :
    ∀ y ∈ L, x * y = y * x := by
  obtain ⟨a, hxy⟩ := exists_pow_conj_eq_of_normalizer hn φ hw hxN hxw hxJ
  have hwo : orderOf w = 3 := by
    have h : orderOf (φ w) = orderOf w := by
      simpa only [MulEquiv.coe_toMonoidHom] using
        orderOf_injective (MulEquiv.toMonoidHom φ) φ.injective w
    rw [hw, orderOf_tOne] at h
    exact h.symm
  have hwa : w ^ a = 1 := pow_eq_one_of_conj_eq φ hwo hx3 hxy
  intro y hy
  have h : x * y * x⁻¹ = y := by
    have h' := hxy ⟨y, hy⟩
    rw [hwa] at h'
    simpa using h'
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h]

end CFSG.StandardType.FF81
