module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4MRad
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Map
public import CFSG.Quasithin.Vol2.F134LieSp4Borel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aRankTwo
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord2
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch4Sec3L436
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.Quasithin.H13.Ch4.Sp4M

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat.Sp4
  CFSG.Quasithin.Lie2Parabolic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (unitri isUnitriangular_unitri inv_unitri)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.Open (pCoreOf)
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def rad1 (C : Matrix (Fin 2) (Fin 2) F) : StatedSp 2 F :=
  xC (C 0 0) * xAB (C 0 1) * xB (C 1 1)

theorem spMat_rad1M {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    spMat (rad1 C) = fromBlocks 1 C 0 1 := by
  rw [rad1, spMat_rad1]
  congr 1
  have h10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    rwa [transpose_apply] at this
  ext i k
  fin_cases i <;> fin_cases k <;> simp [h10]

theorem rad1_eq (c₀ c₁ c₂ : F) : rad1 !![c₀, c₁; c₁, c₂] = xC c₀ * xAB c₁ * xB c₂ := rfl

theorem rad1_mul' (C D : Matrix (Fin 2) (Fin 2) F) : rad1 C * rad1 D = rad1 (C + D) := by
  rw [rad1, rad1, rad1, rad1_mul]
  rfl

theorem rad1_zero : rad1 (0 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [rad1]
  simp [xC_zero, xAB_zero, xB_zero]

theorem rad1_inv (C : Matrix (Fin 2) (Fin 2) F) : (rad1 C)⁻¹ = rad1 (-C) := by
  rw [inv_eq_iff_mul_eq_one, rad1_mul', add_neg_cancel, rad1_zero]

theorem conj_rad1 {ℓ : StatedSp 2 F} (hℓ : ℓ ∈ Q2 F 1) {C : Matrix (Fin 2) (Fin 2) F}
    (hC : Cᵀ = C) :
    ℓ * rad1 C * ℓ⁻¹ = rad1 ((spMat ℓ).toBlocks₁₁ * C * (spMat ℓ).toBlocks₁₁ᵀ) := by
  have h21 : (spMat ℓ).toBlocks₂₁ = 0 := by
    ext i k
    exact spMat_inr_inl_of_mem_Q2_one hℓ i k
  obtain ⟨hA, C', -, hM⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
  generalize hAdef : (spMat ℓ).toBlocks₁₁ = A at hM hA ⊢
  have hsym : (A * C * Aᵀ)ᵀ = A * C * Aᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]
  rw [mul_inv_eq_iff_eq_mul]
  apply statedSp_ext
  change spMat ℓ * spMat (rad1 C) = spMat (rad1 (A * C * Aᵀ)) * spMat ℓ
  have hb1 : ∀ D : Matrix (Fin 2) (Fin 2) F, fromBlocks 1 D 0 1 = blockMat 1 D := fun D => by
    simp [blockMat]
  rw [spMat_rad1M hC, spMat_rad1M hsym, show spMat ℓ = blockMat A C' from hM, hb1, hb1,
    blockMat_mul (by simp), blockMat_mul hA]
  have hAt : IsUnit Aᵀ.det := by rwa [det_transpose]
  have e : A⁻¹ * (A * C * Aᵀ) * A⁻¹ᵀ = C := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul A hA, Matrix.one_mul,
      Matrix.mul_assoc, transpose_nonsing_inv, mul_nonsing_inv _ hAt, Matrix.mul_one]
  rw [e]
  simp [add_comm]

theorem mul_sym_mul_transpose_apply [CharP F 2] (A C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C) :
    (A * C * Aᵀ) 0 0 = A 0 0 ^ 2 * C 0 0 + A 0 1 ^ 2 * C 1 1 ∧
      (A * C * Aᵀ) 1 1 = A 1 0 ^ 2 * C 0 0 + A 1 1 ^ 2 * C 1 1 ∧
      (A * C * Aᵀ) 0 1 = A 0 0 * A 1 0 * C 0 0 + A.det * C 0 1 + A 0 1 * A 1 1 * C 1 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hC10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    rwa [transpose_apply] at this
  rw [det_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, hC10]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (A 0 0 * A 0 1 * C 0 1) * h2
  · linear_combination (A 1 0 * A 1 1 * C 0 1) * h2
  · linear_combination (A 0 1 * A 1 0 * C 0 1) * h2

theorem transpose_mul_mul_transpose {A C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    (A * C * Aᵀ)ᵀ = A * C * Aᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]

theorem rad1_eq_rad1_iff {X Y : Matrix (Fin 2) (Fin 2) F} :
    rad1 X = rad1 Y ↔ X 0 0 = Y 0 0 ∧ X 0 1 = Y 0 1 ∧ X 1 1 = Y 1 1 := by
  constructor
  · exact rad1_inj
  · rintro ⟨h0, h1, h2⟩
    rw [rad1, rad1, h0, h1, h2]

theorem toBlocks₁₁_eq_blkIdx (g : StatedSp 2 F) :
    (spMat g).toBlocks₁₁ = blkIdx (sigma2 1) (spMat g) := by
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

theorem L1_le_Q2 : perfectCore (Q2 F 1) ≤ Q2 F 1 := perfectCore_le _

variable [Finite F] [CharP F 2] {n : ℕ}

omit [CharP F 2] in
theorem det_toBlocks₁₁_of_mem_L1 {ℓ : StatedSp 2 F} (hℓ : ℓ ∈ perfectCore (Q2 F 1)) :
    (spMat ℓ).toBlocks₁₁.det = 1 := by
  have h := (blkN 1 ⟨ℓ, hℓ⟩).2
  rw [blkN_coe, ← toBlocks₁₁_eq_blkIdx] at h
  exact h

theorem exists_rad1_of_mem_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {g : StatedSp 2 F}
    (hg : g ∈ pCoreOf 2 (perfectCore (Q2 F 1))) :
    ∃ C : Matrix (Fin 2) (Fin 2) F, Cᵀ = C ∧ g = rad1 C := by
  obtain ⟨c₀, c₁, c₂, rfl⟩ := (mem_R1_iff hn hF).mp hg
  refine ⟨!![c₀, c₁; c₁, c₂], ?_, rfl⟩
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

theorem rad1_mem_R1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (C : Matrix (Fin 2) (Fin 2) F) :
    rad1 C ∈ pCoreOf 2 (perfectCore (Q2 F 1)) :=
  mem_R1 hn hF _ _ _

omit [CharP F 2] in
theorem spLevi_dg2_mem_L1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (s : Fˣ) :
    spLevi 1 (NQCat.dg2 s) ∈ perfectCore (Q2 F 1) :=
  spLevi_mem_perfectCore (NQCat.exists_finset_card_four_of_card hn hF) 1 _

omit [Finite F] [CharP F 2] in
theorem toBlocks₁₁_spLevi_one (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (spMat (spLevi 1 A)).toBlocks₁₁ = (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [spMat_leviSp_one]
  simp

omit [Finite F] in
theorem sq_ne_one_of_ne_one {s : F} (hs : s ≠ 1) : s ^ 2 ≠ 1 := fun h =>
  hs (CharTwo.sq_injective (h.trans (one_pow 2).symm))

omit [Finite F] [CharP F 2] in
theorem eq_zero_of_mul_eq {w c : F} (hw : w ≠ 1) (h : w * c = c) : c = 0 := by
  by_contra hc
  exact hw (mul_right_cancel₀ hc (h.trans (one_mul c).symm))

theorem sp4C_eq (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    L436.sp4C (Q2 F 1) (pCoreOf 2 (perfectCore (Q2 F 1))) = XAB F := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  apply le_antisymm
  · intro g hg
    obtain ⟨hgR, hgC⟩ := hg
    obtain ⟨C, hC, rfl⟩ := exists_rad1_of_mem_R1 hn hF hgR
    obtain ⟨s, hs1⟩ := NQCat.exists_unit_ne_one hK4
    have hcomm := Subgroup.mem_centralizer_iff.mp hgC _ (spLevi_dg2_mem_L1 hn hF s)
    have hconj : spLevi 1 (NQCat.dg2 s) * rad1 C * (spLevi 1 (NQCat.dg2 s))⁻¹ = rad1 C := by
      rw [hcomm, mul_inv_cancel_right]
    rw [conj_rad1 (L1_le_Q2 (spLevi_dg2_mem_L1 hn hF s)) hC, toBlocks₁₁_spLevi_one,
      rad1_eq_rad1_iff] at hconj
    obtain ⟨h00, -, h11⟩ := hconj
    obtain ⟨e00, e11, -⟩ := mul_sym_mul_transpose_apply
      ((NQCat.dg2 s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) C hC
    rw [e00] at h00
    rw [e11] at h11
    simp only [NQCat.dg2] at h00 h11
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_add]
      at h00 h11
    have hc00 : C 0 0 = 0 :=
      eq_zero_of_mul_eq (sq_ne_one_of_ne_one hs1) h00
    have hc11 : C 1 1 = 0 :=
      eq_zero_of_mul_eq (sq_ne_one_of_ne_one (NQCat.units_inv_ne_one hs1)) h11
    rw [rad1, hc00, hc11, xC_zero, xB_zero, one_mul, mul_one]
    exact xAB_mem_XAB _
  · rintro _ ⟨b, rfl⟩
    refine ⟨xAB_mem_R1 hn hF b, Subgroup.mem_centralizer_iff.mpr fun ℓ hℓ => ?_⟩
    have hdet := det_toBlocks₁₁_of_mem_L1 hℓ
    have hb : xAB b = rad1 !![0, b; b, 0] := by rw [rad1_eq, xC_zero, xB_zero, one_mul, mul_one]
    have hsym : (!![0, b; b, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, b; b, 0] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    rw [← mul_inv_eq_iff_eq_mul, hb, conj_rad1 (L1_le_Q2 hℓ) hsym, rad1_eq_rad1_iff]
    obtain ⟨e00, e11, e01⟩ := mul_sym_mul_transpose_apply (spMat ℓ).toBlocks₁₁ _ hsym
    rw [e00, e11, e01, hdet]
    simp

omit [Finite F] [CharP F 2] in
theorem xA_one_eq : xA (1 : F) = spLevi 1 (up2 1) := (spLevi_one_up2 1).symm

theorem R1_inf_centralizer_U (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 1)) ⊓ Subgroup.centralizer (unipotent 2 F : Set (StatedSp 2 F)) =
      XC F ⊔ XAB F := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgR, hgC⟩ := hg
    obtain ⟨C, hC, rfl⟩ := exists_rad1_of_mem_R1 hn hF hgR
    have hcomm := Subgroup.mem_centralizer_iff.mp hgC (xA 1) (xA_mem 1)
    have hconj : xA 1 * rad1 C * (xA 1)⁻¹ = rad1 C := by rw [hcomm, mul_inv_cancel_right]
    rw [xA_one_eq, conj_rad1 (spLevi_mem 1 _) hC, toBlocks₁₁_spLevi_one, rad1_eq_rad1_iff]
      at hconj
    obtain ⟨-, h01, -⟩ := hconj
    rw [(mul_sym_mul_transpose_apply _ C hC).2.2] at h01
    simp [up2, det_fin_two] at h01
    rw [← R1_inf_R0 hn hF]
    refine ⟨rad1_mem_R1 hn hF C, ?_⟩
    rw [rad1, h01, xB_zero, mul_one]
    exact mul_mem (xC_mem_R0 hn hF _) (xAB_mem_R0 hn hF _)
  · intro g hg
    rw [← R1_inf_R0 hn hF] at hg
    refine ⟨hg.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hU : unipotent 2 F ≤ Subgroup.centralizer {g} := by
      rw [unipotent_eq_sup hn hF]
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (R1_comm hn hF hh hg.1)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (R0_comm hn hF hh hg.2)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hU hu)

omit [Finite F] [CharP F 2] in
theorem spLevi_dg2_mem_borel (s : Fˣ) : spLevi 1 (NQCat.dg2 s) ∈ borelSubgroup 2 F := by
  refine CFSG.Quasithin.F134.Sp4.mem_borelSubgroup_iff.mpr ⟨?_, spLevi_mem 1 _⟩
  rw [CFSG.Quasithin.F134.Sp4.mem_stabilizer_one_iff]
  change spMat (spLevi 1 (NQCat.dg2 s)) (Sum.inr 0) (Sum.inl 0) = 0 ∧
    spMat (spLevi 1 (NQCat.dg2 s)) (Sum.inr 1) (Sum.inl 0) = 0 ∧
    spMat (spLevi 1 (NQCat.dg2 s)) (Sum.inl 1) (Sum.inl 0) = 0
  rw [spMat_spLevi_dg2]
  simp

theorem sp4Z_eq (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    L436.sp4Z (Q2 F 1) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 1))) = XC F := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  rw [L436.sp4Z, R1_inf_centralizer_U hn hF]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg ℓ hℓ
    obtain ⟨a, b, rfl⟩ := mem_XC_sup_XAB hn hF hg
    obtain ⟨hℓL, hℓN⟩ := hℓ
    have hB : ℓ ∈ borelSubgroup 2 F := by rwa [← normalizer_unipotent]
    have htri := (toBlocks_of_mem_borelSubgroup hB).2
    have hdet := det_toBlocks₁₁_of_mem_L1 hℓL
    have h10 : (spMat ℓ).toBlocks₁₁ 1 0 = 0 := htri (show (0 : Fin 2) < 1 by decide)
    have hsym : (!![-a, -b; -b, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![-a, -b; -b, 0] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    have hg : xC a * xAB b = rad1 !![a, b; b, 0] := by rw [rad1_eq, xB_zero, mul_one]
    have hginv : (rad1 !![a, b; b, 0])⁻¹ = rad1 !![-a, -b; -b, 0] := by
      rw [rad1_inv]
      congr 1
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    rw [commutatorElement_def, hg, mul_assoc, mul_assoc, ← mul_assoc ℓ, hginv,
      conj_rad1 (L1_le_Q2 hℓL) hsym, rad1_mul']
    obtain ⟨e00, e11, e01⟩ := mul_sym_mul_transpose_apply (spMat ℓ).toBlocks₁₁ _ hsym
    refine ⟨a - (spMat ℓ).toBlocks₁₁ 0 0 ^ 2 * a, ?_⟩
    have hx : ∀ t : F, xC t = rad1 !![t, 0; 0, 0] := fun t => by
      rw [rad1_eq, xAB_zero, xB_zero, mul_one, mul_one]
    rw [hx, rad1_eq_rad1_iff]
    simp only [Matrix.add_apply, e00, e11, e01, hdet, h10]
    simp
    ring
  · rintro _ ⟨t, rfl⟩
    obtain ⟨s, hs1⟩ := NQCat.exists_unit_ne_one hK4
    have hd : spLevi 1 (NQCat.dg2 s) ∈
        perfectCore (Q2 F 1) ⊓ Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) := by
      refine ⟨spLevi_dg2_mem_L1 hn hF s, ?_⟩
      rw [normalizer_unipotent]
      exact spLevi_dg2_mem_borel s
    exact root_mem_commutator_of xC xC_mul (spLevi 1 (NQCat.dg2 s)) ((s : F) ^ 2)
      (sq_ne_one_of_ne_one hs1) (conj_one_xC s) hd
      (fun t => Subgroup.mem_sup_left (xC_mem_XC t)) t

omit [Finite F] in
@[expose] noncomputable def frobSL : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(StatedSL 2 F) :=
  (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (frobenius F 2))

omit [Finite F] in
theorem coe_frobSL (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((frobSL A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F).map (· ^ 2) := by
  ext i k
  simp [frobSL, specialLinearGroupEquivStatedSL_coe, frobenius_def]

omit [Finite F] in
theorem frobSL_injective : Function.Injective (frobSL (F := F)) := by
  intro A B h
  have h' := congrArg (fun g : ↥(StatedSL 2 F) => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
  simp only [coe_frobSL] at h'
  apply Subtype.ext
  ext i k
  exact CharTwo.sq_injective (congrFun₂ h' i k)

theorem frobSL_surjective : Function.Surjective (frobSL (F := F)) := by
  intro g
  obtain ⟨B, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective g
  refine ⟨Matrix.SpecialLinearGroup.map ((frobeniusEquiv F 2).symm : F →+* F) B, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_frobSL, specialLinearGroupEquivStatedSL_coe]
  ext i k
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply]
  rw [← frobenius_def, RingEquiv.coe_toRingHom, frobenius_apply_frobeniusEquiv_symm]

@[expose] noncomputable def beta1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ↥(pCoreOf 2 (perfectCore (Q2 F 1))) →* Multiplicative (Fin 2 → F) where
  toFun v := Multiplicative.ofAdd
    ![spMat v.1 (Sum.inl 0) (Sum.inr 0), spMat v.1 (Sum.inl 1) (Sum.inr 1)]
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    ext i
    fin_cases i <;> simp [spMat_one]
  map_mul' v w := by
    obtain ⟨C, hC, hv⟩ := exists_rad1_of_mem_R1 hn hF v.2
    obtain ⟨D, hD, hw⟩ := exists_rad1_of_mem_R1 hn hF w.2
    have hvw : (v * w : ↥(pCoreOf 2 (perfectCore (Q2 F 1)))).1 = rad1 (C + D) := by
      rw [Subgroup.coe_mul, hv, hw, rad1_mul']
    have hCD : (C + D)ᵀ = C + D := by rw [transpose_add, hC, hD]
    rw [← ofAdd_add]
    congr 1
    rw [hvw, hv, hw, spMat_rad1M hC, spMat_rad1M hD, spMat_rad1M hCD]
    ext i
    fin_cases i <;> simp

theorem toAdd_beta1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (v : ↥(pCoreOf 2 (perfectCore (Q2 F 1)))) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    (hv : (v : StatedSp 2 F) = rad1 C) :
    Multiplicative.toAdd (beta1 hn hF v) = ![C 0 0, C 1 1] := by
  change ![spMat v.1 (Sum.inl 0) (Sum.inr 0), spMat v.1 (Sum.inl 1) (Sum.inr 1)] = _
  rw [hv, spMat_rad1M hC]
  simp

omit [Finite F] [CharP F 2] in
theorem mem_unipotent_of_mem_Q1 {ℓ : StatedSp 2 F} (hℓ : ℓ ∈ Q2 F 1)
    (hA : IsUnitriangular (spMat ℓ).toBlocks₁₁) : ℓ ∈ unipotent 2 F := by
  have h21 : (spMat ℓ).toBlocks₂₁ = 0 := by
    ext i k
    exact spMat_inr_inl_of_mem_Q2_one hℓ i k
  obtain ⟨-, C, hC, hM⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
  exact ⟨_, C, hA, hC, hM⟩

omit [Finite F] [CharP F 2] in
theorem toBlocks₁₁_of_mem_unipotent {ℓ : StatedSp 2 F} (hℓ : ℓ ∈ unipotent 2 F) :
    (spMat ℓ).toBlocks₁₁ = !![1, (spMat ℓ).toBlocks₁₁ 0 1; 0, 1] := by
  obtain ⟨A, C, hA, -, hM⟩ := hℓ
  have hA' : (spMat ℓ).toBlocks₁₁ = A := by
    rw [show spMat ℓ = blockMat A C from hM, blockMat]
    simp
  rw [hA']
  ext i k
  fin_cases i <;> fin_cases k
  · exact hA.2 0
  · rfl
  · exact hA.1 (show (0 : Fin 2) < 1 by decide)
  · exact hA.2 1

theorem sp4Coord_one (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    L436.Sp4Coord n (Q2 F 1) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 1))) := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  have : Fintype F := Fintype.ofFinite F
  have hrad : ∀ v : ↥(pCoreOf 2 (perfectCore (Q2 F 1))),
      ∃ C : Matrix (Fin 2) (Fin 2) F, Cᵀ = C ∧ (v : StatedSp 2 F) = rad1 C :=
    fun v => exists_rad1_of_mem_R1 hn hF v.2
  refine ⟨F, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card]; exact hF,
    frobSL.comp (blkN 1), beta1 hn hF, frobSL_surjective.comp (blkN_surjective hK4 1),
    fun ℓ => ?_, fun w => ?_, fun v => ?_, fun a u v hv => ?_, fun ℓ => ?_, fun v => ?_⟩
  · rw [MonoidHom.comp_apply, ← map_one (frobSL (F := F)), frobSL_injective.eq_iff,
      mem_pCoreOf_perfectCore_Q2 hn hF 1 ℓ.2, ← blkN_coe]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  · refine ⟨⟨xC (Multiplicative.toAdd w 0) * xAB 0 * xB (Multiplicative.toAdd w 1),
      mem_R1 hn hF _ _ _⟩, ?_⟩
    have hsym : (!![Multiplicative.toAdd w 0, 0; 0, Multiplicative.toAdd w 1] :
        Matrix (Fin 2) (Fin 2) F)ᵀ =
          !![Multiplicative.toAdd w 0, 0; 0, Multiplicative.toAdd w 1] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    apply Multiplicative.toAdd.injective
    rw [toAdd_beta1 hn hF _ hsym rfl]
    ext i
    fin_cases i <;> rfl
  · obtain ⟨C, hC, hv⟩ := hrad v
    rw [sp4C_eq hn hF, ← toAdd_eq_zero, toAdd_beta1 hn hF v hC hv, hv]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [cons_val_zero, cons_val_one, Pi.zero_apply] at h0 h1
      rw [rad1, h0, h1, xC_zero, xB_zero, one_mul, mul_one]
      exact xAB_mem_XAB _
    · rintro ⟨b, hb⟩
      have hb' : rad1 !![0, b; b, 0] = rad1 C := by
        rw [rad1_eq, xC_zero, xB_zero, one_mul, mul_one, hb]
      obtain ⟨h0, -, h1⟩ := rad1_inj hb'
      ext i
      fin_cases i
      · simp [← h0]
      · simp [← h1]
  · obtain ⟨C, hC, hu⟩ := hrad u
    have hvC : (v : StatedSp 2 F) = rad1 ((spMat (a : StatedSp 2 F)).toBlocks₁₁ * C *
        (spMat (a : StatedSp 2 F)).toBlocks₁₁ᵀ) := by
      rw [hv, Subgroup.coe_inv, hu, conj_rad1 (L1_le_Q2 a.2) hC]
    rw [toAdd_beta1 hn hF v (transpose_mul_mul_transpose hC) hvC, toAdd_beta1 hn hF u hC hu,
      MonoidHom.comp_apply, coe_frobSL, blkN_coe, ← toBlocks₁₁_eq_blkIdx]
    obtain ⟨e00, e11, -⟩ := mul_sym_mul_transpose_apply (spMat (a : StatedSp 2 F)).toBlocks₁₁ C hC
    rw [e00, e11]
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  · rw [MonoidHom.comp_apply]
    constructor
    · intro hℓ
      have hA := toBlocks₁₁_of_mem_unipotent hℓ
      refine ⟨(spMat (ℓ : StatedSp 2 F)).toBlocks₁₁ 0 1 ^ 2, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rw [coe_frobSL, blkN_coe, ← toBlocks₁₁_eq_blkIdx, hA]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [L436.uT]
    · rintro ⟨t, ht⟩
      have h' := congrArg (fun g : ↥(StatedSL 2 F) => ((g : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) ht
      simp only [coe_frobSL, blkN_coe, ← toBlocks₁₁_eq_blkIdx] at h'
      have h00 := congrFun₂ h' 0 0
      have h10 := congrFun₂ h' 1 0
      have h11 := congrFun₂ h' 1 1
      simp [L436.uT] at h00 h10 h11
      refine mem_unipotent_of_mem_Q1 (L1_le_Q2 ℓ.2) ⟨fun i k hik => ?_, fun i => ?_⟩
      · fin_cases i <;> fin_cases k <;> simp at hik
        exact h10
      · fin_cases i
        · exact h00.elim id fun h => h.trans (CharTwo.neg_eq 1)
        · exact h11.elim id fun h => h.trans (CharTwo.neg_eq 1)
  · obtain ⟨C, hC, hv⟩ := hrad v
    rw [sp4C_eq hn hF, sp4Z_eq hn hF, sup_comm, toAdd_beta1 hn hF v hC hv, hv]
    simp only [cons_val_one, cons_val_zero]
    constructor
    · intro h
      obtain ⟨a, b, hab⟩ := mem_XC_sup_XAB hn hF h
      have hab' : rad1 C = rad1 !![a, b; b, 0] := by rw [hab, rad1_eq, xB_zero, mul_one]
      exact (rad1_inj hab').2.2
    · intro h
      rw [rad1, h, xB_zero, mul_one]
      exact mul_mem (Subgroup.mem_sup_left (xC_mem_XC _)) (Subgroup.mem_sup_right (xAB_mem_XAB _))

end CFSG.Quasithin.H13.Ch4.Sp4M
