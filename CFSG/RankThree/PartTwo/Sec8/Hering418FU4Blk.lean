module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
public import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Tr
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.RankThree.PartOne.KFU (diagU diagU_val diagU_mul diagU_apply_same)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blk2_one blk2_mul blk2_injective det_blk2
  blk2_gram blkGL2 coe_blkGL2 blkSU2 blkSU2_le blkSU2Equiv nonempty_blkSU2_mulEquiv mem_blkSU2_of
  dvecD0 phiD0 ker_phiD0 blkSU2_le_centralizer)
open CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof (blk3SU blk3SUEquiv commutator_mem_blk3SU
  blk3SU_le_uS blk3SU_le_centralizer mem_blk3SU_diagonal statedSU_eq_uS mem_blk3SU_of coe_iota3
  iota3)

local notation "blk3'" => CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof.blk3

section Scalars

variable {f : ℕ} {K : Type} [Field K]

theorem exists_primitiveRoot_nine [Finite K] (h9 : 9 ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, IsPrimitiveRoot ζ 9 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hn : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have h9' : 9 ∣ orderOf g := by rw [hg, hn]; exact h9
  obtain ⟨m, hm⟩ := h9'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (orderOf_pos g).ne' hm
  refine ⟨g ^ m, ?_⟩
  have hdiv : m ∣ orderOf g := ⟨9, by rw [hm, mul_comm]⟩
  have h' : orderOf (g ^ m) = 9 := by
    rw [orderOf_pow_of_dvd hm0 hdiv, hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have := IsPrimitiveRoot.orderOf (g ^ m)
  rwa [h'] at this


theorem exists_unitary_cube_root (h : UnitaryFieldData 2 f K) (h9 : 9 ∣ 2 ^ f + 1) {δ : Kˣ}
    (hδ : δ ^ 3 = 1) : ∃ l : Kˣ, l ^ 3 = δ ∧ h.bar (l : K) * (l : K) = 1 := by
  have hfin := h.finite
  have h9' : 9 ∣ Nat.card K - 1 := by
    rw [h.card, show 2 * f = f + f by ring, pow_add]
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : 2 ^ f * 2 ^ f - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      zify [hq, Nat.one_le_pow f 2 (by norm_num), Nat.mul_le_mul hq hq]
      ring
    rw [this]
    exact Dvd.dvd.mul_left h9 _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_nine h9'
  have hζ3 : IsPrimitiveRoot (ζ ^ 3) 3 := by
    have := hζ.pow_of_dvd (by norm_num : 3 ≠ 0) (by norm_num : 3 ∣ 9)
    simpa using this
  obtain ⟨i, -, hi⟩ := hζ3.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 δ).mpr hδ)
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← hi, ← pow_mul, ← pow_mul, mul_comm]
  · rw [UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val, ← pow_succ, ← pow_mul,
      mul_comm, pow_mul]
    have : (ζ : K) ^ (2 ^ f + 1) = 1 := by
      have := (hζ.pow_eq_one_iff_dvd (2 ^ f + 1)).mpr h9
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    rw [this, one_pow]

end Scalars


section Diag

variable {f : ℕ} {K : Type} [Field K]

open CFSG.RankThree.PartOne.KFU (det_diagU)

theorem bar_mul_self_of_pow_three (h : UnitaryFieldData 2 f K) (h3 : 3 ∣ 2 ^ f + 1) {c : Kˣ}
    (hc : c ^ 3 = 1) : h.bar (c : K) * (c : K) = 1 := by
  have hc' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  exact CFSG.RankThree.PartOne.KCUnitaryPlane.bar_eq_inv_of_pow_eq_one h h3 hc'

theorem bar_inv_mul_inv (h : UnitaryFieldData 2 f K) {c : Kˣ} (hc : h.bar (c : K) * (c : K) = 1) :
    h.bar ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) = 1 := by
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hb0 : h.bar (c : K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc
    exact zero_ne_one hc
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hc, inv_one]

theorem bar_mul_mul (h : UnitaryFieldData 2 f K) {c d : Kˣ} (hc : h.bar (c : K) * (c : K) = 1)
    (hd : h.bar (d : K) * (d : K) = 1) : h.bar ((c * d : Kˣ) : K) * ((c * d : Kˣ) : K) = 1 := by
  rw [Units.val_mul, map_mul]
  calc h.bar (c : K) * h.bar (d : K) * ((c : K) * (d : K))
      = (h.bar (c : K) * (c : K)) * (h.bar (d : K) * (d : K)) := by ring
    _ = 1 := by rw [hc, hd, one_mul]

theorem diagU_apply_ne (d : Fin 4 → Kˣ) {i j : Fin 4} (hij : i ≠ j) :
    ((diagU d : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
  rw [diagU_val, Matrix.diagonal_apply_ne _ hij]

theorem diagU_mem_unitarySU (h : UnitaryFieldData 2 f K) {d : Fin 4 → Kˣ}
    (hd : ∀ i, h.bar (d i : K) * (d i : K) = 1) (hp : ∏ i, d i = 1) :
    diagU d ∈ unitarySU 2 f K 4 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [det_diagU]
    have := congrArg (fun u : Kˣ => (u : K)) hp
    simpa using this
  · rw [diagU_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun i => h.bar (d i : K) * (d i : K)) = fun _ => 1 := funext hd
    rw [this, Matrix.diagonal_one]

end Diag




section TypeA

variable {f : ℕ} {K : Type} [Field K]

open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof (uS)

theorem diagU_vec4 (a b c d : Kˣ) :
    ((diagU ![a, b, c, d] : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(a : K), b, c, d] := by
  rw [diagU_val]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem blk3_comm_diagonal (A : Matrix (Fin 3) (Fin 3) K) (l m : K) :
    diagonal ![l, l, l, m] * blk3' A = blk3' A * diagonal ![l, l, l, m] := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof.blk3, mul_comm]

theorem blockData_A (h : UnitaryFieldData 2 f K) (hf2 : 2 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    (h9 : 9 ∣ 2 ^ f + 1) {ω : Kˣ} (hω1 : ω ≠ 1) {u : Fin 4 → Kˣ} (hu3 : ∀ i, u i ^ 3 = 1)
    (hup : ∏ i, u i = 1) :
    BlockData (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}) (diagU u) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : GL (Fin 4) K := diagU ![ω, ω, ω, 1] with hDdef
  have hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![(ω : K), ω, ω, 1] := by
    rw [hDdef, diagU_vec4]
    simp
  have hω1' : (ω : K) ≠ 1 := fun h1 => hω1 (Units.ext h1)
  have hS : unitarySU 2 f K 4 = uS h 4 := statedSU_eq_uS h 4
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {D} with hC
  have hCe : C = uS h 4 ⊓ Subgroup.centralizer {D} := by rw [hC, hS]
  have hNC : blk3SU h ≤ C := by
    rw [hCe]
    exact le_inf (blk3SU_le_uS h) (blk3SU_le_centralizer h hD)
  have hcomm : ⁅C, C⁆ ≤ blk3SU h := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    rw [hCe] at hg hk
    exact commutator_mem_blk3SU h hω1' hD hg hk
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq : IsQuasisimple (unitarySU 2 f K 3) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl (by
      intro hh
      simp only [Prod.mk.injEq, true_and] at hh
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega)).1
  have hU3 : uS h 3 = unitarySU 2 f K 3 := (statedSU_eq_uS h 3).symm
  have hq' : IsQuasisimple (blk3SU h) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((blk3SUEquiv h).trans (MulEquiv.subgroupCongr hU3)).symm hq
  have hδ : (u 0 * u 1 * u 2) ^ 3 = 1 := by
    rw [mul_pow, mul_pow, hu3 0, hu3 1, hu3 2]
    simp
  obtain ⟨l, hl3, hlbar⟩ := exists_unitary_cube_root h h9 hδ
  have hlinv := bar_inv_mul_inv h hlbar
  have hy : ∃ j ∈ blk3SU h, ∃ z ∈ Subgroup.centralizer (blk3SU h : Set (GL (Fin 4) K)),
      diagU u = j * z := by
    refine ⟨diagU ![u 0 * l⁻¹, u 1 * l⁻¹, u 2 * l⁻¹, 1], ?_, diagU ![l, l, l, u 3], ?_, ?_⟩
    · refine mem_blk3SU_of h ?_ ?_ ?_
      · rw [← hS]
        refine diagU_mem_unitarySU h ?_ ?_
        · intro i
          fin_cases i
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 0)) hlinv
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 1)) hlinv
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 2)) hlinv
          · simp
        · rw [Fin.prod_univ_four]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
          calc u 0 * l⁻¹ * (u 1 * l⁻¹) * (u 2 * l⁻¹) * 1 =
                (u 0 * u 1 * u 2) * (l⁻¹ * l⁻¹ * l⁻¹) := by
                simp only [mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm]
            _ = 1 := by rw [← hl3]; group
      · exact ⟨diagU_apply_ne _ (by decide), diagU_apply_ne _ (by decide),
          diagU_apply_ne _ (by decide), diagU_apply_ne _ (by decide),
          diagU_apply_ne _ (by decide), diagU_apply_ne _ (by decide)⟩
      · rw [diagU_apply_same]
        simp
    · intro g hg
      obtain ⟨A, rfl⟩ := hg
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_iota3, diagU_vec4]
      exact (blk3_comm_diagonal _ _ _).symm
    · rw [diagU_mul]
      congr 1
      funext i
      fin_cases i <;> simp
  exact ⟨blk3SU h, blk3SU h, hNC, hNC, by rw [sup_idem]; exact hcomm,
    normal_subgroupOf_of_commutator_le hcomm, normal_subgroupOf_of_commutator_le hcomm, hq', hq',
    hy, hy⟩

end TypeA


section TypeBC

variable {f : ℕ} {K : Type} [Field K]

theorem pair_data {a b : Kˣ} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    ((a * b) ^ 2) ^ 3 = 1 ∧ a * ((a * b) ^ 2)⁻¹ * (b * ((a * b) ^ 2)⁻¹) = 1 := by
  have hc : (a * b) ^ 3 = 1 := by rw [mul_pow, ha, hb, one_mul]
  refine ⟨?_, ?_⟩
  · calc ((a * b) ^ 2) ^ 3 = ((a * b) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hc, one_pow]
  · calc a * ((a * b) ^ 2)⁻¹ * (b * ((a * b) ^ 2)⁻¹) =
          (a * b) * ((a * b) ^ 2)⁻¹ * ((a * b) ^ 2)⁻¹ := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = ((a * b) ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc, inv_one]

theorem blk2_comm_diagonal (X : Matrix (Fin 2) (Fin 2) K) (l a b : K) :
    diagonal ![l, l, a, b] * blk2 X = blk2 X * diagonal ![l, l, a, b] := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [blk2, mul_comm]

theorem blk2L_comm_diagonal (X : Matrix (Fin 2) (Fin 2) K) (a b l : K) :
    diagonal ![a, b, l, l] * blk2L X = blk2L X * diagonal ![a, b, l, l] := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [blk2L, mul_comm]

end TypeBC


section TypeB

variable {f : ℕ} {K : Type} [Field K]

theorem blockData_B (h : UnitaryFieldData 2 f K) (hf2 : 2 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) {ω : Kˣ}
    (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹) {u : Fin 4 → Kˣ} (hu3 : ∀ i, u i ^ 3 = 1)
    (hup : ∏ i, u i = 1) :
    BlockData (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) (diagU u) := by
  have := h.finite
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} with hC
  have hNC : blkSU2 f K ≤ C := blkSU2_le_centralizer h ω
  have hcomm : ⁅C, C⁆ ≤ blkSU2 f K := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have hmem : (⟨g, hg⟩ * ⟨k, hk⟩ * ⟨g, hg⟩⁻¹ * ⟨k, hk⟩⁻¹ : C) ∈ (phiD0 h h1 h2).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm
        (phiD0 h h1 h2 ⟨g, hg⟩) (phiD0 h h1 h2 ⟨k, hk⟩)]
      group
    rw [ker_phiD0 h h1 h2, Subgroup.mem_subgroupOf] at hmem
    rw [commutatorElement_def]
    exact hmem
  have hq : IsQuasisimple (blkSU2 f K) :=
    ((sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hf2).1
  obtain ⟨hl3, hlu⟩ := pair_data (hu3 0) (hu3 1)
  set l := (u 0 * u 1) ^ 2 with hl
  have hlbar := bar_mul_self_of_pow_three h h3 hl3
  have hlinv := bar_inv_mul_inv h hlbar
  have hy : ∃ j ∈ blkSU2 f K, ∃ z ∈ Subgroup.centralizer (blkSU2 f K : Set (GL (Fin 4) K)),
      diagU u = j * z := by
    refine ⟨diagU ![u 0 * l⁻¹, u 1 * l⁻¹, 1, 1], ?_, diagU ![l, l, u 2, u 3], ?_, ?_⟩
    · refine mem_blkSU2_of h ?_ (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide)) ?_ ?_
      · refine diagU_mem_unitarySU h ?_ ?_
        · intro i
          fin_cases i
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 0)) hlinv
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 1)) hlinv
          · simp
          · simp
        · rw [Fin.prod_univ_four]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
          rw [mul_one, mul_one, hlu]
      · rw [diagU_apply_same]
        simp
      · rw [diagU_apply_same]
        simp
    · rintro g ⟨X, -, rfl⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_blkGL2, diagU_vec4]
      exact (blk2_comm_diagonal _ _ _ _).symm
    · rw [diagU_mul]
      congr 1
      funext i
      fin_cases i <;> simp
  exact ⟨blkSU2 f K, blkSU2 f K, hNC, hNC, by rw [sup_idem]; exact hcomm,
    normal_subgroupOf_of_commutator_le hcomm, normal_subgroupOf_of_commutator_le hcomm, hq, hq,
    hy, hy⟩

end TypeB


section TypeC

variable {f : ℕ} {K : Type} [Field K]

theorem blockData_C (h : UnitaryFieldData 2 f K) (hf2 : 2 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) {ω : Kˣ}
    (hω : ω ≠ ω⁻¹) {u : Fin 4 → Kˣ} (hu3 : ∀ i, u i ^ 3 = 1) (hup : ∏ i, u i = 1) :
    BlockData (centC f K ω) (diagU u) := by
  have := h.finite
  have hn₁ : ((blkSU2 f K).subgroupOf (centC f K ω)).Normal := by
    rw [← ker_blockLow h hω]
    exact MonoidHom.normal_ker _
  have hn₂ : ((blkSU2L f K).subgroupOf (centC f K ω)).Normal := by
    rw [← ker_blockUp h hω]
    exact MonoidHom.normal_ker _
  have hq₁ : IsQuasisimple (blkSU2 f K) :=
    ((sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hf2).1
  have hq₂ : IsQuasisimple (blkSU2L f K) :=
    ((sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)).1 hf2).1
  obtain ⟨hl3, hlu⟩ := pair_data (hu3 0) (hu3 1)
  obtain ⟨hm3, hmu⟩ := pair_data (hu3 2) (hu3 3)
  set l := (u 0 * u 1) ^ 2 with hl
  set m := (u 2 * u 3) ^ 2 with hm
  have hlbar := bar_mul_self_of_pow_three h h3 hl3
  have hlinv := bar_inv_mul_inv h hlbar
  have hmbar := bar_mul_self_of_pow_three h h3 hm3
  have hminv := bar_inv_mul_inv h hmbar
  have hy₁ : ∃ j ∈ blkSU2 f K, ∃ z ∈ Subgroup.centralizer (blkSU2 f K : Set (GL (Fin 4) K)),
      diagU u = j * z := by
    refine ⟨diagU ![u 0 * l⁻¹, u 1 * l⁻¹, 1, 1], ?_, diagU ![l, l, u 2, u 3], ?_, ?_⟩
    · refine mem_blkSU2_of h ?_ (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide)) ?_ ?_
      · refine diagU_mem_unitarySU h ?_ ?_
        · intro i
          fin_cases i
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 0)) hlinv
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 1)) hlinv
          · simp
          · simp
        · rw [Fin.prod_univ_four]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
          rw [mul_one, mul_one, hlu]
      · rw [diagU_apply_same]
        simp
      · rw [diagU_apply_same]
        simp
    · rintro g ⟨X, -, rfl⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_blkGL2, diagU_vec4]
      exact (blk2_comm_diagonal _ _ _ _).symm
    · rw [diagU_mul]
      congr 1
      funext i
      fin_cases i <;> simp
  have hy₂ : ∃ j ∈ blkSU2L f K, ∃ z ∈ Subgroup.centralizer (blkSU2L f K : Set (GL (Fin 4) K)),
      diagU u = j * z := by
    refine ⟨diagU ![1, 1, u 2 * m⁻¹, u 3 * m⁻¹], ?_, diagU ![u 0, u 1, m, m], ?_, ?_⟩
    · refine mem_blkSU2L_of h ?_ (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide))
        (diagU_apply_ne _ (by decide)) (diagU_apply_ne _ (by decide)) ?_ ?_
      · refine diagU_mem_unitarySU h ?_ ?_
        · intro i
          fin_cases i
          · simp
          · simp
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 2)) hminv
          · exact bar_mul_mul h (bar_mul_self_of_pow_three h h3 (hu3 3)) hminv
        · rw [Fin.prod_univ_four]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
          rw [one_mul, one_mul, hmu]
      · rw [diagU_apply_same]
        simp
      · rw [diagU_apply_same]
        simp
    · rintro g ⟨X, -, rfl⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_blkGL2L, diagU_vec4]
      exact (blk2L_comm_diagonal _ _ _ _).symm
    · rw [diagU_mul]
      congr 1
      funext i
      fin_cases i <;> simp
  exact ⟨blkSU2 f K, blkSU2L f K, blkSU2_le_centC h ω, blkSU2L_le_centC h ω,
    commutator_centC_le h hω, hn₁, hn₂, hq₁, hq₂, hy₁, hy₂⟩

end TypeC

end CFSG.RankThree.PartTwo.Sec8.Hering418
