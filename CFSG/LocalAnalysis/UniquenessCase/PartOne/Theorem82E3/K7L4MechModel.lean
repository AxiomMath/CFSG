module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Realize
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.GroupTheory.WeirSylow.UniqueE27GLFour
public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Blocks
public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddBlock
import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Blk
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.RankThree.PartOne.KF.SUSylow
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Cent
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Wt
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
import CFSG.ClassicalInvolution.Asc77.AscSCH03

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open CFSG.Open.StatedAPI Subgroup Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
open CFSG.RankThree.PartTwo.Sec4.Item419Res3
open CFSG.RankThree.PartTwo.Sec21.U4OddLines
open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K]

theorem isElemAbelian_D₀ (ζ : CubeRoot K) : IsElemAbelian 3 (D₀ ζ) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => D₀_pow_three ζ hx⟩
  obtain ⟨v, hv⟩ : ∃ v, stdDiagHom ζ v = (a : GL (Fin 4) K) := by
    simpa [D₀] using a.2
  obtain ⟨w, hw⟩ : ∃ w, stdDiagHom ζ w = (b : GL (Fin 4) K) := by
    simpa [D₀] using b.2
  apply Subtype.ext
  change (a : GL (Fin 4) K) * b = (b : GL (Fin 4) K) * a
  rw [← hv, ← hw, ← map_mul, ← map_mul, mul_comm]

theorem diagUnit_comm_blkGL2L (X : GL (Fin 2) K) (u : Fin 4 → Kˣ) (h23 : u 2 = u 3) :
    diagUnit u * blkGL2L X = blkGL2L X * diagUnit u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL2L]
  let v : Fin 4 → K := fun i => (u i : K)
  change Matrix.diagonal v * blk2L (X : Matrix (Fin 2) (Fin 2) K) =
    blk2L (X : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal v
  have hv23 : v 2 = v 3 := congrArg (fun x : Kˣ => (x : K)) h23
  have hu : v = ![v 0, v 1, v 2, v 3] := by funext i; fin_cases i <;> rfl
  have hv : (![v 0, v 1, v 2, v 3] : Fin 4 → K) = ![v 0, v 1, v 2, v 2] := by
    funext i; fin_cases i <;> simp [hv23]
  rw [hu, hv]
  exact CFSG.RankThree.PartTwo.Sec8.Hering418.blk2L_comm_diagonal
    (X : Matrix (Fin 2) (Fin 2) K) _ _ _

theorem diagUnit_comm_blkGL2 (X : GL (Fin 2) K) (u : Fin 4 → Kˣ) (h01 : u 0 = u 1) :
    diagUnit u * blkGL2 X = blkGL2 X * diagUnit u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL2]
  let v : Fin 4 → K := fun i => (u i : K)
  change Matrix.diagonal v * blk2 (X : Matrix (Fin 2) (Fin 2) K) =
    blk2 (X : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal v
  have hv01 : v 0 = v 1 := congrArg (fun x : Kˣ => (x : K)) h01
  have hu : v = ![v 0, v 1, v 2, v 3] := by funext i; fin_cases i <;> rfl
  have hv : (![v 0, v 1, v 2, v 3] : Fin 4 → K) = ![v 0, v 0, v 2, v 3] := by
    funext i; fin_cases i <;> simp [hv01]
  rw [hu, hv]
  exact CFSG.RankThree.PartTwo.Sec8.Hering418.blk2_comm_diagonal
    (X : Matrix (Fin 2) (Fin 2) K) _ _ _

theorem blkGL2L_mem_centralizer_stdDiagHomH {H : Subgroup (GL (Fin 4) K)} {ζ : CubeRoot K}
    (hD : D₀ ζ ≤ H) (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3)
    {X : GL (Fin 2) K} (hXH : blkGL2L X ∈ H) :
    (⟨blkGL2L X, hXH⟩ : H) ∈ Subgroup.centralizer (stdDiagHomH ζ hD '' S) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨v, hv, rfl⟩
  apply Subtype.ext
  change (stdDiagHomH ζ hD v : GL (Fin 4) K) * blkGL2L X =
    blkGL2L X * (stdDiagHomH ζ hD v : GL (Fin 4) K)
  exact diagUnit_comm_blkGL2L X _ (by simp only [CubeRoot.pow, hS v hv])

theorem blkGL2_mem_centralizer_stdDiagHomH {H : Subgroup (GL (Fin 4) K)} {ζ : CubeRoot K}
    (hD : D₀ ζ ≤ H) (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1)
    {X : GL (Fin 2) K} (hXH : blkGL2 X ∈ H) :
    (⟨blkGL2 X, hXH⟩ : H) ∈ Subgroup.centralizer (stdDiagHomH ζ hD '' S) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨v, hv, rfl⟩
  apply Subtype.ext
  change (stdDiagHomH ζ hD v : GL (Fin 4) K) * blkGL2 X =
    blkGL2 X * (stdDiagHomH ζ hD v : GL (Fin 4) K)
  exact diagUnit_comm_blkGL2 X _ (by simp only [CubeRoot.pow, hS v hv])

private theorem exists_diagUnit_of_mem_centralizer_D₀ {H : Subgroup (GL (Fin 4) K)}
    {ζ : CubeRoot K} (hD : D₀ ζ ≤ H) {g : H}
    (hg : g ∈ Subgroup.centralizer (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) :
    ∃ u : Fin 4 → Kˣ, diagUnit u = (g : GL (Fin 4) K) :=
  mem_D₀_of_diag_exists_diagUnit (centralizer_D₀_comm_diag ζ hD hg)

private theorem pow_eq_one_of_diagUnit {g : GL (Fin 4) K} {u : Fin 4 → Kˣ} {n : ℕ}
    (hu : diagUnit u = g) (hn : u ^ n = 1) : g ^ n = 1 := by
  rw [← hu, ← mem_D₀_of_diag_diagUnit_pow, hn, diagUnit_one]

theorem not_dvd_card_centralizer_D0_sl {q p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = q) (hpq : p ∣ q + 1) (ζ : CubeRoot K) (hD : D₀ ζ ≤ StatedSL 4 K) :
    ¬ p ∣ Nat.card (Subgroup.centralizer
      (((D₀ ζ).subgroupOf (StatedSL 4 K) : Subgroup (StatedSL 4 K)) :
        Set (StatedSL 4 K))) := by
  intro hdvd
  have hq : 1 ≤ q := by rw [← hK]; exact Nat.succ_le_of_lt (Nat.card_pos (α := K))
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup (StatedSL 4 K) := Subgroup.centralizer
    (((D₀ ζ).subgroupOf (StatedSL 4 K) : Subgroup (StatedSL 4 K)) : Set (StatedSL 4 K))
  have hdvd' : p ∣ Nat.card C := hdvd
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hdvd'
  set g : StatedSL 4 K := (x : StatedSL 4 K) with hg
  have hgc : g ∈ C := by rw [hg]; exact x.2
  obtain ⟨u, hu⟩ := exists_diagUnit_of_mem_centralizer_D₀ hD hgc
  letI : Fintype K := Fintype.ofFinite K
  have huq : u ^ (q - 1) = 1 := by
    funext i
    apply Units.ext
    rw [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one]
    have h := FiniteField.pow_card_sub_one_eq_one (u i : K) (u i).ne_zero
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hgn : (g : GL (Fin 4) K) ^ (q - 1) = 1 := pow_eq_one_of_diagUnit hu huq
  have hxCpow : x ^ (q - 1) = 1 := by
    apply Subtype.ext
    simpa [hg] using Subtype.ext hgn
  have hdvdq : p ∣ q - 1 := by
    rw [← hxord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hxCpow
  exact (CFSG.RankThree.PartOne.KFU.not_dvd_add_one_of_dvd_sub_one
    hp (by omega) hq hdvdq) hpq

private theorem pow_eq_one_of_diagUnit_mem_statedSU {f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    {u : Fin 4 → Kˣ} (hu : diagUnit u ∈ StatedSU 4 (2 ^ f) K) :
    u ^ (2 ^ f + 1) = 1 := by
  have hF : Nat.card K = (2 ^ f) ^ 2 := by
    rw [hU.card, Nat.mul_comm 2 f, ← pow_mul]
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP K 2 := hU.charP
  have hSU : (diagUnit u : GL (Fin 4) K) ∈
      CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 f) 4 := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF]
    exact hu
  obtain ⟨-, hgram⟩ := CFSG.LieType.Universal.Unitary.mem_SUid.mp hSU
  have hmat : ((diagUnit u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => (u i : K)) := rfl
  have hconj : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 f)
      (Matrix.diagonal (fun i => (u i : K))) =
      Matrix.diagonal (fun i => (u i : K) ^ 2 ^ f) := by
    rw [CFSG.LieType.Universal.Unitary.conjTr,
      Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    rfl
  rw [hmat, hconj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hgram
  funext i
  apply Units.ext
  rw [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one, pow_succ]
  exact congrFun (Matrix.diagonal_injective hgram) i

theorem not_dvd_card_centralizer_D0_su {f p : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 (2 ^ f) K) :
    ¬ p ∣ Nat.card (Subgroup.centralizer
      (((D₀ ζ).subgroupOf (StatedSU 4 (2 ^ f) K) : Subgroup (StatedSU 4 (2 ^ f) K)) :
        Set (StatedSU 4 (2 ^ f) K))) := by
  intro hdvd
  have hq : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup (StatedSU 4 (2 ^ f) K) := Subgroup.centralizer
    (((D₀ ζ).subgroupOf (StatedSU 4 (2 ^ f) K) : Subgroup (StatedSU 4 (2 ^ f) K)) :
      Set (StatedSU 4 (2 ^ f) K))
  have hdvd' : p ∣ Nat.card C := hdvd
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hdvd'
  set g : StatedSU 4 (2 ^ f) K := (x : StatedSU 4 (2 ^ f) K) with hg
  have hgc : g ∈ C := by rw [hg]; exact x.2
  obtain ⟨u, hu⟩ := exists_diagUnit_of_mem_centralizer_D₀ hD hgc
  have huSU : diagUnit u ∈ StatedSU 4 (2 ^ f) K := by rw [hu]; exact g.2
  have hupow : u ^ (2 ^ f + 1) = 1 := pow_eq_one_of_diagUnit_mem_statedSU hU huSU
  have hgn : (g : GL (Fin 4) K) ^ (2 ^ f + 1) = 1 := pow_eq_one_of_diagUnit hu hupow
  have hxCpow : x ^ (2 ^ f + 1) = 1 := by
    apply Subtype.ext
    simpa [hg] using Subtype.ext hgn
  have hdvdq : p ∣ 2 ^ f + 1 := by
    rw [← hxord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hxCpow
  exact CFSG.RankThree.PartOne.KFU.not_dvd_add_one_of_dvd_sub_one
    hp (by omega) hq hpq hdvdq

theorem one_le_pRank_centralizer_stdDiagHomH_sl23 {q p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = q) (hpq : p ∣ q + 1) (ζ : CubeRoot K) (hD : D₀ ζ ≤ StatedSL 4 K)
    (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3) :
    1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
  have hq1 : 1 ≤ q := by rw [← hK]; exact Nat.succ_le_of_lt (Nat.card_pos (α := K))
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  have hpdvd : p ∣ Nat.card ((StatedSL 2 K).map (blkGL2L (K := K))) := by
    rw [Subgroup.card_map_of_injective (blkGL2L_injective (K := K)),
      CFSG.Open.StatedAPI.card_statedSL_two, hK, hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpq (q - 1)) q
  have hBleSL : (StatedSL 2 K).map (blkGL2L (K := K)) ≤ StatedSL 4 K := by
    rintro b ⟨X, hX, rfl⟩
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, coe_blkGL2L, det_blk2L]
    exact CFSG.Open.StatedAPI.det_of_mem_statedSL hX
  have hBleC : ((StatedSL 2 K).map (blkGL2L (K := K))).subgroupOf (StatedSL 4 K) ≤
      Subgroup.centralizer (stdDiagHomH ζ hD '' S) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    obtain ⟨X, hX, hXb⟩ := Subgroup.mem_map.mp hb
    have hmem : blkGL2L X ∈ StatedSL 4 K := hBleSL (Subgroup.mem_map_of_mem _ hX)
    have hb_eq : b = ⟨blkGL2L X, hmem⟩ := Subtype.ext hXb.symm
    rw [hb_eq]
    exact blkGL2L_mem_centralizer_stdDiagHomH hD S hS hmem
  have hpdvdB' : p ∣ Nat.card
      (((StatedSL 2 K).map (blkGL2L (K := K))).subgroupOf (StatedSL 4 K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleSL).toEquiv]
    exact hpdvd
  have hpdvdC : p ∣ Nat.card (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) :=
    hpdvdB'.trans (Subgroup.card_dvd_of_le hBleC)
  have h1 : 1 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (↥(Subgroup.centralizer (stdDiagHomH ζ hD '' S)))) :=
    CFSG.one_le_pRank_of_dvd_card hp hpdvdC
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h1

theorem one_le_pRank_centralizer_stdDiagHomH_sl01 {q p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = q) (hpq : p ∣ q + 1) (ζ : CubeRoot K) (hD : D₀ ζ ≤ StatedSL 4 K)
    (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1) :
    1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
  have hq1 : 1 ≤ q := by rw [← hK]; exact Nat.succ_le_of_lt (Nat.card_pos (α := K))
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  have hpdvd : p ∣ Nat.card ((StatedSL 2 K).map (blkGL2 (K := K))) := by
    rw [Subgroup.card_map_of_injective (blkGL2_injective (K := K)),
      CFSG.Open.StatedAPI.card_statedSL_two, hK, hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpq (q - 1)) q
  have hBleSL : (StatedSL 2 K).map (blkGL2 (K := K)) ≤ StatedSL 4 K := by
    rintro b ⟨X, hX, rfl⟩
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, coe_blkGL2, det_blk2]
    exact CFSG.Open.StatedAPI.det_of_mem_statedSL hX
  have hBleC : ((StatedSL 2 K).map (blkGL2 (K := K))).subgroupOf (StatedSL 4 K) ≤
      Subgroup.centralizer (stdDiagHomH ζ hD '' S) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    obtain ⟨X, hX, hXb⟩ := Subgroup.mem_map.mp hb
    have hmem : blkGL2 X ∈ StatedSL 4 K := hBleSL (Subgroup.mem_map_of_mem _ hX)
    have hb_eq : b = ⟨blkGL2 X, hmem⟩ := Subtype.ext hXb.symm
    rw [hb_eq]
    exact blkGL2_mem_centralizer_stdDiagHomH hD S hS hmem
  have hpdvdB' : p ∣ Nat.card
      (((StatedSL 2 K).map (blkGL2 (K := K))).subgroupOf (StatedSL 4 K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleSL).toEquiv]
    exact hpdvd
  have hpdvdC : p ∣ Nat.card (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) :=
    hpdvdB'.trans (Subgroup.card_dvd_of_le hBleC)
  have h1 : 1 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (↥(Subgroup.centralizer (stdDiagHomH ζ hD '' S)))) :=
    CFSG.one_le_pRank_of_dvd_card hp hpdvdC
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h1

theorem one_le_pRank_centralizer_stdDiagHomH_su23 {f p : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 (2 ^ f) K)
    (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3) :
    1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
  have hF : Nat.card K = (2 ^ f) ^ 2 := by
    rw [hU.card, Nat.mul_comm 2 f, ← pow_mul]
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP K 2 := hU.charP
  have hsq : (2 ^ f) ^ 2 - 1 = ((2 ^ f) + 1) * ((2 ^ f) - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ f) 1
  have hpdvd : p ∣ Nat.card (blkSU2L f K) := by
    rw [show blkSU2L f K = (unitarySU 2 f K 2).map (blkGL2L (K := K)) from rfl,
      Subgroup.card_map_of_injective (blkGL2L_injective (K := K)),
      show unitarySU 2 f K 2 = StatedSU 2 (2 ^ f) K from rfl,
      CFSG.RankThree.SubgroupLists.card_statedSU_two (K := K) (r := 2) (f := f) hF, hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpq ((2 ^ f) + 1)) (2 ^ f)
  have hBleSU : blkSU2L f K ≤ StatedSU 4 (2 ^ f) K := by
    intro b hb
    exact blkSU2L_le hU hb
  have hBleC : (blkSU2L f K).subgroupOf (StatedSU 4 (2 ^ f) K) ≤
      Subgroup.centralizer (stdDiagHomH ζ hD '' S) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    obtain ⟨X, hX, hXb⟩ := Subgroup.mem_map.mp hb
    have hmem : blkGL2L X ∈ StatedSU 4 (2 ^ f) K := hBleSU (Subgroup.mem_map_of_mem _ hX)
    have hb_eq : b = ⟨blkGL2L X, hmem⟩ := Subtype.ext hXb.symm
    rw [hb_eq]
    exact blkGL2L_mem_centralizer_stdDiagHomH hD S hS hmem
  have hpdvdB' : p ∣ Nat.card ((blkSU2L f K).subgroupOf (StatedSU 4 (2 ^ f) K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleSU).toEquiv]
    exact hpdvd
  have hpdvdC : p ∣ Nat.card (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) :=
    hpdvdB'.trans (Subgroup.card_dvd_of_le hBleC)
  have h1 : 1 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (↥(Subgroup.centralizer (stdDiagHomH ζ hD '' S)))) :=
    CFSG.one_le_pRank_of_dvd_card hp hpdvdC
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h1

theorem one_le_pRank_centralizer_stdDiagHomH_su01 {f p : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 (2 ^ f) K)
    (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1) :
    1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
  have hF : Nat.card K = (2 ^ f) ^ 2 := by
    rw [hU.card, Nat.mul_comm 2 f, ← pow_mul]
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP K 2 := hU.charP
  have hsq : (2 ^ f) ^ 2 - 1 = ((2 ^ f) + 1) * ((2 ^ f) - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ f) 1
  have hpdvd : p ∣ Nat.card (blkSU2 f K) := by
    rw [show blkSU2 f K = (unitarySU 2 f K 2).map (blkGL2 (K := K)) from rfl,
      Subgroup.card_map_of_injective (blkGL2_injective (K := K)),
      show unitarySU 2 f K 2 = StatedSU 2 (2 ^ f) K from rfl,
      CFSG.RankThree.SubgroupLists.card_statedSU_two (K := K) (r := 2) (f := f) hF, hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpq ((2 ^ f) + 1)) (2 ^ f)
  have hBleSU : blkSU2 f K ≤ StatedSU 4 (2 ^ f) K := by
    intro b hb
    exact blkSU2_le hU hb
  have hBleC : (blkSU2 f K).subgroupOf (StatedSU 4 (2 ^ f) K) ≤
      Subgroup.centralizer (stdDiagHomH ζ hD '' S) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    obtain ⟨X, hX, hXb⟩ := Subgroup.mem_map.mp hb
    have hmem : blkGL2 X ∈ StatedSU 4 (2 ^ f) K := hBleSU (Subgroup.mem_map_of_mem _ hX)
    have hb_eq : b = ⟨blkGL2 X, hmem⟩ := Subtype.ext hXb.symm
    rw [hb_eq]
    exact blkGL2_mem_centralizer_stdDiagHomH hD S hS hmem
  have hpdvdB' : p ∣ Nat.card ((blkSU2 f K).subgroupOf (StatedSU 4 (2 ^ f) K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleSU).toEquiv]
    exact hpdvd
  have hpdvdC : p ∣ Nat.card (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) :=
    hpdvdB'.trans (Subgroup.card_dvd_of_le hBleC)
  have h1 : 1 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (↥(Subgroup.centralizer (stdDiagHomH ζ hD '' S)))) :=
    CFSG.one_le_pRank_of_dvd_card hp hpdvdC
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
