module

public import CFSG.RankThree.PartOne.S15K.LayerData
public import CFSG.RankThree.PartOne.S15K.Row1
public import CFSG.RankThree.PartOne.S15K.PSylowRow1
import CFSG.RankThree.PartOne.S15K.LayerInner
import CFSG.RankThree.PartOne.S15K.BlockFacts
import CFSG.RankThree.PartOne.KC.LinearCommutantSetting
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartOne.S15K.LayerTransport

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary Matrix
open scoped _root_.Classical
open Polynomial

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_scalar_det_one {K : Type} [Field K] [CharP K 2] {u : GL (Fin 4) K}
    (hdet : (u : Matrix (Fin 4) (Fin 4) K).det = 1) (c : Kˣ)
    (hu : u = GeneralLinearGroup.scalar (Fin 4) c) : u = 1 := by
  have h4 : (c : K) ^ 4 = 1 := by
    rw [← det_scalar_gl, ← hu]
    exact hdet
  have hc : c = 1 := Units.ext (CFSG.RankThree.PartOne.S15K.eq_one_of_pow_four_eq_one h4)
  rw [hu, hc, map_one]

theorem layerData_of_lifts {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {E I : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hpK : p ∣ Nat.card K - 1)
    (hEI : E ≤ Subgroup.normalizer (I : Set G)) (φ : ↥I ≃* projectiveSL 4 K)
    (B : ↥E → GL (Fin 4) K) (hBdet : ∀ e, (B e : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hBp : ∀ e, B e ^ p = 1)
    (hBact : ∀ e : ↥E, actP φ ⟨(e : G), hEI e.2⟩ = LinearFlag.conjAut 4 K (B e))
    (hBcomm : ∀ e e' : ↥E, B e * B e' = B e' * B e) : LayerDataP p E I := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp hpK
  let ψ : ↥I →* MulAut (projectiveSL 4 K) :=
    (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).comp φ.toMonoidHom
  have hψ : Function.Injective ψ :=
    (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)).comp φ.injective
  have hψrange : ψ.range = (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ x, rfl⟩
    · rintro ⟨p0, rfl⟩
      exact ⟨φ.symm p0, by simp [ψ]⟩
  have hInnB : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ≤ ψ.range :=
    hψrange.ge
  have hBD : ψ.range ≤ (LinearFlag.conjAut 4 K).range := by
    rw [hψrange, ← KCLinComm.map_toGL_range_eq_conj_range (n := 4) (K := K)]
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  intro b hb hb1
  set bE : ↥E := ⟨b, hb⟩ with hbE
  set a : GL (Fin 4) K := B bE with ha
  have hap : a ^ p = 1 := hBp bE
  have hadet : (a : Matrix (Fin 4) (Fin 4) K).det = 1 := hBdet bE
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff K 2 p).1 h0)).symm
  have hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K))) := by
    refine squarefree_minpoly_of_pow_eq_one hpK ?_
    rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hap, Units.val_one, Matrix.toLin'_one]
    rfl
  have hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ 4 = 1 → c = 1 := fun c _ h4 =>
    Units.ext (eq_one_of_pow_four_eq_one (by simpa using congrArg Units.val h4))
  have hDn : (LinearFlag.conjAut 4 K).range.Normal := conjAut_range_normal (by norm_num)
  have S := projSetting (n := 4) (by norm_num) hK4 hZp hDn ψ.range hInnB a hap hadet hsq
  have hbI : b ∈ Subgroup.normalizer (I : Set G) := hEI hb
  have hcompb : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨b, hbI⟩ x) =
      LinearFlag.conjAut 4 K a * ψ x * (LinearFlag.conjAut 4 K a)⁻¹ := compat_of_actP φ (hBact bE)
  obtain ⟨Q, hQH, hQc, hder, hmem⟩ := layer_of_projSetting ψ hψ hbI hcompb hBD S
  have hFB : ∀ i : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) //
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c},
      (blockImage hsq i.1).map (LinearFlag.conjAut 4 K) ≤ ψ.range := fun i => S.map_le_B i
  have hmultle : ∀ c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)),
      mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c ≤ 4 := fun c => by
    have := primaryMultiplicity_le_finrank hsq c
    simpa using this
  have hmult : ∀ i : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) //
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c},
      ¬ p ∣ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) i.1 := fun i =>
    Nat.not_dvd_of_pos_of_lt (by have := i.2; omega) (by have := hmultle i.1; omega)
  have hρ : ∀ i : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) //
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c},
      ∀ u ∈ blockImage hsq i.1, LinearFlag.conjAut 4 K u = 1 → u = 1 := by
    intro i u hu hu1
    have hdetu : (u : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      have := blockImage_le_range_toGL hsq hK4 i.1 i.2 hu
      rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker] at this
      rw [← Matrix.GeneralLinearGroup.val_det_apply, this, Units.val_one]
    obtain ⟨c', hc'⟩ := (conjAut_eq_one_iff (by norm_num) u).1 hu1
    exact eq_one_of_scalar_det_one hdetu c' hc'.symm
  refine ⟨_, Q, hQH, hQc, hder, fun i => ⟨?_, ?_⟩, fun i => ?_⟩
  · intro e' he'
    set eE : ↥E := ⟨e', he'⟩ with heE
    have hmemr : B eE ∈ (commutantUnitsToGL (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K))).range := by
      rw [range_commutantUnitsToGL_eq_centralizer a rfl]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hBcomm eE bE)
    obtain ⟨X, hX, hy'⟩ := exists_block_decomp hp hsq i.1 (hmult i) hmemr (hBp eE)
    have hcompe : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨e', hEI he'⟩ x) =
        LinearFlag.conjAut 4 K (B eE) * ψ x * (LinearFlag.conjAut 4 K (B eE))⁻¹ :=
      compat_of_actP φ (hBact eE)
    exact exists_mul_mem_centralizer_of_decomp ψ hψ (LinearFlag.conjAut 4 K) (hmem i) (hFB i)
      (hEI he') hcompe (by group) hX hy'
  · exact not_dvd_card_inf_centralizer ψ hψ (LinearFlag.conjAut 4 K) (hmem i) (hFB i) (hρ i) hp
      (block_center_pow hp hsq i.1 i.2 (hmult i))
  · exact psylowIn_of_transport ψ hψ (LinearFlag.conjAut 4 K) (hmem i) (hFB i) (hρ i)
      (psylowSub_blockImage hp hζ hsq i.1 (hmult i))

theorem layerRowOne : LayerRowOne := by
  intro G _ _ p A c L E h15 hF h13 hout
  obtain ⟨f, hf, hpq, ⟨φ₀⟩, -, hEA, -⟩ := hout
  have h := h15.h12
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    have hpos : 0 < 2 ^ f - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    have := Nat.le_of_dvd hpos hpq
    rw [hK]
    omega
  obtain ⟨φ, -⟩ : ∃ φ : ↥(lieGenerated p E) ≃* projectiveSL 4 (GaloisField 2 f), True :=
    ⟨φ₀.trans (projSLEquivProjectiveSL 4 (GaloisField 2 f)), trivial⟩
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  exact (row1_lifts h h13 hEA hf φ).elim fun B hB =>
    layerData_of_lifts hp h5 hK4 hpK (E_le_normalizer_lieGenerated hp) φ B hB.1 hB.2.1 hB.2.2.1
      hB.2.2.2

end CFSG.RankThree.PartOne.S15K
