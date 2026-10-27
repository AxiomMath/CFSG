module

public import CFSG.RankThree.SubgroupLists.KleinFourCentralizer
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Unipotent

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def unipMat (a c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, c; 0, 1, -σ a; 0, 0, 1]

theorem det_unipMat (a c : K) : (unipMat σ a c).det = 1 := by
  simp [unipMat, Matrix.det_fin_three]

theorem unipMat_mul (a c a' c' : K) :
    unipMat σ a c * unipMat σ a' c' = unipMat σ (a + a') (c + c' - a * σ a') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem unipMat_zero_zero : unipMat σ 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat]

@[expose] noncomputable def unipGL (a c : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' (unipMat σ a c) (by rw [det_unipMat]; exact isUnit_one)

theorem coe_unipGL (a c : K) :
    ((unipGL σ a c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unipMat σ a c :=
  rfl

theorem unipGL_mul (a c a' c' : K) :
    unipGL σ a c * unipGL σ a' c' = unipGL σ (a + a') (c + c' - a * σ a') :=
  Units.ext (by rw [Units.val_mul, coe_unipGL, coe_unipGL, coe_unipGL, unipMat_mul])

theorem unipGL_congr {a c a' c' : K} (ha : a = a') (hc : c = c') :
    unipGL σ a c = unipGL σ a' c' := by
  subst ha hc
  rfl

theorem unipGL_zero_zero : unipGL σ 0 0 = 1 :=
  Units.ext (by rw [coe_unipGL, unipMat_zero_zero, Units.val_one])

theorem antidiag_three :
    (antidiag 3 : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag]

theorem unipGL_mem_SU (hσ : ∀ x, σ (σ x) = x) {a c : K} (h : c + σ c + a * σ a = 0) :
    unipGL σ a c ∈ SU σ 3 := by
  refine ⟨det_unipMat σ a c, ?_⟩
  rw [coe_unipGL, antidiag_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, conjTr, Matrix.mul_apply, Fin.sum_univ_three, hσ]
  linear_combination h

end Unipotent

section FourGroup

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

theorem exists_four_group_witness_psu34 (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ∃ a b x y : StatedProj (StatedSU 3 (2 ^ 2) K), a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a ≠ b ∧ a * b = b * a ∧ x * a = a * x ∧ x * b = b * x ∧ y * a = a * y ∧
      y * b = b * y ∧ x * y ≠ y * x := by
  classical
  set σ := unitaryInvolution K 2 2 with hσdef
  have hσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ω, hω0, hω1, hωσ⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ σ ω = ω := by
    have hcard := CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 2) (f := 2) hK
    by_contra hno
    push Not at hno
    have hsub : (CFSG.LieType.Steinberg.fixedSubfield K 2 2 : Set K) ⊆ ({0, 1} : Finset K) := by
      intro w hw
      have hwσ : σ w = w := hw
      by_cases hw0 : w = 0
      · simp [hw0]
      · by_cases hw1 : w = 1
        · simp [hw1]
        · exact absurd hwσ (hno w hw0 hw1)
    have : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K 2 2) ≤ 2 := by
      calc Nat.card (CFSG.LieType.Steinberg.fixedSubfield K 2 2)
          = Nat.card (CFSG.LieType.Steinberg.fixedSubfield K 2 2 : Set K) := rfl
        _ ≤ Nat.card (({0, 1} : Finset K) : Set K) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; exact Finset.card_le_two
    rw [hcard] at this
    norm_num at this
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq (K := K) (p := 2) (f := 2) hK
    (a := -1) (by rw [map_neg, map_one])
  obtain ⟨β, hβ, hβ1⟩ := exists_norm_eq_one_ne_one (F := K) (p := 2) (f := 2) hK
  have hβσ : σ β ≠ β := by
    intro h
    rw [h] at hβ
    have : (β + 1) * (β + 1) = 0 := by linear_combination hβ + (β + 1) * h2
    have hb := mul_self_eq_zero.mp this
    apply hβ1
    linear_combination hb - h2
  have hz : ∀ b : K, σ b = b → b + σ b + 0 * σ 0 = 0 := by
    intro b hb
    rw [hb, zero_mul, add_zero, ← two_mul, h2, zero_mul]
  have hu1 : c + σ c + 1 * σ 1 = 0 := by
    rw [map_one, one_mul, hc]
    ring
  have huβ : c + σ c + β * σ β = 0 := by
    rw [hc, mul_comm, hβ]
    ring
  set e := equivStatedSU (p := 2) (f := 2) hK 3
  set π := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ 2) K))
  let Z1 : SU σ 3 := ⟨unipGL σ 0 1, unipGL_mem_SU σ hσ (hz 1 (map_one σ))⟩
  let Zω : SU σ 3 := ⟨unipGL σ 0 ω, unipGL_mem_SU σ hσ (hz ω hωσ)⟩
  let X : SU σ 3 := ⟨unipGL σ 1 c, unipGL_mem_SU σ hσ hu1⟩
  let Y : SU σ 3 := ⟨unipGL σ β c, unipGL_mem_SU σ hσ huβ⟩
  set Φ : SU σ 3 →* StatedProj (StatedSU 3 (2 ^ 2) K) := π.comp e.toMonoidHom with hΦ
  have hΦe : ∀ M, π (e M) = Φ M := fun M => rfl
  have hval : ∀ M N : SU σ 3, (M : GL (Fin 3) K) = N → M = N := fun M N h => Subtype.ext h
  have cZ1 : (Z1 : GL (Fin 3) K) = unipGL σ 0 1 := rfl
  have cZω : (Zω : GL (Fin 3) K) = unipGL σ 0 ω := rfl
  have cX : (X : GL (Fin 3) K) = unipGL σ 1 c := rfl
  have cY : (Y : GL (Fin 3) K) = unipGL σ β c := rfl
  have hinv : ∀ (M : SU σ 3) (c : K), (M : GL (Fin 3) K) = unipGL σ 0 c → M * M = 1 := by
    intro M c hM
    apply hval
    rw [Subgroup.coe_mul, hM, unipGL_mul, Subgroup.coe_one, ← unipGL_zero_zero σ]
    exact unipGL_congr σ (by ring)
      (by rw [map_zero, mul_zero, sub_zero]; linear_combination c * h2)
  have hnsc : ∀ (M : SU σ 3) (c : K), (M : GL (Fin 3) K) = unipGL σ 0 c → c ≠ 0 →
      Φ M ≠ 1 := by
    intro M c' hM hc' h
    rw [← hΦe, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨μ, hμ⟩ := h
    have hsq : ((e M : StatedSU 3 (2 ^ 2) K) : GL (Fin 3) K) *
        ((e M : StatedSU 3 (2 ^ 2) K) : GL (Fin 3) K) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, hinv M c' hM, map_one, Subgroup.coe_one]
    rw [← hμ, ← map_mul] at hsq
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hsq
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, Units.val_one,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
    have hμ1 : μ = 1 := by
      have hsq0 : ((μ : K) - 1) * ((μ : K) - 1) = 0 := by
        linear_combination h00 + (1 - (μ : K)) * h2
      exact Units.ext (by rw [Units.val_one]; linear_combination mul_self_eq_zero.mp hsq0)
    rw [hμ1, map_one] at hμ
    have hM1 : M = 1 := e.injective (by rw [map_one]; exact Subtype.ext hμ.symm)
    have h02 := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2)
      hM1
    simp only [hM, coe_unipGL, unipMat, Subgroup.coe_one, Units.val_one] at h02
    simp at h02
    exact hc' h02
  have hcommΦ : ∀ M N : SU σ 3, M * N = N * M → Φ M * Φ N = Φ N * Φ M := by
    intro M N h
    rw [← map_mul, ← map_mul, h]
  have hsqΦ : ∀ M : SU σ 3, M * M = 1 → Φ M ^ 2 = 1 := by
    intro M h
    rw [← map_pow, show M ^ 2 = M * M from sq M, h, map_one]
  refine ⟨Φ Z1, Φ Zω, Φ X, Φ Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsqΦ Z1 (hinv Z1 1 cZ1)
  · exact hsqΦ Zω (hinv Zω ω cZω)
  · exact hnsc Z1 1 cZ1 one_ne_zero
  · exact hnsc Zω ω cZω hω0
  · intro h
    have h' : Φ (Z1 * Zω) = 1 := by
      rw [map_mul, h]
      have hZZ := hsqΦ Zω (hinv Zω ω cZω)
      rw [show Φ Zω ^ 2 = Φ Zω * Φ Zω from sq _] at hZZ
      exact hZZ
    apply hnsc (Z1 * Zω) (1 + ω) ?_ ?_ h'
    · rw [Subgroup.coe_mul, cZ1, cZω, unipGL_mul]
      exact unipGL_congr σ (by ring) (by rw [map_zero, mul_zero, sub_zero])
    · intro h1
      apply hω1
      linear_combination h1 - h2
  · apply hcommΦ
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cZ1, cZω, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by simp only [map_zero, mul_zero, sub_zero]; ring)
  · apply hcommΦ
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cX, cZ1, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by simp only [map_zero, mul_zero, sub_zero, zero_mul]; ring)
  · apply hcommΦ
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cX, cZω, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by simp only [map_zero, mul_zero, sub_zero, zero_mul]; ring)
  · apply hcommΦ
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cY, cZ1, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by simp only [map_zero, mul_zero, sub_zero, zero_mul]; ring)
  · apply hcommΦ
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cY, cZω, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by simp only [map_zero, mul_zero, sub_zero, zero_mul]; ring)
  · intro h
    have hz' : σ (σ β - β) + (σ β - β) + 0 * σ 0 = 0 := by
      rw [map_sub, hσ β, map_zero, mul_zero, add_zero]
      ring
    let W : SU σ 3 := ⟨unipGL σ 0 (σ β - β), unipGL_mem_SU σ hσ (by
      rw [add_comm (σ β - β)]; exact hz')⟩
    have hXY : X * Y = Y * X * W := by
      apply hval
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, cX, cY, unipGL_mul, unipGL_mul,
        unipGL_mul]
      show unipGL σ (1 + β) (c + c - 1 * σ β) = unipGL σ (β + 1 + 0) (c + c - β * σ 1 + (σ β - β) -
        (β + 1) * σ 0)
      exact unipGL_congr σ (by ring)
        (by rw [map_one, map_zero]; linear_combination (β - σ β) * h2)
    have hW : Φ W = 1 := by
      have h1 : Φ (X * Y) = Φ (Y * X) := by rw [map_mul, map_mul, h]
      rw [hXY, map_mul (Φ) (Y * X) W] at h1
      exact mul_left_cancel (a := Φ (Y * X)) (by rw [h1, mul_one])
    exact hnsc W (σ β - β) rfl (sub_ne_zero.mpr hβσ) hW

end FourGroup

theorem false_of_psu34 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSU 3 (2 ^ 2) K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two
    (by rw [hK, ← pow_mul])
  obtain ⟨a, b, x, y, ha2, hb2, ha1, hb1, hab, habc, hxa, hxb, hya, hyb, hxy⟩ :=
    exists_four_group_witness_psu34 hK
  apply hxy
  have := commute_of_centralize_four_group hp2 hdet hZ (a := e.symm a) (b := e.symm b)
    (x := e.symm x) (y := e.symm y) (by rw [← map_pow, ha2, map_one])
    (by rw [← map_pow, hb2, map_one]) (fun h => ha1 (e.symm.injective (by rw [h, map_one])))
    (fun h => hb1 (e.symm.injective (by rw [h, map_one]))) (fun h => hab (e.symm.injective h))
    (by rw [← map_mul, ← map_mul, habc]) (by rw [← map_mul, ← map_mul, hxa])
    (by rw [← map_mul, ← map_mul, hxb]) (by rw [← map_mul, ← map_mul, hya])
    (by rw [← map_mul, ← map_mul, hyb])
  apply e.symm.injective
  rw [map_mul, map_mul, this]

end CFSG.RankThree.SubgroupLists
