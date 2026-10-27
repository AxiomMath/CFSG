module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open Matrix Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.KFU (D8Mod)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD coe_torusD longSL shortSL
  perfectResidual_long perfectResidual_short nonempty_longSL_mulEquiv
  nonempty_shortSL_mulEquiv_galois)
open CFSG.RankThree.PartTwo.Sec21 (projSLTwoEquivSL sl2OrderThree orderOf_sl2OrderThree
  isPerfect_of_mulEquiv_projSL isSimpleGroup_projSL_two)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

private theorem nonempty_bar2_self_of_simple_not_two {G : Type} [Group G] (L : Subgroup G)
    (hsimple : IsSimpleGroup ↥L) (h2 : ¬ IsPGroup 2 ↥L) : Nonempty (Bar2 L ≃* ↥L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
    (@CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_simple ↥L _ hsimple h2)).trans
      QuotientGroup.quotientBot⟩

theorem nonempty_bar2_derInf8_line_one (hb : 0 < b) (hbe : Even b)
    (hF : Nat.card F = (2 ^ b) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    Nonempty (Bar2 (F08.DerInf8 (SU (unitaryInvolution F 2 b) 4 ⊓
      centralizer (zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F)))) ≃*
      SpecialLinearGroup (Fin 2) (GaloisField 2 b)) := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have hinv1 : (1 : F) ≠ a⁻¹ := fun h => ha1 (by rw [← inv_inv a, ← h, inv_one])
  have ht₁ : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, 1, 1, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  obtain ⟨eL⟩ := nonempty_longSL_mulEquiv (F := F) hb hF
  have hperfL : ⁅longSL σ, longSL σ⁆ = longSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hb2 eL)
  have hS₁ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      longSL σ := perfectResidual_long σ ht₁ ha1 hainv hinv1 hperfL
  let e : ↥(longSL σ) ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 b) :=
    eL.trans (projSLTwoEquivSL (GaloisField 2 b))
  have hsimple : IsSimpleGroup ↥(longSL σ) :=
    (MulEquiv.isSimpleGroup_congr eL).mpr (isSimpleGroup_projSL_two hb2)
  have hnot : ¬ IsPGroup 2 ↥(longSL σ) := by
    intro hpg
    obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hpg (e.symm sl2OrderThree)
    have h3 : orderOf (e.symm sl2OrderThree) = 3 := by
      rw [MulEquiv.orderOf_eq, orderOf_sl2OrderThree]
    have hdvd : 3 ∣ 2 ^ n := by
      rw [← h3, orderOf_dvd_iff_pow_eq_one]
      exact hn
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  change Nonempty (Bar2 (inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
    (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F)))) ≃*
    SpecialLinearGroup (Fin 2) (GaloisField 2 b))
  rw [hS₁]
  obtain ⟨eB⟩ := nonempty_bar2_self_of_simple_not_two (longSL σ) hsimple hnot
  exact ⟨eB.trans e⟩

theorem nonempty_bar2_derInf8_line_three (hb : 0 < b) (hbe : Even b)
    (hF : Nat.card F = (2 ^ b) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    Nonempty (Bar2 (F08.DerInf8 (SU (unitaryInvolution F 2 b) 4 ⊓
      centralizer (zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F)))) ≃*
      SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * b))) := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have hinv1 : (1 : F) ≠ a⁻¹ := fun h => ha1 (by rw [← inv_inv a, ← h, inv_one])
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have ht₃ : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois σ hb hF
  have hperfS : ⁅shortSL σ, shortSL σ⁆ = shortSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL (by omega) eS)
  have hS₃ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      shortSL σ := perfectResidual_short σ hσσ ht₃ hainv hperfS
  let e : ↥(shortSL σ) ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * b)) :=
    eS.trans (projSLTwoEquivSL (GaloisField 2 (2 * b)))
  have hsimple : IsSimpleGroup ↥(shortSL σ) :=
    (MulEquiv.isSimpleGroup_congr eS).mpr (isSimpleGroup_projSL_two (by omega))
  have hnot : ¬ IsPGroup 2 ↥(shortSL σ) := by
    intro hpg
    obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hpg (e.symm sl2OrderThree)
    have h3 : orderOf (e.symm sl2OrderThree) = 3 := by
      rw [MulEquiv.orderOf_eq, orderOf_sl2OrderThree]
    have hdvd : 3 ∣ 2 ^ n := by
      rw [← h3, orderOf_dvd_iff_pow_eq_one]
      exact hn
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  change Nonempty (Bar2 (inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
    (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F)))) ≃*
    SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * b)))
  rw [hS₃]
  obtain ⟨eB⟩ := nonempty_bar2_self_of_simple_not_two (shortSL σ) hsimple hnot
  exact ⟨eB.trans e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
