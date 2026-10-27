module

public import CFSG.RankThree.PartTwo.Sec8.Hering88DCommon
public import CFSG.RankThree.PartTwo.Sec8.Hering88CL2
public import CFSG.RankThree.PartTwo.Sec8.Hering88COdd
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofSU3KFact

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88D

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSU)
open Matrix


theorem kF88StepDCaseThreeOdd_of
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hC : KF88SwapCent) (hF : KF84Field)
    (hAut : Sec4.K419AutThree) (hT : Hering88C.KF89JCentType419)
    (h47 : Sec4.Inputs47ClassesD4) : KF88StepDCaseThreeOdd := by
  rintro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hY3, -, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY3' := hY3
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hY3
  have hm1 : 1 ≤ m := hodd.pos
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY
  have hOTC : KFacts.OutThreeCyclic (Y ⧸ aschbacherSolvableCore 3 Y) :=
    KFacts.outThreeCyclic_of_statedSU hQ (by omega : 1 ≤ 3 * m) hK e₁
  obtain ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne, E, hEA, hdE, hInv⟩ :=
    exists_inner_d_two_local h45 h84 hC hF hAut hT h hY hIJ hx hxY hOTC
  obtain ⟨w, hw⟩ : ∃ w : StatedSU 3 (2 ^ (3 * m)) K,
      KFacts.inducedAutHom Y e₁ ⟨d, hdN⟩ = MulAut.conj w := by
    obtain ⟨w, hw⟩ := (KFacts.isInnerAut_congr e₁ _).mpr hin
    exact ⟨w, hw.symm⟩
  have hne' : KFacts.inducedAutHom Y e₁ ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hne
    have h2 : MulAut.congr e₁ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) = 1 := h1
    exact (MulAut.congr e₁).injective (h2.trans (map_one _).symm)
  have hg3c : w ^ 3 ∈ Subgroup.center (StatedSU 3 (2 ^ (3 * m)) K) := by
    apply Item83Proof.mem_center_of_conj_eq_one
    rw [map_pow, ← hw]
    exact KFacts.inducedAutHom_pow_eq_one Y e₁ hdN hd3
  have hgc : w ∉ Subgroup.center (StatedSU 3 (2 ^ (3 * m)) K) := by
    intro hgc
    apply hne'
    rw [hw]
    ext z
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hgc z).symm,
      mul_inv_cancel_right]
  have hws : ∀ c : K, ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c' hc'
    apply hgc
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    apply Units.ext
    change ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hc', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hmod : Sec4.ModThree false (2 ^ (3 * m)) := by
    have := KFacts.three_dvd_two_pow_three_mul_add_one hodd
    change 2 ^ (3 * m) % 3 = 2
    omega
  have hPi : Sec4.PiField false 2 (3 * m) K := ⟨Nat.prime_two, by omega, hK⟩
  have hw3 : w ^ 3 ≠ 1 := fun hw3 =>
    KFacts.not_invTwoBarNontrivial_of_inducedAutHom_eq_conj hPi hmod e₁ hdE hdN w hw3 hws hw hInv
  obtain ⟨ι⟩ := Item83Proof.kF83SUThree K m hodd hK w hg3c hw3
  have hd3' : ∃ j : ℕ, d ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hd3⟩
  obtain ⟨κ⟩ := KFacts.nonempty_imageModTheta_perfectResidual_mulEquiv hdN hd3' e₁
    (Subgroup.centralizer {w}) (fun z => by
      rw [hw, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hz
        rw [← hz, mul_inv_cancel_right]
      · intro hz
        calc z * w = w * z * w⁻¹ * w := by rw [hz]
          _ = w * z := by group)
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hxA : x ∈ A := by
    rcases hx with rfl | rfl
    · exact h.mem_A
    · exact (Item87Proof.isGammaIndex_cases h.isGammaIndex).1
  exact ⟨d, hdcl, hdx, Hering88C.good88_of_l2 h47 hodd hxY (hA3 x hxA) (hAc d hdA x hxA)
    (Or.inr (Or.inl hY3')) (κ.trans ι)⟩

end Hering88D

end CFSG.RankThree.PartTwo.Sec8
