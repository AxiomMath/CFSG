module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofField
import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofLinFix
import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField fixedField_card_pow)

namespace Item424Res3

theorem two_pow_mod_three_of_odd {k : ℕ} (hk : Odd k) : 2 ^ k % 3 = 2 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem isFieldCent424_of_sl {X : Type} [Group X] {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : Odd m) (hF : Nat.card F = 2 ^ (3 * m)) (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    IsFieldCent424 X := by
  have hm1 : 1 ≤ m := hm.pos
  have h3m : 2 ^ (3 * m) % 3 = 2 := two_pow_mod_three_of_odd ((by decide : Odd 3).mul hm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (3 * m)) = 2 ^ (3 * m) := GaloisField.card 2 (3 * m) (by omega)
  let φ : F ≃+* GaloisField 2 (3 * m) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 (3 * m) (by omega) hF
  obtain ⟨ψ⟩ := KFacts.nonempty_sl3_mulEquiv_projSL (F := GaloisField 2 (3 * m))
    (by rw [hK]; exact h3m)
  exact Or.inr ⟨m, hm1, Or.inr ⟨h3m, ⟨(e.trans
    (CFSG.ClassicalModels.specialLinearFieldEquiv φ (Fin 3))).trans ψ⟩⟩⟩

theorem orderOf_eq_three_of_conj {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    {d : MulAut (projectiveSL n F)} {σ : F ≃+* F} (hφ1 : fieldAut n F σ ≠ 1)
    (h3 : (d * fieldAut n F σ * d⁻¹) ^ 3 = 1) : orderOf σ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [conj_pow, conj_eq_one_iff, ← map_pow] at h3
  have hσ3 : σ ^ 3 = 1 :=
    (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 (σ ^ 3) (by rw [map_one, one_mul, h3])).1
  refine orderOf_eq_prime hσ3 fun h => hφ1 ?_
  rw [h, map_one]

end Item424Res3

open Item424Res3

theorem k424FieldCentLinear : K424FieldCentLinear := by
  intro G _ _ L K c n F _ _ hn hind hc3 hK hT
  rcases hind with ⟨e, hcN, hk⟩ | ⟨e, hcN, hk⟩
  ·
    obtain ⟨φ, hφ, hφ1, d, -, hα⟩ := hk
    obtain ⟨σ, rfl⟩ := hφ
    have hHas := (Item424Res2.hasType424_fixSub_of_mem hcN hc3 hK hT).of_mulEquiv
      (Sec11.KS11Lie2Proof.fixSubCongr e (Item426.thetaAut L hcN))
    have hα' : MulAut.congr e (Item426.thetaAut L hcN) = d * fieldAut n F σ * d⁻¹ := hα
    rw [hα'] at hHas
    obtain ⟨hn3, m, hm, hmo⟩ := hasType424_fieldAut_imp hn σ (hasType424_fixSub_of_conj hHas)
    subst hn3
    have hσ3 : orderOf σ = 3 := orderOf_eq_three_of_conj hn hφ1 (by
      rw [← hα]
      exact KFacts.inducedAutHom_pow_eq_one L e hcN hc3)
    have hFcard : Nat.card F = 2 ^ (3 * m) := by
      rw [← fixedField_card_pow σ, hσ3, hm, ← pow_mul, mul_comm]
    have hF3 : Nat.card F % 3 = 2 := by
      rw [hFcard]
      exact two_pow_mod_three_of_odd ((by decide : Odd 3).mul hmo)
    exact isFieldCent424_of_sl hmo hFcard (e.trans (MulEquiv.ofBijective (proj 3 F)
      ⟨KFacts.proj_three_injective hF3, proj_surjective 3 F⟩).symm)
  ·
    obtain ⟨φ, hφ, hφ1, d, hd, hα⟩ := hk
    obtain ⟨σ, rfl⟩ := hφ
    obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hd
    set β := KFacts.inducedAutHom L e ⟨c, hcN⟩ with hβ
    set γ := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F H
      with hγ
    set ψ := CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin n) F σ
      with hψ
    have hβeq : β = γ * ψ * γ⁻¹ := by
      apply CFSG.RankThree.PartOne.AUTSL.descendAut_injective hn
      rw [hα, map_mul, map_mul, map_inv]
      rfl
    have hHas := (Item424Res2.hasType424_fixSub_of_mem hcN hc3 hK hT).of_mulEquiv
      (Sec11.KS11Lie2Proof.fixSubCongr e (Item426.thetaAut L hcN))
    have hβ' : MulAut.congr e (Item426.thetaAut L hcN) = γ * ψ * γ⁻¹ := hβeq
    rw [hβ'] at hHas
    obtain ⟨hn3, m, hm, hmo⟩ := hasType424_slFieldAut_imp hn σ (hasType424_fixSub_of_conj hHas)
    subst hn3
    have hσ3 : orderOf σ = 3 := orderOf_eq_three_of_conj hn hφ1 (by
      rw [← hα, ← map_pow, KFacts.inducedAutHom_pow_eq_one L e hcN hc3, map_one])
    have hFcard : Nat.card F = 2 ^ (3 * m) := by
      rw [← fixedField_card_pow σ, hσ3, hm, ← pow_mul, mul_comm]
    exact isFieldCent424_of_sl hmo hFcard e

end CFSG.RankThree.PartTwo.Sec4
