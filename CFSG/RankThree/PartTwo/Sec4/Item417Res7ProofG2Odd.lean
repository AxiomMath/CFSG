module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofExc
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddB
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddA

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open Res417Three Res417Five Res417Six

namespace Res417Seven

theorem pow_two_pow_odd_eq_inv {L : Type} [Field L] {f : ℕ} (hf : Odd f) {ζ : Lˣ}
    (hζ : ζ ^ 3 = 1) : (ζ : L) ^ (2 ^ f) = ((ζ⁻¹ : Lˣ) : L) := by
  have hmod : 2 ^ f % 3 = 2 := (two_pow_mod_three f).2 hf
  have h1 : ζ ^ (2 ^ f) = ζ ^ 2 := by
    rw [← Nat.div_add_mod (2 ^ f) 3, hmod, pow_add, pow_mul, hζ, one_pow, one_mul]
  have h2 : ζ ^ 2 = ζ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hζ]
  rw [← Units.val_pow_eq_pow_val, h1, h2]

section Main


theorem k417G2OddCentSU3_holds : K417G2OddCentSU3 := by
  intro X _ f hf hX e he3
  obtain ⟨-, K, _, _, hK, ⟨eX⟩⟩ := hX
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hf
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φX : X ≃* adjointGroup .G2 K := eX.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot) with hφX
  obtain ⟨L, _, _, _, σ₀, hdeg, hσ₀⟩ := exists_quadratic_ext' K
  have hL : Nat.card L = (2 ^ f) ^ 2 := by rw [natCard_quadratic hdeg, hK]
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set σ := CFSG.LieType.BorelTits.unitaryInvolution L 2 f with hσdef
  have hσapp : ∀ c, σ c = c ^ (2 ^ f) := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_apply L 2 f c
  have hσK : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L := by
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hσapp]
    have := Fintype.ofFinite K
    rw [← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set β : X →* adjointGroup .G2 L := (bcG2 K L).comp φX.toMonoidHom with hβdef
  have hβ : Function.Injective β := bcG2_injective.comp φX.injective
  have hβσ : ∀ x, baseChangeGL (σ : L →+* L) (β x : ModGL .G2 L) = β x := fun x =>
    baseChangeGL_bcG2 _ hσK _
  have hbe3 : β e ^ 3 = 1 := by rw [← map_pow, ← he3, pow_orderOf_eq_one, map_one]
  have hbe1 : β e ≠ 1 := by
    intro h
    have : e = 1 := hβ (h.trans (map_one β).symm)
    rw [this, orderOf_one] at he3
    exact absurd he3 (by norm_num)
  have h31 : 3 ∣ Nat.card L - 1 := by
    rw [hL, ← pow_mul]
    have h := (two_pow_mod_three (f * 2)).1 ⟨f, by ring⟩
    generalize 2 ^ (f * 2) = m at h ⊢
    omega
  obtain ⟨g, b, hgb⟩ := exists_conj_torus_of_cube h31 (β e) hbe3
  have hb3 : b ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := .G2) (K := L)
    change rootDiagUnitHom .G2 L (b ^ 3) = rootDiagUnitHom .G2 L 1
    rw [map_pow, map_one]
    change rootDiagUnit .G2 b ^ 3 = 1
    rw [← hgb, ← Subgroup.coe_pow, conj_pow, hbe3, mul_one, mul_inv_cancel, Subgroup.coe_one]
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hbe1
    have h1 : g * β e * g⁻¹ = 1 := Subtype.ext (by
      rw [hgb, Subgroup.coe_one]
      exact rootDiagUnit_one)
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  have hge : (β e : ModGL .G2 L) = (g⁻¹ : ModGL .G2 L) * rootDiagUnit .G2 b * g := by
    rw [← hgb]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨ι, hι, hιSU⟩ : ∃ ι : Subgroup.centralizer ({e} : Set X) →* GL (Fin 3) L,
      Function.Injective ι ∧ ∀ x, ι x ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) L := by
    by_cases hb0 : b g2ia = 1
    ·
      set ζ := b g2ir with hζdef
      have hbζ : b = Pi.mulSingle g2ir ζ := by
        funext j
        rcases fin_G2_cases j with rfl | rfl
        · rw [hb0, Pi.mulSingle_eq_of_ne (by decide)]
        · rw [Pi.mulSingle_eq_same]
      have hζ3 : ζ ^ 3 = 1 := by simpa using congrFun hb3 g2ir
      have hζ1 : ζ ≠ 1 := by
        intro h
        apply hb1
        rw [hbζ, h, Pi.mulSingle_one]
      have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
      refine exists_su3_of_threeA hL β hβ hβσ (y := (g⁻¹ : ModGL .G2 L)) (inv_mem g.2) hζo
        (pow_two_pow_odd_eq_inv hf hζ3) ?_
      rw [hge, ← hbζ]
      simp only [inv_inv]
    ·
      obtain ⟨w, ζ, hζo, hw⟩ := exists_weyl_threeB hb3 hb0
      have hζ3 : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
      have h1 := (rootDiagUnit_eq_conj_canonicalRep_iff b (Pi.mulSingle g2ia ζ) w).mpr hw
      refine exists_su3_of_threeB hL β hβ hβσ
        (y := (g⁻¹ : ModGL .G2 L) * canonicalRep (coxeterSystem .G2) L w)
        (mul_mem (inv_mem g.2) (canonicalRep_mem_adjointGroup _ L w)) hζo
        (pow_two_pow_odd_eq_inv hf hζ3) ?_
      rw [hge, h1]
      group
  refine ⟨L, inferInstance, ι, hι, ⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr hf0, ?_⟩, hιSU⟩
  rw [hL]
  rfl

end Main

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
