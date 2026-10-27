module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137SUFourNonsing
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137SUFourIso
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

open scoped MatrixGroups

theorem k_Table13_7_SU4_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
      2 ≤ n → IsSUn ↥H 4 n → p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
        ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
          ∀ (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
            (ψ : W ≃* Multiplicative (Fin 4 → F)),
            NatCoordsSU4 H n F ε ψ → ∀ v : W, v ≠ 1 →
              ((∑ i, (Multiplicative.toAdd (ψ v)) i ^ (2 ^ n + 1)) ≠ 0 →
                  IsSU3 (Bar2 (Opp p (centVec H v))) n) ∧
                ((∑ i, (Multiplicative.toAdd (ψ v)) i ^ (2 ^ n + 1)) = 0 →
                  IsL2 (Bar2 (Opp p (centVec H v))) n) := by
  classical
  intro W _ _ H p n hn _ hp hcong F _ _ hF ε ψ hψ v hv
  set w : Fin 4 → F := Multiplicative.toAdd (ψ v) with hwdef
  have hiff : ∀ l : ↥H, (l : MulAut W) v = v ↔
      ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w := by
    intro l
    rw [← ψ.injective.eq_iff, hψ l v]
    constructor
    · intro h
      exact congrArg Multiplicative.toAdd h
    · intro h
      rw [h]
      rfl
  have hpq : p ∣ 2 ^ n + 1 := CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨e⟩ := exists_vecStab_SU4_nonsing_equiv hn hF hw
    obtain ⟨x, hx, hxp⟩ := exists_noncentral_statedSU_three hn hF hp hpq
    have hSU3 := isSU3_statedSU_three hn hF
    obtain ⟨e'⟩ := nonempty_bar2_opp_centVec_equiv ε v w hiff e.toMonoidHom e.surjective
      (IsPGroup.ker_isPGroup_of_injective e.injective) hSU3.1 (pCore_two_statedSU_three hn hF)
      hp hx hxp
    exact uc22p20p_isSU3_of_mulEquiv e'.symm hSU3
  · have hw0 : w ≠ 0 := by
      intro h0
      apply hv
      apply ψ.injective
      rw [map_one]
      exact congrArg Multiplicative.ofAdd h0
    obtain ⟨K₀, _, _, hK₀, σ, hσ, hker⟩ := exists_vecStab_SU4_iso_hom hF hw0 hw
    have hK₀' : Nat.card K₀ = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK₀]
    have : CharP K₀ 2 :=
      CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK₀'
    have h4 : 4 ≤ Nat.card K₀ := by
      rw [hK₀']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨hS, hS2, x, hx, hxp⟩ := sl2_inputs h4 hp (by rw [hK₀']; exact hpq)
    obtain ⟨e⟩ := nonempty_bar2_opp_centVec_equiv ε v w hiff σ hσ hker hS hS2 hp hx hxp
    exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two hn hK₀ e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
