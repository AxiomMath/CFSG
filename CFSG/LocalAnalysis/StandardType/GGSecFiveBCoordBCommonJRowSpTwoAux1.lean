module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import CFSG.LinearAlgebra.SL2CharTwoInvolution

public section

namespace CFSG.StandardType.CommonJSpTwo

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.SpJoin

private lemma zmodPowHom_injective_of_order {G : Type} [Group G] {p : ℕ} [NeZero p] {t : G}
    (ht : t ^ p = 1) (hto : orderOf t = p) :
    Function.Injective (CFSG.StandardType.TableBSymp.zmodPowHom ht) := by
  intro a b hab
  have h : CFSG.StandardType.TableBSymp.zmodPowHom ht (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp
    ((CFSG.StandardType.TableBSymp.zmodPowHom_eq_one_iff ht hto).mp h)

theorem ggCommonJSpTwo_exists_torus {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Injective ζ ∧ (∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) ∧ SpPlaneConj K 3 ζ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hpF : (3 : K) ≠ 0 := natCast_ne_zero_of_two_eq_zero h2 (by norm_num) (by norm_num)
  rcases OrthTorus.three_dvd_card_sub_or_add (K := K) with hsplit | hnon
  · obtain ⟨ω, hωo⟩ : ∃ ω : Kˣ, orderOf ω = 3 := by
      apply exists_prime_orderOf_dvd_card' 3
      rwa [Nat.card_units]
    have hω1 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
    refine ⟨spPlaneZetaSplit (p := 3) ω hω1, ?_,
      fun a => ?_, spPlaneConj_split (p := 3) (by norm_num) hpF hω1 hωo⟩
    · exact CFSG.LinearAlgebra.sl2Diag_injective.comp
        (zmodPowHom_injective_of_order hω1 hωo)
    · have hinv : CFSG.StandardType.TableBSymp.zmodPowHom hω1 a⁻¹ =
          (CFSG.StandardType.TableBSymp.zmodPowHom hω1 a)⁻¹ := map_inv _ _
      show sl2W * sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω1 a) * sl2W⁻¹ =
        sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω1 a⁻¹)
      rw [hinv, mul_inv_eq_iff_eq_mul]
      exact sl2W_mul_sl2Diag _
  · obtain ⟨t, hirr, hgd⟩ :=
      exists_quadratic_cyclotomic_factor (p := 3) (by norm_num) (by norm_num) hpF hnon
    have ht : spCompanion t ^ 3 = 1 := spCompanion_pow_eq_one (p := 3) (by norm_num) hgd
    have htne : spCompanion t ≠ 1 := by
      intro h
      have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
        (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
      simpa [coe_spCompanion] using h00
    have hto : orderOf (spCompanion t) = 3 := orderOf_eq_prime ht htne
    exact ⟨spPlaneZetaCompanion (p := 3) t ht,
      zmodPowHom_injective_of_order ht hto,
      spPlaneZetaCompanion_conj_sl2W (p := 3) (by norm_num) h2 t ht,
      spPlaneConj_companion (p := 3) h2 (by norm_num) (by norm_num) hnon hirr hgd ht⟩

end CFSG.StandardType.CommonJSpTwo

end
