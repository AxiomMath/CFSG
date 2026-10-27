module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Roots

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint

theorem ggTBJ_zeta_zpow_eq_iff {K : Type} [Field K] {ζ : Kˣ} {p : ℕ}
    (hζ : orderOf ζ = p) (x y : ℤ) :
    ζ ^ x = ζ ^ y ↔ (p : ℤ) ∣ x - y := by
  rw [← hζ, orderOf_dvd_iff_zpow_eq_one, zpow_sub, ← div_eq_mul_inv]
  exact div_eq_one.symm

theorem ggTBJ_ggTBJa_refl (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (ζ : Kˣ)
    (hζ : orderOf ζ = p) {β : Fin 4 → ℤ}
    (hfunvec : ggTBJFun p β (ggTBJVec p β) = 2)
    (f : Multiplicative (Fin 4 → ZMod p)) :
    (fun i => ggTBJa p ζ f i *
        rootChar (ggTBJa p ζ f) β ^ (-(corootPair (τ := Tag.F4) β (Pi.single i 1))))
      = ggTBJa p ζ (ggTBJReflAut p β f) := by
  funext i
  set S : ℤ := ∑ j : Fin 4, ((Multiplicative.toAdd f j).val : ℤ) * β j with hS
  set ci : ℤ := corootPair (τ := Tag.F4) β (Pi.single i 1) with hci
  have hroot : rootChar (ggTBJa p ζ f) β = ζ ^ S := by
    rw [hS]
    show (∏ j, ggTBJa p ζ f j ^ β j) =
      ζ ^ ∑ j : Fin 4, ((Multiplicative.toAdd f j).val : ℤ) * β j
    calc ∏ j, ggTBJa p ζ f j ^ β j
        = ∏ j, ζ ^ (((Multiplicative.toAdd f j).val : ℤ) * β j) := by
          apply Finset.prod_congr rfl
          intro j _
          rw [ggTBJa, ← zpow_natCast ζ (Multiplicative.toAdd f j).val, ← zpow_mul]
      _ = ζ ^ ∑ j : Fin 4, ((Multiplicative.toAdd f j).val : ℤ) * β j :=
          Finset.prod_zpow_eq_zpow_sum Finset.univ ζ
            (fun j => ((Multiplicative.toAdd f j).val : ℤ) * β j)
  have hfun : ggTBJFun p β (Multiplicative.toAdd f) = (S : ZMod p) := by
    rw [hS, ggTBJFun_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  have hmod : (((Multiplicative.toAdd (ggTBJReflAut p β f) i).val : ℤ) : ZMod p) =
      (((Multiplicative.toAdd f i).val : ℤ) - S * ci : ℤ) := by
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id,
      ggTBJReflAut_apply p hfunvec f i, hfun, hci]
    push_cast
    simp only [ggTBJVec]
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdiv : (p : ℤ) ∣ ((Multiplicative.toAdd (ggTBJReflAut p β f) i).val : ℤ) -
      (((Multiplicative.toAdd f i).val : ℤ) - S * ci) := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((Multiplicative.toAdd (ggTBJReflAut p β f) i).val : ℤ)
      (((Multiplicative.toAdd f i).val : ℤ) - S * ci) p).mp hmod
    simpa only [neg_sub] using dvd_neg.mpr h
  calc ggTBJa p ζ f i * rootChar (ggTBJa p ζ f) β ^ (-ci)
      = ζ ^ ((Multiplicative.toAdd f i).val : ℤ) * (ζ ^ S) ^ (-ci) := by
          rw [hroot, ggTBJa, ← zpow_natCast ζ (Multiplicative.toAdd f i).val]
    _ = ζ ^ ((Multiplicative.toAdd f i).val : ℤ) * ζ ^ (S * (-ci)) := by
          rw [zpow_mul]
    _ = ζ ^ (((Multiplicative.toAdd f i).val : ℤ) + S * (-ci)) := by
          rw [← zpow_add]
    _ = ζ ^ ((Multiplicative.toAdd (ggTBJReflAut p β f) i).val : ℤ) := by
          rw [(ggTBJ_zeta_zpow_eq_iff hζ _ _).mpr hdiv]
          congr 1
          ring
    _ = ggTBJa p ζ (ggTBJReflAut p β f) i := by
          rw [ggTBJa, zpow_natCast]

end CFSG.StandardType

end

