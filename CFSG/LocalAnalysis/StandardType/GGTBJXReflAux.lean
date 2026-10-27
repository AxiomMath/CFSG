module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJXRoots
public import CFSG.LocalAnalysis.StandardType.GGTBJF4ReflAux

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint

theorem ggTBJX_ggTBJXa_refl (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (ζ : Kˣ)
    (hζ : orderOf ζ = p) {τ : Tag} {β : Fin τ.rank → ℤ}
    (hfunvec : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2)
    (f : Multiplicative (Fin τ.rank → ZMod p)) :
    (fun i => ggTBJXa p τ ζ f i *
        rootChar (ggTBJXa p τ ζ f) β ^ (-(corootPair (τ := τ) β (Pi.single i 1))))
      = ggTBJXa p τ ζ (ggTBJXReflAut p τ β f) := by
  funext i
  set S : ℤ := ∑ j : Fin τ.rank, ((Multiplicative.toAdd f j).val : ℤ) * β j with hS
  set ci : ℤ := corootPair (τ := τ) β (Pi.single i 1) with hci
  have hroot : rootChar (ggTBJXa p τ ζ f) β = ζ ^ S := by
    rw [hS]
    show (∏ j, ggTBJXa p τ ζ f j ^ β j) =
      ζ ^ ∑ j : Fin τ.rank, ((Multiplicative.toAdd f j).val : ℤ) * β j
    calc ∏ j, ggTBJXa p τ ζ f j ^ β j
        = ∏ j, ζ ^ (((Multiplicative.toAdd f j).val : ℤ) * β j) := by
          apply Finset.prod_congr rfl
          intro j _
          rw [ggTBJXa, ← zpow_natCast ζ (Multiplicative.toAdd f j).val, ← zpow_mul]
      _ = ζ ^ ∑ j : Fin τ.rank, ((Multiplicative.toAdd f j).val : ℤ) * β j :=
          Finset.prod_zpow_eq_zpow_sum Finset.univ ζ
            (fun j => ((Multiplicative.toAdd f j).val : ℤ) * β j)
  have hfun : ggTBJXFun p τ β (Multiplicative.toAdd f) = (S : ZMod p) := by
    rw [hS, ggTBJXFun_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  have hmod : (((Multiplicative.toAdd (ggTBJXReflAut p τ β f) i).val : ℤ) : ZMod p) =
      (((Multiplicative.toAdd f i).val : ℤ) - S * ci : ℤ) := by
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id,
      ggTBJXReflAut_apply p τ hfunvec f i, hfun, hci]
    push_cast
    simp only [ggTBJXVec]
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdiv : (p : ℤ) ∣ ((Multiplicative.toAdd (ggTBJXReflAut p τ β f) i).val : ℤ) -
      (((Multiplicative.toAdd f i).val : ℤ) - S * ci) := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((Multiplicative.toAdd (ggTBJXReflAut p τ β f) i).val : ℤ)
      (((Multiplicative.toAdd f i).val : ℤ) - S * ci) p).mp hmod
    simpa only [neg_sub] using dvd_neg.mpr h
  calc ggTBJXa p τ ζ f i * rootChar (ggTBJXa p τ ζ f) β ^ (-ci)
      = ζ ^ ((Multiplicative.toAdd f i).val : ℤ) * (ζ ^ S) ^ (-ci) := by
          rw [hroot, ggTBJXa, ← zpow_natCast ζ (Multiplicative.toAdd f i).val]
    _ = ζ ^ ((Multiplicative.toAdd f i).val : ℤ) * ζ ^ (S * (-ci)) := by
          rw [zpow_mul]
    _ = ζ ^ (((Multiplicative.toAdd f i).val : ℤ) + S * (-ci)) := by
          rw [← zpow_add]
    _ = ζ ^ ((Multiplicative.toAdd (ggTBJXReflAut p τ β f) i).val : ℤ) := by
          rw [(ggTBJ_zeta_zpow_eq_iff hζ _ _).mpr hdiv]
          congr 1
          ring
    _ = ggTBJXa p τ ζ (ggTBJXReflAut p τ β f) i := by
          rw [ggTBJXa, zpow_natCast]

end CFSG.StandardType

end
