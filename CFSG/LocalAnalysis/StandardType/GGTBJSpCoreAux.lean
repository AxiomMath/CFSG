module

public import CFSG.LocalAnalysis.StandardType.GGTBJCoordRefl
public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpGen

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open Multiplicative

variable {p m : ℕ} {K : Type} [Field K] {ζ : Kˣ}

theorem ggTBJSpC_spTorusSp_eq_diagSp (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    TableBSymp.spTorusSp hζ f = diagSp K m (fun i => TableBSymp.zmodPowHom hζ (f i)) := by
  apply mat_injective (n := m) (F := K)
  rw [mat_apply, TableBSymp.spTorusSp_coe, TableBSymp.spTorusGL_apply, mat_diagSp,
    TauCeti.diagGL_coe]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem ggTBJSpC_pairSwap_mul_comm {u w : Fin m} (huw : u ≠ w) :
    TableBSymp.pairSwap u * TableBSymp.pairSwap w =
      TableBSymp.pairSwap w * TableBSymp.pairSwap u := by
  ext a
  rcases a with i | i <;>
    by_cases hiu : i = u <;> by_cases hiw : i = w <;>
    simp [Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.swap_apply_def, hiu, hiw, huw,
      Ne.symm huw]

theorem ggTBJSpC_spSwapSp_mul_comm [CharP K 2] {u w : Fin m} (huw : u ≠ w) :
    TableBSymp.spSwapSp (K := K) (m := m) u * TableBSymp.spSwapSp (K := K) (m := m) w =
      TableBSymp.spSwapSp (K := K) (m := m) w * TableBSymp.spSwapSp (K := K) (m := m) u := by
  apply Subtype.ext
  change (TauCeti.permutationGL (k := K) (TableBSymp.pairSwap u) *
      TauCeti.permutationGL (k := K) (TableBSymp.pairSwap w) : GL (Fin m ⊕ Fin m) K) =
      TauCeti.permutationGL (k := K) (TableBSymp.pairSwap w) *
      TauCeti.permutationGL (k := K) (TableBSymp.pairSwap u)
  rw [← map_mul, ← map_mul, ggTBJSpC_pairSwap_mul_comm huw]

@[expose] noncomputable def ggTBJSpC_reflElt {K : Type} [Field K] [CharP K 2] {m : ℕ}
    (t : Fin m → Kˣ) (u w : Fin m) : StatedSp m K := by
  classical
  exact if t u = t w then permSp K (Equiv.swap u w)
    else TableBSymp.spSwapSp u * TableBSymp.spSwapSp w * permSp K (Equiv.swap u w)

theorem ggTBJSpC_reflElt_eq_same [CharP K 2] {t : Fin m → Kˣ} {u w : Fin m} (h : t u = t w) :
    ggTBJSpC_reflElt t u w = permSp K (Equiv.swap u w) := by
  rw [ggTBJSpC_reflElt]
  simp only [if_pos h]

theorem ggTBJSpC_reflElt_eq_mixed [CharP K 2] {t : Fin m → Kˣ} {u w : Fin m} (h : t u ≠ t w) :
    ggTBJSpC_reflElt t u w =
      TableBSymp.spSwapSp u * TableBSymp.spSwapSp w * permSp K (Equiv.swap u w) := by
  rw [ggTBJSpC_reflElt]
  simp only [if_neg h]

theorem ggTBJSpC_reflElt_mem_of_paired [CharP K 2] {t : Fin m → Kˣ}
    {J : Subgroup (StatedSp m K)} {lam : Kˣ} (hlam : lam ≠ 1)
    (hperm : ∀ i k : Fin m, i ≠ k → t i = t k → (t i = lam ∨ t i = lam⁻¹) →
      permSp K (Equiv.swap i k) ∈ J)
    (hmixed : ∀ i k : Fin m, t i = lam → t k = lam⁻¹ → lam ≠ 1 →
      TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈ J)
    {u w : Fin m} (hu : t u = lam ∨ t u = lam⁻¹) (hw : t w = lam ∨ t w = lam⁻¹)
    (huw : u ≠ w) : ggTBJSpC_reflElt t u w ∈ J := by
  by_cases h : t u = t w
  · rw [ggTBJSpC_reflElt_eq_same h]
    exact hperm u w huw h hu
  · rw [ggTBJSpC_reflElt_eq_mixed h]
    rcases hu with hu | hu
    · have hw' : t w = lam⁻¹ := by
        rcases hw with hw | hw
        · exact absurd (hu.trans hw.symm) h
        · exact hw
      exact hmixed u w hu hw' hlam
    · have hw' : t w = lam := by
        rcases hw with hw | hw
        · exact hw
        · exact absurd (hu.trans hw.symm) h
      have hmem := hmixed w u hw' hu hlam
      have heq : TableBSymp.spSwapSp u * TableBSymp.spSwapSp w * permSp K (Equiv.swap u w) =
          TableBSymp.spSwapSp w * TableBSymp.spSwapSp u * permSp K (Equiv.swap w u) := by
        rw [ggTBJSpC_spSwapSp_mul_comm huw, Equiv.swap_comm]
      rwa [heq]

theorem ggTBJSpC_conj_permSp (hζ : ζ ^ p = 1) (π : Equiv.Perm (Fin m))
    (f : Fin m → Multiplicative (ZMod p)) :
    permSp K π * TableBSymp.spTorusSp hζ f * (permSp K π)⁻¹ =
      TableBSymp.spTorusSp hζ (SpCoord.permAut π f) := by
  rw [ggTBJSpC_spTorusSp_eq_diagSp, ggTBJSpC_spTorusSp_eq_diagSp, conj_permSp_diagSp]
  rfl

theorem ggTBJSpC_conj_spSwapSp [CharP K 2] (hζ : ζ ^ p = 1) (i : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) :
    TableBSymp.spSwapSp i * TableBSymp.spTorusSp hζ f * (TableBSymp.spSwapSp i)⁻¹ =
      TableBSymp.spTorusSp hζ (SpCoord.sgnAut i f) := by
  rw [ggTBJSpC_spTorusSp_eq_diagSp, ggTBJSpC_spTorusSp_eq_diagSp, spSwapSp_conj_diagSp]
  congr 1
  funext k
  rw [SpCoord.sgnAut_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Function.update_of_ne hk]

theorem ggTBJSpC_reflElt_conj_same [CharP K 2] (hζ : ζ ^ p = 1) {t : Fin m → Kˣ}
    {u w : Fin m} (h : t u = t w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflElt t u w * TableBSymp.spTorusSp hζ f * (ggTBJSpC_reflElt t u w)⁻¹ =
      TableBSymp.spTorusSp hζ (ggTBJSpC_reflAut p m t u w f) := by
  rw [ggTBJSpC_reflElt_eq_same h, ggTBJSpC_reflAut_apply_same h]
  exact ggTBJSpC_conj_permSp hζ (Equiv.swap u w) f

theorem ggTBJSpC_reflElt_conj_mixed [CharP K 2] (hζ : ζ ^ p = 1) {t : Fin m → Kˣ}
    {u w : Fin m} (h : t u ≠ t w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflElt t u w * TableBSymp.spTorusSp hζ f * (ggTBJSpC_reflElt t u w)⁻¹ =
      TableBSymp.spTorusSp hζ (ggTBJSpC_reflAut p m t u w f) := by
  rw [ggTBJSpC_reflElt_eq_mixed h, ggTBJSpC_reflAut_apply_mixed h, ggTBJSpC_invSwapAut,
    MulAut.mul_apply, MulAut.mul_apply]
  calc (TableBSymp.spSwapSp u * TableBSymp.spSwapSp w * permSp K (Equiv.swap u w)) *
        TableBSymp.spTorusSp hζ f *
        (TableBSymp.spSwapSp u * TableBSymp.spSwapSp w * permSp K (Equiv.swap u w))⁻¹
      = TableBSymp.spSwapSp u *
          (TableBSymp.spSwapSp w *
            (permSp K (Equiv.swap u w) * TableBSymp.spTorusSp hζ f *
              (permSp K (Equiv.swap u w))⁻¹) *
            (TableBSymp.spSwapSp w)⁻¹) *
          (TableBSymp.spSwapSp u)⁻¹ := by group
    _ = TableBSymp.spSwapSp u *
          (TableBSymp.spSwapSp w *
            TableBSymp.spTorusSp hζ (SpCoord.permAut (Equiv.swap u w) f) *
            (TableBSymp.spSwapSp w)⁻¹) *
          (TableBSymp.spSwapSp u)⁻¹ := by
        rw [ggTBJSpC_conj_permSp hζ (Equiv.swap u w) f]
    _ = TableBSymp.spSwapSp u *
          TableBSymp.spTorusSp hζ (SpCoord.sgnAut w (SpCoord.permAut (Equiv.swap u w) f)) *
          (TableBSymp.spSwapSp u)⁻¹ := by
        rw [ggTBJSpC_conj_spSwapSp hζ w (SpCoord.permAut (Equiv.swap u w) f)]
    _ = TableBSymp.spTorusSp hζ
          (SpCoord.sgnAut u (SpCoord.sgnAut w (SpCoord.permAut (Equiv.swap u w) f))) := by
        rw [ggTBJSpC_conj_spSwapSp hζ u]

end CFSG.StandardType

end
