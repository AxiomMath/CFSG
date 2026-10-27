module

public import CFSG.LieType.RootSystem.Basic
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.OfCartan

@[expose] noncomputable def ggWeylMat {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) (w : (coxeterMatrix hC).Group) : Matrix ι ι ℤ :=
  LinearMap.toMatrix' (weylAction hC w)

theorem ggWeylCartan {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) :
    ∃ (C : Matrix ι ι ℤ) (hC : TauCeti.IsFiniteType C), GGIntCartan M C ∧
      coxeterMatrix hC = M := by
  classical
  have hSL : GGSimplyLaced M := (ggSimplyLacedConnected_of_weyl hM h3).1
  let C : Matrix ι ι ℤ := fun i j => if i = j then 2 else if M.M i j = 3 then -1 else 0
  have hCart : GGIntCartan M C := by
    refine ⟨fun i => by simp [C], ?_⟩
    intro i j hij
    rcases hSL i j hij with h2 | h3'
    · have hji : M.M j i = 2 := (M.symmetric j i).trans h2
      exact Or.inl ⟨h2, by simp [C, hij, h2], by simp [C, Ne.symm hij, hji]⟩
    · have hji : M.M j i = 3 := (M.symmetric j i).trans h3'
      exact Or.inr (Or.inl ⟨h3', by simp [C, hij, h3'], by simp [C, Ne.symm hij, hji]⟩)
  have hMF : GGIsWeylMatrixFixed M := hM
  have hFT : TauCeti.IsFiniteType C := isFiniteType_of_ggIsWeylMatrixFixed hMF hCart
  exact ⟨C, hFT, hCart, coxeterMatrix_eq_of_ggIntCartan hFT hCart⟩

theorem ggWeyl_conj_simple_eq_of_root_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (w w' : (coxeterMatrix hC).Group) (i k : ι)
    {c : ℚ} (hc : c ≠ 0)
    (h : toRat (weylAction hC w (Pi.single i 1 : ι → ℤ)) =
      c • toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) :
    w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹ =
      w' * (coxeterMatrix hC).toCoxeterSystem.simple k * w'⁻¹ := by
  classical
  apply weylAction_injective hC
  apply LinearMap.ext
  intro v
  set n : ℤ := coroot C i (weylAction hC w⁻¹ v) with hn
  set m : ℤ := coroot C k (weylAction hC w'⁻¹ v) with hm
  have hρ'ne : toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)) ≠ 0 :=
    toRat_weylAction_single_ne_zero hC w' k
  have hd : (0 : ℚ) < form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
      (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) := form_pos hC hρ'ne
  have hself : form hC (toRat (weylAction hC w (Pi.single i 1 : ι → ℤ)))
        (toRat (weylAction hC w (Pi.single i 1 : ι → ℤ))) =
      c ^ 2 * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
        (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) := by
    rw [h]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hcross : form hC (toRat (weylAction hC w (Pi.single i 1 : ι → ℤ))) (toRat v) =
      c * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) (toRat v) := by
    rw [h]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have e1 := coroot_mul_form_self hC w i v
  have e2 := coroot_mul_form_self hC w' k v
  rw [← hn, hself, hcross] at e1
  rw [← hm] at e2
  have h1 : ((n : ℚ) * c) * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
        (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) =
      2 * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) (toRat v) := by
    have hc1 : c * (((n : ℚ) * c) * form hC
            (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
            (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))) =
        c * (2 * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) (toRat v)) := by
      calc c * (((n : ℚ) * c) * form hC
              (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
              (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))))
          = (n : ℚ) * (c ^ 2 * form hC
              (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
              (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))) := by ring
        _ = 2 * (c * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) (toRat v)) := e1
        _ = c * (2 * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) (toRat v)) := by
              ring
    exact mul_left_cancel₀ hc hc1
  have h2 : (m : ℚ) * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
        (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) =
      2 * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) (toRat v) := e2
  have hEq : ((n : ℚ) * c) * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
        (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) =
      (m : ℚ) * form hC (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ)))
        (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))) := by
    rw [h1, h2]
  have key : (n : ℚ) * c = (m : ℚ) :=
    mul_right_cancel₀ (ne_of_gt hd) hEq
  have hsmul : n • weylAction hC w (Pi.single i 1 : ι → ℤ) =
      m • weylAction hC w' (Pi.single k 1 : ι → ℤ) := by
    apply toRat_injective
    rw [map_zsmul, map_zsmul, h]
    rw [← Int.cast_smul_eq_zsmul (R := ℚ) n
      (c • toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))), smul_smul]
    rw [← Int.cast_smul_eq_zsmul (R := ℚ) m
      (toRat (weylAction hC w' (Pi.single k 1 : ι → ℤ))), key]
  rw [weylAction_conj_simple hC w i v, weylAction_conj_simple hC w' k v]
  rw [← hn, ← hm]
  rw [hsmul]

end CFSG.StandardType
