module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuEichler
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary
import CFSG.Quasithin.Background.F7TwoInvU3OddBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem exists_isotropic_conjFixed (h : UnitaryFieldData p f K) (hn : 3 ≤ 2 * r + ε)
    {τ : (HypIndex r ε → K) →ₛₗ[h.bar] (HypIndex r ε → K)}
    (hfin : finrank h.fixedField (conjFixed h τ) = 2 * r + ε)
    {s : K} (hs0 : s ≠ 0) {B : LinearMap.BilinForm h.fixedField (conjFixed h τ)}
    (hBs : ∀ v w, (B v w : K) = s * hypForm h r ε v w) :
    ∃ v : conjFixed h τ, v ≠ 0 ∧
      hypForm h r ε (v : HypIndex r ε → K) (v : HypIndex r ε → K) = 0 := by
  classical
  have : Finite K := h.finite
  have hfin3 : 3 ≤ finrank h.fixedField (conjFixed h τ) := by rw [hfin]; omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := h.fixedField)
    (M := conjFixed h τ) (n := 3) hfin3
  let U : Submodule h.fixedField (conjFixed h τ) := Submodule.span h.fixedField (Set.range f)
  have hU : finrank h.fixedField U = 3 := by
    rw [finrank_span_eq_card hf, Fintype.card_fin]
  obtain ⟨w, hw0, hwB⟩ :=
    CFSG.Quasithin.F7Two.U3Odd.exists_isotropic_of_finrank_three hU (B.restrict U)
  have hBww : B (w : conjFixed h τ) (w : conjFixed h τ) = 0 := by
    rw [LinearMap.BilinForm.restrict_apply] at hwB
    exact hwB
  refine ⟨w, fun h0 => hw0 (Subtype.ext h0), ?_⟩
  have h1 := hBs (w : conjFixed h τ) (w : conjFixed h τ)
  rw [hBww] at h1
  exact (mul_eq_zero.mp (by simpa using h1.symm)).resolve_left hs0

private theorem norm_eq_one_of_smul_semilinear_involution (h : UnitaryFieldData p f K)
    {A : GL (HypIndex r ε) K} {b : Kˣ}
    (hc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = 1)
    (hττ : ∀ v, ((b : K) • semilinearMatrixMap h
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
      (((b : K) • semilinearMatrixMap h
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) v) = v)
    {x : HypIndex r ε → K} (hx : x ≠ 0) :
    h.norm (b : K) = 1 := by
  have hτ₀τ₀ : ∀ v, semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v) = v := by
    intro v
    rw [semilinearMatrixMap_apply, semilinearMatrixMap_apply]
    have hbar : (fun i => h.bar (((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        fun j => h.bar (v j)) i)) =
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar) *ᵥ v := by
      funext i
      rw [RingHom.map_mulVec]
      congr 1
      funext j
      exact h.bar_bar (v j)
    rw [hbar, mulVec_mulVec, hc, one_mulVec]
  have hkey : (h.norm (b : K)) • x = x := by
    have h1 := hττ x
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smulₛₗ, hτ₀τ₀, smul_smul,
      show (b : K) * h.bar (b : K) = h.norm (b : K) from rfl] at h1
    exact h1
  have hsub : (h.norm (b : K) - 1) • x = 0 := by
    rw [sub_smul, hkey, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hx)

theorem exists_eichler_inv_barOne (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε)
    (hc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = 1) :
    ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map h.bar =
        hypEichler h v (-w) (h.bar γ) * A := by
  classical
  obtain ⟨b, t, s, ht, hs0, hττ, hfin, B, hBs, -, -⟩ :=
    exists_descended_form h hp2 (by omega) hA one_ne_zero (by rw [hc, one_smul])
  obtain ⟨v, hv0, hiso⟩ := exists_isotropic_conjFixed h hn hfin hs0 hBs
  have hv : (v : HypIndex r ε → K) ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hfix : ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) (v : HypIndex r ε → K) =
        (v : HypIndex r ε → K) := mem_conjFixed.mp v.2
  have hAv : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      (fun i => h.bar ((v : HypIndex r ε → K) i)) =
        (b : K)⁻¹ • (v : HypIndex r ε → K) := by
    have h1 : (b : K) • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        fun i => h.bar ((v : HypIndex r ε → K) i)) = (v : HypIndex r ε → K) := by
      simpa only [LinearMap.smul_apply, semilinearMatrixMap_apply] using hfix
    calc (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
          (fun i => h.bar ((v : HypIndex r ε → K) i))
        = (b : K)⁻¹ • ((b : K) • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
            fun i => h.bar ((v : HypIndex r ε → K) i))) := by
          rw [smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul]
      _ = (b : K)⁻¹ • (v : HypIndex r ε → K) := by rw [h1]
  have hbN : h.norm (b : K) = 1 :=
    norm_eq_one_of_smul_semilinear_involution h hc hττ hv
  have hd : IsEichlerDatum h (v : HypIndex r ε → K) 0 (t : K) :=
    ⟨hv, hiso, by simp [hypForm_apply], by rw [ht]; simp, Or.inr ⟨rfl, t.ne_zero⟩⟩
  refine ⟨(v : HypIndex r ε → K), 0, (t : K), hd, ?_⟩
  have hmap : (hypEichler h (v : HypIndex r ε → K) 0 (t : K)).map h.bar =
      hypEichler h (fun i => h.bar ((v : HypIndex r ε → K) i)) 0 (-(t : K)) := by
    rw [map_bar_hypEichler, ht]
    rw [show (fun i => h.bar ((0 : HypIndex r ε → K) i)) = (0 : HypIndex r ε → K) from
      funext fun i => by simp]
  calc (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (hypEichler h (v : HypIndex r ε → K) 0 (t : K)).map h.bar
      = (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          hypEichler h (fun i => h.bar ((v : HypIndex r ε → K) i)) 0 (-(t : K)) := by
        rw [hmap]
    _ = hypEichler h ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
          (fun i => h.bar ((v : HypIndex r ε → K) i)))
          ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (0 : HypIndex r ε → K))
          (-(t : K)) * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
        mul_hypEichler_of_mem_hypUnitary h hA _ _ _
    _ = hypEichler h ((b : K)⁻¹ • (v : HypIndex r ε → K)) 0 (-(t : K)) *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
        rw [hAv, mulVec_zero]
    _ = hypEichler h (v : HypIndex r ε → K)
          (h.bar ((b : K)⁻¹) • (0 : HypIndex r ε → K))
          (h.norm ((b : K)⁻¹) * (-(t : K))) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
        rw [hypEichler_smul_left]
    _ = hypEichler h (v : HypIndex r ε → K) (-(0 : HypIndex r ε → K)) (h.bar (t : K)) *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
        rw [smul_zero, norm_inv_eq h, hbN, inv_one, one_mul, ← ht, neg_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
