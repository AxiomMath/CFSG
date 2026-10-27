module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaE
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaSDesc
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139HHerm
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139HNorm
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaSThreeAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.GroupTheory.GL52 (F4poly)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.alpha_not_symplectic_three (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : n = 3) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (hB : HasSympForm K) : False := by
  obtain ⟨x, hxgen, hx3, hxne, hfixX, hsx⟩ := Std139.exists_gen hw2 S
  have hfix : fixV (Subgroup.zpowers x) = ⊥ := hxgen ▸ hfixX
  have hx_ord3 : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have h3n : 3 ≤ n := by omega
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  letI := galoisModule hw2 x hx3 hfix
  have hcent : Subgroup.centralizer (K : Set (MulAut W)) = Subgroup.zpowers x := by
    rw [← hxgen]
    exact Std139.alpha_centralizer hw2 S h3n hK hirr
  have hcommK : ∀ k ∈ K, k * x = x * k := by
    intro k hk
    exact S.component_commutes_X hK.comp k hk x hxX
  obtain ⟨B, hnd, halt, hinv⟩ := hB
  have hadj : ∀ μ : GaloisField 2 2, ∃ μ' : GaloisField 2 2,
      ∀ u v : Additive W, w1369_addForm B (μ • u) v = w1369_addForm B u (μ' • v) :=
    fun μ => w1369_smul_adjoint hw2 x hx3 hfix hx_ord3 B hnd halt K hinv hcommK hcent μ
  obtain ⟨θ, b, hbtr, hbnd, hθ2, hbsymm, hbalt⟩ :=
    trace_descent_f4 (w1369_addForm B) (w1369_addForm_left_nondegenerate B hnd)
      (w1369_addForm_alt B halt) hadj
  have hbinv := w1369_b_invariant hw2 x hx3 hfix B K hinv hcommK θ b hbtr
  by_cases hθid : θ = RingHom.id (GaloisField 2 2)
  · subst hθid
    let B' : LinearMap.BilinForm (GaloisField 2 2) (Additive W) := b
    have hAlt : B'.IsAlt := hbalt rfl
    have hBnd : B'.Nondegenerate := ⟨hbnd, fun v hv => hbnd v fun u => by
      rw [show B' v u = B' u v from by simpa using hbsymm u v]
      exact hv u⟩
    have hEven : Even (Module.finrank (GaloisField 2 2) (Additive W)) :=
      LinearMap.BilinForm.IsAlt.even_finrank hAlt hBnd
    have hfrV : Module.finrank (GaloisField 2 2) (Additive W) = 3 := by
      have hcardW : Nat.card (Additive W) = 4 ^ 3 := by
        change Nat.card W = 4 ^ 3
        rw [S.card, hn]
      have hKcard : Nat.card (GaloisField 2 2) = 4 := by
        rw [GaloisField.card 2 2 (by norm_num)]; norm_num
      have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Additive W)
      rw [hcardW, hKcard] at h
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
    rw [hfrV] at hEven
    norm_num at hEven
  · exact w1369_hermitian_case hw2 S hn hK hirr hxgen hx3 hxne hfix hx_ord3 hcommK hcent
      hnd halt hinv hθ2 hθid b hbtr hbnd hbsymm hbinv

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
