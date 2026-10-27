module

public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Hyp
public import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ} {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}

theorem orbN_of_wt_eq_of_fk
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) {w : Fin (n + 1) → ZMod 3} (hw : wt w = wt v) :
    OrbN Xg w := by
  obtain ⟨σ, s, hs, hsw⟩ := exists_spMat_mulVec_eq hw.symm
  obtain ⟨A, hA, hAmat⟩ := hFK σ s hs
  rw [← hsw, ← hAmat]
  exact orbN_mulVec hv hA

theorem card_le_of_orbN_wt_one
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    (h1 : ∀ v, OrbN Xg v → wt v = 1) : Nat.card ↥Xg ≤ 2 ^ (n + 1) * (n + 1).factorial := by
  classical
  have hwtcol : ∀ (A : ↥Xg) (m : Fin (n + 1)),
      wt (((A : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) = 1 := by
    intro A m
    obtain ⟨P, hPX, hPmat⟩ := hFK (Equiv.swap 0 m) (fun _ => (1 : ZMod 3))
      (fun _ => Or.inl rfl)
    have hPe : ((P : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single m 1 := by
      rw [hPmat, spMat_mulVec]
      funext i
      by_cases hi : i = m
      · have hsym : (Equiv.swap (0 : Fin (n + 1)) m).symm i = 0 := by
          rw [hi]
          rw [← Equiv.swap_apply_left (0 : Fin (n + 1)) m]
          exact Equiv.symm_apply_apply _ _
        rw [hsym]
        simp [hi]
      · have hsym : (Equiv.swap (0 : Fin (n + 1)) m).symm i ≠ 0 := by
          intro h
          apply hi
          have := congrArg (Equiv.swap (0 : Fin (n + 1)) m) h
          simpa [Equiv.swap_apply_left] using this
        rw [Pi.single_eq_of_ne hsym]
        simp [hi]
    have horb : OrbN Xg (((A : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) := by
      have h := orbN_mulVec (Xg := Xg) (orbN_e0 (Xg := Xg)) (Xg.mul_mem A.2 hPX)
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec, hPe] at h
    exact h1 _ horb
  let f : ↥Xg → ↥(spSet fun _ _ => True) := fun A =>
    ⟨((A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)),
      mem_spSet_of_wt_col (hwtcol A)⟩
  have hf_inj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hAB
  calc Nat.card ↥Xg ≤ Nat.card ↥(spSet fun _ _ => True) :=
        Nat.card_le_card_of_injective f hf_inj
    _ ≤ 2 ^ (n + 1) * (n + 1).factorial := card_spSet_le (n + 1) _

namespace MonoN0Hyp

variable (h : MonoN0Hyp Xg)
include h

theorem wt_orbN
    (hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s)
    {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) : wt v = 1 ∨ wt v = 2 ∨ wt v = n + 1 := by
  have hle : wt v ≤ n + 1 := by
    have := Finset.card_le_univ (Finset.univ.filter fun i : Fin (n + 1) => v i ≠ 0)
    simpa [wt, Fintype.card_fin] using this
  by_cases htop : wt v = n + 1
  · exact Or.inr (Or.inr htop)
  · have hex : ∃ i : Fin (n + 1), v i = 0 := by
      by_contra hnone
      push Not at hnone
      exact htop ((wt_eq_iff_forall_ne_zero v).mpr hnone)
    obtain ⟨i, hi⟩ := hex
    obtain ⟨P, hPX, hPmat⟩ := hFK (Equiv.swap 0 i) (fun _ => (1 : ZMod 3))
      (fun _ => Or.inl rfl)
    let v' : Fin (n + 1) → ZMod 3 :=
      ((P : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v
    have hv' : OrbN Xg v' := orbN_mulVec hv hPX
    have hv'0 : v' 0 = 0 := by
      have hsym : (Equiv.swap (0 : Fin (n + 1)) i).symm 0 = i := by
        have := Equiv.symm_apply_apply (Equiv.swap (0 : Fin (n + 1)) i) i
        simpa [Equiv.swap_apply_right] using this
      change (((P : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 0 = 0
      rw [hPmat, spMat_mulVec]
      simpa [hsym, hi]
    have hwtv' : wt v' = wt v := by
      change wt (((P : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) = wt v
      rw [hPmat]
      exact wt_spMat_mulVec (σ := Equiv.swap 0 i) (s := fun _ => (1 : ZMod 3))
        (fun _ => Or.inl rfl) v
    rcases h.wt_of_orbN_zero hv' hv'0 with h1 | h2
    · exact Or.inl (by rw [← hwtv']; exact h1)
    · exact Or.inr (Or.inl (by rw [← hwtv']; exact h2))

end MonoN0Hyp

end CFSG.StandardType.FrameRoute.FS81
