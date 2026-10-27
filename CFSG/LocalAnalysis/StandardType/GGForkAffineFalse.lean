module

public import CFSG.LocalAnalysis.StandardType.GGForkAffineWord

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section False

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {N : Type} [Fintype N]
  [DecidableEq N] {X : Matrix N N ℤ}

theorem ggAffine_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) (D : GGReflDatum p ι X)
    {n : N → ℕ} (hn : ∀ i, ∑ j, (n j : ℤ) * X j i = 0) {j₀ : N} (hj₀ : n j₀ = 1)
    {w : List N} (hw : ∀ k ∈ w, k ≠ j₀) {j₁ : N} (hj₁ : j₁ ≠ j₀)
    (hroot : ggWordRoot X w j₁ = fun j => if j = j₀ then 0 else (n j : ℤ)) : False := by
  obtain ⟨ψ₂, hψ₂, x₂, f₂, hfx₂, hl₂, hf₂, hx₂⟩ := D.exists_wordConj w j₁
  have hfx₁ : D.root j₀ (D.coroot j₀) = 2 := by
    rw [D.pair j₀ j₀, D.diag j₀]
    norm_num
  have hf₂' : f₂ = ∑ i, (if i = j₀ then (0 : ZMod p) else (n i : ZMod p)) • D.root i := by
    rw [hf₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hroot, Int.cast_ite, Int.cast_zero, Int.cast_natCast]
  have hroot₀ : D.root j₀ = ∑ i, (if i = j₀ then (n i : ZMod p) else 0) • D.root i := by
    simp [Finset.sum_ite_eq', hj₀]
  have hmain : D.root j₀ + ∑ i, (if i = j₀ then (0 : ZMod p) else (n i : ZMod p)) • D.root i
      = ∑ i, (n i : ZMod p) • D.root i := by
    rw [hroot₀, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hf : D.root j₀ + f₂ = 0 := by
    rw [hf₂', hmain, D.sum_root_eq_zero hn]
  have hx : D.coroot j₀ + x₂ ≠ 0 := by
    intro h0
    have hcoroot₀ : D.coroot j₀ = ∑ i, (if i = j₀ then (1 : ZMod p) else 0) • D.coroot i := by
      simp [Finset.sum_ite_eq']
    have hsum : ∑ i, ((if i = j₀ then (1 : ZMod p) else 0) +
        (ggWordCoroot X w j₁ i : ZMod p)) • D.coroot i = 0 := by
      have hthis : ∑ i, ((if i = j₀ then (1 : ZMod p) else 0) +
          (ggWordCoroot X w j₁ i : ZMod p)) • D.coroot i = D.coroot j₀ + x₂ := by
        rw [hx₂, hcoroot₀, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_smul]
      rw [hthis, h0]
    have hc0 := (Fintype.linearIndependent_iff.mp D.ind)
      (fun i => (if i = j₀ then (1 : ZMod p) else 0) + (ggWordCoroot X w j₁ i : ZMod p)) hsum j₀
    have hcz : ((ggWordCoroot X w j₁ j₀ : ℤ) : ZMod p) = 0 := by
      rw [ggWordCoroot_apply_eq_zero hw hj₁, Int.cast_zero]
    simp only [eq_self_iff_true, if_true, hcz, add_zero] at hc0
    exact one_ne_zero hc0
  exact ggFalse_of_opposite_roots (ψ₁ := D.refl j₀) (ψ₂ := ψ₂) (x₁ := D.coroot j₀) (x₂ := x₂)
    (f₁ := D.root j₀) (f₂ := f₂) hp2 hNT ι (D.mem j₀) hψ₂ hfx₁ hfx₂ (D.lin j₀) hl₂ hf hx

end False

end CFSG.StandardType
