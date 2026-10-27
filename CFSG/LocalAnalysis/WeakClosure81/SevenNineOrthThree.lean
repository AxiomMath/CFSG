module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthModel
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthFrameThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace OrthFrameThree

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (F : OrthFrameThree f)

private theorem a_orth_t : f F.a F.t = 0 := by
  rw [F.symm F.a F.t]
  exact F.t_orth_a

private theorem a_orth_t' : f F.a F.t' = 0 := by
  rw [F.symm F.a F.t']
  exact F.t'_orth_a

private theorem a_orth_c : f F.a F.c = 0 := by
  rw [F.symm F.a F.c]
  exact F.c_orth_a

private theorem t_orth_c : f F.t F.c = 0 := by
  rw [F.symm F.t F.c]
  exact F.c_orth_t

private theorem t'_orth_c : f F.t' F.c = 0 := by
  rw [F.symm F.t' F.c]
  exact F.c_orth_t'

private theorem t'_orth_t : f F.t' F.t = 1 := by
  rw [F.symm F.t' F.t]
  exact F.pair_t

private theorem t_mem_U : F.t ∈ F.U := F.mem_U.2 ⟨F.t_orth_s, F.t_orth_s'⟩

private theorem t'_mem_U : F.t' ∈ F.U := F.mem_U.2 ⟨F.t'_orth_s, F.t'_orth_s'⟩

private theorem c_mem_U : F.c ∈ F.U := F.mem_U.2 ⟨F.c_orth_s, F.c_orth_s'⟩

private theorem a_add_t_mem_U : F.a + F.t ∈ F.U := F.U.add_mem F.a_mem_U (t_mem_U F)

private theorem a_add_t'_mem_U : F.a + F.t' ∈ F.U := F.U.add_mem F.a_mem_U (t'_mem_U F)

private theorem a_add_gamma_t'_add_c_mem_U :
    F.a + F.t + F.γ • F.t' + F.c ∈ F.U :=
  F.U.add_mem (F.U.add_mem (F.U.add_mem F.a_mem_U (t_mem_U F))
    (F.U.smul_mem F.γ (t'_mem_U F))) (c_mem_U F)

private theorem norm_a_add_t : f (F.a + F.t) (F.a + F.t) = -2 := by
  simp [map_add, F.norm_a, F.isotropic_t, a_orth_t, F.t_orth_a]

private theorem norm_a_add_t' : f (F.a + F.t') (F.a + F.t') = -2 := by
  simp [map_add, F.norm_a, F.isotropic_t', a_orth_t', F.t'_orth_a]

private theorem coeff_four (γ : ZMod 3) : -2 + 2 * γ + γ = -2 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h : -2 + 2 * γ + γ = -2 + 3 * γ := by ring
  rw [h, h3, zero_mul, add_zero]

private theorem norm_a_add_gamma_t'_add_c :
    f (F.a + F.t + F.γ • F.t' + F.c) (F.a + F.t + F.γ • F.t' + F.c) = -2 := by
  have h : f (F.a + F.t + F.γ • F.t' + F.c) (F.a + F.t + F.γ • F.t' + F.c) =
      -2 + 2 * F.γ + F.γ := by
    simp [map_add, map_smul, smul_eq_mul, F.norm_a, F.norm_c, F.isotropic_t,
      F.isotropic_t', a_orth_t, a_orth_t', a_orth_c, F.t_orth_a, F.t'_orth_a, F.c_orth_a,
      t_orth_c, t'_orth_c, F.c_orth_t, F.c_orth_t', F.pair_t, t'_orth_t] <;> ring
  rw [h]
  exact coeff_four F.γ

private theorem pair_a_a_add_t : f F.a (F.a + F.t) ≠ 0 := by
  simp [map_add, F.norm_a, a_orth_t] <;> decide

private theorem pair_a_a_add_t' : f F.a (F.a + F.t') ≠ 0 := by
  simp [map_add, F.norm_a, a_orth_t'] <;> decide

private theorem pair_a_a_add_gamma_t'_add_c :
    f F.a (F.a + F.t + F.γ • F.t' + F.c) ≠ 0 := by
  simp [map_add, map_smul, smul_eq_mul, F.norm_a, a_orth_t, a_orth_t', a_orth_c] <;>
    decide

private theorem pair_t'_a_add_t : f F.t' (F.a + F.t) ≠ 0 := by
  simp [map_add, F.t'_orth_a, t'_orth_t] <;> decide

private def goodSpan (F : OrthFrameThree f) : Submodule (ZMod 3) (Fin 6 → ZMod 3) :=
  Submodule.span (ZMod 3) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0}

private def perpSpan (F : OrthFrameThree f) : Submodule (ZMod 3) (Fin 6 → ZMod 3) :=
  Submodule.span (ZMod 3) {v | v ∈ F.U ∧ f v v = -2 ∧ f v F.a = 0}

private theorem a_mem_goodSpan : F.a ∈ goodSpan F :=
  Submodule.subset_span ⟨F.a_mem_U, F.norm_a, by rw [F.norm_a]; decide⟩

private theorem a_add_t_mem_goodSpan : F.a + F.t ∈ goodSpan F :=
  Submodule.subset_span ⟨a_add_t_mem_U F, norm_a_add_t F, pair_a_a_add_t F⟩

private theorem a_add_t'_mem_goodSpan : F.a + F.t' ∈ goodSpan F :=
  Submodule.subset_span ⟨a_add_t'_mem_U F, norm_a_add_t' F, pair_a_a_add_t' F⟩

private theorem a_add_gamma_t'_add_c_mem_goodSpan :
    F.a + F.t + F.γ • F.t' + F.c ∈ goodSpan F :=
  Submodule.subset_span ⟨a_add_gamma_t'_add_c_mem_U F, norm_a_add_gamma_t'_add_c F,
    pair_a_a_add_gamma_t'_add_c F⟩

private theorem gamma_eq_one_or_two : F.γ = 1 ∨ F.γ = 2 := by
  have h : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h F.γ with h0 | h1 | h2
  · exact absurd h0 F.γ_ne_zero
  · exact Or.inl h1
  · exact Or.inr h2

private theorem norm_t_sub_t' : f (F.t - F.t') (F.t - F.t') = -2 := by
  simp [map_sub, F.isotropic_t, F.isotropic_t', F.pair_t, t'_orth_t] <;> decide

private theorem norm_t_add_c_of_gamma_one (hγ : F.γ = 1) :
    f (F.t + F.c) (F.t + F.c) = -2 := by
  have hcc : f F.c F.c = 1 := by rw [F.norm_c, hγ]
  simp [map_add, F.isotropic_t, hcc, t_orth_c, F.c_orth_t] <;> decide

private theorem norm_t'_add_c_of_gamma_one (hγ : F.γ = 1) :
    f (F.t' + F.c) (F.t' + F.c) = -2 := by
  have hcc : f F.c F.c = 1 := by rw [F.norm_c, hγ]
  simp [map_add, F.isotropic_t', hcc, t'_orth_c, F.c_orth_t'] <;> decide

private theorem norm_t_add_t'_add_c_of_gamma_two (hγ : F.γ = 2) :
    f (F.t + F.t' + F.c) (F.t + F.t' + F.c) = -2 := by
  have hcc : f F.c F.c = 2 := by rw [F.norm_c, hγ]
  simp [map_add, F.isotropic_t, F.isotropic_t', F.pair_t, t'_orth_t, hcc, t_orth_c,
    t'_orth_c, F.c_orth_t, F.c_orth_t'] <;> decide

private theorem norm_t_add_t'_sub_c_of_gamma_two (hγ : F.γ = 2) :
    f (F.t + F.t' - F.c) (F.t + F.t' - F.c) = -2 := by
  have hcc : f F.c F.c = 2 := by rw [F.norm_c, hγ]
  simp [map_sub, map_add, F.isotropic_t, F.isotropic_t', F.pair_t, t'_orth_t, hcc,
    t_orth_c, t'_orth_c, F.c_orth_t, F.c_orth_t'] <;> decide

private theorem t_add_t'_eq_neg :
    F.t + F.t' = -((F.t + F.t' + F.c) + (F.t + F.t' - F.c)) := by
  have h : (F.t + F.t' + F.c) + (F.t + F.t' - F.c) = -(F.t + F.t') := by
    calc
      (F.t + F.t' + F.c) + (F.t + F.t' - F.c) = (F.t + F.t') + (F.t + F.t') := by
        abel
      _ = (2 : ZMod 3) • (F.t + F.t') := by rw [two_smul]
      _ = (-1 : ZMod 3) • (F.t + F.t') := by
        rw [show (2 : ZMod 3) = -1 by decide]
      _ = -(F.t + F.t') := by rw [neg_one_smul]
  rw [h, neg_neg]

private theorem c_eq_sub :
    F.c = (F.t + F.t' - F.c) - (F.t + F.t' + F.c) := by
  calc
    F.c = (1 : ZMod 3) • F.c := by rw [one_smul]
    _ = (-2 : ZMod 3) • F.c := by rw [show (-2 : ZMod 3) = 1 by decide]
    _ = -((2 : ZMod 3) • F.c) := by rw [neg_smul]
    _ = -(F.c + F.c) := by rw [two_smul]
    _ = (F.t + F.t' - F.c) - (F.t + F.t' + F.c) := by abel

private theorem t_eq_neg : F.t = -((F.t - F.t') + (F.t + F.t')) := by
  have h : (F.t - F.t') + (F.t + F.t') = -F.t := by
    calc
      (F.t - F.t') + (F.t + F.t') = F.t + F.t := by abel
      _ = (2 : ZMod 3) • F.t := by rw [two_smul]
      _ = (-1 : ZMod 3) • F.t := by rw [show (2 : ZMod 3) = -1 by decide]
      _ = -F.t := by rw [neg_one_smul]
  rw [h, neg_neg]

private theorem c_mem_perpSpan_of_gamma_one (hγ : F.γ = 1) : F.c ∈ perpSpan F :=
  Submodule.subset_span ⟨c_mem_U F, by rw [F.norm_c, hγ]; decide, F.c_orth_a⟩

private theorem t_add_c_mem_perpSpan_of_gamma_one (hγ : F.γ = 1) :
    F.t + F.c ∈ perpSpan F :=
  Submodule.subset_span ⟨F.U.add_mem (t_mem_U F) (c_mem_U F),
    norm_t_add_c_of_gamma_one F hγ, by simp [map_add, F.t_orth_a, F.c_orth_a]⟩

private theorem t'_add_c_mem_perpSpan_of_gamma_one (hγ : F.γ = 1) :
    F.t' + F.c ∈ perpSpan F :=
  Submodule.subset_span ⟨F.U.add_mem (t'_mem_U F) (c_mem_U F),
    norm_t'_add_c_of_gamma_one F hγ, by simp [map_add, F.t'_orth_a, F.c_orth_a]⟩

private theorem t_sub_t'_mem_perpSpan : F.t - F.t' ∈ perpSpan F :=
  Submodule.subset_span ⟨F.U.sub_mem (t_mem_U F) (t'_mem_U F), norm_t_sub_t' F,
    by simp [map_sub, F.t_orth_a, F.t'_orth_a]⟩

private theorem t_add_t'_add_c_mem_perpSpan_of_gamma_two (hγ : F.γ = 2) :
    F.t + F.t' + F.c ∈ perpSpan F :=
  Submodule.subset_span
    ⟨F.U.add_mem (F.U.add_mem (t_mem_U F) (t'_mem_U F)) (c_mem_U F),
      norm_t_add_t'_add_c_of_gamma_two F hγ,
      by simp [map_add, F.t_orth_a, F.t'_orth_a, F.c_orth_a]⟩

private theorem t_add_t'_sub_c_mem_perpSpan_of_gamma_two (hγ : F.γ = 2) :
    F.t + F.t' - F.c ∈ perpSpan F :=
  Submodule.subset_span
    ⟨F.U.sub_mem (F.U.add_mem (t_mem_U F) (t'_mem_U F)) (c_mem_U F),
      norm_t_add_t'_sub_c_of_gamma_two F hγ,
      by simp [map_sub, map_add, F.t_orth_a, F.t'_orth_a, F.c_orth_a]⟩

theorem span_le :
    F.U ≤ Submodule.span (ZMod 3) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0} := by
  intro w hw
  change w ∈ goodSpan F
  have hws : f w F.s = 0 := (F.mem_U.1 hw).1
  have hws' : f w F.s' = 0 := (F.mem_U.1 hw).2
  have hrepr := F.span w hws hws'
  have ht : F.t ∈ goodSpan F := by
    have h := (goodSpan F).sub_mem (a_add_t_mem_goodSpan F) (a_mem_goodSpan F)
    convert h using 1
    abel
  have ht' : F.t' ∈ goodSpan F := by
    have h := (goodSpan F).sub_mem (a_add_t'_mem_goodSpan F) (a_mem_goodSpan F)
    convert h using 1
    abel
  have hc : F.c ∈ goodSpan F := by
    have h1 := (goodSpan F).sub_mem (a_add_gamma_t'_add_c_mem_goodSpan F) (a_mem_goodSpan F)
    have h2 := (goodSpan F).sub_mem h1 ht
    have h3 := (goodSpan F).sub_mem h2 ((goodSpan F).smul_mem F.γ ht')
    convert h3 using 1
    abel
  rw [hrepr]
  exact (goodSpan F).add_mem
    ((goodSpan F).add_mem
      ((goodSpan F).add_mem ((goodSpan F).smul_mem (f w F.a) (a_mem_goodSpan F))
        ((goodSpan F).smul_mem (f w F.t') ht))
      ((goodSpan F).smul_mem (f w F.t) ht'))
    ((goodSpan F).smul_mem (F.γ * f w F.c) hc)

theorem exists_vw :
    ∃ v w, v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0 ∧ w ∈ F.U ∧ f w F.a = 0 ∧ f w v ≠ 0 := by
  exact ⟨F.a + F.t, F.t', a_add_t_mem_U F, norm_a_add_t F, pair_a_a_add_t F,
    t'_mem_U F, F.t'_orth_a, pair_t'_a_add_t F⟩

theorem mem_span_perp {w : Fin 6 → ZMod 3} (hw : w ∈ F.U) (hwa : f w F.a = 0) :
    w ∈ Submodule.span (ZMod 3) {v | v ∈ F.U ∧ f v v = -2 ∧ f v F.a = 0} := by
  change w ∈ perpSpan F
  have hws : f w F.s = 0 := (F.mem_U.1 hw).1
  have hws' : f w F.s' = 0 := (F.mem_U.1 hw).2
  have hdecomp : w = f w F.t' • F.t + f w F.t • F.t' + (F.γ * f w F.c) • F.c := by
    conv_lhs => rw [F.span w hws hws']
    rw [hwa, zero_smul, zero_add]
  have hcomb : ∀ (ht : F.t ∈ perpSpan F) (ht' : F.t' ∈ perpSpan F)
      (hc : F.c ∈ perpSpan F), w ∈ perpSpan F := by
    intro ht ht' hc
    rw [hdecomp]
    exact (perpSpan F).add_mem
      ((perpSpan F).add_mem ((perpSpan F).smul_mem (f w F.t') ht)
        ((perpSpan F).smul_mem (f w F.t) ht'))
      ((perpSpan F).smul_mem (F.γ * f w F.c) hc)
  rcases gamma_eq_one_or_two F with hγ | hγ
  · have hc := c_mem_perpSpan_of_gamma_one F hγ
    have htc := t_add_c_mem_perpSpan_of_gamma_one F hγ
    have ht'c := t'_add_c_mem_perpSpan_of_gamma_one F hγ
    have ht : F.t ∈ perpSpan F := by
      have h := (perpSpan F).sub_mem htc hc
      convert h using 1
      abel
    have ht' : F.t' ∈ perpSpan F := by
      have h := (perpSpan F).sub_mem ht'c hc
      convert h using 1
      abel
    exact hcomb ht ht' hc
  · have hA := t_sub_t'_mem_perpSpan F
    have hB := t_add_t'_add_c_mem_perpSpan_of_gamma_two F hγ
    have hC := t_add_t'_sub_c_mem_perpSpan_of_gamma_two F hγ
    have hS : F.t + F.t' ∈ perpSpan F := by
      have h := (perpSpan F).neg_mem ((perpSpan F).add_mem hB hC)
      rw [t_add_t'_eq_neg F]
      exact h
    have hc : F.c ∈ perpSpan F := by
      have h := (perpSpan F).sub_mem hC hB
      rw [c_eq_sub F]
      exact h
    have ht : F.t ∈ perpSpan F := by
      have h := (perpSpan F).neg_mem ((perpSpan F).add_mem hA hS)
      rw [t_eq_neg F]
      exact h
    have ht' : F.t' ∈ perpSpan F := by
      have h := (perpSpan F).sub_mem hS ht
      convert h using 1
      abel
    exact hcomb ht ht' hc

theorem siegel_mem_orthConjSup :
    ∀ w ∈ F.U, f w F.a = 0 → F.siegel w ∈ orthConjSup f F.a := by
  intro w hw hwa
  have hspan : w ∈ Submodule.span (ZMod 3) {v | v ∈ F.U ∧ f v v = -2 ∧ f v F.a = 0} :=
    F.mem_span_perp hw hwa
  have hmem : w ∈ F.U ∧ F.siegel w ∈ orthConjSup f F.a := by
    refine Submodule.span_induction
      (p := fun x _ => x ∈ F.U ∧ F.siegel x ∈ orthConjSup f F.a) ?_ ?_ ?_ ?_ hspan
    · rintro x ⟨hxU, hxnorm, hxa⟩
      have hp : (3 : ℕ) = 3 ∨ 3 = 5 := Or.inl rfl
      exact ⟨hxU,
        by simpa using F.toOrthFrame.siegel_smul_mem_orthConjSup hp hxU hxnorm hxa 1⟩
    · exact ⟨F.U.zero_mem, by
        simpa [F.siegel_zero] using (orthConjSup f F.a).one_mem⟩
    · intro x y _ _ ihx ihy
      have hx0 : f x F.s = 0 := (F.mem_U.1 ihx.1).1
      have hy0 : f y F.s = 0 := (F.mem_U.1 ihy.1).1
      refine ⟨F.U.add_mem ihx.1 ihy.1, ?_⟩
      rw [F.toOrthFrame.siegel_add hx0 hy0]
      exact (orthConjSup f F.a).mul_mem ihx.2 ihy.2
    · intro a x _ ih
      have hx0 : f x F.s = 0 := (F.mem_U.1 ih.1).1
      have hsm : a • x = a.val • x := by
        calc
          a • x = (a.val : ZMod 3) • x := by rw [ZMod.natCast_zmod_val a]
          _ = a.val • x := Nat.cast_smul_eq_nsmul (ZMod 3) a.val x
      have hstep : F.siegel (a • x) = F.siegel x ^ a.val := by
        rw [hsm]
        exact F.toOrthFrame.siegel_nsmul hx0 a.val
      refine ⟨F.U.smul_mem a ih.1, ?_⟩
      rw [hstep]
      exact (orthConjSup f F.a).pow_mem ih.2 a.val
  exact hmem.2

theorem sevenNineConfig :
    SevenNineConfig (Subgroup.closure (orthReflSet 3 6 f)) (Subgroup.zpowers F.refl) 3 F.Y F.Z :=
  F.toOrthFrame.sevenNineConfig_of_span (by decide) F.span_le F.exists_vw
    F.siegel_mem_orthConjSup

end OrthFrameThree

end CFSG.LocalAnalysis.WeakClosure81
