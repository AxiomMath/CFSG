module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.SpinGeom
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Matrix

private lemma sixteenC8SpinCent_zmod_two (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h := CharTwo.natCast_cases (R := ZMod 2) a.val
  rwa [ZMod.natCast_zmod_val a] at h

theorem spinCent : ∀ c : MulAut SpinW, (∀ h ∈ spinH, c * h = h * c) → c = 1 := by
  intro c hc
  let E : SpinW := Multiplicative.ofAdd (frameE (ZMod 2) 0)
  have hEne : E ≠ 1 := by
    intro h
    have h0 : frameE (ZMod 2) 0 = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa [E] using this
    have h1 : coordX (ZMod 2) (frameE (ZMod 2) 0) 0 = 1 := by
      rw [coordX_frameE]
      simp
    rw [h0, coordX_zero] at h1
    exact one_ne_zero h1.symm
  have hc_apply : ∀ (h : MulAut SpinW), h ∈ spinH → ∀ w : SpinW, c (h w) = h (c w) := by
    intro h hh w
    have := congrArg (fun f : MulAut SpinW => f w) (hc h hh)
    simpa using this
  have hfixE : c E = E := by
    let vE : Fin (2 * 4) → ZMod 2 := Multiplicative.toAdd (c E)
    have hv : ∀ h ∈ spinSeven (ZMod 2),
        ((h : GL (Fin (2 * 4)) (ZMod 2)) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ
            frameE (ZMod 2) 0 = frameE (ZMod 2) 0 →
          ((h : GL (Fin (2 * 4)) (ZMod 2)) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ
            vE = vE := by
      intro h hh hfix
      have hmem : spinHom h ∈ spinH := (mem_spinH_iff (spinHom h)).2 ⟨h, hh, rfl⟩
      have hE : spinHom h E = E := by
        rw [spinHom_apply]
        simp [E, hfix]
      have happ := hc_apply (spinHom h) hmem E
      rw [hE] at happ
      have h2 := congrArg Multiplicative.toAdd happ
      rw [spinHom_apply] at h2
      simpa [vE] using h2.symm
    have hvne : vE ≠ 0 := by
      intro h0
      have hcE : c E = 1 := by
        have := congrArg Multiplicative.ofAdd h0
        simpa [vE] using this
      exact hEne (c.injective (hcE.trans (map_one c).symm))
    rcases fixed_of_stab_frameE vE hv with h | h
    · exact absurd h hvne
    · have hcE : c E = Multiplicative.ofAdd (frameE (ZMod 2) 0) := by
        have := congrArg Multiplicative.ofAdd h
        simpa [vE] using this
      simpa [E] using hcE
  have hfix_sing : ∀ b : Fin (2 * 4) → ZMod 2, b ≠ 0 →
      coordinateQuadPlus 4 (ZMod 2) b = 0 →
      c (Multiplicative.ofAdd b) = Multiplicative.ofAdd b := by
    intro b hb hQ
    obtain ⟨h, hh, hact⟩ := spinSeven_transitive (ZMod 2) b hb hQ
    have hmem : spinHom h ∈ spinH := (mem_spinH_iff (spinHom h)).2 ⟨h, hh, rfl⟩
    have hbE : spinHom h E = Multiplicative.ofAdd b := by
      rw [spinHom_apply]
      simp [E, hact]
    calc c (Multiplicative.ofAdd b) = c (spinHom h E) := by rw [hbE]
      _ = spinHom h (c E) := hc_apply (spinHom h) hmem E
      _ = spinHom h E := by rw [hfixE]
      _ = Multiplicative.ofAdd b := hbE
  have hEfix : ∀ k : Fin 4,
      c (Multiplicative.ofAdd (frameE (ZMod 2) k)) =
        Multiplicative.ofAdd (frameE (ZMod 2) k) := by
    intro k
    apply hfix_sing
    · intro h0
      have h1 : coordX (ZMod 2) (frameE (ZMod 2) k) k = 1 := by
        rw [coordX_frameE]
        simp
      rw [h0, coordX_zero] at h1
      exact one_ne_zero h1.symm
    · exact quad_frameE k
  have hFfix : ∀ k : Fin 4,
      c (Multiplicative.ofAdd (frameF (ZMod 2) k)) =
        Multiplicative.ofAdd (frameF (ZMod 2) k) := by
    intro k
    apply hfix_sing
    · intro h0
      have h1 : coordY (ZMod 2) (frameF (ZMod 2) k) k = 1 := by
        rw [coordY_frameF]
        simp
      rw [h0, coordY_zero] at h1
      exact one_ne_zero h1.symm
    · exact quad_frameF k
  have hfix_add : ∀ x y : Fin (2 * 4) → ZMod 2,
      c (Multiplicative.ofAdd x) = Multiplicative.ofAdd x →
      c (Multiplicative.ofAdd y) = Multiplicative.ofAdd y →
      c (Multiplicative.ofAdd (x + y)) = Multiplicative.ofAdd (x + y) := by
    intro x y hx hy
    change c (Multiplicative.ofAdd x * Multiplicative.ofAdd y) =
      Multiplicative.ofAdd x * Multiplicative.ofAdd y
    rw [map_mul, hx, hy]
  have hfix_smul : ∀ (a : ZMod 2) (x : Fin (2 * 4) → ZMod 2),
      c (Multiplicative.ofAdd x) = Multiplicative.ofAdd x →
      c (Multiplicative.ofAdd (a • x)) = Multiplicative.ofAdd (a • x) := by
    intro a x hx
    rcases sixteenC8SpinCent_zmod_two a with rfl | rfl
    · simp
    · simpa using hx
  have hfix_all : ∀ v : Fin (2 * 4) → ZMod 2,
      c (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
    intro v
    have hsum : ∀ s : Finset (Fin 4),
        c (Multiplicative.ofAdd (∑ k ∈ s, (coordX (ZMod 2) v k • frameE (ZMod 2) k +
          coordY (ZMod 2) v k • frameF (ZMod 2) k))) =
        Multiplicative.ofAdd (∑ k ∈ s, (coordX (ZMod 2) v k • frameE (ZMod 2) k +
          coordY (ZMod 2) v k • frameF (ZMod 2) k)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact hfix_add _ _ (hfix_add _ _ (hfix_smul _ _ (hEfix a))
            (hfix_smul _ _ (hFfix a))) ih
    have := hsum Finset.univ
    rw [← vec_eq_sum v] at this
    exact this
  apply MulEquiv.ext
  intro w
  have h := hfix_all (Multiplicative.toAdd w)
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
