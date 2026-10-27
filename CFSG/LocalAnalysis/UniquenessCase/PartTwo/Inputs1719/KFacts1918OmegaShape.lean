module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Shapes
import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
import CFSG.HardMathSupport.Foote.E27.Q2OrthMinus
import CFSG.HardMathSupport.Foote.E27.Q2OrthPlus
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaPlus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.HardMathSupport.Foote.E27

private theorem nonempty_mulEquiv_statedOmega_minus {X : Type} [Group X] {n : ℕ}
    (h : IsOmegaMinus X (2 * n) 1) :
    Nonempty (X ≃* ↥(StatedOmega (StatedQuadMinus ((2 * n) / 2) (ZMod 2) 1 1))) := by
  obtain ⟨-, K, hKfield, hKfinite, b, c, hKcard, hpoly, ⟨eY⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  rw [pow_one] at hKcard
  exact ⟨eY.trans (Q2.statedProjOmegaEquiv (StatedQuadMinus ((2 * n) / 2) K b c) hKcard
    (StatedQuadMinus ((2 * n) / 2) (ZMod 2) 1 1)
    (fun v σ => Q2.quadMinus_comp ((2 * n) / 2) σ hpoly v))⟩

private theorem nonempty_mulEquiv_statedOmega_plus {X : Type} [Group X] {n : ℕ}
    (h : IsOmegaPlus X (2 * n) 1) :
    Nonempty (X ≃* ↥(StatedOmega (StatedQuadPlus ((2 * n) / 2) (ZMod 2)))) := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eY⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  rw [pow_one] at hKcard
  exact ⟨eY.trans (Q2.statedProjOmegaEquiv (StatedQuadPlus ((2 * n) / 2) K) hKcard
    (StatedQuadPlus ((2 * n) / 2) (ZMod 2))
    (fun v σ => Q2.quadPlus_comp ((2 * n) / 2) σ v))⟩

private theorem exists_congr_fixed {X Z : Type} [Group X] [Group Z] (e : X ≃* Z)
    (τ : MulAut X) (hτ2 : τ * τ = 1)
    (hτout : τ ∉ (MulAut.conj : X →* MulAut X).range)
    (Y : Subgroup X) (hY : ∀ y : X, y ∈ Y ↔ τ y = y) :
    ∃ (α : MulAut Z) (Y' : Subgroup Z), α * α = 1 ∧
      α ∉ (MulAut.conj : Z →* MulAut Z).range ∧
      (∀ y : Z, y ∈ Y' ↔ α y = y) ∧
      Nat.card Y' = Nat.card Y ∧ Nonempty (↥Y ≃* ↥Y') := by
  have hcongr : ∀ (σ : MulAut X) (b : X), (MulAut.congr e σ) (e b) = e (σ b) := by
    intro σ b
    rw [MulAut.congr_apply]
    simp [MulEquiv.trans_apply]
  have hconj : ∀ z : Z, MulAut.congr e.symm (MulAut.conj z) = MulAut.conj (e.symm z) := by
    intro z
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hback : MulAut.congr e.symm (MulAut.congr e τ) = τ := by
    ext x
    simp [MulAut.congr_apply]
  refine ⟨MulAut.congr e τ, Y.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hτ2, map_one]
  · intro h
    apply hτout
    obtain ⟨z, hz⟩ := h
    refine ⟨e.symm z, ?_⟩
    calc MulAut.conj (e.symm z) = MulAut.congr e.symm (MulAut.conj z) := (hconj z).symm
      _ = MulAut.congr e.symm (MulAut.congr e τ) := by rw [hz]
      _ = τ := hback
  · intro y
    constructor
    · intro hy
      obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
      change ((MulAut.congr e) τ) (e y₀) = e y₀
      rw [hcongr, (hY y₀).mp hy₀]
    · intro hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply (hY (e.symm y)).mpr
      apply e.injective
      rw [← hcongr τ (e.symm y), e.apply_symm_apply y]
      exact hy
  · exact Subgroup.card_map_of_injective e.injective
  · exact ⟨Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective⟩

theorem nonempty_mulEquiv_statedSp_of_isOmegaEps2 {X : Type} [Group X] [Finite X] {ε : Bool}
    {m : ℕ} (hm : (m = 3 ∧ ε = false) ∨ m = 4) (hX : IsOmegaEps2 X ε m) {Y : Subgroup X}
    (hY : IsCentralizerOfTransvectionIn X m Y) :
    Nonempty (↥Y ≃* ↥(StatedSp (m - 1) (ZMod 2))) := by
  obtain ⟨τ, hτ2, hτout, hYfix, hYcard⟩ := hY
  rcases hm with ⟨rfl, rfl⟩ | rfl
  · have hXm : IsOmegaMinus X (2 * 3) 1 := by simpa [IsOmegaEps2] using hX
    obtain ⟨e⟩ := nonempty_mulEquiv_statedOmega_minus (n := 3) hXm
    have hdiv : (2 * 3) / 2 = 3 := by norm_num
    have e' : X ≃* ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) := hdiv ▸ e
    have hYc : Nat.card Y = 720 := by norm_num at hYcard; exact hYcard
    obtain ⟨α, Y', hα2, hαout, hY'fix, hY'card, ⟨eYY'⟩⟩ :=
      exists_congr_fixed e' τ hτ2 hτout Y hYfix
    have h5 : 5 ∣ Nat.card Y' := by rw [hY'card, hYc]; norm_num
    obtain ⟨eSp⟩ := nonempty_mulEquiv_statedSp_minus (n := 2) (Or.inl rfl) α hα2 hαout
      Y' hY'fix h5
    exact ⟨eYY'.trans eSp⟩
  · cases ε with
    | false =>
      have hXm : IsOmegaMinus X (2 * 4) 1 := by simpa [IsOmegaEps2] using hX
      obtain ⟨e⟩ := nonempty_mulEquiv_statedOmega_minus (n := 4) hXm
      have hdiv : (2 * 4) / 2 = 4 := by norm_num
      have e' : X ≃* ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)) := hdiv ▸ e
      have hYc : Nat.card Y = 1451520 := by norm_num at hYcard; exact hYcard
      obtain ⟨α, Y', hα2, hαout, hY'fix, hY'card, ⟨eYY'⟩⟩ :=
        exists_congr_fixed e' τ hτ2 hτout Y hYfix
      have h5 : 5 ∣ Nat.card Y' := by rw [hY'card, hYc]; norm_num
      obtain ⟨eSp⟩ := nonempty_mulEquiv_statedSp_minus (n := 3) (Or.inr rfl) α hα2 hαout
        Y' hY'fix h5
      exact ⟨eYY'.trans eSp⟩
    | true =>
      have hXp : IsOmegaPlus X (2 * 4) 1 := by simpa [IsOmegaEps2] using hX
      obtain ⟨e⟩ := nonempty_mulEquiv_statedOmega_plus (n := 4) hXp
      have hdiv : (2 * 4) / 2 = 4 := by norm_num
      have e' : X ≃* ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))) := hdiv ▸ e
      have hYc : Nat.card Y = 1451520 := by norm_num at hYcard; exact hYcard
      obtain ⟨α, Y', hα2, hαout, hY'fix, hY'card, ⟨eYY'⟩⟩ :=
        exists_congr_fixed e' τ hτ2 hτout Y hYfix
      have h5 : 5 ∣ Nat.card Y' := by rw [hY'card, hYc]; norm_num
      obtain ⟨eSp⟩ := nonempty_mulEquiv_statedSp_plus_eight α hα2 hαout Y' hY'fix h5
      exact ⟨eYY'.trans eSp⟩

theorem omegaCentralizerShape_holds : OmegaCentralizerShape := by
  intro X _ _ ε m Y hX hY
  constructor
  · intro hm3 hε
    subst m
    subst ε
    obtain ⟨e1⟩ := nonempty_mulEquiv_statedSp_of_isOmegaEps2 (X := X) (Y := Y)
      (Or.inl ⟨rfl, rfl⟩) hX hY
    obtain ⟨e2⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
    exact ⟨e1.trans e2⟩
  · intro hm4
    subst m
    obtain ⟨e1⟩ := nonempty_mulEquiv_statedSp_of_isOmegaEps2 (X := X) (Y := Y)
      (Or.inr rfl) hX hY
    haveI : IsSimpleGroup ↥(StatedSp 3 (ZMod 2)) :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts.isSimpleGroup_statedSp_zmod_two
        (n := 3) (by norm_num)
    exact e1.isSimpleGroup

theorem k_19_18_minNormal_holds : K_19_18_minNormal :=
  k_19_18_minNormal_of_omegaCentralizerShape omegaCentralizerShape_holds

theorem k_19_20_J0shape_holds : K_19_20_J0shape :=
  k_19_20_J0shape_of_omegaCentralizerShape omegaCentralizerShape_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
