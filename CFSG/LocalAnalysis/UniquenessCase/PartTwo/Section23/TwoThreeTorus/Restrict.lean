module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoordsRestrict
import CFSG.Quasithin.Background.B69Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

private theorem restrict_realizesVia_commV_Tor2 {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {W : Type} [CommGroup W] {X : Subgroup (MulAut W)} {π : ↥Γ →* ↥X}
    (hπ : (FFModel.nat Γ).RealizesVia X (commV X) ⊥ π) :
    ∃ (H : Subgroup (MulAut ↥(commV X))) (f : ↥X ≃* ↥H),
      (FFModel.nat Γ).Realizes H ⊤ ⊥ ∧
      ∀ (x : ↥X) (u : ↥(commV X)),
        (((f x : ↥H) : MulAut ↥(commV X)) u : W) = (x : MulAut W) (u : W) := by
  obtain ⟨H', π', hH'eq, hπ'val, hπ'real⟩ := Inputs1719.exists_realizesVia_restrict hπ
  let hKA : ∀ a ∈ X, ∀ u ∈ commV X, a u ∈ commV X :=
    fun a ha u hu => hπ.2.2.2.1 ⟨a, ha⟩ u hu
  let ρ : ↥X →* MulAut ↥(commV X) := actOnSub hKA
  have hρeq : H' = ρ.range := hH'eq
  have hπ'inj : Function.Injective π' := B69.natRealizes_injective hπ'real
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have h1 : ρ (x * y⁻¹) = 1 := by rw [map_mul, hxy, map_inv, mul_inv_cancel]
    obtain ⟨γ, hγ⟩ := hπ.1 (x * y⁻¹)
    have hπ'γ : π' γ = 1 := by
      apply Subtype.ext
      change ((π' γ : ↥H') : MulAut ↥(commV X)) = 1
      rw [hπ'val γ, hγ]
      exact h1
    have hγ1 : γ = 1 := hπ'inj (by rw [hπ'γ, map_one])
    have hxy1 : x * y⁻¹ = 1 := by
      rw [← hγ, hγ1]
      exact map_one π
    have h3 : x * y⁻¹ * y = 1 * y := congrArg (· * y) hxy1
    simpa [mul_assoc] using h3
  let f : ↥X ≃* ↥H' :=
    (MulEquiv.ofBijective ρ.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.2 hρinj, ρ.rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr hρeq.symm)
  refine ⟨H', f, ⟨π', hπ'real⟩, ?_⟩
  intro x u
  have hfx : ((f x : ↥H') : MulAut ↥(commV X)) = ρ x := rfl
  rw [hfx]
  exact actOnSub_apply hKA x u

theorem exists_mulEquiv_isNaturalClassicalModule {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {n : ℕ} (hn : 2 < n)
    (hnat : (IsL2 ↥X n ∧ BinaryNaturalSL X (commV X) ⊥ 2 n) ∨
      (Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧ NatOmegaMinus X (commV X) ⊥ 4 (n / 2))) :
    ∃ (H : Subgroup (MulAut ↥(commV X))) (k : ℕ) (f : ↥X ≃* ↥H),
      2 ≤ k ∧ IsNaturalClassicalModule H k ∧
      ∀ (x : ↥X) (u : ↥(commV X)),
        (((f x : ↥H) : MulAut ↥(commV X)) u : W) = (x : MulAut W) (u : W) := by
  rcases hnat with ⟨hL2, hBN⟩ | ⟨hEven, hOM, hNOM⟩
  · obtain ⟨K, hKf, hKfin, hKc, hreal⟩ := hBN
    obtain ⟨π, hπ⟩ := hreal
    obtain ⟨H, f, hreal', hcompat⟩ := restrict_realizesVia_commV_Tor2 hπ
    have hL2' : IsL2 ↥H n := CFSG.Blueprint.LieModel.of_mulEquiv f hL2
    have hBN' : BinaryNaturalSL H ⊤ ⊥ 2 n := ⟨K, hKf, hKfin, hKc, hreal'⟩
    exact ⟨H, n, f, by omega, Or.inl ⟨hL2', hBN'⟩, hcompat⟩
  · obtain ⟨hEven4, K, hKf, hKfin, b, c, hKc, hirr, hreal⟩ := hNOM
    obtain ⟨π, hπ⟩ := hreal
    obtain ⟨H, f, hreal', hcompat⟩ := restrict_realizesVia_commV_Tor2 hπ
    obtain ⟨hEven4', K', hKf', hKfin', b', c', hKc', hirr', ⟨e⟩⟩ := hOM
    have hOM' : IsOmegaMinus ↥H 4 (n / 2) :=
      ⟨hEven4', K', hKf', hKfin', b', c', hKc', hirr', ⟨f.symm.trans e⟩⟩
    have hNOM' : NatOmegaMinus H ⊤ ⊥ 4 (n / 2) :=
      ⟨hEven4, K, hKf, hKfin, b, c, hKc, hirr, hreal'⟩
    have h2 : 2 ≤ n / 2 := by
      obtain ⟨m, hm⟩ := hEven
      omega
    exact ⟨H, n / 2, f, h2, Or.inr (Or.inl ⟨hOM', hNOM'⟩), hcompat⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj
