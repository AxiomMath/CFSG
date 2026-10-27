module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQTwoDFrame_rigid {ι : Type} [Fintype ι] {p : ℕ} [Fact p.Prime]
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    [AddCommGroup V'] [Module (ZMod p) V'] [Finite V']
    (h : ι → V) (f : ι → Module.Dual (ZMod p) V) (h' : ι → V')
    (f' : ι → Module.Dual (ZMod p) V')
    (hpair : ∀ i j, f i (h j) = f' i (h' j))
    (hind' : LinearIndependent (ZMod p) h')
    (hker : ∀ v, (∀ i, f i v = 0) → v = 0) (hker' : ∀ v, (∀ i, f' i v = 0) → v = 0) :
    ∃ Θ : V' ≃ₗ[ZMod p] V, (∀ j, Θ (h' j) = h j) ∧
      ∀ i v, Θ (v - f' i v • h' i) = Θ v - f i (Θ v) • h i := by
  classical
  have hle : ∀ {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Finite W]
      (g : ι → Module.Dual (ZMod p) W), (∀ w, (∀ i, g i w = 0) → w = 0) →
      Module.finrank (ZMod p) W ≤ Fintype.card ι := by
    intro W _ _ _ g hg
    have hf : Function.Injective (LinearMap.pi g) := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      apply hg w
      intro i
      have := congr_fun hw i
      simpa using this
    have := LinearMap.finrank_le_finrank_of_injective hf
    rwa [Module.finrank_fintype_fun_eq_card (ZMod p)] at this
  have hVle : Module.finrank (ZMod p) V ≤ Fintype.card ι := hle f hker
  have hV'le : Module.finrank (ZMod p) V' ≤ Fintype.card ι := hle f' hker'
  have hV'eq : Module.finrank (ZMod p) V' = Fintype.card ι :=
    le_antisymm hV'le hind'.fintype_card_le_finrank
  have hind : LinearIndependent (ZMod p) h := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum' : ∑ j, c j • h' j = 0 := by
      apply hker'
      intro i
      calc f' i (∑ j, c j • h' j)
          = ∑ j, c j • f' i (h' j) := by rw [map_sum]; simp [map_smul]
        _ = ∑ j, c j • f i (h j) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hpair i j]
        _ = f i (∑ j, c j • h j) := by rw [map_sum]; simp [map_smul]
        _ = f i 0 := by rw [hc]
        _ = 0 := by simp
    exact Fintype.linearIndependent_iff.mp hind' c hsum'
  have hVeq : Module.finrank (ZMod p) V = Fintype.card ι :=
    le_antisymm hVle hind.fintype_card_le_finrank
  let B : Module.Basis ι (ZMod p) V :=
    basisOfLinearIndependentOfCardEqFinrank' h hind hVeq.symm
  let B' : Module.Basis ι (ZMod p) V' :=
    basisOfLinearIndependentOfCardEqFinrank' h' hind' hV'eq.symm
  have hB : ⇑B = h := coe_basisOfLinearIndependentOfCardEqFinrank' h hind hVeq.symm
  have hB' : ⇑B' = h' := coe_basisOfLinearIndependentOfCardEqFinrank' h' hind' hV'eq.symm
  let Θ : V' ≃ₗ[ZMod p] V := B'.equiv B (Equiv.refl ι)
  have hΘ : ∀ j, Θ (h' j) = h j := by
    intro j
    rw [← hB', Module.Basis.equiv_apply]
    simp [hB]
  refine ⟨Θ, hΘ, ?_⟩
  intro i v
  let L : V' →ₗ[ZMod p] V := Θ.toLinearMap ∘ₗ (LinearMap.id - (f' i).smulRight (h' i))
  let R : V' →ₗ[ZMod p] V := Θ.toLinearMap - ((f i).comp Θ.toLinearMap).smulRight (h i)
  have hLR : L = R := by
    apply B'.ext
    intro j
    show Θ (B' j - f' i (B' j) • h' i) = Θ (B' j) - f i (Θ (B' j)) • h i
    rw [hB', map_sub, map_smul, hΘ j, hΘ i, hpair i j]
  calc Θ (v - f' i v • h' i) = L v := by simp [L]
    _ = R v := by rw [hLR]
    _ = Θ v - f i (Θ v) • h i := by simp [R]

end CFSG.StandardType.QTwo

end
