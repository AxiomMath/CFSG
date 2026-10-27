module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import Mathlib.RingTheory.RootsOfUnity.Basic

public section

namespace CFSG.StandardType

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

private theorem card_le_pow_of_diagonal_ratios
    {F A : Type} [Field F] [Finite F] {p d : ℕ} [NeZero p] (hd : 0 < d)
    (δ : A → Fin d → F) (hne : ∀ a i, δ a i ≠ 0)
    (hpow : ∀ a i j, (δ a i * (δ a j)⁻¹) ^ p = 1)
    (hinj : ∀ a b, (∀ i j, δ a i * (δ a j)⁻¹ = δ b i * (δ b j)⁻¹) → a = b) :
    Nat.card A ≤ p ^ (d - 1) := by
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  let I := {i : Fin d // i ≠ i₀}
  let ρ : A → I → rootsOfUnity p F := fun a i =>
    ⟨Units.mk0 (δ a i * (δ a i₀)⁻¹) (mul_ne_zero (hne a i) (inv_ne_zero (hne a i₀))),
      by
        rw [mem_rootsOfUnity]
        apply Units.ext
        simpa using hpow a i i₀⟩
  have hρ : Function.Injective ρ := by
    intro a b hab
    have hrat : ∀ i, δ a i * (δ a i₀)⁻¹ = δ b i * (δ b i₀)⁻¹ := by
      intro i
      by_cases hi : i = i₀
      · rw [hi, mul_inv_cancel₀ (hne a i₀), mul_inv_cancel₀ (hne b i₀)]
      · exact congrArg (fun x : rootsOfUnity p F => ((x : Fˣ) : F))
          (congrFun hab ⟨i, hi⟩)
    apply hinj a b
    intro i j
    calc δ a i * (δ a j)⁻¹ =
        (δ a i * (δ a i₀)⁻¹) * (δ a j * (δ a i₀)⁻¹)⁻¹ := by
          field_simp [hne a j, hne a i₀]
      _ = (δ b i * (δ b i₀)⁻¹) * (δ b j * (δ b i₀)⁻¹)⁻¹ := by
          rw [hrat i, hrat j]
      _ = δ b i * (δ b j)⁻¹ := by field_simp [hne b j, hne b i₀]
  have hI : Nat.card I = d - 1 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {i : Fin d // ¬ i = i₀} = d - 1
    rw [Fintype.card_subtype_compl (fun i : Fin d => i = i₀),
      Fintype.card_fin, Fintype.card_subtype_eq]
  calc Nat.card A ≤ Nat.card (I → rootsOfUnity p F) := Nat.card_le_card_of_injective ρ hρ
    _ = Nat.card (rootsOfUnity p F) ^ (d - 1) := by rw [Nat.card_fun, hI]
    _ ≤ p ^ (d - 1) := Nat.pow_le_pow_left (card_rootsOfUnity F p) _

namespace TypeANbrDvd

theorem card_le_of_actsDiag
    {F H : Type} [Field F] [Finite F] [Group H] {p d : ℕ} [NeZero p] (hd : 0 < d)
    {φ : SpecialLinearGroup (Fin d) F →* H} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d F)
    (A : Subgroup (MulAut H)) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → F, ActsDiag φ a t) :
    Nat.card A ≤ p ^ (d - 1) := by
  classical
  choose δ hδ using fun a : A => hdiag a a.2
  apply card_le_pow_of_diagonal_ratios hd δ (fun a i => (hδ a).ne_zero i)
    (fun a i j => (hδ a).ratio_pow hφker (hAp a a.2) i j)
  intro a b hrat
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  apply ((hδ a).mul (hδ b).inv).eq_one hd hφs
  intro i j
  have h := hrat i j
  field_simp [(hδ a).ne_zero j, (hδ b).ne_zero j,
    (hδ b).ne_zero i] at h ⊢
  linear_combination h

end TypeANbrDvd

namespace LineU

theorem card_le_of_actsDiagU
    {F H : Type} [Field F] [Finite F] [Group H] {p d f : ℕ} [NeZero p]
    (hF : UnitaryFieldData 2 f F) (hd : 3 ≤ d)
    {φ : ↥(unitarySU 2 f F d) →* H} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 f F d), φ g = 1 →
      ∃ c : F, ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = diagonal (fun _ => c))
    (A : Subgroup (MulAut H)) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → F, ActsDiagU φ a t) :
    Nat.card A ≤ p ^ (d - 1) := by
  classical
  choose δ hδ using fun a : A => hdiag a a.2
  apply card_le_pow_of_diagonal_ratios (by omega : 0 < d) δ
    (fun a i => (hδ a).ne_zero i)
    (fun a i j => (hδ a).ratio_pow hF hd hφker (hAp a a.2) i j)
  intro a b hrat
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  apply ((hδ a).mul (hδ b).inv).eq_one_of_const hφs ⟨0, by omega⟩
  intro i j
  have h := hrat i j
  field_simp [(hδ a).ne_zero j, (hδ b).ne_zero j,
    (hδ b).ne_zero i] at h ⊢
  linear_combination h

end LineU

end CFSG.StandardType

end
