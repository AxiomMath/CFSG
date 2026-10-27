module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTypeASplitPrime (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def KGLangAxisTorACont (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
        p ^ 2 ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} →
        (GGTypeASplitPrime p lab →
          p ^ ((lab.rank + 1) / p + 2) ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I}) →
        ∃ k e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧
          (∀ α ∈ A, kgInducedAut θ α ∈ I → α k = k) ∧ k * (α₀ k)⁻¹ = e

@[expose] def KGLangAxisTorAInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    GGNbrLangTorTypeALabel p lab → LargeEvenLabelAll lab (KGLangAxisTorACont p lab)

theorem ggMarkingAll_of_labelAll_guard {K : Type*} [Group K] {S : LargeEvenLabel → Prop}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (h : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab (P' lab)) :
    GGMarkingAll (K := K) fun lab R _ I F _ => S lab → P' lab R I F := by
  intro Q hQ
  obtain ⟨hX, lab, hlab, hraw⟩ := hQ
  by_cases hs : S lab
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (h lab hlab hs _ hraw)⟩
    rintro R _ I F ⟨⟨hsi, hna, θ, hθ⟩, hc⟩
    exact ⟨hsi, hna, θ, hθ, fun _ => hc⟩
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hsi, hna, θ, hθ⟩
    exact ⟨hsi, hna, θ, hθ, fun h' => absurd h' hs⟩

theorem ggMarkingAll_kgLangAxisTorA (h : KGLangAxisTorAInput) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (K : Type*) [Group K] :
    GGMarkingAll (K := K) fun lab R _ I F _ =>
      GGNbrLangTorTypeALabel p lab → KGLangAxisTorACont p lab R I F :=
  ggMarkingAll_of_labelAll_guard (S := GGNbrLangTorTypeALabel p) (P' := KGLangAxisTorACont p)
    fun lab hlab hs => h p lab hp hp2 hlab hs

end CFSG.StandardType
