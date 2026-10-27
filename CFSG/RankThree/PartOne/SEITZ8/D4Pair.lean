module

public import CFSG.RankThree.PartOne.SEITZ8.D4BigCell
public import CFSG.RankThree.PartOne.SEITZ6.G2Pair

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] [CharP K 2] [Finite K]
  {σ : K →+* K}

theorem full_h_of_pair (hσ : ∀ c, σ (σ (σ c)) = c) (F0 : Subfield (fixedField σ)) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hF : Nat.card (fixedField σ) = Nat.card F0 ^ d)
    (hF4 : 4 ∣ Nat.card F0) {H : Subgroup (twistedGroup σ)} (g : twistedGroup σ)
    (hH1 : ∀ c ∈ F0, psiB σ hσ (sl2Upper c) ∈ H)
    (hH2 : ∀ c ∈ F0, g * psiB σ hσ (sl2Upper c) * g⁻¹ ∈ H)
    (lam : fixedField σ)
    (hlam_eq : (lam : K) =
      coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)))
    (hlam : lam ∉ F0) : ∀ c : fixedField σ, psiB σ hσ (sl2Upper c) ∈ H := by
  have hne0 : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ≠ 0 := by
    rw [← hlam_eq]
    intro h
    exact hlam (by
      have : lam = 0 := Subtype.ext h
      rw [this]
      exact F0.zero_mem)
  obtain ⟨ψ, μ₁, μ₂, h1, h2, hmu, hu, hl⟩ := bigCell_tw hσ g hne0
  have hmu' : μ₁ * μ₂ = lam := Subtype.ext (by rw [hlam_eq, ← hmu]; rfl)
  obtain ⟨s, hs⟩ := exists_sq_eq (K := fixedField σ) μ₁⁻¹
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    exact h1 hs.symm
  set D := dgl s hs0 with hD
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :=
    (H.comap ψ).comap (MulAut.conj D⁻¹).toMonoidHom with hM
  have hmem : ∀ A, A ∈ M ↔ ψ (D⁻¹ * A * D) ∈ H := fun A => by
    simp [hM]
  have hMu : ∀ c ∈ F0, u2 c ∈ M := fun c hc => by
    rw [hmem, hD, dgl_inv_mul_u2_mul_dgl, ← sl2Upper_eq_u2]
    have : s⁻¹ ^ 2 * c = μ₁ * c := by rw [inv_pow, hs, inv_inv]
    rw [this, hu]
    exact hH1 c hc
  have hMl : ∀ c ∈ F0, l2 (c * lam) ∈ M := fun c hc => by
    rw [hmem, hD, dgl_inv_mul_l2_mul_dgl, ← sl2Lower_eq_l2]
    have : s ^ 2 * (c * lam) = μ₂ * c := by
      rw [hs, ← hmu']
      field_simp
    rw [this, hl]
    exact hH2 c hc
  have htop : M = ⊤ :=
    CFSG.RankThree.PartOne.SEITZ2.sl2_eq_top_of_root_lines hd hd2 hF hF4 hlam hMu hMl
  intro c
  have hA : D * sl2Upper (μ₁ * c) * D⁻¹ ∈ M := htop ▸ Subgroup.mem_top _
  rw [hmem, show D⁻¹ * (D * sl2Upper (μ₁ * c) * D⁻¹) * D = sl2Upper (μ₁ * c) by group, hu] at hA
  exact hA

end CFSG.RankThree.PartOne.SEITZ8
