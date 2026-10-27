module

public import CFSG.RankThree.PartOne.SEITZ6.G2BigCell
public import CFSG.RankThree.PartOne.SEITZ2.SL2Line

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K]

theorem sl2Upper_eq_u2 (c : K) : CFSG.LieType.Steinberg.sl2Upper c = u2 c :=
  Subtype.ext (by rw [u2_coe]; rfl)

theorem sl2Lower_eq_l2 (c : K) : CFSG.LieType.Steinberg.sl2Lower c = l2 c :=
  Subtype.ext (by rw [l2_coe]; rfl)

@[expose] def dgl (s : K) (hs : s ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs]⟩

theorem dgl_inv_mul_u2_mul_dgl (s : K) (hs : s ≠ 0) (a : K) :
    (dgl s hs)⁻¹ * u2 a * dgl s hs = u2 (s⁻¹ ^ 2 * a) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, u2_coe, u2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [dgl, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem dgl_inv_mul_l2_mul_dgl (s : K) (hs : s ≠ 0) (b : K) :
    (dgl s hs)⁻¹ * l2 b * dgl s hs = l2 (s ^ 2 * b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, l2_coe, l2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [dgl, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem exists_sq_eq [Finite K] [CharP K 2] (a : K) : ∃ s : K, s ^ 2 = a := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨s, by rw [sq, hs]⟩

theorem full_seven_of_pair [Finite K] [CharP K 2]
    (k : Subfield K) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    (hk4 : 4 ∣ Nat.card k)
    {H : Subgroup (adjointGroup .G2 K)} (g : adjointGroup .G2 K)
    (hH1 : ∀ c ∈ k, xp 7 c ∈ H) (hH2 : ∀ c ∈ k, g * xp 7 c * g⁻¹ ∈ H)
    (hlam : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ∉ k) : Full H 7 := by
  have hne0 : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ≠ 0 := fun h => hlam (h ▸ k.zero_mem)
  obtain ⟨ψ, μ₁, μ₂, h1, h2, hmu, hu, hl⟩ := bigCell g hne0
  obtain ⟨s, hs⟩ := exists_sq_eq (K := K) μ₁⁻¹
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    exact h1 hs.symm
  set D := dgl s hs0 with hD
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (H.comap ψ).comap (MulAut.conj D⁻¹).toMonoidHom with hM
  have hmem : ∀ A, A ∈ M ↔ ψ (D⁻¹ * A * D) ∈ H := fun A => by
    simp [hM]
  have hMu : ∀ c ∈ k, u2 c ∈ M := fun c hc => by
    rw [hmem, hD, dgl_inv_mul_u2_mul_dgl, ← sl2Upper_eq_u2]
    have : s⁻¹ ^ 2 * c = μ₁ * c := by rw [inv_pow, hs, inv_inv]
    rw [this, hu]
    exact hH1 c hc
  have hMl : ∀ c ∈ k, l2 (c * coordAt (rt 10) (g • rootVec .G2 K (rt 7))) ∈ M := fun c hc => by
    rw [hmem, hD, dgl_inv_mul_l2_mul_dgl, ← sl2Lower_eq_l2]
    have : s ^ 2 * (c * coordAt (rt 10) (g • rootVec .G2 K (rt 7))) = μ₂ * c := by
      rw [hs, ← hmu]
      field_simp
    rw [this, hl]
    exact hH2 c hc
  have htop : M = ⊤ := CFSG.RankThree.PartOne.SEITZ2.sl2_eq_top_of_root_lines hd hd2 hK hk4 hlam
    hMu hMl
  intro c
  have hA : D * CFSG.LieType.Steinberg.sl2Upper (μ₁ * c) * D⁻¹ ∈ M := htop ▸ Subgroup.mem_top _
  rw [hmem, show D⁻¹ * (D * CFSG.LieType.Steinberg.sl2Upper (μ₁ * c) * D⁻¹) * D =
    CFSG.LieType.Steinberg.sl2Upper (μ₁ * c) by group, hu] at hA
  exact hA

end CFSG.RankThree.PartOne.SEITZ6
