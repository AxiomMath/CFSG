module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAssembly3
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeHerm
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAlt
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUStd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.Universal.Unitary.Hermitian
public import CFSG.LieType.BorelTits.OrthogonalForm
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary
open LayerCores

private theorem ggA6_SU_core_shape_aux {E : Type} [Field E] [Finite E] [CharP E 2] (f : ℕ)
    (hE : Nat.card E = (2 ^ f) ^ 2) (n : ℕ) (P : Subgroup (GL (Fin n) E))
    (hPU : ∀ A ∈ P, CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution E 2 f)
        (A : Matrix (Fin n) (Fin n) E) * CFSG.LieType.Universal.Unitary.antidiag n * (A : Matrix (Fin n) (Fin n) E) =
        CFSG.LieType.Universal.Unitary.antidiag n)
    (hP : Odd (Nat.card P)) :
    ∃ (β : Type) (S : β → Subgroup (GL (Fin n) E)),
      LayerCores.IsCoreFamily
        (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution E 2 f) n ⊓
          Subgroup.centralizer (P : Set (GL (Fin n) E))) S ∧
      ∀ c, GGA6CharTwoLie ↥(S c) := by
  classical
  let σ : E ≃+* E := unitaryInvolution E 2 f
  have hσσ : ∀ c, σ (σ c) = c := fun c =>
    unitaryInvolution_involutive (K := E) (p := 2) (f := f) hE c
  let adj : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E :=
    fun X => antidiag n * conjTr σ X * antidiag n
  have hJJ : (antidiag n : Matrix (Fin n) (Fin n) E) * antidiag n = 1 :=
    GGOppRadSpU.antidiag_mul_antidiag n
  have hJc : conjTr σ (antidiag n : Matrix (Fin n) (Fin n) E) = antidiag n :=
    GGOppRadSpU.conjTr_antidiag (σ := σ) n
  have hadj : IsInvol adj := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y
      simp only [adj, conjTr_add, Matrix.mul_add, Matrix.add_mul]
    · intro x y
      simp only [adj, conjTr_mul]
      calc antidiag n * (conjTr σ y * conjTr σ x) * antidiag n
          = antidiag n * conjTr σ y * (antidiag n * antidiag n) * conjTr σ x *
              antidiag n := by rw [hJJ]; noncomm_ring
        _ = (antidiag n * conjTr σ y * antidiag n) *
              (antidiag n * conjTr σ x * antidiag n) := by noncomm_ring
    · simp only [adj, conjTr_one, Matrix.mul_one]
      exact hJJ
    · intro x
      simp only [adj, conjTr_mul, hJc, conjTr_conjTr hσσ]
      calc antidiag n * (antidiag n * (x * antidiag n)) * antidiag n
          = (antidiag n * antidiag n) * x * (antidiag n * antidiag n) := by noncomm_ring
        _ = x := by rw [hJJ]; noncomm_ring
  have hU : P ≤ unitaryOf hadj := by
    intro A hA
    rw [mem_unitaryOf]
    simp only [adj]
    calc antidiag n * conjTr σ (A : Matrix (Fin n) (Fin n) E) * antidiag n *
          (A : Matrix (Fin n) (Fin n) E)
        = antidiag n * (conjTr σ (A : Matrix (Fin n) (Fin n) E) * antidiag n *
            (A : Matrix (Fin n) (Fin n) E)) := by noncomm_ring
      _ = antidiag n * antidiag n := by rw [hPU A hA]
      _ = 1 := hJJ
  have hstab : ∀ X : Matrix (Fin n) (Fin n) E,
      (∀ g ∈ P, X * (g : Matrix (Fin n) (Fin n) E) = (g : Matrix (Fin n) (Fin n) E) * X) →
      ∀ g ∈ P, adj X * (g : Matrix (Fin n) (Fin n) E) =
        (g : Matrix (Fin n) (Fin n) E) * adj X :=
    fun X hX g hg => hadj.mul_comm_of_le_unitaryOf hU hX hg
  have hsymd : ∃ Y : Matrix (Fin n) (Fin n) E,
      (∀ g ∈ P, Y * (g : Matrix (Fin n) (Fin n) E) = (g : Matrix (Fin n) (Fin n) E) * Y) ∧
        Y + adj Y = 1 := by
    obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq (K := E) (p := 2) (f := f) hE (map_one σ)
    refine ⟨c • 1, fun g _ => by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one], ?_⟩
    have h1 : adj (c • (1 : Matrix (Fin n) (Fin n) E)) = σ c • 1 := by
      simp only [adj, conjTr_smul, conjTr_one, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hJJ]
    rw [h1, ← add_smul, hc, one_smul]
  have hA : (Nat.card P : E) ≠ 0 := natCast_card_ne_zero_of_odd hP
  have h4 : 4 ≤ Nat.card E := by
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_pow] at hE
      have hcard1 : 1 < Nat.card E := Finite.one_lt_card
      omega
    have hf1 : 1 ≤ f := by omega
    rw [hE]
    have h2 : 2 ≤ 2 ^ f := by
      simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf1
    calc (4 : ℕ) = 2 * 2 := by norm_num
      _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul h2 h2
      _ = (2 ^ f) ^ 2 := by rw [pow_two]
  obtain ⟨β, S, hS, hshape⟩ := CoreShape.exists_coreFamily_adjCent_lie
    CoreShape.hermCoreInputLie_holds CoreShape.altCoreInputLie_holds hA hadj hstab hsymd
    (Or.inl h4)
  have hdet : ∀ g : GL (Fin n) E, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin n) (Fin n) E).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hSdet : ∀ c, S c ≤ adjCent P hadj ⊓ (Matrix.GeneralLinearGroup.det).ker := by
    intro c
    refine le_inf (hS.1 c) ?_
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (hS.2.2.1 c)]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 : LayerCores.IsCoreFamily
      (adjCent P hadj ⊓ (Matrix.GeneralLinearGroup.det).ker) S := hS.mono inf_le_left hSdet
  have hunit : ∀ g : GL (Fin n) E, g ∈ unitaryOf hadj ↔
      conjTr σ (g : Matrix (Fin n) (Fin n) E) * antidiag n *
        (g : Matrix (Fin n) (Fin n) E) = antidiag n := by
    intro g
    rw [mem_unitaryOf]
    simp only [adj]
    constructor
    · intro h
      calc conjTr σ (g : Matrix (Fin n) (Fin n) E) * antidiag n * (g : Matrix (Fin n) (Fin n) E)
          = (antidiag n * antidiag n) * conjTr σ (g : Matrix (Fin n) (Fin n) E) * antidiag n *
              (g : Matrix (Fin n) (Fin n) E) := by rw [hJJ, Matrix.one_mul]
        _ = antidiag n * (antidiag n * conjTr σ (g : Matrix (Fin n) (Fin n) E) * antidiag n *
              (g : Matrix (Fin n) (Fin n) E)) := by noncomm_ring
        _ = antidiag n := by rw [h, Matrix.mul_one]
    · intro h
      calc antidiag n * conjTr σ (g : Matrix (Fin n) (Fin n) E) * antidiag n *
            (g : Matrix (Fin n) (Fin n) E)
          = antidiag n * (conjTr σ (g : Matrix (Fin n) (Fin n) E) * antidiag n *
              (g : Matrix (Fin n) (Fin n) E)) := by noncomm_ring
        _ = antidiag n * antidiag n := by rw [h]
        _ = 1 := hJJ
  have hC : adjCent P hadj ⊓ (Matrix.GeneralLinearGroup.det).ker =
      SU σ n ⊓ Subgroup.centralizer (P : Set (GL (Fin n) E)) := by
    ext g
    simp only [adjCent, Subgroup.mem_inf, mem_SU, hunit g, hdet g]
    constructor
    · rintro ⟨⟨hgc, hgu⟩, hgd⟩
      exact ⟨⟨hgd, hgu⟩, hgc⟩
    · rintro ⟨⟨hgd, hgu⟩, hgc⟩
      exact ⟨⟨hgc, hgu⟩, hgd⟩
  rw [hC] at hS0
  exact ⟨β, S, hS0, hshape⟩

theorem ggA6_shape_SU {E : Type} [Field E] [Finite E] [CharP E 2] (f : ℕ)
    (hE : Nat.card E = (2 ^ f) ^ 2) (n : ℕ) (P : Subgroup (GL (Fin n) E))
    (hPU : ∀ A ∈ P, CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution E 2 f)
        (A : Matrix (Fin n) (Fin n) E) * CFSG.LieType.Universal.Unitary.antidiag n * (A : Matrix (Fin n) (Fin n) E) =
        CFSG.LieType.Universal.Unitary.antidiag n)
    (hP : Odd (Nat.card P)) (J : Subgroup (GL (Fin n) E))
    (hJ : IsComponentOf J (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution E 2 f) n ⊓
      Subgroup.centralizer (P : Set (GL (Fin n) E)))) : GGA6CharTwoLie J := by
  obtain ⟨β, S, hS, hshape⟩ := ggA6_SU_core_shape_aux f hE n P hPU hP
  exact GGA6CharTwoLie_of_isCoreFamily hS hshape hJ

end CFSG.StandardType.A6Red

end
