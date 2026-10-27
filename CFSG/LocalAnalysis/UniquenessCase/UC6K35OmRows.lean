module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_sylow_coe_eq [Fact p.Prime] {S : Subgroup X} (hS : IsSylowOf p S ⊤) :
    ∃ U : Sylow p X, (U : Subgroup X) = S := by
  rw [isSylowOf_iff] at hS
  obtain ⟨-, hSp, hnd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hnd
  exact ⟨hSp.toSylow hnd, rfl⟩

theorem card_le_sq_of_omega [Fact p.Prime] {S B : Subgroup X} (hS : IsSylowOf p S ⊤)
    (hBcard : Nat.card B = p ^ 2) (hΩ : ∀ x ∈ S, x ^ p = 1 → x ∈ B) {E : Subgroup X}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  obtain ⟨T, hT, hET⟩ := UC6.exists_isSylowOf_ge (le_top : E ≤ ⊤) hE.isPGroup
  obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hT
  have hle : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj k⁻¹).toMonoidHom x = k⁻¹ * x * k := by
      simp [MulAut.conj_apply]
    rw [h1]
    refine hΩ _ ((hk x).1 (hET hx)) ?_
    have h2 := map_pow (MulAut.conj k⁻¹) x p
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv] at h2
    rw [← h2, hE.2 x hx, mul_one, inv_mul_cancel]
  have h := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hBcard] at h

theorem false_of_lieModel_psu3 [hp : Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (hU : LieModel X .PSU 3 p n) {S B : Subgroup X} (hS : IsSylowOf p S ⊤)
    (hBcard : Nat.card B = p ^ 2) (hΩ : ∀ x ∈ S, x ^ p = 1 → x ∈ B) : False := by
  have hst := hU.statedClassicalModel (by decide)
  obtain ⟨-, hf, -, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu hst
  have : CharP K p := CFSG.AGLEmbedding.UnitaryModel.charP_of_card hp.out hK
  obtain ⟨S', hS'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨U, rfl⟩ := exists_sylow_coe_eq hS
  obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_equiv_map_eq e U S'
  have hU' : (U : Subgroup X).map e'.toMonoidHom =
      CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ := he'.trans hS'
  have hUB : (U : Subgroup X) ≤ B := by
    intro x hx
    refine hΩ x hx ?_
    have h1 : e' x ∈ CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ := by
      rw [← hU']
      exact ⟨x, hx, rfl⟩
    have h2 := CFSG.AGLEmbedding.UnitaryModel.pow_prime_of_mem_rootGroup J hJ hp.out hp2 h1
    rw [← map_pow, ← map_one e'] at h2
    exact e'.injective h2
  have hcard : Nat.card (U : Subgroup X) = p ^ (3 * n) := by
    rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hU']
    exact CFSG.AGLEmbedding.UnitaryModel.card_rootGroup_eq J hJ hK hfix
  have h1 := Subgroup.card_le_of_le hUB
  rw [hcard, hBcard] at h1
  have h2 : p ^ 2 < p ^ (3 * n) := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  omega

end CFSG.LocalAnalysis.UniquenessCase.UCK
