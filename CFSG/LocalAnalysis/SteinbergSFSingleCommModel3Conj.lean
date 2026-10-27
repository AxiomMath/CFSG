module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Transfer

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup

section Conj

variable {X : Type*} [Group X]

theorem model3Conj_inf_ker {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') (V : Subgroup Y) :
    V ⊓ e.toMonoidHom.ker = ⊥ := by
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective, inf_bot_eq]

theorem model3Conj_odd_ker {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') :
    Odd (Nat.card e.toMonoidHom.ker) := by
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective, Subgroup.card_bot]
  exact odd_one

theorem model3Conj_A_map {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {V : Subgroup Y}
    {q : ℕ} (h : Model3A Y V q) : Model3A Y' (V.map e.toMonoidHom) q :=
  model3A_map e.toMonoidHom (model3Conj_inf_ker e V) h

theorem model3Conj_B_map {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {V : Subgroup Y}
    (h : Model3B Y V) : Model3B Y' (V.map e.toMonoidHom) :=
  model3B_map e.toMonoidHom e.surjective (model3Conj_odd_ker e) (model3Conj_inf_ker e V) h

theorem model3Conj_C_map {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {V : Subgroup Y}
    (h : Model3C Y V) : Model3C Y' (V.map e.toMonoidHom) :=
  model3C_map e.toMonoidHom e.surjective (model3Conj_inf_ker e V) h

theorem model3Conj_sylow_conj [Finite X] (R₀ R : Sylow 2 X) :
    ∃ g : X, (R : Subgroup X) = (R₀ : Subgroup X).map (MulAut.conj g).toMonoidHom := by
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  haveI : Finite (Sylow 2 X) :=
    Finite.of_injective (fun P : Sylow 2 X => (P : Subgroup X)) (fun _ _ h => Sylow.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R₀ R
  exact ⟨g, by rw [← hg]; rfl⟩

theorem model3TildeA_of_sylow [Finite X] {q : ℕ} (R₀ : Sylow 2 X)
    (h : Model3A X (R₀ : Subgroup X) q) : Model3TildeA X q := by
  intro R
  obtain ⟨g, hg⟩ := model3Conj_sylow_conj R₀ R
  rw [hg]
  exact model3Conj_A_map (MulAut.conj g) h

theorem model3TildeB_of_sylow [Finite X] (R₀ : Sylow 2 X)
    (h : Model3B X (R₀ : Subgroup X)) : Model3TildeB X := by
  intro R
  obtain ⟨g, hg⟩ := model3Conj_sylow_conj R₀ R
  rw [hg]
  exact model3Conj_B_map (MulAut.conj g) h

theorem model3TildeC_of_sylow [Finite X] (R₀ : Sylow 2 X)
    (h : Model3C X (R₀ : Subgroup X)) : Model3TildeC X := by
  intro R
  obtain ⟨g, hg⟩ := model3Conj_sylow_conj R₀ R
  rw [hg]
  exact model3Conj_C_map (MulAut.conj g) h

end Conj

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
