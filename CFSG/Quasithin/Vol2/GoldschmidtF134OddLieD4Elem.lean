module

public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels

public section

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

namespace CFSG.Quasithin.H13.NQCore.D4

theorem exists_map_conj_le_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {E : Subgroup X} (hE : IsPGroup p E) (U : Sylow p X) :
    ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ (U : Subgroup X) := by
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P U
  refine ⟨g, ?_⟩
  have h : ((g • P : Sylow p X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  rw [← hg, h]
  exact Subgroup.map_mono hP


theorem exists_isElemAbelian_le_sylow {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) :
    ∃ E : Subgroup X, E ≤ (U : Subgroup X) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ 16 ≤ Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hn, -⟩, hmod⟩ := hX
  have hrank := CFSG.SectionRank.four_le_pRank_of_trialityD4Model (p := 2) (f := n) hn hmod
  obtain ⟨E₀, -, ⟨-, hE₀2⟩, hE₀card⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hrank
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow (IsPGroup.of_card hE₀card) U
  refine ⟨E₀.map (MulAut.conj g).toMonoidHom, hg, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE₀2 y hy, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀card]
    norm_num

end CFSG.Quasithin.H13.NQCore.D4
