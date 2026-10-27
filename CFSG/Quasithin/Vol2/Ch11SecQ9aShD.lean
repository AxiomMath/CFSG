module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShC
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.QuasithinUnique.Setup.X6 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K]

theorem stabilizer_inf_eq_borel :
    stabilizer 2 K (flag 2 K 1) ⊓ stabilizer 2 K (flag 2 K 2) = borelSubgroup 2 K := by
  ext g
  rw [mem_borelSubgroup, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 1 le_rfl (by norm_num), h 2 (by norm_num) le_rfl⟩

variable [Finite K] [CharP K 2]

theorem projStabilizer_inf_eq :
    projStabilizer 2 K (flag 2 K 1) ⊓ projStabilizer 2 K (flag 2 K 2) =
      Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnipotent 2 (by norm_num), projBorel, ← stabilizer_inf_eq_borel,
    Subgroup.map_inf_eq _ _ _ proj_injective_charTwo]
  rfl

theorem card_normalizer_projUnipotent (hK : Nat.card K = 4) :
    Nat.card ↥(Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K)))) =
      Nat.card ↥(projUnipotent 2 K) * 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnipotent 2 (by norm_num), projBorel, projUnipotent,
    Subgroup.card_map_of_injective proj_injective_charTwo,
    Subgroup.card_map_of_injective proj_injective_charTwo, card_borelSubgroup, card_unipotent, hK]
  norm_num

omit [Finite K] [CharP K 2]

theorem exists_borelPair_sp4 {Q : Type} [Group Q] [Finite Q]
    (hQ : StatedClassicalModel Q .PSp 2 2 2) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : ∃ B : Fin 2 → Subgroup Q, BorelPair S B := by
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q 2 2 2 hQ
  obtain ⟨K, _, _, _, φ, hK, hφ, hres, -⟩ := even_rank_two_residual_symplectic hQ hS
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four (by omega)
  have hB := fun j => dInf_projStabilizer_ne_bot hK4 φ j
  have hpp := parabPair_of_residual hS hres hB
  have hS' : S = (projUnipotent 2 K).map φ.symm.toMonoidHom := by
    rw [← hφ]
    ext x
    simp
  have hinf : (projStabilizer 2 K (flag 2 K 1)).map φ.symm.toMonoidHom ⊓
      (projStabilizer 2 K (flag 2 K 2)).map φ.symm.toMonoidHom ≤
        Subgroup.normalizer (S : Set Q) := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.symm.injective, projStabilizer_inf_eq, hS',
      ← Subgroup.map_equiv_normalizer_eq]
  have hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective φ.symm.injective, card_normalizer_projUnipotent hK']
  exact ⟨_, borelPair_of_residual hS hres hB
    (fun X _ _ hX1 => (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1)
    hpp.top_not hinf hcard⟩

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
