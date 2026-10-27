module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

open CFSG.QuasithinUnique

namespace CFSG.Quasithin.SBc5S8

theorem card_perm8 : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem card_alt8 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_sylow8 {T : Subgroup (Equiv.Perm (Fin 8))} (hT : IsSylowTwoOf T ⊤) :
    Nat.card ↥T = 128 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT.2.1
  have hodd : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have h := Subgroup.card_mul_index T
  rw [card_perm8, hn] at h
  have hle : n ≤ 7 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 8 ∣ 40320 := (pow_dvd_pow 2 hlt).trans (Dvd.intro _ h)
    norm_num at h1
  rw [hn]
  interval_cases n <;> omega

theorem isSylowTwoOf_inf_alt {T : Subgroup (Equiv.Perm (Fin 8))} (hT : IsSylowTwoOf T ⊤) :
    IsSylowTwoOf (T ⊓ alternatingGroup (Fin 8)) (alternatingGroup (Fin 8)) := by
  have hcard := card_sylow8 hT
  refine ⟨inf_le_right, hT.2.1.to_inf_left, ?_⟩
  change ¬ 2 ∣ (T ⊓ alternatingGroup (Fin 8)).relIndex (alternatingGroup (Fin 8))
  have hTA : ¬ T ≤ alternatingGroup (Fin 8) := by
    intro h
    have := Subgroup.card_dvd_of_le h
    rw [hcard, card_alt8] at this
    norm_num at this
  have h2 : (alternatingGroup (Fin 8)).relIndex T = 2 := by
    have hd : (alternatingGroup (Fin 8)).relIndex T ∣ (alternatingGroup (Fin 8)).index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    rw [alternatingGroup.index_eq_two] at hd
    have hne : (alternatingGroup (Fin 8)).relIndex T ≠ 1 := fun h => hTA (Subgroup.relIndex_eq_one.1 h)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h hne
    · exact h
  have hc1 := Subgroup.relIndex_mul_card (T ⊓ alternatingGroup (Fin 8)) T
  rw [inf_eq_left.2 (inf_le_left : T ⊓ alternatingGroup (Fin 8) ≤ T), Subgroup.inf_relIndex_left,
    h2, hcard] at hc1
  have hn64 : Nat.card ↥(T ⊓ alternatingGroup (Fin 8)) = 64 := by omega
  have hc2 := Subgroup.relIndex_mul_card (T ⊓ alternatingGroup (Fin 8)) (alternatingGroup (Fin 8))
  rw [inf_eq_left.2 (inf_le_right : T ⊓ alternatingGroup (Fin 8) ≤ alternatingGroup (Fin 8)), card_alt8,
    hn64] at hc2
  omega

end CFSG.Quasithin.SBc5S8
