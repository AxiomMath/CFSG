module

public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMLie
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.StandardType.LieLayer

open CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti CFSG.Yardstones.Md0ec50421ce4

theorem exists_modelsLieModel_two_of_valid {S : Type} [Group S] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : S ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Models.LieModel S t n 2 f := by
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hp] at h
    exact ⟨_, _, _, h⟩
  | twistedA r q =>
    have h := CFSG.Models.lieModel_twistedA r q hv e
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := hd
    rw [hc] at h
    exact ⟨_, _, _, h⟩
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hp] at h
      exact ⟨_, _, _, h⟩
    · rw [hp] at h
      exact absurd h.1.2.2.2 (by simp)
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    exact absurd hp hr.2
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hp] at h
    exact ⟨_, _, _, h⟩
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp] at h
    exact ⟨_, _, _, h⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E6, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E7, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E8, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.F4, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [PrimePower.card_def, hp] at h3
    exact ⟨.G2, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.twistedE6, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.trialityD4, 0, q.exponent, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨hp, rfl⟩ e⟩
  | suzuki m =>
    exact ⟨.twistedB2, 0, 2 * m + 1, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e⟩
  | reeG2 m =>
    exact absurd hd (by simp)
  | reeF4 m =>
    exact ⟨.twistedF4, 0, 2 * m + 1, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e⟩
  | tits =>
    exact ⟨.Tits, 0, 1, CFSG.Models.lieModel_of_namesTag (p := 2)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e⟩

theorem modelsLieModel_of_blueprint_classical {S : Type} [Group S] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∈ classicalTags) (h : CFSG.Blueprint.LieModel S t n p f) :
    CFSG.Models.LieModel S t n p f :=
  CFSG.Models.lieModel_of_statedClassicalModel (h.statedClassicalModel ht)

theorem lieTwoModel_of_isChevSimple_two {S : Type} [Group S]
    (h : IsChevSimple 2 S) : LayerCycM.LieTwoModel S := by
  have hcl : (StatedLieTag.PSL) ∈ classicalTags := by decide
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact hi.elim
    · exact Or.inl (exists_modelsLieModel_two_of_valid d hi e)
    · exact hi.elim
  · rcases CFSG.StandardType.ChevTwo.ambiguousChev_two_cases hi with ⟨h5, rfl⟩ | ⟨h6, rfl⟩ |
        ⟨h8, rfl⟩ | ⟨q, hv, hq, rfl⟩ | ⟨q, hv, hq, rfl⟩
    · exact Or.inl ⟨.PSL, 2, 2, modelsLieModel_of_blueprint_classical hcl
        (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e)⟩
    · exact Or.inr (Or.inl (CFSG.Models.lieModel_of_statedClassicalModel
        (CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six
          S ⟨e⟩)))
    · exact Or.inl ⟨.PSL, 4, 1, modelsLieModel_of_blueprint_classical hcl
        (CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e)⟩
    · exact Or.inl ⟨.PSL, 3, 1, modelsLieModel_of_blueprint_classical hcl
        (CFSG.StandardType.ChevTwo.lieModel_psl_three_two_of_A_one q hv hq e)⟩
    · exact Or.inr (Or.inr (CFSG.Models.lieModel_of_statedClassicalModel
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq
          e)))

end CFSG.StandardType.LieLayer

end
