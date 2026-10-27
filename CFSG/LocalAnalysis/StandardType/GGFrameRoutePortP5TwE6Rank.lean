module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortOmegaSym
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortSUSym
public import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG.Assembly

private theorem largeEvenRawDatum_label_eq {lab lab₀ : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q)
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → lab = lab₀) :
    lab = lab₀ := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals
    first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h; exact hQ _ _ _ hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h; exact hQ _ _ _ hq)

theorem rank3Witness_cover_of_marking_twA5 {J : Type} [Group J]
    (hM : LargeEvenMarking J fun lab _ _ _ _ _ => lab = ⟨.twA, 5, 1⟩)
    (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J₁) : Rank3Witness J₁ 3 := by
  obtain ⟨hperf, lab, -, hraw⟩ := hM
  have hlab : lab = ⟨.twA, 5, 1⟩ :=
    largeEvenRawDatum_label_eq hraw fun R _ I F hq => hq.2.2.choose_spec
  rw [hlab] at hraw
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hKf, hKfin, hK, hs, hna, θ, -⟩ := hraw
  have hK' : Nat.card K = 4 := by simpa using hK
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) = ⊥ :=
    @TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative _ _ hs fun hc => by
      obtain ⟨a, b, hab⟩ := hna
      exact hab (hc.is_comm.comm a b)
  exact Rank3Witness.of_cover_centerQuot hperf θ
    (rank3SymGens_largeEvenProjSU_six hK' hZ) J₁ π hπ hker

theorem rank3Witness_cover_of_marking_twD5 {J : Type} [Group J]
    (hM : LargeEvenMarking J fun lab _ _ _ _ _ => lab = ⟨.twD, 5, 1⟩)
    (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J₁) : Rank3Witness J₁ 4 := by
  obtain ⟨hperf, lab, -, hraw⟩ := hM
  have hlab : lab = ⟨.twD, 5, 1⟩ :=
    largeEvenRawDatum_label_eq hraw fun R _ I F hq => hq.2.2.choose_spec
  subst lab
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  split_ifs at hraw
  · omega
  · omega
  · obtain ⟨K, hKf, hKfin, hK, b, c, hbc, -, -, θ, -⟩ := hraw
    have hK' : Nat.card K = 2 := by simpa using hK
    exact Rank3Witness.of_cover_centerQuot hperf θ
      (rank3SymGens_largeEvenProjOmegaTenMinus hK' hbc) J₁ π hπ hker

end CFSG.StandardType.FrameRoute.TwE6Model

end
