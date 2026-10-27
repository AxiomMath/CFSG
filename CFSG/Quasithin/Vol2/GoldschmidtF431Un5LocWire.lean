module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocWire
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5System

public section

namespace CFSG.Quasithin.H13.F431.Un

set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Datum

@[expose] def Un5StdDatum : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ζ : traceZero (unitaryInvolution F 2 2)) [Fact ((ζ : F) ≠ 0)],
    ∃ (P P' : Subgroup (SU (unitaryInvolution F 2 2) 5 ⧸
        Subgroup.center (SU (unitaryInvolution F 2 2) 5)))
      (z t : SU (unitaryInvolution F 2 2) 5 ⧸ Subgroup.center (SU (unitaryInvolution F 2 2) 5))
      (V4 V Uc R K : Subgroup (SU (unitaryInvolution F 2 2) 5 ⧸
        Subgroup.center (SU (unitaryInvolution F 2 2) 5))),
      ((P = (un5System hF ζ).P₁ ∧ P' = (un5System hF ζ).P₂) ∨
        (P = (un5System hF ζ).P₂ ∧ P' = (un5System hF ζ).P₁)) ∧
      StdTwo _ (un5System hF ζ).U P P' z t ∧ UnStdV _ (un5System hF ζ).U P P' z t V4 ∧
      UnStdLoc _ (un5System hF ζ).U z t V Uc R K

end Datum

section Final


theorem f431Local_psu5_of_std (hStd : Un5StdDatum) : F431Local .PSU 5 2 := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E hodd
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hDfin : Finite D := Finite.of_equiv _ e.toEquiv
  have hU0 := isSylowTwoOf_un5System hF ζ
  obtain ⟨P, P', z, t, V4, V, Uc, R, K, hPP, S1, SV, SL⟩ := hStd F hF ζ
  obtain ⟨e', hTD, hE⟩ := BN.exists_iso_of_yam (un5System hF ζ) hU0 e E.toLieAmalgamExt
  have hcen : Subgroup.center D = ⊥ := BN.center_eq_bot_of_rankTwo (un5System hF ζ) e
  have hgen := BN.range_conj_le_of_rankTwo (un5System hF ζ) hU0 e E.toLieAmalgamExt
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := fun a b h =>
    F45.conj_injective_of_center hcen h
  have hodd' := unOdd_index_iK E.toLieAmalgamExt hgen hcen hodd
  have hU : E.TD.map e'.symm.toMonoidHom = (un5System hF ζ).U := map_equiv_symm_of_eq e' hTD
  have hBT : Holds D 2 := by
    have : Finite (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) F)) :=
      Finite.of_equiv _ (un5Equiv hF).toEquiv
    exact Holds.of_mulEquiv e (Holds.of_mulEquiv (un5Equiv hF).symm
      (holds_statedProj_statedSU hF 5))
  have hab := BN.yamStd (un5System hF ζ) hU0
  have habS : ∀ B : Subgroup (SU (unitaryInvolution F 2 2) 5 ⧸
      Subgroup.center (SU (unitaryInvolution F 2 2) 5)),
      Subgroup.normalizer ((un5System hF ζ).U : Set _) ≤ B → B ≠ ⊤ → B ≤ P ∨ B ≤ P' := by
    intro B h1 h2
    rcases hab.above B h1 h2 with h | h <;> rcases hPP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
  have key : ∀ Q Q' : Subgroup D, ((Q = E.P1 ∧ Q' = E.P2) ∨ (Q = E.P2 ∧ Q' = E.P1)) →
      Q.map e'.symm.toMonoidHom = P → Q'.map e'.symm.toMonoidHom = P' →
      ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
    intro Q Q' hQ hQP hQP'
    have habove := above_of_std E.toLieAmalgamExt e'.symm habS hQP hQP' hU
    have hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
        Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨
          Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2 := fun E' hE' =>
      AG.ag_of_borelTits E.toLieAmalgamExt hinj hgen hBT (fun X hX hne => by
        rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact habove X hX hne
        · exact (habove X hX hne).symm) hE'
    exact f431Local_un_of_std E e'.symm S1 SV SL hQ hQP hQP' hU hcen hgen hodd' hag hyps
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hPP with ⟨hP, hP'⟩ | ⟨hP, hP'⟩
  · exact key E.P1 E.P2 (Or.inl ⟨rfl, rfl⟩) (by rw [map_equiv_symm_of_eq e' h1, hP])
      (by rw [map_equiv_symm_of_eq e' h2, hP'])
  · exact key E.P2 E.P1 (Or.inr ⟨rfl, rfl⟩) (by rw [map_equiv_symm_of_eq e' h2, hP])
      (by rw [map_equiv_symm_of_eq e' h1, hP'])
  · exact key E.P2 E.P1 (Or.inr ⟨rfl, rfl⟩) (by rw [map_equiv_symm_of_eq e' h2, hP])
      (by rw [map_equiv_symm_of_eq e' h1, hP'])
  · exact key E.P1 E.P2 (Or.inl ⟨rfl, rfl⟩) (by rw [map_equiv_symm_of_eq e' h1, hP])
      (by rw [map_equiv_symm_of_eq e' h2, hP'])

end Final

end CFSG.Quasithin.H13.F431.Un
