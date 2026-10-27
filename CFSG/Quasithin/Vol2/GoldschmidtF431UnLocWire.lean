module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnSystem

public section

namespace CFSG.Quasithin.H13.F431.Un

set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Generic

variable {X D : Type} [Group X] [Group D]

theorem map_equiv_symm_of_eq (e : X ≃* D) {M : Subgroup X} {Q : Subgroup D}
    (h : Q = M.map e.toMonoidHom) : Q.map e.symm.toMonoidHom = M := by
  rw [h, Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [this, Subgroup.map_id]

end Generic

section Index

variable {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)

theorem unOdd_index_iK (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)
    (hcen : Subgroup.center D = ⊥) (hodd : Odd (Nat.card ↥A.K / Nat.card D)) :
    ¬ 2 ∣ (iK A hgen).range.index := by
  have h := Subgroup.card_mul_index (iK A hgen).range
  have hr : Nat.card (iK A hgen).range = Nat.card D :=
    (Nat.card_congr (MonoidHom.ofInjective (iK_injective A hgen hcen)).toEquiv).symm
  rw [hr] at h
  have hpos : 0 < Nat.card D := Nat.card_pos
  have e : (iK A hgen).range.index = Nat.card ↥A.K / Nat.card D := by
    rw [← h, Nat.mul_div_cancel_left _ hpos]
  rw [e]
  exact hodd.not_two_dvd_nat

end Index

section Datum

@[expose] def UnStdDatum (f : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)],
    ∃ (z t : SU (unitaryInvolution F 2 f) 4)
      (V4 V Uc R K : Subgroup (SU (unitaryInvolution F 2 f) 4)),
      StdTwo (SU (unitaryInvolution F 2 f) 4) (unU hF 4) (unSystem hF ζ).P₂ (unSystem hF ζ).P₁ z t ∧
      UnStdV (SU (unitaryInvolution F 2 f) 4) (unU hF 4) (unSystem hF ζ).P₂ (unSystem hF ζ).P₁
        z t V4 ∧
      UnStdLoc (SU (unitaryInvolution F 2 f) 4) (unU hF 4) z t V Uc R K

end Datum

section Final


theorem f431Local_psu4_of_std (f : ℕ) (hStd : UnStdDatum f) : F431Local .PSU 4 f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E hodd
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  have hDfin : Finite D := Finite.of_equiv _ e.toEquiv
  obtain ⟨z, t, V4, V, Uc, R, K, S1, SV, SL⟩ := hStd F hF ζ
  obtain ⟨e', hTD, hP⟩ := BN.exists_iso_of_yam (unSystem hF ζ) (isSylowTwoOf_unU hF) e
    E.toLieAmalgamExt
  have hcen : Subgroup.center D = ⊥ := BN.center_eq_bot_of_rankTwo (unSystem hF ζ) e
  have hgen := BN.range_conj_le_of_rankTwo (unSystem hF ζ) (isSylowTwoOf_unU hF) e
    E.toLieAmalgamExt
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := fun a b h =>
    F45.conj_injective_of_center hcen h
  have hodd' := unOdd_index_iK E.toLieAmalgamExt hgen hcen hodd
  have hU : E.TD.map e'.symm.toMonoidHom = unU hF 4 := map_equiv_symm_of_eq e' hTD
  have hBT : Holds D 2 := by
    have : Finite (StatedProj (StatedSU 4 (2 ^ f) F)) := Finite.of_equiv _ (unEquivProj hF).toEquiv
    exact Holds.of_mulEquiv e (Holds.of_mulEquiv (unEquivProj hF).symm
      (holds_statedProj_statedSU hF 4))
  have hab := BN.yamStd (unSystem hF ζ) (isSylowTwoOf_unU hF)
  have habS : ∀ B : Subgroup (SU (unitaryInvolution F 2 f) 4),
      Subgroup.normalizer (unU hF 4 : Set _) ≤ B → B ≠ ⊤ →
        B ≤ (unSystem hF ζ).P₂ ∨ B ≤ (unSystem hF ζ).P₁ := fun B h1 h2 =>
    (hab.above B h1 h2).symm
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hQP : E.P2.map e'.symm.toMonoidHom = (unSystem hF ζ).P₂ := map_equiv_symm_of_eq e' h2
    have hQP' : E.P1.map e'.symm.toMonoidHom = (unSystem hF ζ).P₁ := map_equiv_symm_of_eq e' h1
    have habove := above_of_std E.toLieAmalgamExt e'.symm habS hQP hQP' hU
    have hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
        Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨
          Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2 := fun E' hE' =>
      AG.ag_of_borelTits E.toLieAmalgamExt hinj hgen hBT
        (fun X hX hne => (habove X hX hne).symm) hE'
    exact f431Local_un_of_std E e'.symm S1 SV SL (Or.inr ⟨rfl, rfl⟩) hQP hQP' hU hcen hgen hodd'
      hag hyps
  · have hQP : E.P1.map e'.symm.toMonoidHom = (unSystem hF ζ).P₂ := map_equiv_symm_of_eq e' h1
    have hQP' : E.P2.map e'.symm.toMonoidHom = (unSystem hF ζ).P₁ := map_equiv_symm_of_eq e' h2
    have habove := above_of_std E.toLieAmalgamExt e'.symm habS hQP hQP' hU
    have hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
        Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨
          Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2 := fun E' hE' =>
      AG.ag_of_borelTits E.toLieAmalgamExt hinj hgen hBT habove hE'
    exact f431Local_un_of_std E e'.symm S1 SV SL (Or.inl ⟨rfl, rfl⟩) hQP hQP' hU hcen hgen hodd'
      hag hyps

end Final

end CFSG.Quasithin.H13.F431.Un
