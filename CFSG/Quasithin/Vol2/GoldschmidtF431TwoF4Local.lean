module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TS3Std
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Out
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGLie
public import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.Sec53F
  CFSG.LieType.BorelTits

section Aux

theorem map_conj_inv_map_aux {Cg : Type} [Group Cg] (S : Subgroup Cg) (c : Cg) :
    (S.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = S := by
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem iK_eq_innK_aux {D : Type} [Group D] (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) : iK A hgen = AG.innK A hgen :=
  MonoidHom.ext fun _ => rfl

theorem not_two_dvd_index_of_odd {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
    (hodd : Odd (Nat.card ↥A.K / Nat.card D)) : ¬ 2 ∣ (iK A hgen).range.index := by
  have hι := iK_injective A hgen hcen
  have hfin : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) DFunLike.coe_injective
  have hcard : Nat.card (iK A hgen).range = Nat.card D :=
    Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm
  have h1 : (iK A hgen).range.index * Nat.card D = Nat.card ↥A.K := by
    rw [← hcard]
    exact Subgroup.index_mul_card (H := (iK A hgen).range)
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h2 : Nat.card ↥A.K / Nat.card D = (iK A hgen).range.index := by
    rw [← h1, Nat.mul_div_cancel _ hpos]
  rw [h2] at hodd
  exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)

end Aux

section Std


set_option linter.unusedSectionVars false

theorem exists_std_iso_f4 {D : Type} [Group D] {f : ℕ} (hD : LieModel D .twistedF4 0 2 f)
    {G : Type} [Group G] {M1 M2 : Subgroup G} (E : LieExt D M1 M2) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime),
      Nat.card K = 2 ^ (2 * a + 1) ∧ 1 ≤ a ∧
      ∃ ε : D ≃* Gm K a, E.TD.map ε.toMonoidHom = Ug K a ∧
        ((E.P1.map ε.toMonoidHom = Pg K a ⟨0, by decide⟩ ∧
            E.P2.map ε.toMonoidHom = Pg K a ⟨1, by decide⟩) ∨
          (E.P1.map ε.toMonoidHom = Pg K a ⟨1, by decide⟩ ∧
            E.P2.map ε.toMonoidHom = Pg K a ⟨0, by decide⟩)) := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have := finite_gm K a
  have hS : Yam.YamStd (Gm K a) (Ug K a) (Pg K a ⟨0, by decide⟩) (Pg K a ⟨1, by decide⟩) :=
    ReeF4.f4_yamStd ha hK
  obtain ⟨c, hTD, hP⟩ := hS.pair e E.yam
  have hε : ∀ S : Subgroup D, S.map (e.trans (MulAut.conj c⁻¹)).toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  refine ⟨a, K, inferInstance, inferInstance, inferInstance, hK, ha, e.trans (MulAut.conj c⁻¹),
    ?_, ?_⟩
  · rw [hε, hTD, map_conj_inv_map_aux]
  · rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [hε, hε, h1, h2, map_conj_inv_map_aux, map_conj_inv_map_aux]
      exact ⟨rfl, rfl⟩
    · right
      rw [hε, hε, h1, h2, map_conj_inv_map_aux, map_conj_inv_map_aux]
      exact ⟨rfl, rfl⟩

theorem f431Local_twistedF4_of_std (f : ℕ)
    (hstd : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
      (hK : Nat.card K = 2 ^ (2 * a + 1)), 1 ≤ a →
      ∃ V L : Subgroup (Gm K a),
        StdTwo (Gm K a) (Ug K a) (Pg K a ⟨1, by decide⟩) (Pg K a ⟨0, by decide⟩) (zg hK)
          (tg hK) ∧
        StdLoc (Gm K a) (Ug K a) (zg hK) (tg hK) V L ∧
        StdOrient3 (Gm K a) (Pg K a ⟨1, by decide⟩) (Pg K a ⟨0, by decide⟩) (zg hK) (tg hK)) :
    F431Local .twistedF4 0 f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E hodd
  obtain ⟨a, K, _, _, _, hK, ha, ε, hU, hP⟩ := exists_std_iso_f4 hD E
  have := finite_gm K a
  have hmodel := f431ModelFacts_f4 f D hD
  have := hmodel.1
  have hcen := hmodel.2
  have hgen := f431Generation_f4 f D hD E.toLieAmalgamExt
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := conj_injective_of_center hcen
  have hodd' := not_two_dvd_index_of_odd E.toLieAmalgamExt hgen hcen hodd
  have hyp := hyps.2.2.2.1 (by decide)
  have hBT : Holds D 2 := holds_of_lieModel hD (by decide)
  have hS : Yam.YamStd (Gm K a) (Ug K a) (Pg K a ⟨0, by decide⟩) (Pg K a ⟨1, by decide⟩) :=
    ReeF4.f4_yamStd ha hK
  obtain ⟨V, L, S1, S2, S3⟩ := hstd K a hK ha
  have habove' : ∀ B : Subgroup (Gm K a), Subgroup.normalizer (Ug K a : Set (Gm K a)) ≤ B →
      B ≠ ⊤ → B ≤ Pg K a ⟨1, by decide⟩ ∨ B ≤ Pg K a ⟨0, by decide⟩ :=
    fun B hB hB' => (hS.above B hB hB').symm
  have finish : ∀ (Q Q' : Subgroup D), ((Q = E.P1 ∧ Q' = E.P2) ∨ (Q = E.P2 ∧ Q' = E.P1)) →
      Q.map ε.toMonoidHom = Pg K a ⟨1, by decide⟩ → Q'.map ε.toMonoidHom = Pg K a ⟨0, by decide⟩ →
      ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
    intro Q Q' hQ hQP hQP'
    have hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
        Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨
          Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2 := by
      intro E' hE'
      rw [iK_eq_innK_aux] at hE'
      refine AG.ag_of_borelTits E.toLieAmalgamExt hinj hgen hBT ?_ hE'
      intro X hX hne
      have := above_of_std E.toLieAmalgamExt ε habove' hQP hQP' hU X hX hne
      rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
    exact f431Local_of_std3 E ε S1 S2 S3 hQ hQP hQP' hU hcen hgen hodd'
      (commutator_mem_inner_gm ha hK) hag hyp.1 hyp.2
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact finish E.P2 E.P1 (Or.inr ⟨rfl, rfl⟩) h2 h1
  · exact finish E.P1 E.P2 (Or.inl ⟨rfl, rfl⟩) h1 h2

end Std

end CFSG.Quasithin.H13.F431.TwoF4
