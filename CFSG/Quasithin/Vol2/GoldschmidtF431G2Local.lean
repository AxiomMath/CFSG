module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelPar
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGLie
public import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.Sec53F.G2 CFSG.Quasithin.H13.Sec53F
  CFSG.LieType.BorelTits

section Aux

theorem map_conj_inv_map {Cg : Type} [Group Cg] (S : Subgroup Cg) (c : Cg) :
    (S.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = S := by
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem iK_eq_innK {D : Type} [Group D] (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    iK A hgen = AG.innK A hgen := MonoidHom.ext fun _ => rfl

theorem not_two_dvd_index_range {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
    (hodd : Odd (Nat.card ↥A.K / Nat.card D)) : ¬ 2 ∣ (iK A hgen).range.index := by
  have hι := iK_injective A hgen hcen
  have hfin : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) DFunLike.coe_injective
  have hK : Finite ↥A.K := inferInstance
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


theorem f431Local_g2_of_std {f : ℕ} (hf : 2 ≤ f)
    (hstd : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∃ (z t v nr na : ↥(adjointGroup Tag.G2 K))
        (V L Zd Qd Xd Yd : Subgroup ↥(adjointGroup Tag.G2 K)),
        StdTwo ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K) (Pmin K ⟨1, by decide⟩)
          (Pmin K ⟨0, by decide⟩) z t ∧
        StdLoc ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K) z t V L ∧
        StdOrient ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K) (Pmin K ⟨1, by decide⟩)
          (Pmin K ⟨0, by decide⟩) z t v nr na Zd Qd Xd Yd (Nat.card K) 2) :
    F431Local .G2 0 f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E hodd
  obtain ⟨-, K, _, _, _, hKcard, ⟨ε₀⟩⟩ := g2_model_data hD
  have hfin : Finite D := (f431ModelFacts_g2 f D hD).1
  have hcen : Subgroup.center D = ⊥ := (f431ModelFacts_g2 f D hD).2
  have hgen := f431Generation_g2 f D hD E.toLieAmalgamExt
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := conj_injective_of_center hcen
  have hfinC : Finite ↥(adjointGroup Tag.G2 K) := by
    have : Finite (ModGL Tag.G2 K) := finite_modGL
    infer_instance
  have YS := g2_yamStd hKcard hf
  obtain ⟨c, hT, hP⟩ := YS.pair ε₀ E.yam
  let ε : D ≃* ↥(adjointGroup Tag.G2 K) := ε₀.trans (MulAut.conj c⁻¹)
  have hε : ∀ S : Subgroup D, S.map ε.toMonoidHom = (S.map ε₀.toMonoidHom).map
      (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  have hU : E.TD.map ε.toMonoidHom = posUnipotentSub Tag.G2 K := by
    rw [hε, hT, map_conj_inv_map]
  have hodd' := not_two_dvd_index_range E.toLieAmalgamExt hgen hcen hodd
  have hyp := hyps.2.2.2.1 (by simp)
  have hBT : Holds D 2 := holds_of_lieModel hD (by decide)
  obtain ⟨z, t, v, nr, na, V, L, Zd, Qd, Xd, Yd, S1, S2, S3⟩ := hstd K hKcard
  have hmapε : ∀ (S : Subgroup D) (S' : Subgroup ↥(adjointGroup Tag.G2 K)),
      S.map ε₀.toMonoidHom = S'.map (MulAut.conj c).toMonoidHom → S.map ε.toMonoidHom = S' :=
    fun S S' h => by rw [hε, h, map_conj_inv_map]
  have fin2 : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by decide
  have hne01 : Setup.X6.g2Index 0 ≠ Setup.X6.g2Index 1 := fun h =>
    absurd (Setup.X6.g2Index_injective h) (by decide)
  have hidx : (Setup.X6.g2Index 0 = ⟨0, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨1, by decide⟩) ∨
      (Setup.X6.g2Index 0 = ⟨1, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨0, by decide⟩) := by
    rcases fin2 (Setup.X6.g2Index 0) with h0 | h0 <;> rcases fin2 (Setup.X6.g2Index 1) with h1 | h1
    · exact absurd (h0.trans h1.symm) hne01
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hne01
  have finish : ∀ (Q Q' : Subgroup D), ((Q = E.P1 ∧ Q' = E.P2) ∨ (Q = E.P2 ∧ Q' = E.P1)) →
      Q.map ε.toMonoidHom = Pmin K ⟨1, by decide⟩ → Q'.map ε.toMonoidHom = Pmin K ⟨0, by decide⟩ →
      (∀ B : Subgroup ↥(adjointGroup Tag.G2 K),
        Subgroup.normalizer (posUnipotentSub Tag.G2 K : Set ↥(adjointGroup Tag.G2 K)) ≤ B →
        B ≠ ⊤ → B ≤ Pmin K ⟨1, by decide⟩ ∨ B ≤ Pmin K ⟨0, by decide⟩) →
      ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
    intro Q Q' hQ hQP hQP' habove'
    have hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
        Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨
          Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2 := by
      intro E' hE'
      rw [iK_eq_innK] at hE'
      refine AG.ag_of_borelTits E.toLieAmalgamExt hinj hgen hBT ?_ hE'
      intro X hX hne
      have := above_of_std E.toLieAmalgamExt ε habove' hQP hQP' hU X hX hne
      rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
    exact f431Local_of_std E ε S1 S2 S3 hQ hQP hQP' hU hcen hgen hodd' hag hyp.1 hyp.2
  have habove := YS.above
  rcases hidx with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    exact finish E.P2 E.P1 (Or.inr ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e1]; exact h2)) (hmapε _ _ (by rw [← e0]; exact h1))
      (fun B hB hB' => by
        have := habove B hB hB'
        rw [e0, e1] at this
        exact this.symm)
  ·
    exact finish E.P1 E.P2 (Or.inl ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e1]; exact h1)) (hmapε _ _ (by rw [← e0]; exact h2))
      (fun B hB hB' => by
        have := habove B hB hB'
        rw [e0, e1] at this
        exact this.symm)
  ·
    exact finish E.P1 E.P2 (Or.inl ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e0]; exact h1)) (hmapε _ _ (by rw [← e1]; exact h2))
      (fun B hB hB' => by
        have := habove B hB hB'
        rw [e0, e1] at this
        exact this)
  ·
    exact finish E.P2 E.P1 (Or.inr ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e0]; exact h2)) (hmapε _ _ (by rw [← e1]; exact h1))
      (fun B hB hB' => by
        have := habove B hB hB'
        rw [e0, e1] at this
        exact this)

end Std

end CFSG.Quasithin.H13.F431.G2
