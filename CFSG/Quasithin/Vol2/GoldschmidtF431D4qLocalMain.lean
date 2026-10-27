module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdIso
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGLie
public import CFSG.LieType.BorelTits.AllModels
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructAut

public section

namespace CFSG.Quasithin.H13.F431.D4q.Local

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.CentralExt.GriessNative
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.Lift
  CFSG.Quasithin.H13.F431.D4q.Struct

set_option linter.unusedSectionVars false


section Generic

variable {D C : Type} [Group D] [Group C]

theorem sup_eq_top_of_map (ε : D ≃* C) {P Q : Subgroup D}
    (h : P.map ε.toMonoidHom ⊔ Q.map ε.toMonoidHom = ⊤) : P ⊔ Q = ⊤ := by
  apply Subgroup.map_injective (f := ε.toMonoidHom) ε.injective
  rw [Subgroup.map_sup, h, Subgroup.map_top_of_surjective _ ε.surjective]

theorem le_of_map_le (ε : D ≃* C) {P Q : Subgroup D}
    (h : P.map ε.toMonoidHom ≤ Q.map ε.toMonoidHom) : P ≤ Q :=
  (Subgroup.map_le_map_iff_of_injective (f := ε.toMonoidHom) ε.injective).1 h

theorem center_eq_bot_of_equiv (ε : D ≃* C) (h : Subgroup.center C = ⊥) :
    Subgroup.center D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : ε x ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := ε.surjective y
    rw [← map_mul, ← map_mul, hx y']
  rw [h, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (ε.injective (h1.trans (map_one ε).symm))

end Generic

section Index

variable {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)

theorem not_two_dvd_index_iK (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)
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

section Main

@[expose] def Std3D4 (f : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f)),
    ∃ (V L Zd Qd Xd Yd : Subgroup (Cm σ)) (v nr na : Cm σ) (q n : ℕ),
      StdTwo (Cm σ) (Ust σ) (Pst0 σ) (Pst1 σ) (Loc.zC σ) (Loc.tC σ (sigma_cube σ hK hσ)) ∧
      StdLoc (Cm σ) (Ust σ) (Loc.zC σ) (Loc.tC σ (sigma_cube σ hK hσ)) V L ∧
      StdOrient (Cm σ) (Ust σ) (Pst0 σ) (Pst1 σ) (Loc.zC σ) (Loc.tC σ (sigma_cube σ hK hσ))
        v nr na Zd Qd Xd Yd q n

theorem f431Local_d4q (f : ℕ) (hStd : Std3D4 f) : F431Local .trialityD4 0 f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E hodd
  obtain ⟨-, hX⟩ := chevalley_of_lieModel hD (by decide)
  obtain ⟨K, hF, hFin, σ, hf, hK, hσ, ε, hU, hP⟩ := exists_std_iso hX E
  have : CharP K 2 := charP_two_of_card hK
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite D := Finite.of_injective ε ε.injective
  obtain ⟨V, L, Zd, Qd, Xd, Yd, v, nr, na, q, n, S1, S2, S3⟩ := hStd K σ hK hσ
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσ
  have hcen : Subgroup.center D = ⊥ := center_eq_bot_of_equiv ε (center_eq_bot σ)
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := fun a b h =>
    conj_injective_of_center hcen h
  have hsup : E.P1 ⊔ E.P2 = ⊤ := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact sup_eq_top_of_map ε (by rw [h1, h2]; exact Pst_sup σ hf hK hσ)
    · exact sup_eq_top_of_map ε (by rw [h1, h2, sup_comm]; exact Pst_sup σ hf hK hσ)
  have hgen := E.toLieAmalgamExt.range_conj_le_K hsup
  have hodd' := not_two_dvd_index_iK E.toLieAmalgamExt hgen hcen hodd
  have hBT : CFSG.LieType.BorelTits.Holds D 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel hD (by decide)
  have habove : ∀ P : Subgroup D, Subgroup.normalizer (E.TD : Set D) ≤ P → P ≠ ⊤ →
      P ≤ E.P1 ∨ P ≤ E.P2 := by
    intro P hNP hPtop
    have h1 : Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ≤
        P.map ε.toMonoidHom := by
      rw [← hU, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hNP
    have h2 : P.map ε.toMonoidHom ≠ ⊤ := fun h =>
      hPtop (by
        apply Subgroup.map_injective (f := ε.toMonoidHom) ε.injective
        rw [h, Subgroup.map_top_of_surjective _ ε.surjective])
    rcases hS.above _ h1 h2 with h | h
    · rcases hP with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Or.inl (le_of_map_le ε (by rw [h1]; exact h))
      · exact Or.inr (le_of_map_le ε (by rw [h2]; exact h))
    · rcases hP with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact Or.inr (le_of_map_le ε (by rw [h2]; exact h))
      · exact Or.inl (le_of_map_le ε (by rw [h1]; exact h))
  have hag : ∀ E' : Subgroup ↥E.K,
      IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
      Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨ Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2 :=
    fun E' hE' => AG.ag_of_borelTits E.toLieAmalgamExt hinj hgen hBT habove hE'
  obtain ⟨hyp1, hyp2⟩ := hyps.2.2.2.1 (by decide)
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact f431Local_of_std E ε S1 S2 S3 (Or.inl ⟨rfl, rfl⟩) h1 h2 hU hcen hgen hodd' hag hyp1 hyp2
  · exact f431Local_of_std E ε S1 S2 S3 (Or.inr ⟨rfl, rfl⟩) h2 h1 hU hcen hgen hodd' hag hyp1 hyp2

end Main

end CFSG.Quasithin.H13.F431.D4q.Local
