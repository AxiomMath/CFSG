module

public import CFSG.LocalAnalysis.StandardType.GGEvenLieOrderSl2Arith
public import CFSG.LocalAnalysis.StandardType.GGEvenLieOrderSmallArith
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowCentReduced
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowElem

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

theorem sq_sub_one_dvd_pow_sq_sub_one (a k : ℕ) : a ^ 2 - 1 ∣ (a ^ k) ^ 2 - 1 := by
  have h1 : (a ^ k) ^ 2 = (a ^ 2) ^ k := by ring
  rw [h1]
  simpa using Nat.sub_dvd_pow_sub_pow (a ^ 2) 1 k

section

@[expose] def GGCompFieldAt {G : Type} [Group G] (Q : ℕ) (X : Subgroup G) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markChar lab = 2 ∧ 2 ^ markDeg lab = Q ∧
    lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4 ∧ lab.tag ≠ .twF4der ∧
    GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
    ∃ (R : Type) (_ : Group R), MarkedModel lab R ∧ Nonempty (↥X ⧸ Subgroup.center ↥X ≃* R)

@[expose] def GGCompFieldData {G : Type} [Group G] (q : ℕ) (X : Subgroup G) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ GGCompFieldAt (q ^ m) X) ∨ (q = 2 ∧ (Nat.card ↥X = 360 ∨ Nat.card ↥X = 6048))

theorem ggCompFieldAt_sl2_dvd {G : Type} [Group G] {Q : ℕ} {X : Subgroup G}
    (h : GGCompFieldAt Q X) : Q * (Q ^ 2 - 1) ∣ ggCQ X := by
  obtain ⟨lab, hlab, hc, hdeg, h1, h2, h3, -, R, _, hR, ⟨θ⟩⟩ := h
  have hR2 : LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hR
    rwa [hc] at hR
  have hcq : ggCQ X = Nat.card R := Nat.card_congr θ.toEquiv
  rw [hcq, CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hR2, ← hdeg]
  exact evenLieOrder_sl2_dvd_of_label hlab hc h1 h2 h3

theorem ggCompFieldAt_dvd {G : Type} [Group G] {Q : ℕ} {X : Subgroup G}
    (h : GGCompFieldAt Q X) : Q ^ 2 - 1 ∣ Nat.card ↥X :=
  (Dvd.intro_left Q rfl).trans ((ggCompFieldAt_sl2_dvd h).trans
    (Subgroup.card_quotient_dvd_card (Subgroup.center ↥X)))

theorem ggCompFieldData_dvd {G : Type} [Group G] {q : ℕ} {X : Subgroup G}
    (h : GGCompFieldData q X) {p : ℕ} (hp : p.Prime) (hpq : p ∣ q ^ 2 - 1) :
    p ∣ Nat.card ↥X := by
  rcases h with ⟨m, hm, hQ⟩ | ⟨rfl, hX⟩
  · exact hpq.trans ((sq_sub_one_dvd_pow_sq_sub_one q m).trans (ggCompFieldAt_dvd hQ))
  · have h3 : p ∣ 3 := by simpa using hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    rcases hX with h | h <;> rw [h] <;> norm_num

theorem ggNotExcThreeOrder_of_markedModel {lab : LargeEvenLabel} {R : Type} [Group R]
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2) (hd : 2 ≤ markDeg lab)
    (hd3 : markDeg lab ≤ 3) (h1 : lab.tag ≠ .twB2) (h2 : lab.tag ≠ .twF4)
    (h3 : lab.tag ≠ .twF4der) (hR : MarkedModel lab R) : GGNotExcThreeOrder (Nat.card R) := by
  have hR2 : LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hR
    rwa [hc] at hR
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hR2]
  exact evenLieOrder_notExcThree_of_label hlab hc hd hd3 h1 h2 h3

theorem ggCompFieldAt_notExcThree {G : Type} [Group G] {Q : ℕ} {X : Subgroup G}
    (h : GGCompFieldAt Q X) (hQ : 4 ≤ Q) : GGNotExcThreeOrder (ggCQ X) := by
  have hsl := ggCompFieldAt_sl2_dvd h
  obtain ⟨lab, hlab, hc, hdeg, h1, h2, h3, -, R, _, hR, ⟨θ⟩⟩ := h
  have hd2 : 2 ≤ markDeg lab := by
    by_contra hlt
    have h1 : markDeg lab ≤ 1 := by omega
    have h2 : Q ≤ 2 := by
      rw [← hdeg]
      calc 2 ^ markDeg lab ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    omega
  by_cases h4 : 4 ≤ markDeg lab
  · rw [← hdeg] at hsl
    exact ggNotExcThreeOrder_of_sl2_dvd h4 hsl
  · have hcq : ggCQ X = Nat.card R := Nat.card_congr θ.toEquiv
    rw [hcq]
    exact ggNotExcThreeOrder_of_markedModel hlab hc hd2 (by omega) h1 h2 h3 hR

end

end CFSG.StandardType
