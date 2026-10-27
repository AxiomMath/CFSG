module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Chev
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LUSa
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

theorem three_dvd_card_ON : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
  rw [CFSG.Sporadic.ON.card_ON_eq]
  norm_num

theorem noA5ONAt_of_lie {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : ValidLieTypeIndex) (h2 : lieIndexChar idx.1 ≠ 2)
    (h5 : lieIndexChar idx.1 ≠ 5) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (β : MulAut S) (hβ : β ^ 3 = 1) : NoA5ONAt β :=
  noA5ONAt_of_data (fun J hJ => (lieComp_holds S hs hna idx he β hβ J hJ).1)
    (not_isChevSimple_alt5 lieOrderBridge_holds h2 h5) (not_isChevSimple_ON lieOrderBridge_holds)
    three_dvd_card_ON

theorem rowOf427_of_lie {X : Type} [Group X] (idx : ValidLieTypeIndex)
    (h2 : lieIndexChar idx.1 ≠ 2) (h5 : lieIndexChar idx.1 ≠ 5)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)) : RowOf427 X := by
  intro S _ _ hs hna ⟨eS⟩
  obtain ⟨eX⟩ := hX
  refine row427_of_noA5ON fun T _ _ ⟨eT⟩ τ hτ => ?_
  obtain ⟨hsT, hnaT⟩ := simple_nonab_of_mulEquiv eT hs hna
  exact noA5ONAt_of_lie hsT hnaT idx h2 h5 ⟨(eT.trans eS).trans eX⟩ τ hτ

theorem kH1_three (hr : (LieTypeIndex.reeG2 1).Valid) :
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group :=
  rowOf427_of_lie ⟨_, hr⟩ (by simp [lieIndexChar]) (by simp [lieIndexChar]) ⟨MulEquiv.refl _⟩

theorem kH1_nine_SL3 (e : ℕ) (he : 1 ≤ e) (_ : e ≤ 3) : RowOf427 (projSL 3 (GaloisField 3 e)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.A 2 ⟨3, e, Fact.out, he⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      have : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
      omega
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]) (by simp [lieIndexChar])
    ⟨(Census.typeAGroupEquivProjSL 2 ⟨3, e, Fact.out, he⟩ hv).symm⟩

theorem kH1_nine_SU3 (e : ℕ) (he : 1 ≤ e) (_ : e ≤ 3) : RowOf427 (projSU 3 3 e) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.twistedA 2 ⟨3, e, Fact.out, he⟩).Valid :=
    valid_twistedA le_rfl fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      exact Nat.le_self_pow (by omega) 3
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]) (by simp [lieIndexChar])
    ⟨(Census.typeTwistedAGroupEquivProjSU 2 ⟨3, e, Fact.out, he⟩ hv).symm⟩

theorem kH1_nine_G2 : RowOf427 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group :=
  rowOf427_of_lie g2ThreeIndex (by simp [lieIndexChar, g2ThreeIndex])
    (by simp [lieIndexChar, g2ThreeIndex]) ⟨MulEquiv.refl _⟩

theorem kH1_nine_SL4 : RowOf427 (projSL 4 (GaloisField 3 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.A 3 ⟨3, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]) (by simp [lieIndexChar])
    ⟨(Census.typeAGroupEquivProjSL 3 ⟨3, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩

theorem kH1_nine_SU4 : RowOf427 (projSU 4 3 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.twistedA 3 ⟨3, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_twistedA (by norm_num) (by omega)
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]) (by simp [lieIndexChar])
    ⟨(Census.typeTwistedAGroupEquivProjSU 3 ⟨3, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩

theorem seven_le_of_ne_five {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) : 7 ≤ p := by
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have h6 : p ≠ 6 := by
    rintro rfl
    exact absurd hp (by decide)
  omega

theorem kH1_one_of (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (hp5 : p ≠ 5)
    (h9 : ¬ (p = 3 ∧ e ≤ 2)) : RowOf427 (projSL 2 (GaloisField p e)) := by
  have hq : 7 ≤ p ^ e := by
    have hp := (Fact.out : p.Prime)
    rcases Nat.lt_or_ge p 4 with h | h
    · have hp3 : p = 3 := by
        have := hp.two_le
        omega
      subst hp3
      have he3 : 3 ≤ e := by omega
      calc 7 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he3
    · exact (seven_le_of_ne_five hp (by omega) hp5).trans (Nat.le_self_pow (by omega) p)
  have h9' : p ^ e ≠ 9 := by
    intro h
    have hp := (Fact.out : p.Prime)
    have hp3 : p = 3 := by
      have hdvd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
    subst hp3
    have : e = 2 := by
      have h' : (3 : ℕ) ^ e = 3 ^ 2 := by rw [h]; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h'
    exact h9 ⟨rfl, by omega⟩
  have hv : (LieTypeIndex.A 1 ⟨p, e, Fact.out, he⟩).Valid :=
    valid_A le_rfl (fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      omega) (fun h => absurd h (by omega))
  exact rowOf427_of_lie ⟨_, hv⟩ (by simpa [lieIndexChar] using hp2)
    (by simpa [lieIndexChar] using hp5)
    ⟨(Census.typeAGroupEquivProjSL 1 ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem kH1_two_SL_of_ne_five (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2)
    (hp5 : p ≠ 5) : RowOf427 (projSL 3 (GaloisField p e)) := by
  have hv : (LieTypeIndex.A 2 ⟨p, e, Fact.out, he⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      have := five_le_pow hp Fact.out he
      omega
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]; omega) (by simpa [lieIndexChar] using hp5)
    ⟨(Census.typeAGroupEquivProjSL 2 ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem kH1_two_SU_of_ne_five (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2)
    (hp5 : p ≠ 5) : RowOf427 (projSU 3 p e) := by
  have hv : (LieTypeIndex.twistedA 2 ⟨p, e, Fact.out, he⟩).Valid :=
    valid_twistedA le_rfl fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      have := five_le_pow hp Fact.out he
      omega
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]; omega) (by simpa [lieIndexChar] using hp5)
    ⟨(Census.typeTwistedAGroupEquivProjSU 2 ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem kH1_four_G2_of_ne_five (p : ℕ) [Fact p.Prime] (hp : 3 < p) (q : PrimePower)
    (hqp : q.p = p) (_ : q.exponent = 1) (hq : (LieTypeIndex.G2 q).Valid) (hp5 : p ≠ 5) :
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  rowOf427_of_lie ⟨_, hq⟩ (by simp [lieIndexChar]; omega) (by simp [lieIndexChar]; omega)
    ⟨MulEquiv.refl _⟩

theorem kH1_four_Sp_of_ne_five (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp5 : p ≠ 5) :
    RowOf427 (projSp 2 (GaloisField p 1)) := by
  have hv : (LieTypeIndex.B 2 ⟨p, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_B_two (by simp only [TauCeti.PrimePower.card_def, pow_one]; omega)
      (by simp only [TauCeti.PrimePower.card_def, pow_one]; omega)
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]; omega) (by simpa [lieIndexChar] using hp5)
    ⟨(Sec4.Census.typeB2GroupEquivProjSp ⟨p, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩

theorem kH1_four_SL_of_ne_five (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp5 : p ≠ 5) :
    RowOf427 (projSL 4 (GaloisField p 1)) := by
  have hv : (LieTypeIndex.A 3 ⟨p, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def, pow_one]
      omega
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]; omega) (by simpa [lieIndexChar] using hp5)
    ⟨(Census.typeAGroupEquivProjSL 3 ⟨p, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩

theorem kH1_four_SU_of_ne_five (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp5 : p ≠ 5) :
    RowOf427 (projSU 4 p 1) := by
  have hv : (LieTypeIndex.twistedA 3 ⟨p, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_twistedA (by norm_num) (by omega)
  exact rowOf427_of_lie ⟨_, hv⟩ (by simp [lieIndexChar]; omega) (by simpa [lieIndexChar] using hp5)
    ⟨(Census.typeTwistedAGroupEquivProjSU 3 ⟨p, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
