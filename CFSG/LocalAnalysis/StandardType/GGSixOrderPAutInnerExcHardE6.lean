module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.PartOne.KE

section Hard


@[expose] def GGOrdPToralE6RestHard : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → ((p = 3 ∧ 3 ∣ 2 ^ f + 1) ∨ (p = 5 ∧ 5 ∣ 2 ^ f - 1)) →
    (∃ A : Subgroup (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f),
      IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f) p

end Hard

section Adjoint


theorem sylowTorus_or_card_lt_adjointE6 {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (h5 : p = 5 → ¬ 5 ∣ 2 ^ f - 1) :
    (∃ m, SylowTorus (adjointGroup .E6 (GaloisField 2 f)) p m) ∨
      ∀ A : Subgroup (adjointGroup .E6 (GaloisField 2 f)), IsElemAbelian p A →
        Nat.card A < p ^ 4 := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  by_cases h7 : 7 ≤ p
  · by_cases hc : 3 ≤ degCount Tag.E6 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p))
    · exact Or.inl (CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sylowTorus_E6
        (GaloisField 2 f) hp h7 hpq hc)
    · refine Or.inr fun A hA => ?_
      have hp1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      have hp2' : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      by_cases h1c : degCount Tag.E6 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≤ 1
      · have hle := rankLE1_E6 (GaloisField 2 f) hp hpq h1c A hA
        rw [pow_one] at hp1
        omega
      · have h2c : degCount Tag.E6 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = 2 := by
          omega
        have hle := CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_E6_of_degCount_eq_two
          (GaloisField 2 f) hp h2c A hA
        omega
  · have hp5' : p = 5 := by
      have h6 : p ≤ 6 := by omega
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp5'
    have h1 : ¬ 5 ∣ Nat.card (GaloisField 2 f) - 1 := by
      rw [hK]
      exact h5 rfl
    by_cases h2 : 5 ∣ Nat.card (GaloisField 2 f) + 1
    · have he : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod 5) = 2 := by
        rw [hK] at h2 ⊢
        exact OrdPInnerExc.orderOf_natCast_eq_two_of_dvd_add_one hp hp2 h2
      exact Or.inl ⟨_, PRankBounds.sylowTorus_of_blocks_of_lt 3 (Or.inl ⟨rfl, rfl⟩)
        (GaloisField 2 f) hp (by norm_num) (IsWeylMatrix.of_word Tag.E6 e6TwoWord)
        [1, 1, 2, 2, 2, 2] e6Two_charpoly e6Two_pow he (by norm_num) (by decide) (by decide)
        (by decide)⟩
    · refine Or.inr fun A hA => ?_
      have he3 := PRankBounds.three_le_orderOf hp hpq Nat.card_pos h1 h2
      have : Fact (Nat.Prime 5) := ⟨hp⟩
      have hdvd : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod 5) ∣ 5 - 1 :=
        ZMod.orderOf_dvd_card_sub_one fun h0 => hpq ((ZMod.natCast_eq_zero_iff _ _).1 h0)
      obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod 5) = e := ⟨_, rfl⟩
      rw [he] at hdvd he3
      have he4 : e = 4 := by
        have hle : e ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases e
        · exact absurd hdvd (by decide)
        · rfl
      subst he4
      have hcnt : degCount Tag.E6 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod 5)) = 2 := by
        rw [he]
        decide
      have hle := CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_E6_of_degCount_eq_two
        (GaloisField 2 f) hp hcnt A hA
      have hp2' : 5 ^ 2 < 5 ^ 4 := by norm_num
      omega

end Adjoint

section Reduction


theorem ggOrdPToralE6Rest_of_hard (h : GGOrdPToralE6RestHard) : GGOrdPToralE6Rest := by
  intro f p hf hp hp2 h3 h7 hA
  by_cases hhard : (p = 3 ∧ 3 ∣ 2 ^ f + 1) ∨ (p = 5 ∧ 5 ∣ 2 ^ f - 1)
  · exact h f p hf hp hhard hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hp3 : p ≠ 3 := by
    rintro rfl
    refine hhard (Or.inl ⟨rfl, ?_⟩)
    have hx : ¬ 3 ∣ 2 ^ f := fun hd =>
      absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hn : ¬ 3 ∣ 2 ^ f - 1 := fun hd => h3 ⟨rfl, hd⟩
    omega
  have hcop : Nat.Coprime (Nat.card (e6Isogeny (GaloisField 2 f)).ker) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le
      (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f)))
      (OrdPInnerExc.coprime_card_center_E6 hp (Or.inl hp3))
  rcases sylowTorus_or_card_lt_adjointE6 hf hp hp2 hp3
      (fun h5 => fun hd => hhard (Or.inr ⟨h5, hd⟩)) with ⟨m, hm⟩ | hlt
  · haveI : Finite (adjointGroup .E6 (GaloisField 2 f)) := generated_group_finite .E6 _
    exact OrdPInnerExc.ggOrdPToralMax_of_surjective hp (e6Isogeny_surjective (GaloisField 2 f))
      (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f)) hcop
      (OrdPInnerExc.ggOrdPToralMax_of_sylowTorus hm)
  · obtain ⟨A, hAel, hAc⟩ := hA
    haveI : Finite (adjointGroup .E6 (GaloisField 2 f)) := generated_group_finite .E6 _
    exact absurd hAc (not_le.2 (OrdPInnerExc.card_lt_of_card_lt_map hcop hlt hAel))

end Reduction

end CFSG.StandardType
