module

public import CFSG.RankThree.PartOne.N143.SectionListBound
public import CFSG.RankThree.PartOne.K159.AutTitsIso
public import CFSG.RankThree.PartOne.K159.AutL2Five
public import CFSG.RankThree.PartOne.K159.AutA10Five
public import CFSG.RankThree.PartOne.K159.AutTitsFive
public import CFSG.RankThree.PartOne.S12.Sec1511AutL2
public import CFSG.RankThree.PartOne.S12.Sec1511AutA10
public import CFSG.RankThree.PartOne.S12.Sec1511AutSz
public import CFSG.RankThree.PartOne.S12.Sec1511AutTits

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K159
  CFSG.RankThree.PartOne.Sec1511 CFSG.ABGLocalTools StrongP

@[expose] def KF159AutList : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeListHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
        Nat.card (omegaOne p P) = p ^ 2 →
        ((∃ q : TauCeti.PrimePower, q.p = p ∧ (q.exponent = 2 ∨ q.exponent = 3) ∧
            Census3.IsoLie ↥S (.A 1 q)) ∨
          (p = 5 ∧ (Nonempty (↥S ≃* alternatingGroup (Fin 10)) ∨ Census3.IsoLie ↥S .tits ∨
            Census3.IsoLie ↥S (.suzuki 2)))) →
        ¬ (Nat.card ↥(torusImage (omegaOne p P) S) ∣ 24 ∧
          ∀ g ∈ torusImage (omegaOne p P) S, orderOf g ≤ 4)

@[expose] def KF159Aut5List : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeListHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
        Nat.card (omegaOne p P) = p ^ 2 →
        ((∃ q : TauCeti.PrimePower, q.p = p ∧ (q.exponent = 2 ∨ q.exponent = 3) ∧
            Census3.IsoLie ↥S (.A 1 q)) ∨
          (p = 5 ∧ (Nonempty (↥S ≃* alternatingGroup (Fin 10)) ∨ Census3.IsoLie ↥S .tits))) →
        ¬ (Nat.card ↥(torusImage (omegaOne p P) S) ∣ 120 ∧
          ∀ g ∈ torusImage (omegaOne p P) S, orderOf g ≤ 6)

@[expose] def KF1511AutList : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeListHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
        (Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) →
        ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 2 ∧ Census3.IsoLie ↥S (.A 1 q)) →
          Nat.card (omegaOne p P) = p ^ 2 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g ((p ^ 2 - 1) / 2)) ∧
        ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 3 ∧ Census3.IsoLie ↥S (.A 1 q)) →
          Nat.card (omegaOne p P) = p ^ 3 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g ((p ^ 3 - 1) / 2)) ∧
        (p = 5 → Nonempty (↥S ≃* alternatingGroup (Fin 10)) →
          Nat.card (omegaOne p P) = 25 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g 8) ∧
        (p = 5 → Census3.IsoLie ↥S .tits →
          Nat.card (omegaOne p P) = 25 ∧
            ∃ F : Finset H, F.card = 48 ∧
              (∀ x ∈ F, x ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H)) ∧
              ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
                x⁻¹ * y ∉ Subgroup.centralizer ((omegaOne p P : Subgroup H) : Set H)) ∧
        (p = 5 → Census3.IsoLie ↥S (.suzuki 2) →
          Nat.card (omegaOne p P) = 25 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g 5)

theorem kf159AutList :
    KF159AutList := by
  intro p hp hp5 H _ _ S hS hS3 hC P hP hΩel hΩ hrows
  rcases hrows with ⟨q, hqp, hq, h⟩ | ⟨rfl, hA | hT | hSz⟩
  · rcases hq with hq | hq
    · exact not_sLike_of_witness hp hS (autWitness_of_isoLie_A1_two hp5 q hqp hq h) hP hΩ
    · intro _
      exact (false_of_bigWitness hp (bigWitness_of_isoLie_A1_three q hqp hq h) hP hΩ).elim
  · obtain ⟨e⟩ := hA
    exact not_sLike_of_witness hp hS (AutWitness.of_mulEquiv e.symm autWitness_alternating_ten) hP hΩ
  · exact not_sLike_of_witness hp hS (autWitness_of_isoLie_tits hT) hP hΩ
  · exact SzAbs.not_sLike_of_isoLie_suzuki hS hS3.isSimpleGroup hSz hC hP hΩel hΩ

theorem kf159Aut5List :
    KF159Aut5List := by
  intro p hp hp5 H _ _ S hS _ _ P hP _ hΩ hrows
  rcases hrows with ⟨q, hqp, hq, h⟩ | ⟨rfl, hA | hT⟩
  · rcases hq with hq | hq
    · exact not_sLike5_of_witness hp hS (autWitnessUpTo_six_of_isoLie_A1_two hp5 q hqp hq h) hP hΩ
    · intro _
      exact (false_of_bigWitness hp (bigWitness_of_isoLie_A1_three q hqp hq h) hP hΩ).elim
  · obtain ⟨e⟩ := hA
    exact not_sLike5_of_witness hp hS
      (AutWitnessUpTo.of_mulEquiv e.symm autWitnessUpTo_six_alternating_ten) hP hΩ
  · exact not_sLike5_of_witness hp hS (autWitnessUpTo_six_of_isoLie_tits hT) hP hΩ

theorem kf1511AutList :
    KF1511AutList := by
  intro p hp hp5 H _ _ S hSn hS3 hC P hP hΩel hΩ
  have := hSn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨q, hqp, hq, hiso⟩
    exact l2_row hp hp5 (Or.inl rfl) hC q hqp hq hiso hP
  · rintro ⟨q, hqp, hq, hiso⟩
    exact l2_row hp hp5 (Or.inr rfl) hC q hqp hq hiso hP
  · rintro rfl ⟨e⟩
    exact a10_row hC e hP
  · rintro rfl hiso
    exact tits_row hiso hC hP
  · rintro rfl hiso
    refine sz_row_exact hS3.1 hiso hC hP hΩel ?_
    rcases hΩ with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)

end CFSG.RankThree.PartOne.N143
