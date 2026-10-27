module

public import CFSG.RankThree.PartOne.K159F.Witness

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP CFSG.RankThree.PartOne.K159F

abbrev AutWitnessUpTo (n p : ℕ) (S : Type*) [Group S] : Prop := AutWitnessN p 2 n S

theorem AutWitnessUpTo.of_mulEquiv {n p : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : AutWitnessUpTo n p S) : AutWitnessUpTo n p T :=
  AutWitnessN.of_mulEquiv e h

variable {H : Type} [Group H] [Finite H]

theorem exists_big_order_of_witness {n p : ℕ} (hp : p.Prime) {S : Subgroup H} (hS : S.Normal)
    (hw : AutWitnessUpTo n p ↥S) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) = p ^ 2) :
    ∃ a ∈ torusImage (omegaOne p P) S, n < orderOf a := by
  have := not_bounded_of_witnessN hp hS hw hP hΩ
  push Not at this
  exact this

theorem not_sLike5_of_witness {p : ℕ} (hp : p.Prime) {S : Subgroup H} (hS : S.Normal)
    (hw : AutWitnessUpTo 6 p ↥S) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) = p ^ 2) :
    ¬ (Nat.card ↥(torusImage (omegaOne p P) S) ∣ 120 ∧
        ∀ a ∈ torusImage (omegaOne p P) S, orderOf a ≤ 6) := by
  rintro ⟨-, hord⟩
  obtain ⟨a, ha, hlt⟩ := exists_big_order_of_witness hp hS hw hP hΩ
  exact absurd (hord a ha) (not_le.2 hlt)

end CFSG.RankThree.PartOne.K159
