module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Blueprint
open scoped commutatorElement

namespace Item211Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_fourGroupsPlus_or_mem_fourGroupsMinus {E U : Subgroup G}
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hU : U ∈ fourGroups E) :
    U ∈ fourGroupsPlus E ∨ U ∈ fourGroupsMinus E := by
  obtain ⟨hEU, -, hU4⟩ := mem_fourGroups_iff.mp hU
  have hconj : ∀ e ∈ E, ∀ x ∈ U, e * x * e⁻¹ ∈ U := fun e he x hx =>
    (Subgroup.mem_normalizer_iff.mp (hEU he) x).mp hx
  by_cases hc : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ = u
  · left
    refine mem_fourGroupsPlus_iff.mpr ⟨hU, fun e he => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hc e he u hu
    calc u * e = e * u * e⁻¹ * e := by rw [h1]
      _ = e * u := by group
  · right
    push Not at hc
    obtain ⟨e, he, u₀, hu₀, hne⟩ := hc
    refine ⟨hU, le_antisymm ?_ ?_⟩
    ·
      have hC : U ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
        by_contra hC
        have h5 := five_le_card_of_not_commute (hE3 e he) (hconj e he) inf_le_left
          (fun x hx => by
            have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx.2
            rw [← h1, mul_inv_cancel_right])
          hC hu₀ hne
        omega
      set φ : U → U := fun x => ⟨(x : G)⁻¹ * (e * x * e⁻¹), U.mul_mem (U.inv_mem x.2)
        (hconj e he x x.2)⟩ with hφ
      have hφinj : Function.Injective φ := by
        intro x y hxy
        have h := congrArg Subtype.val hxy
        simp only [hφ] at h
        have h1 : e * (x : G) * e⁻¹ = x * (y : G)⁻¹ * (e * y * e⁻¹) := by
          calc e * (x : G) * e⁻¹ = x * ((x : G)⁻¹ * (e * x * e⁻¹)) := by group
            _ = x * ((y : G)⁻¹ * (e * y * e⁻¹)) := by rw [h]
            _ = x * (y : G)⁻¹ * (e * y * e⁻¹) := by group
        have hz : (x : G) * (y : G)⁻¹ ∈ U ⊓ Subgroup.centralizer ({e} : Set G) := by
          refine Subgroup.mem_inf.mpr ⟨U.mul_mem x.2 (U.inv_mem y.2), ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (x : G) * (y : G)⁻¹ * e = x * (y : G)⁻¹ * (e * y * e⁻¹) * e * (y : G)⁻¹ := by
                group
            _ = e * (x : G) * e⁻¹ * e * (y : G)⁻¹ := by rw [h1]
            _ = e * (x * (y : G)⁻¹) := by group
        rw [hC, Subgroup.mem_bot] at hz
        exact Subtype.ext (mul_inv_eq_one.mp hz)
      have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
      intro u hu
      obtain ⟨x, hx⟩ := hφsurj ⟨u, hu⟩
      have hxu : (x : G)⁻¹ * (e * x * e⁻¹) = u := congrArg Subtype.val hx
      rw [← hxu]
      have := Subgroup.commutator_mem_commutator (U.inv_mem x.2) he
      rw [commutatorElement_def, inv_inv] at this
      simpa [mul_assoc] using this
    · rw [Subgroup.commutator_le]
      intro u hu e' he'
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine U.mul_mem hu ?_
      have h1 := hconj e' he' u⁻¹ (U.inv_mem hu)
      rwa [mul_assoc] at h1

end Item211Res2Proof

open Item211Res2Proof

variable {G : Type} [Group G]

@[expose] def CaseLieExc (A L : Subgroup G) : Prop :=
  Nat.card A = 3 ^ 3 ∧ ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    (ChevalleyExceptionalModel (lBar L) .G2 p 1 ∨
      Nonempty (lBar L ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (lBar L ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (lBar L ≃* projSL 4 (GaloisField p 1))))

@[expose] def CaseLieL3 (A L : Subgroup G) : Prop :=
  Nat.card A = 3 ^ 3 ∧ ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧ ∃ e : ℕ, 1 ≤ e ∧
    (Sec4.IsSLThreePiAt (lBar L) (p ^ e) ∨ Sec4.IsoLThreePi (lBar L) p e)

@[expose] def CaseLieU42 (A L : Subgroup G) : Prop :=
  Nat.card A = 3 ^ 4 ∧ Nonempty (lBar L ≃* projSU 4 2 1) ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))

@[expose] def CaseLieA9 (A L : Subgroup G) : Prop :=
  Nat.card A = 3 ^ 4 ∧ Nonempty (lBar L ≃* alternatingGroup (Fin 9)) ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))

section Certs


@[expose] def Item211LiePlusU42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsPlus E → CaseLieU42 A L → False

@[expose] def Item211LiePlusExc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsPlus E → CaseLieExc A L → False

@[expose] def Item211LiePlusA9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsPlus E → CaseLieA9 A L → False

@[expose] def Item211LiePlusL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsPlus E → CaseLieL3 A L → False

@[expose] def Item211LieMinusL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsMinus E → CaseLieL3 A L → False

@[expose] def Item211LieMinusU42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsMinus E → CaseLieU42 A L → False

@[expose] def Item211LieMinusA9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsMinus E → CaseLieA9 A L → False

@[expose] def Item211LieMinusExc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    U ∈ fourGroupsMinus E → CaseLieExc A L → False

theorem item211ResidualLie_of (hPU : Item211LiePlusU42) (hPE : Item211LiePlusExc)
    (hPA : Item211LiePlusA9) (hPL : Item211LiePlusL3) (hML : Item211LieMinusL3)
    (hMU : Item211LieMinusU42) (hMA : Item211LieMinusA9) (hME : Item211LieMinusExc) :
    Item211ResidualLie := by
  intro G _ _ A E U c L hpair hnf hcase
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := hpair.mem_E.1.1.2
  rcases hcase with ⟨h27, p, hp, hp3, h | h | h | h | ⟨e, he, h⟩⟩ | hU | hA9
  · have hc : CaseLieExc A L := ⟨h27, p, hp, hp3, Or.inl h⟩
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPE G A E U c L hpair hnf hP hc
    · exact hME G A E U c L hpair hnf hM hc
  · have hc : CaseLieExc A L := ⟨h27, p, hp, hp3, Or.inr (Or.inl h)⟩
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPE G A E U c L hpair hnf hP hc
    · exact hME G A E U c L hpair hnf hM hc
  · have hc : CaseLieExc A L := ⟨h27, p, hp, hp3, Or.inr (Or.inr (Or.inl h))⟩
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPE G A E U c L hpair hnf hP hc
    · exact hME G A E U c L hpair hnf hM hc
  · have hc : CaseLieExc A L := ⟨h27, p, hp, hp3, Or.inr (Or.inr (Or.inr h))⟩
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPE G A E U c L hpair hnf hP hc
    · exact hME G A E U c L hpair hnf hM hc
  · have hc : CaseLieL3 A L := ⟨h27, p, hp, hp3, e, he, h⟩
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPL G A E U c L hpair hnf hP hc
    · exact hML G A E U c L hpair hnf hM hc
  · rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPU G A E U c L hpair hnf hP hU
    · exact hMU G A E U c L hpair hnf hM hU
  · rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hP | hM
    · exact hPA G A E U c L hpair hnf hP hA9
    · exact hMA G A E U c L hpair hnf hM hA9

end Certs

end CFSG.RankThree.PartTwo.Sec21
