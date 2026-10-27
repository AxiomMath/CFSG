module

public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo

open CFSG

universe u

@[expose] def Item37 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A S P : Subgroup X, CFSG.Assembly.IsElemAbelian p A → ¬ p ∣ Nat.card S →
      A ≤ Subgroup.normalizer (S : Set X) → IsPGroup p P →
      A ≤ Subgroup.normalizer (P : Set X) → S ≤ Subgroup.normalizer (P : Set X) →
      (∀ y ∈ (A ⊔ P) ⊓ Subgroup.centralizer (A : Set X), y ^ p = 1 → y ∈ A) →
      ⁅P, S⁆ = ⊥

structure SectionFiveHyp {G : Type u} [Group G] [Finite G] (A S : Subgroup G) : Prop where
  elemAbelian : CFSG.Assembly.IsElemAbelian 3 A
  card_eq : Nat.card A = 27
  mem_inv : S ∈ invariantPiSubgroups ⊤ A (piOf 2)
  commutator_ne_bot : ⁅CFSG.pCore 3 G, S⁆ ≠ ⊥
  evenRank_eq : CFSG.Assembly.evenRank G = 3

@[expose] def omegaOneSub {G : Type u} [Group G] (S : Subgroup G) : Subgroup G :=
  (CFSG.omega₁ S (p := 2)).map S.subtype

@[expose] def IsSymplecticType (S : Type u) [Group S] : Prop :=
  ∀ W : Subgroup S, W.Characteristic → IsMulCommutative W → IsCyclic W

namespace SectionFiveHyp

variable {G : Type u} [Group G] [Finite G] {A S : Subgroup G}

theorem isPGroup (h : SectionFiveHyp A S) : IsPGroup 2 S :=
  ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp h.mem_inv).2.1

theorem le_normalizer (h : SectionFiveHyp A S) : A ≤ Subgroup.normalizer (S : Set G) :=
  ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp h.mem_inv).2.2

theorem ne_bot (h : SectionFiveHyp A S) : S ≠ ⊥ := by
  rintro rfl
  exact h.commutator_ne_bot (Subgroup.commutator_bot_right _)

theorem mono (h : SectionFiveHyp A S) {S' : Subgroup G} (hS' : S' ≤ S)
    (hA : A ≤ Subgroup.normalizer (S' : Set G)) (hc : ⁅CFSG.pCore 3 G, S'⁆ ≠ ⊥) :
    SectionFiveHyp A S' :=
  ⟨h.elemAbelian, h.card_eq, (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
    ⟨le_top, h.isPGroup.to_le hS', hA⟩, hc, h.evenRank_eq⟩

end SectionFiveHyp

theorem omegaOneSub_eq_closure {G : Type u} [Group G] (S : Subgroup G) :
    omegaOneSub S = Subgroup.closure {x : G | x ∈ S ∧ x ^ 2 = 1} := by
  rw [omegaOneSub, CFSG.omega₁, CFSG.omega, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [pow_one, Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by rw [← Subgroup.coe_pow, hy, Subgroup.coe_one]⟩
  · rintro ⟨hxS, hx⟩
    exact ⟨⟨x, hxS⟩, Subtype.ext (by simpa using hx), rfl⟩

theorem omegaOneSub_le {G : Type u} [Group G] (S : Subgroup G) : omegaOneSub S ≤ S :=
  Subgroup.map_subtype_le _

end CFSG.RankThree.PartTwo
