module

import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def Item231Concl (A : Subgroup G) : Prop :=
  (Nonempty (iGroup A ≃* projSU 5 2 3) ∧
      Nonempty (starOf A (iGroup A) ≃* Equiv.Perm (Fin 5)) ∧ Nat.card A = 3 ^ 4) ∨
    (Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2)) ∧
      Nonempty (starOf A (iGroup A) ≃* Equiv.Perm (Fin 4)) ∧ Nat.card A = 3 ^ 3) ∨
    (Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)) ∧
      Nonempty (starOf A (iGroup A) ≃* (ℤˣ × Equiv.Perm (Fin 4))) ∧ Nat.card A = 3 ^ 3)

@[expose] def Item231 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A

theorem inCatalog_projSU_five_eight : CFSG.Assembly.InCatalog (projSU 5 2 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q]
  exact ⟨.lie ⟨.twistedA 4 q, hv⟩,
    ⟨(CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 4 q hv).symm⟩⟩

theorem inCatalog_projSL_four_four : CFSG.Assembly.InCatalog (projSL 4 (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q]
  exact ⟨.lie ⟨.A 3 q, hv⟩,
    ⟨(CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 3 q hv).symm⟩⟩

theorem inCatalog_projSp_three_four : CFSG.Assembly.InCatalog (projSp 3 (GaloisField 2 2)) := by
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.B 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q]
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Census.bridgeSp6Four q hv rfl rfl
  exact ⟨.lie ⟨.B 3 q, hv⟩, ⟨e.symm⟩⟩

theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.Assembly.InCatalog Y) : CFSG.Assembly.InCatalog X :=
  CFSG.Assembly.inCatalog_isoInvariant e h

theorem starOf_bot (A : Subgroup G) : starOf A ⊥ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : (x : G) = 1 := (Subgroup.mem_subgroupOf.mp hx)
  have : x = 1 := Subtype.ext hx1
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem inCatalog_iGroup_of_item231Concl {A : Subgroup G} (h : Item231Concl A) :
    CFSG.Assembly.InCatalog (iGroup A) := by
  rcases h with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
  · exact inCatalog_of_mulEquiv e inCatalog_projSU_five_eight
  · exact inCatalog_of_mulEquiv e inCatalog_projSL_four_four
  · exact inCatalog_of_mulEquiv e inCatalog_projSp_three_four

theorem iGroup_ne_bot_of_item231Concl {A : Subgroup G} (h : Item231Concl A) :
    iGroup A ≠ ⊥ := by
  intro hI
  have hstar : starOf A (iGroup A) = ⊥ := by rw [hI, starOf_bot]
  have hsub : Subsingleton (starOf A (iGroup A)) := by
    rw [hstar]
    infer_instance
  rcases h with ⟨-, ⟨e⟩, -⟩ | ⟨-, ⟨e⟩, -⟩ | ⟨-, ⟨e⟩, -⟩
  · have := e.symm.injective.subsingleton
    exact (show Equiv.swap (0 : Fin 5) 1 ≠ 1 by decide) (Subsingleton.elim _ _)
  · have := e.symm.injective.subsingleton
    exact (show Equiv.swap (0 : Fin 4) 1 ≠ 1 by decide) (Subsingleton.elim _ _)
  · have := e.symm.injective.subsingleton
    exact (show ((-1 : ℤˣ), (1 : Equiv.Perm (Fin 4))) ≠ 1 by decide) (Subsingleton.elim _ _)

theorem iGroup_ne_top_of_item231Concl [Finite G] {A : Subgroup G} (hG : PartTwoStanding G)
    (h : Item231Concl A) : iGroup A ≠ ⊤ := by
  intro hI
  apply hG.not_inCatalog
  have hcat := inCatalog_iGroup_of_item231Concl h
  rw [hI] at hcat
  exact inCatalog_of_mulEquiv Subgroup.topEquiv.symm hcat

theorem nGroup_ne_top_of_item231Concl [Finite G] {A : Subgroup G} (hG : PartTwoStanding G)
    (h : Item231Concl A) : nGroup A ≠ ⊤ := by
  intro hN
  have hnorm : (iGroup A).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hN
  have := hG.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (iGroup A) with hb | ht
  · exact iGroup_ne_bot_of_item231Concl h hb
  · exact iGroup_ne_top_of_item231Concl hG h ht

end CFSG.RankThree.PartTwo.Sec21
