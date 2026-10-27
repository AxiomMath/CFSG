module

public import CFSG.Foundations.Catalog
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

abbrev IsoLie (X : Type) [Group X] (d : LieTypeIndex) : Prop :=
  ∃ hv : d.Valid, Nonempty (X ≃* (CFSGIndex.lie ⟨d, hv⟩).Group)

@[expose] def sporadicsThm3 : List SporadicName :=
  [.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .McL, .Ly, .HS, .He, .Suz, .Ru, .ONan, .Co3,
    .Co2, .HN, .Th]

abbrev ThmThreeItem1 (G : Type) [Group G] : Prop :=
  ∃ q : PrimePower, q.p ≠ 2 ∧ 5 ≤ q.card ∧ IsoLie G (.A 1 q)

abbrev ThmThreeItem2 (G : Type) [Group G] : Prop :=
  ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent ≤ 3 ∧ (IsoLie G (.A 2 q) ∨ IsoLie G (.twistedA 2 q))

abbrev ThmThreeItem3 (G : Type) [Group G] : Prop :=
  IsoLie G (.reeG2 1)

abbrev ThmThreeItem4 (G : Type) [Group G] : Prop :=
  ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent = 1 ∧
    (IsoLie G (.G2 q) ∨ IsoLie G (.B 2 q) ∨ IsoLie G (.twistedA 3 q) ∨ IsoLie G (.A 3 q))

abbrev ThmThreeItem5 (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (G ≃* alternatingGroup (Fin n))

abbrev ThmThreeItem6 (G : Type) [Group G] : Prop :=
  ∃ s ∈ sporadicsThm3, Nonempty (G ≃* (CFSGIndex.sporadic s).Group)

abbrev ThmThreeItem7 (G : Type) [Group G] : Prop :=
  (∃ q : PrimePower, q.p = 2 ∧ IsoLie G (.A 1 q)) ∨ (∃ m : ℕ, IsoLie G (.suzuki m)) ∨
    (∃ q : PrimePower, q.p = 2 ∧
      (IsoLie G (.twistedA 2 q) ∨ IsoLie G (.A 2 q) ∨ IsoLie G (.B 2 q) ∨ IsoLie G (.G2 q) ∨
        IsoLie G (.twistedA 3 q) ∨ IsoLie G (.twistedA 4 q) ∨ IsoLie G (.trialityD4 q))) ∨
    (∃ m : ℕ, IsoLie G (.reeF4 m)) ∨ IsoLie G .tits

abbrev ThmThreeItem8 (G : Type) [Group G] : Prop :=
  ∃ q : PrimePower, q.p = 2 ∧
    (IsoLie G (.A 3 q) ∨ IsoLie G (.B 3 q) ∨ IsoLie G (.twistedD 4 q))

abbrev ThmThreeItem9 (G : Type) [Group G] : Prop :=
  ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
    (IsoLie G (.A 4 q) ∨ IsoLie G (.A 5 q) ∨ IsoLie G (.A 6 q) ∨ IsoLie G (.twistedA 5 q) ∨
      IsoLie G (.B 4 q) ∨ IsoLie G (.D 4 q) ∨ IsoLie G (.F4 q))

@[expose] def TheoremThreeList (G : Type) [Group G] : Prop :=
  ThmThreeItem1 G ∨ ThmThreeItem2 G ∨ ThmThreeItem3 G ∨ ThmThreeItem4 G ∨ ThmThreeItem5 G ∨
    ThmThreeItem6 G ∨ ThmThreeItem7 G ∨ ThmThreeItem8 G ∨ ThmThreeItem9 G

namespace TheoremThreeList

variable {G : Type} [Group G]

theorem item1 (h : ThmThreeItem1 G) : TheoremThreeList G := Or.inl h
theorem item2 (h : ThmThreeItem2 G) : TheoremThreeList G := Or.inr (Or.inl h)
theorem item3 (h : ThmThreeItem3 G) : TheoremThreeList G := Or.inr (Or.inr (Or.inl h))
theorem item4 (h : ThmThreeItem4 G) : TheoremThreeList G := Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem item5 (h : ThmThreeItem5 G) : TheoremThreeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem item6 (h : ThmThreeItem6 G) : TheoremThreeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem item7 (h : ThmThreeItem7 G) : TheoremThreeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem item8 (h : ThmThreeItem8 G) : TheoremThreeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
theorem item9 (h : ThmThreeItem9 G) : TheoremThreeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

variable {q : PrimePower}

theorem of_A1_odd (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.p ≠ 2) (h5 : 5 ≤ q.card)
    (e : G ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : TheoremThreeList G :=
  item1 ⟨q, hq, h5, hv, ⟨e⟩⟩

theorem of_A2_odd (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.p ≠ 2) (hf : q.exponent ≤ 3)
    (e : G ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) : TheoremThreeList G :=
  item2 ⟨q, hq, hf, Or.inl ⟨hv, ⟨e⟩⟩⟩

theorem of_twistedA2_odd (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.p ≠ 2)
    (hf : q.exponent ≤ 3) (e : G ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :
    TheoremThreeList G :=
  item2 ⟨q, hq, hf, Or.inr ⟨hv, ⟨e⟩⟩⟩

theorem of_reeG2_one (hv : (LieTypeIndex.reeG2 1).Valid)
    (e : G ≃* (CFSGIndex.lie ⟨.reeG2 1, hv⟩).Group) : TheoremThreeList G :=
  item3 ⟨hv, ⟨e⟩⟩

theorem of_G2_prime (hv : (LieTypeIndex.G2 q).Valid) (hq : q.p ≠ 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : TheoremThreeList G :=
  item4 ⟨q, hq, hf, Or.inl ⟨hv, ⟨e⟩⟩⟩

theorem of_B2_prime (hv : (LieTypeIndex.B 2 q).Valid) (hq : q.p ≠ 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) : TheoremThreeList G :=
  item4 ⟨q, hq, hf, Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)⟩

theorem of_twistedA3_prime (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.p ≠ 2)
    (hf : q.exponent = 1) (e : G ≃* (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :
    TheoremThreeList G :=
  item4 ⟨q, hq, hf, Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩))⟩

theorem of_A3_prime (hv : (LieTypeIndex.A 3 q).Valid) (hq : q.p ≠ 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.A 3 q, hv⟩).Group) : TheoremThreeList G :=
  item4 ⟨q, hq, hf, Or.inr (Or.inr (Or.inr ⟨hv, ⟨e⟩⟩))⟩

theorem of_alternating {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) (e : G ≃* alternatingGroup (Fin n)) :
    TheoremThreeList G :=
  item5 ⟨n, hn5, hn, ⟨e⟩⟩

theorem of_sporadic {s : SporadicName} (hs : s ∈ sporadicsThm3)
    (e : G ≃* (CFSGIndex.sporadic s).Group) : TheoremThreeList G :=
  item6 ⟨s, hs, ⟨e⟩⟩

theorem of_A1_even (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inl ⟨q, hq, hv, ⟨e⟩⟩)

theorem of_suzuki {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    (e : G ≃* (CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inl ⟨m, hv, ⟨e⟩⟩))

theorem of_twistedA2_even (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl ⟨q, hq, Or.inl ⟨hv, ⟨e⟩⟩⟩)))

theorem of_A2_even (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl ⟨q, hq, Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)⟩)))

theorem of_B2_even (hv : (LieTypeIndex.B 2 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl ⟨q, hq, Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩))⟩)))

theorem of_G2_even (hv : (LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)))⟩)))

theorem of_twistedA3_even (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl
    ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩))))⟩)))

theorem of_twistedA4_even (hv : (LieTypeIndex.twistedA 4 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 4 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl
    ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)))))⟩)))

theorem of_trialityD4_even (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inl
    ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, ⟨e⟩⟩)))))⟩)))

theorem of_reeF4 {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid)
    (e : G ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hv, ⟨e⟩⟩))))

theorem of_tits (hv : LieTypeIndex.tits.Valid) (e : G ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group) :
    TheoremThreeList G :=
  item7 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, ⟨e⟩⟩))))

theorem of_A3_even (hv : (LieTypeIndex.A 3 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.A 3 q, hv⟩).Group) : TheoremThreeList G :=
  item8 ⟨q, hq, Or.inl ⟨hv, ⟨e⟩⟩⟩

theorem of_B3_even (hv : (LieTypeIndex.B 3 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) : TheoremThreeList G :=
  item8 ⟨q, hq, Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)⟩

theorem of_twistedD4_even (hv : (LieTypeIndex.twistedD 4 q).Valid) (hq : q.p = 2)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group) : TheoremThreeList G :=
  item8 ⟨q, hq, Or.inr (Or.inr ⟨hv, ⟨e⟩⟩)⟩

theorem of_A4_two (hv : (LieTypeIndex.A 4 q).Valid) (hq : q.p = 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.A 4 q, hv⟩).Group) : TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inl ⟨hv, ⟨e⟩⟩⟩

theorem of_A5_two (hv : (LieTypeIndex.A 5 q).Valid) (hq : q.p = 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.A 5 q, hv⟩).Group) : TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)⟩

theorem of_A6_two (hv : (LieTypeIndex.A 6 q).Valid) (hq : q.p = 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.A 6 q, hv⟩).Group) : TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩))⟩

theorem of_twistedA5_two (hv : (LieTypeIndex.twistedA 5 q).Valid) (hq : q.p = 2)
    (hf : q.exponent = 1) (e : G ≃* (CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) :
    TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)))⟩

theorem of_B4_two (hv : (LieTypeIndex.B 4 q).Valid) (hq : q.p = 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.B 4 q, hv⟩).Group) : TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩))))⟩

theorem of_D4_two (hv : (LieTypeIndex.D 4 q).Valid) (hq : q.p = 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) : TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, ⟨e⟩⟩)))))⟩

theorem of_F4_two (hv : (LieTypeIndex.F4 q).Valid) (hq : q.p = 2) (hf : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.F4 q, hv⟩).Group) : TheoremThreeList G :=
  item9 ⟨q, hq, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, ⟨e⟩⟩)))))⟩

end TheoremThreeList

structure TheoremThreeHyp (G : Type) [Group G] [Finite G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kGroup : CFSG.IsKGroup G
  twoLocalOddRank_le : CFSG.twoLocalOddRank G ≤ 3

@[expose] def ExcludedIndex (i : CFSGIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    (G ≃* i.Group) → 4 ≤ CFSG.twoLocalOddRank G

@[expose] def TheoremThreeCase (i : CFSGIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremThreeHyp G → (G ≃* i.Group) → TheoremThreeList G

theorem ExcludedIndex.case {i : CFSGIndex} (h : ExcludedIndex i) : TheoremThreeCase i := by
  intro G _ _ hG e
  have h4 := h G hG.isSimpleGroup hG.nonabelian e
  have h3 := hG.twoLocalOddRank_le
  omega

theorem TheoremThreeHyp.exists_index {G : Type} [Group G] [Finite G] (h : TheoremThreeHyp G) :
    ∃ i : CFSGIndex, Nonempty (G ≃* i.Group) := by
  have : IsSimpleGroup G := h.isSimpleGroup
  let e : (⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G)) ≃* G :=
    QuotientGroup.quotientBot.trans Subgroup.topEquiv
  have : IsSimpleGroup ((⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G))) := e.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := h.kGroup ⊤ ⊥ this
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem theorem_three_of_cases (h : ∀ i, TheoremThreeCase i) (G : Type) [Group G] [Finite G]
    (hG : TheoremThreeHyp G) : TheoremThreeList G := by
  obtain ⟨i, ⟨e⟩⟩ := hG.exists_index
  exact h i G hG e

theorem theoremThreeCase_cyclic (p : ℕ) (hp : p.Prime) : TheoremThreeCase (.cyclic p hp) := by
  intro G _ _ hG e
  obtain ⟨a, b, hab⟩ := hG.nonabelian
  have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
  exact absurd (e.injective (by rw [map_mul, map_mul]; exact hc (e a) (e b))) hab

section RankFour

variable {G H : Type} [Group G] [Finite G] [Group H]

theorem four_le_twoLocalOddRank_of_localRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 4 ≤ localRank p G) : 4 ≤ CFSG.twoLocalOddRank G := by
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact h.trans (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank p hp hp2 G)

theorem evenRank_le_of_mulEquiv [Finite H] (e : G ≃* H) : evenRank G ≤ evenRank H := by
  apply csSup_le'
  rintro _ ⟨p, K, hp, hp2, hK, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp e.toMonoidHom
    e.injective K).trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _
      (CFSG.RankThree.PartTwo.Census.isTwoLocal_map_mulEquiv hK e))

theorem twoLocalOddRank_eq_of_mulEquiv [Finite H] (e : G ≃* H) :
    CFSG.twoLocalOddRank G = CFSG.twoLocalOddRank H := by
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact le_antisymm (evenRank_le_of_mulEquiv e) (evenRank_le_of_mulEquiv e.symm)

theorem four_le_twoLocalOddRank_of_mulEquiv (e : G ≃* H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ [Finite H], 4 ≤ localRank p H) : 4 ≤ CFSG.twoLocalOddRank G := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  refine four_le_twoLocalOddRank_of_localRank hp hp2 ?_
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
  exact h

end RankFour

theorem excludedIndex_of_equiv {i : CFSGIndex} {T : Type} [Group T]
    (e : IsSimpleGroup i.Group → Nonempty (i.Group ≃* T)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hT : ∀ [Finite T], 4 ≤ localRank p T) : ExcludedIndex i := by
  intro G _ _ hs _ eG
  have : IsSimpleGroup G := hs
  have : IsSimpleGroup i.Group := eG.symm.isSimpleGroup
  obtain ⟨eT⟩ := e this
  exact four_le_twoLocalOddRank_of_mulEquiv (eG.trans eT) hp hp2 hT

theorem excludedIndex_of_four_le {i : CFSGIndex}
    (h : ∀ [Finite i.Group], 4 ≤ CFSG.twoLocalOddRank i.Group) : ExcludedIndex i := by
  intro G _ _ _ _ e
  have : Finite i.Group := Finite.of_equiv G e.toEquiv
  rw [twoLocalOddRank_eq_of_mulEquiv e]
  exact h

end CFSG.RankThree.PartOne.Census3
