module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofField
import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84
import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


@[expose] def Pair86One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      ∃ b ∈ Subgroup.closure ({c, d} : Set G), b ∉ Subgroup.zpowers c ∧ ∃ X : Subgroup G,
        PairRel A c L b X ∧ IsList86 (X ⧸ aschbacherSolvableCore 3 X) n

@[expose] def Pair86D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) →
        b ∉ Subgroup.zpowers c → PairRel A c L b X →
        IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) n →
          IsoGTwoEven (barCentralizer (Subgroup.zpowers a) X) n ∨
            ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
              IsoGTwoEven (barCentralizer (Subgroup.zpowers (a * c ^ ε)) X) n

@[expose] def Pair86D4N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → (∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
      ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) → PairRel A c L b X →
        ∀ m : ℕ, IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) m →
          IsoGTwoEven (barCentralizer (Subgroup.zpowers a) X) m ∨
            ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
              IsoGTwoEven (barCentralizer (Subgroup.zpowers (a * c ^ ε)) X) m


theorem pair86Exists_of (h418 : Item418Theta) (hF : KF84FieldStd) (h1 : Pair86One)
    (hD4 : Pair86D4) : Pair86Exists := by
  intro G _ _ A c L a d n h hLU3
  have hn1 : 1 ≤ n := h.data83.odd.pos
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  obtain ⟨b, hb, hbc, X, hrel, hlist⟩ := h1 G A c L a d n h hLU3
  refine ⟨b, hb, hbc, X, hrel, hlist, ?_⟩
  obtain ⟨hkind, -⟩ := kinds_of_partner h418 hF h hb hrel
  have hout : Sec4.InducesOuterTheta a X := by
    rcases hkind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  rcases hlist with hD | ⟨K, _, _, hK, ⟨e⟩⟩ | hSp
  · rcases hD4 G A c L a d n h hLU3 b X hb hbc hrel hD with hG2 | ⟨ε, hε, hG2⟩
    · exact Or.inl hG2
    · exact Or.inr (Or.inl ⟨ε, hε, hG2⟩)
  · obtain ⟨-, k, hk, hkf, hkc, hC⟩ :=
      KFacts.barCentralizer_mulEquiv_g2 (by omega) hK ha3 hout e
    exact Or.inl ⟨k, hk, hkf, hkc, hC⟩
  · exact Or.inr (Or.inr (KFacts.barCentralizer_mulEquiv_projSp (by omega) ha3 hout hSp).2)

theorem pair86GTwoN_of (h418 : Item418Theta) (hF : KF84FieldStd) (hD4 : Pair86D4N) :
    Pair86GTwoN := by
  intro G _ _ A c L a d n h hLU b X hb hrel _
  by_cases hD : ∃ m₀ : ℕ, IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) m₀
  · obtain ⟨m₀, hm₀⟩ := hD
    have hm₀1 : 1 ≤ m₀ := one_le_of_isoTrialityD4_or_isoGTwoEven (Or.inl hm₀)
    have key : ∀ x : G, IsoGTwoEven (barCentralizer (Subgroup.zpowers x) X) m₀ →
        ∀ m : ℕ, Sec8PairGTwo X x m := fun x hx =>
      sec8PairGTwo_forall hm₀1 (Or.inr (Or.inl hm₀)) fun _ => hx
    rcases hD4 G A c L a d n h hLU b X hb hrel m₀ hm₀ with hG2 | ⟨ε, -, hG2⟩
    · exact ⟨0, by rw [zpow_zero, mul_one]; exact key a hG2⟩
    · exact ⟨ε, key _ hG2⟩
  · refine ⟨0, fun m hm => ?_⟩
    rw [zpow_zero, mul_one]
    have hm1 := one_le_of_isoTrialityD4_or_isoGTwoEven hm
    rcases hm with hm | ⟨K, _, _, hK, ⟨e⟩⟩
    · exact absurd ⟨m, hm⟩ hD
    ·
      obtain ⟨hkind, -⟩ := kinds_of_partner h418 hF h hb hrel
      have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
      have hout : Sec4.InducesOuterTheta a X := by
        rcases hkind with hk | hk
        · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
        · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
      obtain ⟨-, k, hk, hkf, hkc, hC⟩ :=
        KFacts.barCentralizer_mulEquiv_g2 (by omega) hK ha3 hout e
      exact ⟨k, hk, hkf, hkc, hC⟩

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
