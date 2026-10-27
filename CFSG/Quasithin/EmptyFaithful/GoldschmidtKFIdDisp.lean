module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdRed
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdAmb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdSyl
public import CFSG.Quasithin.EmptyFaithful.F918C19
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.Quasithin
open CFSG.Open (IsSubnormal)

@[expose] def L32Datum (S : Type) [Group S] : Prop :=
  ∃ w : MulAut S, w * w = 1 ∧ ∃ K : Subgroup S, IsSubnormal K (SBd18.fixedSub w) ∧ IsPSL 3 2 1 ↥K

@[expose] def IdentOddL2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) →
    IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → (∃ Q : Sylow 3 S, ¬ IsCyclic ↥(Q : Subgroup S)) →
    IsPSL 2 p f S → ¬ L32Datum S

@[expose] def IdentOddL3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → (∃ Q : Sylow 3 S, ¬ IsCyclic ↥(Q : Subgroup S)) →
    IsPSL 3 p 1 S → L32Datum S → p = 7

@[expose] def IdentOddU3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → (∃ Q : Sylow 3 S, ¬ IsCyclic ↥(Q : Subgroup S)) →
    IsPSU 3 p 1 S → ¬ L32Datum S

theorem row_conclusion {P : ∀ {G : Type} [Group G], Subgroup G → Prop} (hrow : TabIdentFor P)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hQ : ∃ Q : Sylow 3 S, ¬ IsCyclic ↥(Q : Subgroup S)) {w : MulAut S} (hw2 : w * w = 1)
    {K : Subgroup S} (hK : IsSubnormal K (SBd18.fixedSub w)) (hL32 : IsPSL 3 2 1 ↥K)
    (hP : ∀ (G : Type) [Group G] (X : Subgroup G), Nonempty (↥X ≃* S) → P X) :
    IsPSL 3 2 2 S ∨ IsSporadic .J2 S ∨ IsPSL 3 7 1 S := by
  by_cases hw1 : w = 1
  · subst hw1
    exact (false_of_fixedSub_one hQ hK hL32).elim
  · have hKq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_isPSL_three_two hL32
    rcases ident_simple_of_row hrow hnab w hw2 hw1 hK hKq hL32 hP with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

section Families

variable {S : Type} [Group S]

theorem statedClassicalModel_of_lieModel_PSL {X : Type} [Group X] {n p f : ℕ} (hn : n ≠ 0)
    (h : CFSG.Blueprint.LieModel X .PSL n p f) : IsPSL n p f X := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 hn

theorem famSporadic_of {G : Type} [Group G] {X : Subgroup G} [Finite S] [IsSimpleGroup S]
    (e' : ↥X ≃* S) (hnab : ∃ a b : S, a * b ≠ b * a) (s : TauCeti.SporadicName)
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) : Ident.FamSporadic s X := by
  have : Finite ↥X := Finite.of_equiv S e'.symm.toEquiv
  have : IsSimpleGroup ↥X := e'.isSimpleGroup
  have hnabX : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot := pCore_eq_bot_of_isSimpleGroup hnabX 2
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans
    (e'.trans e)⟩

end Families

section Main

open CFSG.Blueprint CFSG.Milestones

theorem identTable_of_families (hF : IdentFamilies) (hL2 : IdentOddL2) (hL3 : IdentOddL3)
    (hU3 : IdentOddU3) (hJ1 : Nat.card (NativeSporadic.Carrier .J1) = 175560) : IdentTable := by
  intro S _ _ hS hnab hlist hQ w hw2 K hK hL32
  have := hS
  rcases hlist with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ | h3 | ⟨n, hn, hmod⟩ | ⟨s, hs, ⟨e⟩⟩
  ·
    interval_cases n
    · exfalso
      obtain ⟨Q, hQ⟩ := hQ
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h9 := sq_dvd_card_of_noncyclic hQ
      have hcard : Nat.card S = 60 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [hcard] at h9
      omega
    · exact row_conclusion hF.a6Simple hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, ⟨e'.trans e⟩⟩)
    · exact row_conclusion hF.alt7 hnab hQ hw2 hK hL32 (fun G _ X ⟨e'⟩ =>
        ⟨⟨(quotCenterEquiv e' hnab).trans e⟩,
          Or.inl (by rw [center_eq_bot_of_equiv e' hnab, Subgroup.card_bot])⟩)
    · exact row_conclusion hF.l4Two hnab hQ hw2 hK hL32 (fun G _ X ⟨e'⟩ =>
        ⟨e'.isSimpleGroup, statedClassicalModel_of_lieModel_PSL (by norm_num)
          ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).mpr
            ⟨e'.trans e⟩)⟩)
  ·
    have hp3 : p = 3 ∨ 5 ≤ p := by
      by_cases h3 : p = 3
      · exact Or.inl h3
      · refine Or.inr ?_
        by_contra h
        interval_cases p <;> first | exact hp2 rfl | exact h3 rfl | exact absurd hp (by norm_num)
    rcases hodd with ⟨f, hf, hmod⟩ | hmod | hmod
    · exact (hL2 S p f hp hp2 hf hS hnab hQ hmod ⟨w, hw2, K, hK, hL32⟩).elim
    · rcases hp3 with rfl | hp5
      · exact row_conclusion hF.l33 hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => IsPSL.of_mulEquiv e'.symm hmod)
      · have h7 := hL3 S p hp hp5 hS hnab hQ hmod ⟨w, hw2, K, hK, hL32⟩
        subst h7
        exact Or.inr (Or.inr hmod)
    · rcases hp3 with rfl | hp5
      · exact row_conclusion hF.u33 hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSU.of_mulEquiv e'.symm hmod⟩)
      · exact (hU3 S p hp hp5 hS hnab hQ hmod ⟨w, hw2, K, hK, hL32⟩).elim
  ·
    rcases h3 with ⟨f, h | h | h | h | h | h | h | h⟩ | htits
    · exact row_conclusion hF.l2Even hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, h.1, IsPSL.of_mulEquiv e'.symm h.2⟩)
    · obtain ⟨hf1, hm⟩ := h
      rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | hf3
      · exact row_conclusion hF.l3Two hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSL.of_mulEquiv e'.symm hm⟩)
      · exact row_conclusion hF.l3Four hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSL.of_mulEquiv e'.symm hm⟩)
      · exact row_conclusion hF.l3Even hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, hf3, IsPSL.of_mulEquiv e'.symm hm⟩)
    · obtain ⟨hf1, hm⟩ := h
      rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | hf3
      · exact row_conclusion hF.u3Four hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSU.of_mulEquiv e'.symm hm⟩)
      · exact row_conclusion hF.u3Even hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, hf3, IsPSU.of_mulEquiv e'.symm hm⟩)
    · obtain ⟨hf1, hm⟩ := h
      rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | hf3
      · exact row_conclusion hF.sp4Four hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSp4.of_mulEquiv e'.symm hm⟩)
      · exact row_conclusion hF.sp4Even hnab hQ hw2 hK hL32
          (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, hf3, IsPSp4.of_mulEquiv e'.symm hm⟩)
    · exact row_conclusion hF.g2Even hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, h.1, IsG2.of_mulEquiv e'.symm h.2⟩)
    · exact row_conclusion hF.trialityEven hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, h.1, Is3D4.of_mulEquiv e'.symm h.2⟩)
    · exact row_conclusion hF.twistedF4 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, h.1, h.2.1, Is2F4.of_mulEquiv e'.symm h.2.2⟩)
    · exact row_conclusion hF.suzuki hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, f, h.1, h.2.1, IsSz.of_mulEquiv e'.symm h.2.2⟩)
    · exact row_conclusion hF.tits hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsTits.of_mulEquiv e'.symm htits⟩)
  ·
    rcases hn with rfl | rfl
    · exact row_conclusion hF.l4Two hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSL.of_mulEquiv e'.symm hmod⟩)
    · exact row_conclusion hF.l5Two hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => ⟨e'.isSimpleGroup, IsPSL.of_mulEquiv e'.symm hmod⟩)
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact row_conclusion hF.m11 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.m12 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.m22 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.m23 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.m24 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exfalso
      obtain ⟨Q, hQ⟩ := hQ
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h9 := sq_dvd_card_of_noncyclic hQ
      rw [Nat.card_congr e.toEquiv, hJ1] at h9
      omega
    · exact row_conclusion hF.j2 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.j4 hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.hs hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.he hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)
    · exact row_conclusion hF.ru hnab hQ hw2 hK hL32
        (fun G _ X ⟨e'⟩ => famSporadic_of e' hnab _ e)

end Main

end CFSG.Quasithin.SBd19F
