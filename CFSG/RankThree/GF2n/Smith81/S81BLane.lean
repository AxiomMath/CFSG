module

public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.Sec216

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Lane

theorem smith216E_of_nonfused (hN : Smith212ENonfusedStatement) (h213 : Smith213EStatement)
    (hCount : Smith216ECountStatement) (hOdd : Smith216EOddStatement) :
    Smith216EStatement := by
  intro G _ _ M Q Z B IH hc z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy
  refine smith_2_16 hc.ctx.hyp hz hz1 ?_ (h213 G M Q Z B IH hc z hz hz1) ?_ ?_ hx hz' hw hy
    hxz hzw hwy
  · intro x' hxM hxQ hxc y' hy'cos hy'c
    have h1 : conjClassSet z ∩ cosetSet x' Z = {x'} :=
      conjClassSet_inter_cosetSet_eq hxc (hN G M Q Z B IH hc z hz hz1 x' hxM hxQ hxc)
    have hmem : y' ∈ conjClassSet z ∩ cosetSet x' Z := ⟨hy'c, hy'cos⟩
    rw [h1] at hmem
    exact hmem
  · exact fun A C hA hC hAC hCA => hCount G M Q Z B IH hc z hz hz1 A C hA hC hAC hCA
  · exact fun x' z'' w' y' hx' hz'' hw' hy' hxz' hzw' hwy' hxw hzy ho1 ho2 =>
      hOdd G M Q Z B IH hc z hz hz1 x' z'' w' y' hx' hz'' hw' hy' hxz' hzw' hwy' hxw hzy ho1 ho2

end Lane

section Cases

variable {G : Type} [Group G]

@[expose] def InCaseE3U (M Q Z B : Subgroup G) : Prop :=
  ∃ t : G, CtxD4 M Q Z B t ∧ CaseE3U M Q Z B

theorem SmithECfg.inCase {M Q Z B : Subgroup G} (h : SmithECfg M Q Z B) :
    InCaseE3U M Q Z B ∨ InCaseE3L M Q Z B ∨ InCaseE4 M Q Z B ∨ InCaseE5 M Q Z B := by
  obtain ⟨t, ht, h'⟩ := (ECase.cases_iff M Q Z B).mp h.e
  rcases h' with h' | h' | h' | h'
  · exact Or.inl ⟨t, ht, h'⟩
  · exact Or.inr (Or.inl ⟨t, ht, h'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t, ht, h'⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨t, ht, h'⟩))

end Cases

@[expose] def Smith212ENonfusedE3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q →
      IsConj z x → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)

@[expose] def Smith212ENonfusedE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q →
      IsConj z x → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)

@[expose] def Smith212ENonfusedE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q →
      IsConj z x → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)

@[expose] def Smith212ENonfusedE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q →
      IsConj z x → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)

theorem smith212ENonfused_iff_cases :
    Smith212ENonfusedStatement ↔ Smith212ENonfusedE3UStatement ∧ Smith212ENonfusedE3LStatement ∧
      Smith212ENonfusedE4Statement ∧ Smith212ENonfusedE5Statement := by
  constructor
  · intro h
    exact ⟨fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc⟩
  · rintro ⟨h3U, h3L, h4, h5⟩ G _ _ M Q Z B IH hc
    rcases hc.inCase with hh | hh | hh | hh
    · exact h3U G M Q Z B IH hc hh
    · exact h3L G M Q Z B IH hc hh
    · exact h4 G M Q Z B IH hc hh
    · exact h5 G M Q Z B IH hc hh

theorem smith212ENonfused_of_cases (h3U : Smith212ENonfusedE3UStatement)
    (h3L : Smith212ENonfusedE3LStatement) (h4 : Smith212ENonfusedE4Statement)
    (h5 : Smith212ENonfusedE5Statement) : Smith212ENonfusedStatement :=
  smith212ENonfused_iff_cases.mpr ⟨h3U, h3L, h4, h5⟩

@[expose] def Smith213E3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ z ∈ Z, z ≠ 1 →
      Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))

@[expose] def Smith213E3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ z ∈ Z, z ≠ 1 →
      Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))

@[expose] def Smith213E4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ z ∈ Z, z ≠ 1 →
      Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))

@[expose] def Smith213E5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ z ∈ Z, z ≠ 1 →
      Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))

theorem smith213E_iff_cases :
    Smith213EStatement ↔ Smith213E3UStatement ∧ Smith213E3LStatement ∧ Smith213E4Statement ∧
      Smith213E5Statement := by
  constructor
  · intro h
    exact ⟨fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc⟩
  · rintro ⟨h3U, h3L, h4, h5⟩ G _ _ M Q Z B IH hc
    rcases hc.inCase with hh | hh | hh | hh
    · exact h3U G M Q Z B IH hc hh
    · exact h3L G M Q Z B IH hc hh
    · exact h4 G M Q Z B IH hc hh
    · exact h5 G M Q Z B IH hc hh

theorem smith213E_of_cases (h3U : Smith213E3UStatement) (h3L : Smith213E3LStatement)
    (h4 : Smith213E4Statement) (h5 : Smith213E5Statement) : Smith213EStatement :=
  smith213E_iff_cases.mpr ⟨h3U, h3L, h4, h5⟩

@[expose] def Smith216ECountE3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ A C : Subgroup G,
      IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
        ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
          Nat.card Z ^ 2 < Nat.card S

@[expose] def Smith216ECountE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ A C : Subgroup G,
      IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
        ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
          Nat.card Z ^ 2 < Nat.card S

@[expose] def Smith216ECountE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ A C : Subgroup G,
      IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
        ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
          Nat.card Z ^ 2 < Nat.card S

@[expose] def Smith216ECountE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ A C : Subgroup G,
      IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
        ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
          Nat.card Z ^ 2 < Nat.card S

theorem smith216ECount_iff_cases :
    Smith216ECountStatement ↔ Smith216ECountE3UStatement ∧ Smith216ECountE3LStatement ∧
      Smith216ECountE4Statement ∧ Smith216ECountE5Statement := by
  constructor
  · intro h
    exact ⟨fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc⟩
  · rintro ⟨h3U, h3L, h4, h5⟩ G _ _ M Q Z B IH hc
    rcases hc.inCase with hh | hh | hh | hh
    · exact h3U G M Q Z B IH hc hh
    · exact h3L G M Q Z B IH hc hh
    · exact h4 G M Q Z B IH hc hh
    · exact h5 G M Q Z B IH hc hh

theorem smith216ECount_of_cases (h3U : Smith216ECountE3UStatement)
    (h3L : Smith216ECountE3LStatement) (h4 : Smith216ECountE4Statement)
    (h5 : Smith216ECountE5Statement) : Smith216ECountStatement :=
  smith216ECount_iff_cases.mpr ⟨h3U, h3L, h4, h5⟩

@[expose] def Smith219EInspectionE3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B →
      (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
        Timmesfeld.Outcome (FStar G) →
          ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .E6 0 2 f

@[expose] def Smith219EInspectionE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B →
      (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
        Timmesfeld.Outcome (FStar G) →
          ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .twistedE6 0 2 f

@[expose] def Smith219EInspectionE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B →
      (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
        Timmesfeld.Outcome (FStar G) →
          ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .E7 0 2 f

@[expose] def Smith219EInspectionE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B →
      (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
        Timmesfeld.Outcome (FStar G) →
          ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .E8 0 2 f

theorem smith219EInspection_iff_cases :
    Smith219EInspectionStatement ↔ Smith219EInspectionE3UStatement ∧
      Smith219EInspectionE3LStatement ∧ Smith219EInspectionE4Statement ∧
      Smith219EInspectionE5Statement := by
  constructor
  · intro h
    exact ⟨fun G _ _ M Q Z B IH hc hh hr ho =>
        let ⟨t, ht, h'⟩ := hh; (h G M Q Z B IH hc hr ho).1 t ht h',
      fun G _ _ M Q Z B IH hc hh hr ho =>
        let ⟨t, ht, h'⟩ := hh; (h G M Q Z B IH hc hr ho).2.1 t ht h',
      fun G _ _ M Q Z B IH hc hh hr ho =>
        let ⟨t, ht, h'⟩ := hh; (h G M Q Z B IH hc hr ho).2.2.1 t ht h',
      fun G _ _ M Q Z B IH hc hh hr ho =>
        let ⟨t, ht, h'⟩ := hh; (h G M Q Z B IH hc hr ho).2.2.2 t ht h'⟩
  · rintro ⟨h3U, h3L, h4, h5⟩ G _ _ M Q Z B IH hc hr ho
    refine ⟨fun t ht h => ?_, fun t ht h => ?_, fun t ht h => ?_, fun t ht h => ?_⟩
    · exact h3U G M Q Z B IH hc ⟨t, ht, h⟩ hr ho
    · exact h3L G M Q Z B IH hc ⟨t, ht, h⟩ hr ho
    · exact h4 G M Q Z B IH hc ⟨t, ht, h⟩ hr ho
    · exact h5 G M Q Z B IH hc ⟨t, ht, h⟩ hr ho

theorem smith219EInspection_of_cases (h3U : Smith219EInspectionE3UStatement)
    (h3L : Smith219EInspectionE3LStatement) (h4 : Smith219EInspectionE4Statement)
    (h5 : Smith219EInspectionE5Statement) : Smith219EInspectionStatement :=
  smith219EInspection_iff_cases.mpr ⟨h3U, h3L, h4, h5⟩

end CFSG.RankThree.GF2n.Smith81
