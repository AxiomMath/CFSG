module

public import CFSG.RankThree.GF2n.Smith81.Statement
public import CFSG.RankThree.GF2n.Stroth80.Ctx
public import CFSG.RankThree.GF2n.Tim81.Basic
public import CFSG.Timmesfeld.Outcome

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem _root_.CFSG.RankThree.GF2n.Stroth80.StrothHyp.toTim81Hyp {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) : Tim81.Hyp M Z := by
  obtain ⟨n, k, -, hcp⟩ := H.cp
  exact ⟨H.o2, H.maxLocal, H.fitting, H.maxAb, ⟨H.maxAb.prop.2.2, sq_eq_one_of_cp hcp⟩, H.ti⟩

theorem _root_.CFSG.RankThree.GF2n.Stroth80.StrothHyp.isSylow_of_sylow_M [Finite G]
    {M Q Z : Subgroup G} (H : StrothHyp M Q Z) (S : Sylow 2 M) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = (S : Subgroup M).map M.subtype :=
  H.toTim81Hyp.isSylow_of_sylow_M S

theorem isRootInvolutionSet_of_local {D : Set G} (hD2 : ∀ d ∈ D, orderOf d = 2)
    (hloc : ∀ v ∈ D, ∀ x ∈ D, ∀ y ∈ D, Commute x v → Commute y v →
      (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
        (orderOf (x * y) = 4 → (x * y) ^ 2 ∈ D))
    (hdiam : ∀ x ∈ D, ∀ y ∈ D, ∃ v ∈ D, Commute x v ∧ Commute y v) :
    Timmesfeld.IsRootInvolutionSet D := by
  refine ⟨hD2, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · obtain ⟨v, hv, hdv, hev⟩ := hdiam d hd e he
    exact (hloc v hv d hd e he hdv hev).1
  · obtain ⟨v, hv, hdv, hev⟩ := hdiam d hd e he
    exact (hloc v hv d hd e he hdv hev).2 h4

section Cases

variable (M Q Z B : Subgroup G)

@[expose] def TypeE6 (n : ℕ) : Prop :=
  (¬ IsTIMod M Q (LB M Q B) ∧ CaseE6 M Q Z B n) ∨
    (n = 2 ∧ CaseD2 M Q Z B ∧ ¬ NoA2 Q Z (LB M Q B))

@[expose] def OrthCase : Prop :=
  ∃ t : G, CtxD4 M Q Z B t ∧ (CaseE1 M Q Z B t ∨ ∃ m : ℕ, CaseE2 M Q Z B t m)

@[expose] def ECase : Prop :=
  ∃ t : G, CtxD4 M Q Z B t ∧ (CaseE3 M Q Z B ∨ CaseE4 M Q Z B t ∨ CaseE5 M Q Z B t)

@[expose] def Remaining : Prop :=
  OrthCase M Q Z B ∨ ECase M Q Z B ∨ ∃ n : ℕ, TypeE6 M Q Z B n

end Cases

structure Cfg (M Q Z B : Subgroup G) : Prop where
  ctx : Ctx M Q Z B
  conclusion : StrothConclusion M Q Z B

structure RemCfg (M Q Z B : Subgroup G) : Prop extends Cfg M Q Z B where
  remaining : Remaining M Q Z B

@[expose] def Smith1981TheoremBelow (N : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < N → ∀ (M Q Z : Subgroup G), StrothHyp M Q Z →
    ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
      StrothConclusion M Q Z B → SmithConclusion M Q Z B

@[expose] def Smith216At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (M Q Z B : Subgroup G), Smith1981TheoremBelow (Nat.card G) → RemCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ x z' w y : G, IsConj z x → IsConj z z' → IsConj z w → IsConj z y →
      Commute x z' → Commute z' w → Commute w y →
        ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y

@[expose] def Smith216Below (N : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < N → Smith216At G

@[expose] def Smith1981Below (N : ℕ) : Prop := Smith1981TheoremBelow N ∧ Smith216Below N

theorem Smith1981TheoremBelow.mono {N N' : ℕ} (h : N ≤ N') (hb : Smith1981TheoremBelow N') :
    Smith1981TheoremBelow N :=
  fun G _ _ hG => hb G (lt_of_lt_of_le hG h)

theorem Smith1981Below.zero : Smith1981Below 0 :=
  ⟨fun G _ _ hG => absurd hG (Nat.not_lt_zero _), fun G _ _ hG => absurd hG (Nat.not_lt_zero _)⟩

theorem Smith1981Below.succ {N : ℕ} (hb : Smith1981Below N)
    (hT : ∀ (G : Type) [Group G] [Finite G], Nat.card G = N → ∀ (M Q Z : Subgroup G),
      StrothHyp M Q Z → ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
        StrothConclusion M Q Z B → SmithConclusion M Q Z B)
    (h216 : ∀ (G : Type) [Group G] [Finite G], Nat.card G = N → Smith216At G) :
    Smith1981Below (N + 1) := by
  refine ⟨fun G _ _ hG => ?_, fun G _ _ hG => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hG with h | h
    · exact hb.1 G h
    · exact hT G h
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hG with h | h
    · exact hb.2 G h
    · exact h216 G h

theorem smith1981_of_below (h : ∀ N : ℕ, Smith1981Below N → Smith1981Below (N + 1)) :
    Smith1981Statement := by
  have key : ∀ N : ℕ, Smith1981Below N := by
    intro N
    induction N with
    | zero => exact Smith1981Below.zero
    | succ N ih => exact h N ih
  intro G _ _ M Q Z hH B hB hBQ hBZ hC
  exact (key (Nat.card G + 1)).1 G (Nat.lt_succ_self _) M Q Z hH B hB hBQ hBZ hC

@[expose] def TimmesfeldOutcomeStatement : Prop :=
  ∀ (X : Type) [Group X] (D : Set X), Timmesfeld.Hyp X D → Timmesfeld.Outcome X

section Normal

variable [Finite G]

theorem closure_conjClass_eq_normalClosure (z : G) :
    Subgroup.closure {g : G | IsConj z g} = Subgroup.normalClosure ({z} : Set G) := by
  rw [Subgroup.normalClosure]
  congr 1
  ext g
  simp [Group.mem_conjugatesOfSet_iff]

theorem outcome_normalClosure (hT : TimmesfeldOutcomeStatement) {z : G}
    (hroot : Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g})
    (hconj : ∀ w : G, IsConj z w →
      ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹)
    (hodd : pPrimeCore 2 G = ⊥) (hO2 : pCore 2 G = ⊥)
    (hnondeg : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4) :
    Timmesfeld.Outcome ↥(Subgroup.normalClosure ({z} : Set G)) := by
  classical
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  haveI : X.Normal := Subgroup.normalClosure_normal
  have hzX : z ∈ X := Subgroup.subset_normalClosure rfl
  have hCX : ∀ w : G, IsConj z w → w ∈ X := fun w hw =>
    Subgroup.conjugatesOfSet_subset_normalClosure (Group.mem_conjugatesOfSet_iff.mpr ⟨z, rfl, hw⟩)
  let D : Set ↥X := {x | IsConj z (x : G)}
  refine hT ↥X D ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨⟨z, hzX⟩, Set.ext fun x => ?_⟩
    simp only [D, Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨c, hcX, hc⟩ := hconj x hx
      exact isConj_iff.mpr ⟨⟨c, hcX⟩, Subtype.ext (by simp [hc])⟩
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      exact isConj_iff.mpr ⟨c, by simpa using congrArg Subtype.val hc⟩
  ·
    refine ⟨fun d hd => ?_, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact hroot.1 _ hd
    · have := hroot.2.1 _ hd _ he
      simpa [← Subgroup.orderOf_coe] using this
    · have h4' : orderOf ((d : G) * (e : G)) = 4 := by
        simpa [← Subgroup.orderOf_coe] using h4
      have := hroot.2.2 _ hd _ he h4'
      show IsConj z (((d * e) ^ 2 : ↥X) : G)
      simpa using this
  ·
    have h1 : (Subgroup.closure D).map X.subtype = X := by
      rw [MonoidHom.map_closure]
      have himg : X.subtype '' D = {g : G | IsConj z g} := by
        ext g
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx
        · intro hg
          exact ⟨⟨g, hCX g hg⟩, hg, rfl⟩
      rw [himg, closure_conjClass_eq_normalClosure]
    apply Subgroup.map_injective X.subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  ·
    intro N hN hNodd
    have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hNodd
    have hle : N ≤ pPrimeCore 2 ↥X := le_sSup ⟨hN, hcop⟩
    have hnorm : ((pPrimeCore 2 ↥X).map X.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hcard : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥X).map X.subtype)) := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact pPrimeCore_coprime_card
    have hle2 : (pPrimeCore 2 ↥X).map X.subtype ≤ pPrimeCore 2 G := le_sSup ⟨hnorm, hcard⟩
    rw [hodd, le_bot_iff] at hle2
    have hbot := (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hle2
    exact le_bot_iff.mp (hbot ▸ hle)
  ·
    intro N hN hNp
    have hle : N ≤ pCore 2 ↥X := le_sSup ⟨hN, hNp⟩
    have hnorm : ((pCore 2 ↥X).map X.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hp : IsPGroup 2 ((pCore 2 ↥X).map X.subtype) :=
      (pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
    have hle2 : (pCore 2 ↥X).map X.subtype ≤ pCore 2 G := le_sSup ⟨hnorm, hp⟩
    rw [hO2, le_bot_iff] at hle2
    have hbot := (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hle2
    exact le_bot_iff.mp (hbot ▸ hle)
  ·
    obtain ⟨d, e, hd, he, h4⟩ := hnondeg
    exact ⟨⟨d, hCX d hd⟩, hd, ⟨e, hCX e he⟩, he, by
      rw [← Subgroup.orderOf_coe]
      simpa using h4⟩

end Normal

end CFSG.RankThree.GF2n.Smith81
