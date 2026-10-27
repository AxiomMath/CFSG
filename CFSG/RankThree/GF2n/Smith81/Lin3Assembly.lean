module

public import CFSG.RankThree.GF2n.Smith81.LinEven
public import CFSG.RankThree.GF2n.Smith81.Lin212Cond
public import CFSG.RankThree.GF2n.Smith81.Lin31Back
public import CFSG.RankThree.GF2n.Smith81.LinOdd

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Lin212RestProp (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
    ((Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z) ∧
    (∃ K : Subgroup G, K ≤ M ∧ K ⊓ Q = ⊥ ∧ K ⊔ Q = M ∧ ∃ q ∈ Q, q * x * q⁻¹ ∈ K)

@[expose] def Lin212RestStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      Lin212RestProp M Q Z

@[expose] def Lin212TwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B 2 V₁ V₂ →
      Lin212Prop M Q Z B V₁ V₂

@[expose] def Lin28aBelowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B X : Subgroup G) (x : G) (n : ℕ)
    (V₁ V₂ : Subgroup G), Smith1981Below (Nat.card G) → Ctx M Q Z B →
    LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → Sit M Q Z X x → Q ⊓ QB X ≠ ⊥

theorem lin28aBelow_of_parity (hE : Lin28aEvenBelowStatement) (hO : Lin28aOddBelowStatement) :
    Lin28aBelowStatement := fun G _ _ M Q Z B X x n V₁ V₂ hb hc hS hn hs => by
  rcases Nat.even_or_odd n with h | h
  · exact hE G M Q Z B X x n V₁ V₂ hb hc hS hn h hs
  · exact hO G M Q Z B X x n V₁ V₂ hb hc hS hn h hs

section Assembly

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem cqt_eq_of_class (hs : Sit M Q Z X x) (h4 : ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) :
    CQt Q Z (Subgroup.zpowers x) =
      (((Q ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ Z : Subgroup G) : Set G) := by
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hZle : Z ≤ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    refine ⟨hs.hyp.Z_normal.1 hz, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hxZ z hz
    calc z * x = (x * z * x⁻¹) * x := by rw [this]
      _ = x * z := by group
  rw [sup_eq_left.mpr hZle]
  have hcl : InZClass Z x := inZClass_of_mem_root hs.conj hs.mem hs.ne_one
  refine ((smith_1_11_first hs.hyp hxZ hx2).mp ?_).symm
  ext y
  constructor
  · rintro ⟨⟨s, hs', rfl⟩, ⟨z', hz', hzy⟩⟩
    have h1 : InZClass Z (x * z') := by
      have := hcl.conj s
      rw [← hzy] at this
      exact this
    have := h4 z' hz' h1
    rw [Set.mem_singleton_iff, ← hzy, this]
    simp
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨⟨1, Q.one_mem, by simp⟩, ⟨1, Z.one_mem, by simp⟩⟩

theorem lin212Statement_of (hcond : Lin212CondStatement) (h28a : Lin28aBelowStatement)
    (hrest : Lin212RestStatement) (htwo : Lin212TwoStatement) : Lin212Statement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    subst hn2
    exact htwo G M Q Z B V₁ V₂ hb hc hS
  · intro X x hs
    have hne := h28a G M Q Z B X x n V₁ V₂ hb hc hS h hs
    obtain ⟨c1, c2, c3, c4, c7⟩ := hcond G M Q Z B n V₁ V₂ hb hc hS h X x hs hne
    obtain ⟨c5, c8⟩ := hrest G M Q Z B n V₁ V₂ hb hc hS h X x hs hne
    exact ⟨c1, c2, c3, c4, c5, cqt_eq_of_class hs c4, c7, c8⟩

@[expose] def Lin28TwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B 2 V₁ V₂ → Lin28Prop M Q Z

theorem lin28Statement_of (h28a : Lin28aBelowStatement) (h28c : Lin28CondStatement)
    (htwo : Lin28TwoStatement) : Lin28Statement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    subst hn2
    exact htwo G M Q Z B V₁ V₂ hb hc hS
  · intro X x hs
    have hne := h28a G M Q Z B X x n V₁ V₂ hb hc hS h hs
    exact h28c G M Q Z B X x n V₁ V₂ hb hc hS h hs hne

theorem lin3Statement_of_leaves (hBin : LinBInStatement) (hFwd : Lin31FwdStatement)
    (hTwo : Lin31TwoStatement) (h28c : Lin28CondStatement) (hmod : LinModuleStatement)
    (h7 : Lin212C7Statement) (hrest : Lin212RestStatement) (h212two : Lin212TwoStatement)
    (h28two : Lin28TwoStatement) (h213 : Lin213Statement) (h26 : Lin26Statement) :
    Lin3Statement := by
  have h31 := lin31Statement_of hBin hFwd hTwo
  have hcond := lin212Cond_of h28c hmod h7 h31
  have h28a := lin28aBelow_of_parity (lin28aEven_of h31 hcond) (lin28aOdd_of h31 hcond)
  exact lin3Statement_of h31 (lin28Statement_of h28a h28c h28two)
    (lin212Statement_of hcond h28a hrest h212two) h213 h26

end Assembly

end CFSG.RankThree.GF2n.Smith81
