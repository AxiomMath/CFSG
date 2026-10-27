module

public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.R3c3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def RankOneConcl (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, Even n ∧ IsPSL 2 2 n X) ∨ (∃ n : ℕ, Even n ∧ IsPSU 3 2 n X) ∨ IsPSL 3 2 1 X

theorem isPSU_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : IsPSU n p f Y) : IsPSU n p f X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem isPSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : IsPSL n p f Y) : IsPSL n p f X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem RankOneConcl.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : RankOneConcl X) : RankOneConcl Y := by
  rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
  · exact Or.inl ⟨n, hn, isPSL_of_mulEquiv e.symm h⟩
  · exact Or.inr (Or.inl ⟨n, hn, isPSU_of_mulEquiv e.symm h⟩)
  · exact Or.inr (Or.inr (isPSL_of_mulEquiv e.symm h))

section Center

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_le_pCore_of_centerOf_eq {L : Subgroup G}
    (h : centerOf L = CFSG.Open.pCoreOf 2 L) :
    Subgroup.center ↥L ≤ CFSG.Open.pCore 2 ↥L := by
  intro x hx
  have hxc : (x : G) ∈ centerOf L := by
    show (x : G) ∈ L ⊓ Subgroup.centralizer (L : Set G)
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)
  rw [h] at hxc
  obtain ⟨y, hy, hyx⟩ := hxc
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

theorem isPGroup_two_center {L : Subgroup G} (h : centerOf L = CFSG.Open.pCoreOf 2 L) :
    IsPGroup 2 ↥(Subgroup.center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.to_le (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2)
    (center_le_pCore_of_centerOf_eq h)

theorem pRank_three_eq_quotient_center {L : Subgroup G}
    (h : centerOf L = CFSG.Open.pCoreOf 2 L) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  exact R3c.pRank_three_top_eq_center_quotient (isPGroup_two_center h)

theorem false_of_two_le_quotient {L : Subgroup G} (h : centerOf L = CFSG.Open.pCoreOf 2 L)
    (hrk : CFSG.Open.pRank 3 L = 1) {Y : Type} [Group Y] [Finite Y]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* Y) (hY : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) : False := by
  rw [pRank_three_eq_quotient_center h,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e] at hrk
  omega

theorem false_of_two_le_top {L : Subgroup G} (hrk : CFSG.Open.pRank 3 L = 1) {Y : Type} [Group Y]
    [Finite Y] (e : ↥L ≃* Y) (hY : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) : False := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e] at hrk
  omega

end Center

section Simple

variable {X : Type} [Group X]

theorem center_eq_bot_of_simple_perfect (hs : IsSimpleGroup X) (hp : Group.IsPerfect X) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
      have : b ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp this a
    have : Nontrivial X := hs.toNontrivial
    have : Group.IsPerfect X := hp
    exact Group.IsPerfect.not_isSolvable (G := X) (Group.isSolvable_of_comm hcomm)

theorem exists_noncomm_of_simple_perfect (hs : IsSimpleGroup X) (hp : Group.IsPerfect X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : Nontrivial X := hs.toNontrivial
  have : Group.IsPerfect X := hp
  exact Group.IsPerfect.not_isSolvable (G := X) (Group.isSolvable_of_comm hcon)

noncomputable def quotCenterEquivOfSimple (hs : IsSimpleGroup X) (hp : Group.IsPerfect X) :
    (X ⧸ Subgroup.center X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_perfect hs hp)).trans
    QuotientGroup.quotientBot

variable [Finite X]

theorem pCore_eq_bot_of_simple_perfect (hs : IsSimpleGroup X) (hp : Group.IsPerfect X) :
    CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Unc25Small.normal_pGroup_eq_bot_of_simple hs (exists_noncomm_of_simple_perfect hs hp) _
    CFSG.pCore_isPGroup

noncomputable def quotPCoreEquivOfSimple (hs : IsSimpleGroup X) (hp : Group.IsPerfect X) :
    (X ⧸ CFSG.pCore 2 X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq (pCore_eq_bot_of_simple_perfect hs hp)).trans
    QuotientGroup.quotientBot

end Simple

end CFSG.Quasithin.R3c3
