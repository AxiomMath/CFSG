module

public import CFSG.Timmesfeld.Bridge.Asc72WIso
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Bridge.Asc72WreathConn

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

theorem derivedSeries_one_eq_two_of_sup_eq_top {X : Type*} [Group X] {N A : Subgroup X}
    [N.Normal] (hN : ⁅N, N⁆ = N) (hA : IsMulCommutative A) (hNA : N ⊔ A = ⊤) :
    derivedSeries X 1 = N ∧ derivedSeries X 2 = N := by
  have h1 : derivedSeries X 1 = N := by
    rw [derivedSeries_one]
    refine le_antisymm (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNA hA) ?_
    calc N = ⁅N, N⁆ := hN.symm
      _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := Subgroup.commutator_mono le_top le_top
  refine ⟨h1, ?_⟩
  rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ, h1, hN]

theorem commutator_self_eq_of_isSimpleGroup {X : Type*} [Group X] {M : Subgroup X}
    (hMs : IsSimpleGroup M) (hMna : ¬ IsMulCommutative M) : ⁅M, M⁆ = M := by
  haveI := hMs
  haveI := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hMna
  exact Subgroup.isPerfect_iff.mp inferInstance

theorem sup_subgroupOf_sup_eq_top {X : Type*} [Group X] (A B : Subgroup X) :
    A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
  apply Subgroup.map_injective (A ⊔ B).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_isMulCommutative_of_ne_bot
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : M ≠ ⊥) : ¬ IsMulCommutative M := by
  intro hc
  exact hM (hrad M inferInstance (Group.isSolvable_of_comm fun a b => hc.is_comm.comm a b))

theorem sup_zpowers_eq_top_of_not_two_lt_index {M : Subgroup G} (hidx : ¬ 2 < M.index) {u : G}
    (hu : u ∉ M) : M ⊔ Subgroup.zpowers u = ⊤ := by
  have hlt : M < M ⊔ Subgroup.zpowers u :=
    lt_of_le_of_ne le_sup_left fun h => hu (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
  have hmul := Subgroup.relIndex_mul_index (le_sup_left : M ≤ M ⊔ Subgroup.zpowers u)
  have hM0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel1 : M.relIndex (M ⊔ Subgroup.zpowers u) ≠ 1 := fun h =>
    hlt.not_ge (Subgroup.relIndex_eq_one.mp h)
  have hrel0 : M.relIndex (M ⊔ Subgroup.zpowers u) ≠ 0 := fun h => hM0 (by rw [← hmul, h, zero_mul])
  have hidx0 : (M ⊔ Subgroup.zpowers u).index ≠ 0 := fun h => hM0 (by rw [← hmul, h, mul_zero])
  have h2 : 2 * (M ⊔ Subgroup.zpowers u).index ≤ M.index :=
    hmul ▸ Nat.mul_le_mul_right _ (by omega)
  rw [← Subgroup.index_eq_one]
  omega

theorem derivedSeries_eq_or_l2Wreath_or_almostSimpleCase
    (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    derivedSeries G 1 = derivedSeries G 2 ∨
      (∃ f r : ℕ, 2 ≤ f ∧ 2 ≤ r ∧ ∃ Φ : G ≃* L2Wreath f r, ∀ u ∈ D, ∃ i j : Fin r, i ≠ j ∧
        IsConj (SemidirectProduct.inr (Equiv.swap i j)) (Φ u)) ∨
      AlmostSimpleCase G D := by
  obtain ⟨M, hM⟩ := exists_minimalNormal hS
  haveI := hM.1
  have hC := centralizer_eq_bot_of_minimal hS hrad hM
  by_cases hMs : IsSimpleGroup M
  · have hperf : ⁅M, M⁆ = M :=
      commutator_self_eq_of_isSimpleGroup hMs (not_isMulCommutative_of_ne_bot hrad hM.2.1)
    obtain ⟨u, hu⟩ := hS.nonempty
    rcases simple_minimal_cases hS hrad hM hMs with hDM | ⟨hdisj, hcong⟩
    ·
      left
      obtain ⟨h1, h2⟩ := derivedSeries_one_eq_two_of_sup_eq_top hperf
        (Subgroup.zpowers_isMulCommutative u) (by rw [hS.eq_top_of_subset M hDM, top_sup_eq])
      rw [h1, h2]
    · by_cases hidx : 2 < M.index
      · exact Or.inr (Or.inr ⟨M, hM.1, hM, fun N hN => eq_of_minimal hS hrad hM hN, hMs, hC,
          hidx, widthOne_of_disjoint hS hdisj hcong,
          fun u hu => isOddTranspClass_conjSet hS hrad hM hMs hu⟩)
      ·
        left
        obtain ⟨h1, h2⟩ := derivedSeries_one_eq_two_of_sup_eq_top hperf
          (Subgroup.zpowers_isMulCommutative u)
          (sup_zpowers_eq_top_of_not_two_lt_index hidx (hdisj u hu))
        rw [h1, h2]
  ·
    right; left
    obtain ⟨W⟩ := nonempty_wreathData hS hrad hM hMs
    obtain ⟨f, hf, Φ, hΦ⟩ := W.exists_mulEquiv_l2Wreath hS hC
    refine ⟨f, W.r, hf, W.two_le, Φ, fun u hu => ?_⟩
    obtain ⟨i, j, hij, hΦu⟩ := hΦ u hu
    exact ⟨i, j, hij, (WreathConn.isConj_inr_swap_iff hij (Φ u)).2 ⟨i, j, hij, hΦu⟩⟩

section SupZpowers

variable {M : Subgroup G} {u : G}

theorem setup_sup_zpowers (hcls : IsOddTranspClass (conjSet M u)) :
    Setup ↥(M ⊔ Subgroup.zpowers u) (conjSet M u) :=
  ⟨hcls.1, hcls.2.1, hcls.2.2⟩

theorem eq_bot_of_not_le_subgroupOf [M.Normal] (hMs : IsSimpleGroup M)
    (hcent : Subgroup.centralizer (M : Set G) = ⊥) {N : Subgroup ↥(M ⊔ Subgroup.zpowers u)}
    [hN : N.Normal] (hNM : ¬ M.subgroupOf (M ⊔ Subgroup.zpowers u) ≤ N) : N = ⊥ := by
  have hle : M ≤ M ⊔ Subgroup.zpowers u := le_sup_left
  haveI := hMs
  haveI hM'n : (M.subgroupOf (M ⊔ Subgroup.zpowers u)).Normal := Subgroup.normal_subgroupOf
  haveI : IsSimpleGroup ↥(M.subgroupOf (M ⊔ Subgroup.zpowers u)) :=
    (Subgroup.subgroupOfEquivOfLe hle).isSimpleGroup
  have hdisj : Disjoint N (M.subgroupOf (M ⊔ Subgroup.zpowers u)) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((N ⊓ M.subgroupOf (M ⊔ Subgroup.zpowers u)).subgroupOf
          (M.subgroupOf (M ⊔ Subgroup.zpowers u))) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      rw [disjoint_iff]
      exact h.eq_bot_of_le inf_le_right
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact absurd (h.trans inf_le_left) hNM
  rw [eq_bot_iff]
  intro n hn
  have hnc : (n : G) ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := Subgroup.commute_of_normal_of_disjoint N _ hN hM'n hdisj n ⟨m, hle hm⟩ hn
      (Subgroup.mem_subgroupOf.mpr hm)
    exact (congrArg Subtype.val h.eq).symm
  rw [hcent, Subgroup.mem_bot] at hnc
  exact Subgroup.mem_bot.mpr (Subtype.ext hnc)

theorem solvableRadical_sup_zpowers_eq_bot [M.Normal] (hMs : IsSimpleGroup M)
    (hMna : ¬ IsMulCommutative M) (hcent : Subgroup.centralizer (M : Set G) = ⊥) :
    ∀ N : Subgroup ↥(M ⊔ Subgroup.zpowers u), N.Normal → Group.IsSolvable N → N = ⊥ := by
  intro N hN hNs
  refine eq_bot_of_not_le_subgroupOf hMs hcent fun hle => hMna ?_
  have e := Subgroup.subgroupOfEquivOfLe (le_sup_left : M ≤ M ⊔ Subgroup.zpowers u)
  haveI : Group.IsSolvable ↥(M.subgroupOf (M ⊔ Subgroup.zpowers u)) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  haveI : Group.IsSolvable ↥M := solvable_of_solvable_injective (f := e.symm.toMonoidHom)
    e.symm.injective
  haveI := hMs
  exact ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩

theorem derivedSeries_sup_zpowers [M.Normal] (hMs : IsSimpleGroup M)
    (hMna : ¬ IsMulCommutative M) :
    derivedSeries ↥(M ⊔ Subgroup.zpowers u) 1 = derivedSeries ↥(M ⊔ Subgroup.zpowers u) 2 := by
  have e := Subgroup.subgroupOfEquivOfLe (le_sup_left : M ≤ M ⊔ Subgroup.zpowers u)
  haveI := hMs
  haveI : (M.subgroupOf (M ⊔ Subgroup.zpowers u)).Normal := Subgroup.normal_subgroupOf
  have hM'na : ¬ IsMulCommutative ↥(M.subgroupOf (M ⊔ Subgroup.zpowers u)) := by
    rintro ⟨⟨hc⟩⟩
    exact hMna ⟨⟨fun a b => by simpa using congrArg e (hc (e.symm a) (e.symm b))⟩⟩
  have hperf := commutator_self_eq_of_isSimpleGroup e.isSimpleGroup hM'na
  haveI := Subgroup.zpowers_isMulCommutative u
  obtain ⟨h1, h2⟩ := derivedSeries_one_eq_two_of_sup_eq_top hperf
    (Subgroup.subgroupOf_isMulCommutative (H := Subgroup.zpowers u) (K := M ⊔ Subgroup.zpowers u))
    (sup_subgroupOf_sup_eq_top M (Subgroup.zpowers u))
  rw [h1, h2]

end SupZpowers

end CFSG.OddTranspositions.PartFour
