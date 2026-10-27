module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapRankOneFixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignCores

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance twistedE6PilotSwapPiecesNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotSwapPiecesNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Model

variable {K : Type} [Field K]

theorem relLevi_le_centralizer_relLevi {I J : Finset (Fin Tag.F4.rank)}
    (h : ∀ α ∈ F4Pilot.signedSimpleRoots (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)),
      ∀ β ∈ F4Pilot.signedSimpleRoots (relNodeSet J : Set (Fin TwistTag.E6.tag.rank)),
        α ≠ β ∧ α ≠ -β ∧ ¬ IsRoot Tag.E6 (α + β)) :
    relLevi K J ≤ centralizer (relLevi K I : Set (ModGL TwistTag.E6.tag K)) := by
  refine iSup₂_le fun β hβ => ?_
  rw [← le_centralizer_iff]
  refine iSup₂_le fun α hα => ?_
  obtain ⟨h1, h2, h3⟩ := h α hα β hβ
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact ((CFSG.LieType.Chevalley.simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (F4Pilot.isRoot_of_mem_signedSimpleRoots hα) (F4Pilot.isRoot_of_mem_signedSimpleRoots hβ)
    h1 h2).2 h3 K x hx y hy).eq.symm

theorem relLevi_zero_root_check : ∀ j ∈ ([0, 2, 4, 5] : List (Fin Tag.E6.rank)),
    ∀ a ∈ ([1, -1] : List ℤ), ∀ b ∈ ([1, -1] : List ℤ),
      (a • Pi.single 1 1 : Fin Tag.E6.rank → ℤ) ≠ b • Pi.single j 1 ∧
      (a • Pi.single 1 1 : Fin Tag.E6.rank → ℤ) ≠ -(b • Pi.single j 1) ∧
      (a • Pi.single 1 1 + b • Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6 := by
  decide +kernel

theorem eq_of_mem_relNodeSet_zero {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ relNodeSet ({0} : Finset (Fin Tag.F4.rank))) : i = (1 : Fin Tag.E6.rank) := by
  rw [mem_relNodeSet, Finset.mem_singleton] at hi
  have key : ∀ i : Fin Tag.E6.rank, e6IndexToF4 i = 0 → i = 1 := by decide
  exact key i hi

theorem mem_of_mem_relNodeSet_two_three {r : Fin Tag.F4.rank} (hr : r = 2 ∨ r = 3)
    {j : Fin TwistTag.E6.tag.rank} (hj : j ∈ relNodeSet ({r} : Finset (Fin Tag.F4.rank))) :
    j ∈ ([0, 2, 4, 5] : List (Fin Tag.E6.rank)) := by
  rw [mem_relNodeSet, Finset.mem_singleton] at hj
  have key : ∀ j : Fin Tag.E6.rank, (e6IndexToF4 j = 2 ∨ e6IndexToF4 j = 3) →
      j ∈ ([0, 2, 4, 5] : List (Fin Tag.E6.rank)) := by decide
  exact key j (hj ▸ hr)

theorem relLevi_le_centralizer_zero {r : Fin Tag.F4.rank} (hr : r = 2 ∨ r = 3) :
    relLevi K {r} ≤ centralizer (relLevi K {0} : Set (ModGL TwistTag.E6.tag K)) := by
  refine relLevi_le_centralizer_relLevi fun α hα β hβ => ?_
  obtain ⟨i, hi, hαi⟩ := hα
  obtain ⟨j, hj, hβj⟩ := hβ
  have hi1 := eq_of_mem_relNodeSet_zero hi
  subst hi1
  have hj' := mem_of_mem_relNodeSet_two_three hr hj
  have hsign : ∀ (γ : Fin Tag.E6.rank → ℤ) (k : Fin Tag.E6.rank),
      (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) →
        ∃ c ∈ ([1, -1] : List ℤ), γ = c • Pi.single k 1 := by
    rintro γ k (rfl | rfl)
    · exact ⟨1, by simp, by rw [one_smul]⟩
    · exact ⟨-1, by simp, by rw [neg_one_smul]⟩
  obtain ⟨a, ha, rfl⟩ := hsign α 1 hαi
  obtain ⟨b, hb, rfl⟩ := hsign β j hβj
  obtain ⟨h1, h2, h3⟩ := relLevi_zero_root_check j hj' a ha b hb
  exact ⟨h1, h2, fun hr' => h3 (mem_rootFinset.2 hr')⟩

theorem relRankOne_le_su6Levi (σ : K →+* K) {r : Fin Tag.F4.rank} (hr : r ≠ 0) :
    relRankOne σ r ≤ su6Levi σ := by
  refine le_inf ((relRankOne_le_relLevi σ r).trans (relLevi_le_subsystemGroup fun j hj => ?_))
    (relRankOne_le_C0 σ r)
  rw [mem_relNodeSet, Finset.mem_singleton] at hj
  have key : ∀ j : Fin Tag.E6.rank, e6IndexToF4 j ≠ 0 → j ≠ 1 := by decide
  exact key j (hj ▸ hr)

theorem relRankOne_le_omegaMinusLevi (σ : K →+* K) {r : Fin Tag.F4.rank} (hr : r ≠ 3) :
    relRankOne σ r ≤ omegaMinusLevi σ := by
  refine le_inf ((relRankOne_le_relLevi σ r).trans (relLevi_le_subsystemGroup fun j hj => ?_))
    (relRankOne_le_C0 σ r)
  rw [mem_relNodeSet, Finset.mem_singleton] at hj
  have key : ∀ j : Fin Tag.E6.rank, e6IndexToF4 j ≠ 3 → j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
  exact key j (hj ▸ hr)

theorem pow_card_eq_one_of_mem_relLeviTorus {A : Subgroup Kˣ} [Finite A]
    {I : Finset (Fin Tag.F4.rank)} {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ relLeviTorus K A I) : g ^ Nat.card A = 1 := by
  obtain ⟨B, hB, rfl⟩ := hg
  rw [← map_pow]
  convert map_one ((rootDiagUnitHom TwistTag.E6.tag K).comp (relTupleHom K))
  funext a
  rw [Pi.pow_apply, Pi.one_apply]
  have hBa : B a ∈ (if a ∈ I then (⊥ : Subgroup Kˣ) else A) := hB a (Set.mem_univ a)
  split_ifs at hBa with ha
  · rw [mem_bot] at hBa
    rw [hBa, one_pow]
  · exact congrArg Subtype.val (pow_card_eq_one' (G := A) (x := ⟨B a, hBa⟩))

end Model

section InG

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}
  (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ)

@[expose] noncomputable def relTorusG (r : Fin Tag.F4.rank) : Subgroup G :=
  modelToG e (relLeviTorus K A {r})

@[expose] noncomputable def relRankOneG (r : Fin Tag.F4.rank) : Subgroup G :=
  modelToG e (relRankOne σ r)

theorem relTorusG_le_centralizer_self (r : Fin Tag.F4.rank) :
    relTorusG e A r ≤ centralizer (relTorusG e A r : Set G) :=
  modelToG_le_centralizer e (relLeviTorus_le_centralizer_self A {r})

theorem relTorusG_le_centralizer_singleton {t : G} (htL : t ∈ centralizer (L : Set G))
    (r : Fin Tag.F4.rank) : relTorusG e A r ≤ centralizer ({t} : Set G) := fun τ hτ =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL τ (modelToG_le e _ hτ))

theorem odd_orderOf_of_mem_relTorusG [Finite A] (hA : Odd (Nat.card A)) (r : Fin Tag.F4.rank) :
    ∀ x ∈ relTorusG e A r, Odd (orderOf x) := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_modelToG e).1 hx
  have h1 : orderOf (((e.symm c : L) : G)) = orderOf (c : ModGL TwistTag.E6.tag K) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  rw [h1]
  exact hA.of_dvd_nat (orderOf_dvd_of_pow_eq_one (pow_card_eq_one_of_mem_relLeviTorus hc))

theorem relTorusG_le_centralizer_neighbourTorus (N : F4Pilot.AmalgamNeighbour)
    {r : Fin Tag.F4.rank} (hr : r ∈ N.nodes) :
    relTorusG e A r ≤ centralizer (modelToG e (neighbourTorus K A N) : Set G) := by
  have h1 : modelToG e (neighbourTorus K A N) ≤ relTorusG e A r :=
    modelToG_mono e (neighbourTorus_le_relLeviTorus A N (Finset.singleton_subset_iff.2 hr))
  exact (relTorusG_le_centralizer_self e A r).trans (centralizer_le (SetLike.coe_subset_coe.2 h1))

theorem relRankOneG_le_centralizer (r : Fin Tag.F4.rank) :
    relRankOneG e r ≤ centralizer (relTorusG e A r : Set G) :=
  modelToG_le_centralizer e (relRankOne_le_centralizer σ A r)

theorem perfect_le_modelToG_perfectCore [Finite G] [Finite K] {P : Subgroup G} (hPL : P ≤ L)
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) {r : Fin Tag.F4.rank}
    (hPT : P ≤ centralizer (relTorusG e A r : Set G)) (hPp : ⁅P, P⁆ = P) :
    P ≤ modelToG e (perfectCore (graphFixedRootGroup TwistTag.E6 K σ ⊓
      centralizer (relLeviTorus K A {r} : Set (ModGL TwistTag.E6.tag K)))) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Q : Subgroup (ModGL TwistTag.E6.tag K) :=
    ((P.subgroupOf L).map e.toMonoidHom).map (graphFixedRootGroup TwistTag.E6 K σ).subtype with hQ
  have hQC : Q ≤ graphFixedRootGroup TwistTag.E6 K σ := map_subtype_le _
  have hQp : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← map_commutator, ← map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self hPL hPp]
  have hTC := relLeviTorus_le_C0 hA ({r} : Finset (Fin Tag.F4.rank))
  have hQT : Q ≤ centralizer (relLeviTorus K A {r} : Set (ModGL TwistTag.E6.tag K)) := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro τ hτ
    have hτG : ((e.symm ⟨τ, hTC hτ⟩ : L) : G) ∈ relTorusG e A r := symm_mem_modelToG e hτ
    have h1 : (p : G) * ((e.symm ⟨τ, hTC hτ⟩ : L) : G) = ((e.symm ⟨τ, hTC hτ⟩ : L) : G) * p :=
      (mem_centralizer_iff.1 (hPT (mem_subgroupOf.1 hp)) _ hτG).symm
    have h2 : p * e.symm ⟨τ, hTC hτ⟩ = e.symm ⟨τ, hTC hτ⟩ * p := Subtype.ext h1
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul] at h4
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    exact h4.symm
  have hQle : Q ≤ perfectCore (graphFixedRootGroup TwistTag.E6 K σ ⊓
      centralizer (relLeviTorus K A {r} : Set (ModGL TwistTag.E6.tag K))) :=
    CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hQC hQT) hQp
  intro x hx
  refine (mem_modelToG e).2 ⟨e ⟨x, hPL hx⟩, hQle ⟨_, ⟨⟨x, hPL hx⟩, hx, rfl⟩, rfl⟩, ?_⟩
  rw [MulEquiv.symm_apply_apply]

theorem perfect_le_modelToG_relLevi [Finite G] [Finite K] (hA3 : 3 ≤ Nat.card A)
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) {P : Subgroup G} (hPL : P ≤ L)
    {r : Fin Tag.F4.rank} (hPT : P ≤ centralizer (relTorusG e A r : Set G)) (hPp : ⁅P, P⁆ = P) :
    P ≤ modelToG e (relLevi K {r}) := by
  refine (perfect_le_modelToG_perfectCore e A hPL hA hPT hPp).trans (modelToG_mono e ?_)
  rw [perfectCore_C0_inf_centralizer_relLeviTorus σ hA3 (by simp)]
  exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

theorem perfect_le_relRankOneG_one [Finite G] [Finite K] [CharP K 2] (hA3 : 3 ≤ Nat.card A)
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    (hperf : ⁅relRankOne σ 1, relRankOne σ 1⁆ = relRankOne σ 1) {P : Subgroup G} (hPL : P ≤ L)
    (hPT : P ≤ centralizer (relTorusG e A 1 : Set G)) (hPp : ⁅P, P⁆ = P) :
    P ≤ relRankOneG e 1 := by
  have h := perfect_le_modelToG_perfectCore e A hPL hA hPT hPp
  rwa [perfectCore_C0_inf_centralizer_one σ hA3 hperf] at h

end InG

end CFSG.SeitzReduction.TwistedE6Pilot
