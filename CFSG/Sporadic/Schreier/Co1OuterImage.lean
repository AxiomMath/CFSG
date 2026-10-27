module

public import CFSG.Sporadic.Schreier.Co1Lift
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions

@[expose] noncomputable def stabSub : Subgroup GA := stabH.subgroupOf GA

theorem mem_stabSub {g : GA} : g ∈ stabSub ↔ (g : GL24) ∈ stabH := Subgroup.mem_subgroupOf

@[expose] noncomputable def stabSubEquiv :
    stabSub ≃* Blueprint.NativeSporadic.Co2 :=
  (Subgroup.subgroupOfEquivOfLe stabH_le_GA).trans stabCo2Equiv

noncomputable def co1GAEquiv : Blueprint.NativeSporadic.Co1 ≃* GA :=
  CFSG.Sporadic.SmallF2.seedEquiv CFSG.Sporadic.Co1.co1Facts.toBaseFacts

@[expose] noncomputable def stabSubCo1 :
    Subgroup Blueprint.NativeSporadic.Co1 :=
  stabSub.map (co1GAEquiv.symm : GA →* Blueprint.NativeSporadic.Co1)

noncomputable def stabSubCo1Equiv : stabSubCo1 ≃* stabSub :=
  (@MulEquiv.subgroupMap (↥GA) Blueprint.NativeSporadic.Co1 (Subgroup.toGroup GA) Units.instGroup
    co1GAEquiv.symm stabSub).symm

theorem finite_GA :
    Finite GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)

theorem finite_Co1 : Finite Blueprint.NativeSporadic.Co1 :=
  have := finite_GA
  Finite.of_equiv _ co1GAEquiv.symm.toEquiv

theorem stabSub_fix_trivial
    (α : MulAut GA) (hα : ∀ h ∈ stabSub, α h = h) : α = 1 :=
  pointwise_Co2_automorphism_stabilizer_trivial α fun h hh => hα h (mem_stabSub.mpr hh)

theorem stabSubCo1_fix_trivial
    (α : MulAut Blueprint.NativeSporadic.Co1)
    (hα : ∀ h ∈ stabSubCo1, α h = h) : α = 1 := by
  have hβ := stabSub_fix_trivial ((co1GAEquiv.symm.trans α).trans co1GAEquiv) fun h hh => by
    have hm : co1GAEquiv.symm h ∈ stabSubCo1 := Subgroup.mem_map_of_mem _ hh
    change co1GAEquiv (α (co1GAEquiv.symm h)) = h
    rw [hα _ hm, MulEquiv.apply_symm_apply]
  refine MulEquiv.ext fun x => ?_
  have hx := congrArg (fun β : MulAut GA => co1GAEquiv.symm (β (co1GAEquiv x))) hβ
  simpa using hx

@[expose] def ClassInvariant {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ α : MulAut G, ∃ g : G, H.map α.toMonoidHom = H.map (MulAut.conj g).toMonoidHom

theorem card_outer_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (equivalence e).toEquiv

theorem isPGroup_two_of_card_dvd {X : Type*} [Group X] {n : ℕ} (h : Nat.card X ∣ 2 ^ n) :
    IsPGroup 2 X := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact IsPGroup.of_card hk

universe u

theorem exists_card_outer_stabSub
    (hCo2 : ∀ (K : Type u) [Group K], K ≃* Blueprint.NativeSporadic.Co2 →
      Finite (Outer K) ∧ IsPGroup 2 (Outer K) ∧ Group.IsSolvable (Outer K)) :
    ∃ n : ℕ, Nat.card (Outer stabSub) = 2 ^ n := by
  obtain ⟨hfin, hpH, -⟩ : Finite (Outer (ULift.{u} stabSub)) ∧
      IsPGroup 2 (Outer (ULift.{u} stabSub)) ∧ Group.IsSolvable (Outer (ULift.{u} stabSub)) :=
    hCo2 _ (MulEquiv.ulift.trans stabSubEquiv)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpH
  have hU : Nat.card (Outer (ULift.{u} stabSub)) = Nat.card (Outer stabSub) :=
    card_outer_congr MulEquiv.ulift
  exact ⟨n, hU ▸ hn⟩

theorem co2_stabilizing_outer_image_two_group_of_inputs
    (hCo2 : ∀ (K : Type*) [Group K], K ≃* Blueprint.NativeSporadic.Co2 →
      Finite (Outer K) ∧ IsPGroup 2 (Outer K) ∧ Group.IsSolvable (Outer K)) :
    (Finite ((subgroupStabAut stabSub).map (QuotientGroup.mk' (inner GA))) ∧
      IsPGroup 2 ((subgroupStabAut stabSub).map (QuotientGroup.mk' (inner GA))) ∧
      Nat.card ((subgroupStabAut stabSub).map (QuotientGroup.mk' (inner GA))) ∣
        Nat.card (Outer Blueprint.NativeSporadic.Co2)) ∧
    (Finite ((subgroupStabAut stabSubCo1).map
        (QuotientGroup.mk' (inner Blueprint.NativeSporadic.Co1))) ∧
      IsPGroup 2 ((subgroupStabAut stabSubCo1).map
        (QuotientGroup.mk' (inner Blueprint.NativeSporadic.Co1))) ∧
      Nat.card ((subgroupStabAut stabSubCo1).map
        (QuotientGroup.mk' (inner Blueprint.NativeSporadic.Co1))) ∣
        Nat.card (Outer Blueprint.NativeSporadic.Co2)) ∧
    (ClassInvariant stabSub →
      Finite (Outer Blueprint.NativeSporadic.Co1) ∧
        IsPGroup 2 (Outer Blueprint.NativeSporadic.Co1) ∧
        ∀ K : Subgroup (Outer Blueprint.NativeSporadic.Co1), Odd (Nat.card K) → K = ⊥) := by
  have hfinGA := finite_GA
  have hfinCo1 := finite_Co1
  obtain ⟨n, hn⟩ := exists_card_outer_stabSub hCo2
  have hOutH : Nat.card (Outer stabSub) = Nat.card (Outer Blueprint.NativeSporadic.Co2) :=
    card_outer_congr stabSubEquiv
  have hOutH' : Nat.card (Outer stabSubCo1) = Nat.card (Outer stabSub) :=
    card_outer_congr stabSubCo1Equiv
  obtain ⟨-, -, -, -, hdiv, hall⟩ :=
    subgroup_stabilizer_outer_restriction_bound stabSub stabSub_fix_trivial
  obtain ⟨-, -, -, -, hdiv', -⟩ :=
    subgroup_stabilizer_outer_restriction_bound stabSubCo1 stabSubCo1_fix_trivial
  rw [hOutH'] at hdiv'
  have h1 : Nat.card ((subgroupStabAut stabSub).map (QuotientGroup.mk' (inner GA))) ∣ 2 ^ n := by
    rw [← hn]
    exact hdiv
  have h1' : Nat.card ((subgroupStabAut stabSubCo1).map
      (QuotientGroup.mk' (inner Blueprint.NativeSporadic.Co1))) ∣ 2 ^ n := by
    rw [← hn]
    exact hdiv'
  rw [hOutH] at hdiv hdiv'
  refine ⟨⟨inferInstance, isPGroup_two_of_card_dvd h1, hdiv⟩,
    ⟨inferInstance, isPGroup_two_of_card_dvd h1', hdiv'⟩, fun hcls => ?_⟩
  have hGA : Nat.card (Outer GA) ∣ 2 ^ n := by
    rw [← hn]
    exact hall hcls
  have hCo1GA : Nat.card (Outer Blueprint.NativeSporadic.Co1) = Nat.card (Outer GA) :=
    card_outer_congr co1GAEquiv
  have hCo1 : Nat.card (Outer Blueprint.NativeSporadic.Co1) ∣ 2 ^ n := by
    rw [hCo1GA]
    exact hGA
  refine ⟨inferInstance, isPGroup_two_of_card_dvd hCo1, fun K hK => ?_⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    ((Subgroup.card_subgroup_dvd_card K).trans hCo1)
  refine Subgroup.eq_bot_of_card_eq K ?_
  rcases k with _ | k
  · rw [hk, pow_zero]
  · rw [hk, pow_succ] at hK
    exact absurd (Nat.odd_mul.mp hK).2 (by decide)

end CFSG.Sporadic.Co1Schreier
