module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint TableBExc.E6Three CFSG.SeitzReduction

namespace E6ThreeEnd

local instance e6TwoPilotLayerNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem e6RepPreHigh_two_eq_bE6 : E6Pilot.e6RepPreHigh 2 = bE6 0 := by
  decide

section Weyl


theorem e6RepWeyl_two_smul_bE6 : E6Pilot.e6RepWeyl 2 • bE6 0 = highRoot .E6 := by
  rw [← e6RepPreHigh_two_eq_bE6]
  exact E6Pilot.e6RepWeyl_smul_e6RepPreHigh 2

theorem image_perpB0 : (E6Pilot.e6RepWeyl 2 • ·) '' perpB0 = E6Pilot.a5LeviRoots := by
  ext δ
  constructor
  · rintro ⟨γ, ⟨hγ, hγ0⟩, rfl⟩
    refine ⟨CFSG.LieType.Chevalley.IsRoot.smul hγ _, ?_⟩
    change (E6Pilot.e6RepWeyl 2 • γ) (highNode .E6) = 0
    rw [← EPilot.iform_highRoot (Or.inl rfl) (E6Pilot.e6RepWeyl 2 • γ), ← e6RepWeyl_two_smul_bE6,
      iform_smul, iform_comm, hγ0]
  · rintro ⟨hδ, hδ0⟩
    refine ⟨(E6Pilot.e6RepWeyl 2)⁻¹ • δ, ⟨CFSG.LieType.Chevalley.IsRoot.smul hδ _, ?_⟩,
      smul_inv_smul _ δ⟩
    rw [← iform_smul (E6Pilot.e6RepWeyl 2), smul_inv_smul, e6RepWeyl_two_smul_bE6, iform_comm,
      EPilot.iform_highRoot (Or.inl rfl) δ]
    exact hδ0

end Weyl

section Conj

variable {K : Type} [Field K]

theorem map_conj_rootSpan_perpB0 :
    (rootSpan .E6 K perpB0).map
        (MulAut.conj (E6Pilot.e6RepConj K 2 : ModGL .E6 K)).toMonoidHom =
      rootSpan .E6 K E6Pilot.a5LeviRoots := by
  rw [E6Pilot.map_conj_e6RepConj_rootSpan 2 (fun ρ hρ => hρ.1), image_perpB0]

theorem mem_leviB0_iff_conj {x : adjointGroup .E6 K} :
    x ∈ leviB0 K ↔
      E6Pilot.e6RepConj K 2 * x * (E6Pilot.e6RepConj K 2)⁻¹ ∈ E6Pilot.a5Levi K := by
  rw [leviB0, Subgroup.mem_subgroupOf, E6Pilot.a5Levi, Subgroup.mem_subgroupOf,
    ← map_conj_rootSpan_perpB0, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have e : y = (x : ModGL .E6 K) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at hyx
      simpa using hyx
    rw [← e]
    exact hy

theorem map_conj_leviB0 :
    (leviB0 K).map (MulAut.conj (E6Pilot.e6RepConj K 2)).toMonoidHom = E6Pilot.a5Levi K := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_leviB0_iff_conj.mp hy
  · intro hx
    refine ⟨(E6Pilot.e6RepConj K 2)⁻¹ * x * E6Pilot.e6RepConj K 2, ?_, ?_⟩
    · rw [mem_leviB0_iff_conj]
      simpa [mul_assoc] using hx
    · simp [MulAut.conj_apply, mul_assoc]


variable [CharP K 2]

theorem coe_conj_uE6Two_zero :
    ((E6Pilot.e6RepConj K 2 * uE6Two 0 * (E6Pilot.e6RepConj K 2)⁻¹ : adjointGroup .E6 K) :
        ModGL .E6 K) =
      pinnedX .E6 K (highRoot .E6) 1 * pinnedX .E6 K (-highRoot .E6) 1 := by
  have h1 := E6Pilot.canonicalRep_mul_pinnedX_mul_inv_of_charTwo (E6Pilot.e6RepWeyl 2)
    (isRoot_bE6 0) (1 : K)
  have h2 := E6Pilot.canonicalRep_mul_pinnedX_mul_inv_of_charTwo (E6Pilot.e6RepWeyl 2)
    (isRoot_neg_bE6 0) (1 : K)
  rw [e6RepWeyl_two_smul_bE6] at h1
  rw [smul_neg, e6RepWeyl_two_smul_bE6] at h2
  change canonicalRep (coxeterSystem .E6) K (E6Pilot.e6RepWeyl 2) *
      (pinnedX .E6 K (bE6 0) 1 * pinnedX .E6 K (-bE6 0) 1) *
        (canonicalRep (coxeterSystem .E6) K (E6Pilot.e6RepWeyl 2))⁻¹ = _
  rw [← h1, ← h2]
  group

theorem coe_conj_uE6Two_zero_mem_highRootSL2 :
    ((E6Pilot.e6RepConj K 2 * uE6Two 0 * (E6Pilot.e6RepConj K 2)⁻¹ : adjointGroup .E6 K) :
        ModGL .E6 K) ∈ EPilot.highRootSL2 .E6 K := by
  rw [coe_conj_uE6Two_zero]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨1, rfl⟩))

end Conj

section Layer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isQuasisimple_leviB0 : CFSG.IsQuasisimple (leviB0 K) := by
  have e : leviB0 K ≃* E6Pilot.a5Levi K :=
    ((MulAut.conj (E6Pilot.e6RepConj K 2)).subgroupMap (leviB0 K)).trans
      (MulEquiv.subgroupCongr map_conj_leviB0)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm E6Pilot.isQuasisimple_a5Levi

theorem exists_mul_of_mem_centralizer_uE6Two_zero (hK : Nat.card K = 2) {c : adjointGroup .E6 K}
    (hc : c ∈ Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K))) :
    ∃ y ∈ Subgroup.zpowers (uE6Two (K := K) 0), ∃ l ∈ leviB0 K, c = y * l := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set N := E6Pilot.e6RepConj K 2 with hN
  set x := N * uE6Two 0 * N⁻¹ with hx
  have hXJ : Subgroup.zpowers x ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact coe_conj_uE6Two_zero_mem_highRootSL2
  have hord : orderOf x = 3 := by
    rw [hx, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj N).injective, orderOf_uE6Two h2 0]
  have hcard : Nat.card (Subgroup.zpowers x) = Nat.card K + 1 := by
    rw [Nat.card_zpowers, hord, hK]
  have hcx :
      N * c * N⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers x : Set (adjointGroup .E6 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    have hc' : c * uE6Two 0 = uE6Two 0 * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hxc : x * (N * c * N⁻¹) = N * c * N⁻¹ * x := by
      rw [hx]
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc (uE6Two 0) c, ← hc', mul_assoc]
    exact ((Commute.zpow_left hxc k).eq)
  obtain ⟨y, hy, d, hd, hcyd⟩ := E6Pilot.exists_mul_of_mem_centralizer_nonsplit_E6 hXJ hcard
    (Subgroup.isCyclic_zpowers x) hcx
  refine ⟨N⁻¹ * y * N, ?_, N⁻¹ * d * N, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [hx, conj_zpow]
    group
  · rw [mem_leviB0_iff_conj, ← hN]
    simpa [mul_assoc] using hd
  · have e : c = N⁻¹ * (N * c * N⁻¹) * N := by group
    rw [e, hcyd]
    group

theorem largeEvenLayer_centralizer_uE6Two_zero (hK : Nat.card K = 2) :
    LargeEvenLayer (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K))) = leviB0 K ∧
      IsComponentOf (leviB0 K)
        (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K))) := by
  have hcomm : ∀ y ∈ Subgroup.zpowers (uE6Two (K := K) 0), ∀ l ∈ leviB0 K, y * l = l * y := by
    rintro _ ⟨k, rfl⟩ l hl
    exact (Commute.zpow_left (uE6Two_zero_comm_of_mem_leviB0 hl) k).eq
  refine TableBSymp.largeEvenLayer_eq_of_commutator_mem ?_ ?_ isQuasisimple_leviB0
  · intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mpr (uE6Two_zero_comm_of_mem_leviB0 hj).symm
  · intro g hg h hh
    obtain ⟨y₁, hy₁, l₁, hl₁, rfl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hg
    obtain ⟨y₂, hy₂, l₂, hl₂, rfl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hh
    have hm : l₁ * l₂ * l₁⁻¹ * l₂⁻¹ ∈ leviB0 K :=
      mul_mem (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁)) (inv_mem hl₂)
    have h12 : y₁ * y₂ = y₂ * y₁ := by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₁
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₂
      exact (Commute.zpow_zpow_self _ a b).eq
    have e : y₁ * l₁ * (y₂ * l₂) * (y₁ * l₁)⁻¹ * (y₂ * l₂)⁻¹ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by
      have c1 := hcomm y₂ hy₂ l₁ hl₁
      have c2 := hcomm y₁⁻¹ (inv_mem hy₁) (l₁ * l₂ * l₁⁻¹) (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁))
      have c3 := hcomm y₂⁻¹ (inv_mem hy₂) _ hm
      calc y₁ * l₁ * (y₂ * l₂) * (y₁ * l₁)⁻¹ * (y₂ * l₂)⁻¹
          = y₁ * (l₁ * y₂) * l₂ * l₁⁻¹ * y₁⁻¹ * l₂⁻¹ * y₂⁻¹ := by group
        _ = y₁ * y₂ * ((l₁ * l₂ * l₁⁻¹) * y₁⁻¹) * l₂⁻¹ * y₂⁻¹ := by rw [← c1]; group
        _ = y₁ * y₂ * y₁⁻¹ * ((l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * y₂⁻¹) := by rw [← c2]; group
        _ = (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) := by rw [← c3]; group
        _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [h12]; group
    rw [e]
    exact hm

end Layer

section Input


theorem ggE6TwoLayerInput_holds : GGE6TwoLayerInput := by
  intro K _ _ hK
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  exact largeEvenLayer_centralizer_uE6Two_zero hK

end Input

end E6ThreeEnd

end CFSG.StandardType
