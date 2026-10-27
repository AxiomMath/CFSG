module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree

public section

namespace CFSG.Quasithin.H13.Sec53F.TriD4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem entry_rootDiagUnit {τ : Tag} (δ : K ≃+* K) (a : Fin τ.rank → Kˣ) :
    Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit τ a) =
      rootDiagUnit τ (fun i => Units.map δ.toRingHom.toMonoidHom (a i)) :=
  Units.ext (entrywise_rootDiag (τ := τ) δ.toRingHom a)

theorem entry_torusElt {τ : Tag} (δ : K ≃+* K) (i : Fin τ.rank) (t : Kˣ) :
    Units.map (entrywiseHom δ.toRingHom) (torusElt τ K i t) =
      torusElt τ K i (Units.map δ.toRingHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, entry_rootDiagUnit]
  congr 1
  funext j
  simp [map_zpow]

theorem entry_mem_torusGroup {τ : Tag} (δ : K ≃+* K) {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    Units.map (entrywiseHom δ.toRingHom) h ∈ torusGroup τ K := by
  have : torusGroup τ K ≤ (torusGroup τ K).comap (Units.map (entrywiseHom δ.toRingHom)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [entry_torusElt]
    exact torusElt_mem_torusGroup _ _
  exact this hh

section Struct

variable [Finite K] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "U₀" => graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom
local notation "H₁" => graphFixedRootTorus TwistTag.D4 K σ.toRingHom
local notation "𝒰" => Subgroup.subgroupOf U₀ C₀
local notation "ℋ" => Subgroup.subgroupOf H₁ C₀

theorem d4_center : ∀ y : ↥C₀, (∀ x, y * x = x * y) → y = 1 := by
  intro y hy
  have : y ∈ Subgroup.center ↥C₀ := Subgroup.mem_center_iff.mpr fun g => (hy g).symm
  rw [exceptional_fixed_center_trivial TwistTag.D4 K σ] at this
  exact Subgroup.mem_bot.mp this

theorem d4_sylow [CharP K 2] : IsSylowTwoOf (𝒰) ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : U₀ ≤ C₀ := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf U₀ C₀ := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  exact isSylowTwoOf_subgroupOf_top hUsyl

theorem d4_H_comm : ∀ a ∈ ℋ, ∀ b ∈ ℋ, a * b = b * a := by
  intro a ha b hb
  exact Subtype.ext (graphFixedRootTorus_mul_comm (Subgroup.mem_subgroupOf.1 ha)
    (Subgroup.mem_subgroupOf.1 hb))

theorem d4_H_le : ℋ ≤ Subgroup.normalizer ((𝒰 : Subgroup ↥C₀) :
    Set ↥C₀) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have := Subgroup.mem_normalizer_iff.mp
    (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hh)) u.1
  exact this

theorem d4_U_inf_H : ∀ x ∈ 𝒰, x ∈ ℋ → x = 1 := by
  intro x hx hxH
  have : (x : ModGL TwistTag.D4.tag K) ∈ H₁ ⊓ U₀ := ⟨hxH, hx⟩
  rw [graphFixedRootTorus_inf_graphFixedPosUnipotent] at this
  exact Subtype.ext (Subgroup.mem_bot.mp this)

theorem d4_B_eq : ∀ g ∈ Subgroup.normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀),
    ∃ u ∈ 𝒰, ∃ h ∈ ℋ, g = u * h := by
  intro g hg
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  have hUC : U₀ ≤ C₀ := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  rw [normalizer_subgroupOf_eq' hUC,
    (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1, Subgroup.mem_subgroupOf]
    at hg
  have hg' : (g : ModGL TwistTag.D4.tag K) ∈
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := hg
  rw [graphFixedRootBorel_eq_mul' σ.surjective] at hg'
  obtain ⟨u, hu, h, hh, hgh⟩ := hg'
  exact ⟨⟨u, hUC hu⟩, Subgroup.mem_subgroupOf.2 hu,
    ⟨h, graphFixedRootTorus_le _ _ _ hh⟩, Subgroup.mem_subgroupOf.2 hh, Subtype.ext hgh.symm⟩

end Struct

end CFSG.Quasithin.H13.Sec53F.TriD4
