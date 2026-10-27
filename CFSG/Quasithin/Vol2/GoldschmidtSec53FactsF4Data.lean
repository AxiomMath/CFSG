module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut
public import CFSG.LieType.Ree.LargeReeFixedGroupSchreier
public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LieType.Ree.BorelSelfNormalizers
public import CFSG.LieType.Ree.FixedBruhatDecomposition
public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum

public section

namespace CFSG.Quasithin.H13.Sec53F.ReeF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Open CFSG.QuasithinUnique

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

local notation "Γ₄" => F4.reeGamma K a
local notation "U₄" => F4.reeFixedPosUnipotent K a
local notation "H₄" => F4.reeFixedTorus K a
local notation "𝒰" => Subgroup.subgroupOf U₄ Γ₄
local notation "ℋ" => Subgroup.subgroupOf H₄ Γ₄

theorem f4_center (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ y : ↥Γ₄, (∀ x, y * x = x * y) → y = 1 := by
  intro y hy
  have : y ∈ Subgroup.center ↥Γ₄ := Subgroup.mem_center_iff.mpr fun g => (hy g).symm
  rw [large_Ree_fixed_group_center_trivial a K hK] at this
  exact Subgroup.mem_bot.mp this

theorem f4_sylow : IsSylowTwoOf (𝒰) ⊤ := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨P, hP⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have h := isSylowTwoOf_top_of_sylow (show Sylow 2 ↥Γ₄ from P)
  rwa [show ((show Sylow 2 ↥Γ₄ from P) : Subgroup ↥Γ₄) = 𝒰 from hP] at h

theorem f4_H_comm : ∀ x ∈ ℋ, ∀ y ∈ ℋ, x * y = y * x := by
  intro x hx y hy
  exact Subtype.ext (reeFixedTorus_mul_comm (Subgroup.mem_subgroupOf.1 hx)
    (Subgroup.mem_subgroupOf.1 hy))

theorem f4_H_le : ℋ ≤ Subgroup.normalizer ((𝒰 : Subgroup ↥Γ₄) : Set ↥Γ₄) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact Subgroup.mem_normalizer_iff.mp (reeFixedBorel_le_normalizer_reeFixedPosUnipotent
    (reeFixedTorus_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hh))) u.1

theorem f4_U_inf_H : ∀ x ∈ 𝒰, x ∈ ℋ → x = 1 := by
  intro x hx hxH
  have : (x : ModGL F4.tag K) ∈ torusGroup F4.tag K ⊓ posUnipotent F4.tag K :=
    ⟨(Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hxH)).1,
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1⟩
  rw [torusGroup_inf_posUnipotent] at this
  exact Subtype.ext (Subgroup.mem_bot.mp this)

theorem f4_B_eq : ∀ g ∈ Subgroup.normalizer ((𝒰 : Subgroup ↥Γ₄) : Set ↥Γ₄),
    ∃ u ∈ 𝒰, ∃ h ∈ ℋ, g = u * h := by
  intro g hg
  rw [normalizer_reeFixedPosUnipotent_subgroupOf, Subgroup.mem_subgroupOf] at hg
  have hg' : (g : ModGL F4.tag K) ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hg
  rw [reeFixedBorel_eq_mul'] at hg'
  obtain ⟨u, hu, h, hh, hgh⟩ := hg'
  exact ⟨⟨u, (Subgroup.mem_inf.1 hu).2⟩, Subgroup.mem_subgroupOf.2 hu,
    ⟨h, (Subgroup.mem_inf.1 hh).2⟩, Subgroup.mem_subgroupOf.2 hh, Subtype.ext hgh.symm⟩

end CFSG.Quasithin.H13.Sec53F.ReeF4
