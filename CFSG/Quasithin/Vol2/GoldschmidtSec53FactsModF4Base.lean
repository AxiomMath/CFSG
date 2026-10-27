module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsF4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieF4
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral

public section

namespace CFSG.Quasithin.H13.Sec53F.ReeF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.BA
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (generation_zero generation_one levi_hom)
open CFSG.QuasithinUnique.Setup.X6 (large_Ree_opposite_simple_blocks_generate_rank_one_model)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem mem_perfectCore_subgroupOf {G : Type} [Group G] {Γ P : Subgroup G} (hP : P ≤ Γ)
    (x : ↥Γ) : x ∈ perfectCore (P.subgroupOf Γ) ↔ (x : G) ∈ perfectCore P := by
  have h := perfectCore_map_inj Γ.subtype Γ.subtype_injective (P.subgroupOf Γ)
  rw [Subgroup.map_subgroupOf_eq_of_le hP] at h
  rw [h]
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [Subtype.ext hyx] at hy

theorem commutator_le_perfectCore {G : Type*} [Group G] {P V : Subgroup G} (hV : V ≤ P) :
    ⁅V, perfectCore P⁆ ≤ perfectCore P := by
  rw [Subgroup.commutator_le]
  intro v hv g hg
  have hvN : v ∈ Subgroup.normalizer (perfectCore P : Set G) :=
    normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hV hv))
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.1 hvN g).1 hg) (inv_mem hg)

theorem reeLocalParabolic_le_reeGamma (j : Fin F4.fixedOrbitCount) :
    F4.reeLocalParabolic K a j ≤ F4.reeGamma K a := inf_le_left

theorem reeFixedOrbitComplementUnipotent_le_reeGamma (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeGamma K a := inf_le_right

theorem parabolic_subgroupOf_le_normalizer (j : Fin F4.fixedOrbitCount) :
    (F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a) ≤
      Subgroup.normalizer (((F4.reeFixedOrbitComplementUnipotent K a j).subgroupOf
        (F4.reeGamma K a) : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have h := Subgroup.mem_normalizer_iff.1
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.parabolic_le_normalizer_rad (K := K) (a := a) j
      hp) (v : ModGL F4.tag K)
  simpa [Subgroup.mem_subgroupOf] using h

theorem isPGroup_subgroupOf_rad (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) :
    IsPGroup 2 ↥((F4.reeFixedOrbitComplementUnipotent K a j).subgroupOf (F4.reeGamma K a)) :=
  IsPGroup.of_injective
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.isPGroup_rad ha hK j)
    (Subgroup.subgroupOfEquivOfLe (reeFixedOrbitComplementUnipotent_le_reeGamma j)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (reeFixedOrbitComplementUnipotent_le_reeGamma j)).injective

theorem reeFixedPosUnipotent_le_perfectCore_zero (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedPosUnipotent K a ≤ perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩) := by
  have hsimple := isSimpleGroup_rankOneGroupOne ha hK
  have := hsimple.1
  obtain ⟨⟨h0eq, -, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hMP := (levi_hom ha hK ⟨0, by decide⟩ (M := rankOneGroupOne K a) h0eq hsimple.2).2
  rw [← reeFixedOrbitComplementUnipotent_sup (K := K) (a := a) ⟨0, by decide⟩]
  refine sup_le ((generation_zero ha hK).trans (commutator_le_perfectCore
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.rad_le_parabolic _))) ?_
  exact (reeFixedOrbitUnipotent_le_reeLocalBlock _).trans (h0eq.le.trans hMP)

theorem reeFixedPosUnipotent_le_perfectCore_one (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedPosUnipotent K a ≤ perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) := by
  have hsimple := isSimpleGroup_rankOneGroupTwo ha hK
  have := hsimple.1
  obtain ⟨-, ⟨h1eq, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hMP := (levi_hom ha hK ⟨1, by decide⟩ (M := rankOneGroupTwo K a) h1eq hsimple.2).2
  rw [← reeFixedOrbitComplementUnipotent_sup (K := K) (a := a) ⟨1, by decide⟩]
  refine sup_le ((generation_one ha hK).trans (commutator_le_perfectCore
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.rad_le_parabolic _))) ?_
  exact (reeFixedOrbitUnipotent_le_reeLocalBlock _).trans (h1eq.le.trans hMP)

end CFSG.Quasithin.H13.Sec53F.ReeF4
