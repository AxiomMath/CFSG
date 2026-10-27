module

public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne
public import CFSG.Quasithin.H13.NQCatLieOverRank2

public section

namespace CFSG.Quasithin.H13.NQCat.BN

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.QuasithinUnique
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem le_reeFixedBorel_of_isSolvable
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {A : Subgroup (ModGL F4.tag K)}
    (hAΓ : A ≤ F4.reeGamma K a) (hUA : F4.reeFixedPosUnipotent K a ≤ A)
    (hA : Group.IsSolvable A) : A ≤ F4.reeFixedBorel K a := by
  intro g hg
  have hg' : g ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := hAΓ hg
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb hb'
  exfalso
  set n := canonicalRep (coxeterSystem F4.tag) K w with hn
  have hnΓ : n ∈ F4.reeGamma K a :=
    (Subgroup.mem_inf.1 (canonicalRep_mem_reeFixedMonomial F4 K a hw)).2
  have hbinv : b⁻¹ ∈ (F4.reeFixedTorus K a : Set (ModGL F4.tag K)) *
      (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    rw [← reeFixedBorel_eq_mul]
    exact inv_mem hb
  obtain ⟨h₁, hh₁, u₁, hu₁, he₁⟩ := hbinv
  have he₁' : h₁ * u₁ = b⁻¹ := he₁
  have hb'' : b' ∈ (F4.reeFixedTorus K a : Set (ModGL F4.tag K)) *
      (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    rw [← reeFixedBorel_eq_mul]
    exact hb'
  obtain ⟨h₂, hh₂, u₂, hu₂, he₂⟩ := hb''
  have he₂' : h₂ * u₂ = b' := he₂
  set m := h₁⁻¹ * n * h₂ with hm
  have hmA : m ∈ A := by
    have h1 : m = u₁ * (b * n * b') * u₂⁻¹ := by
      rw [← he₂', show b = (h₁ * u₁)⁻¹ by rw [he₁', inv_inv], hm]
      group
    rw [h1]
    exact mul_mem (mul_mem (hUA hu₁) hg) (inv_mem (hUA hu₂))
  obtain ⟨j, hj⟩ := exists_fixedOrbitRoots_neg (inv_mem hw) (inv_ne_one.mpr hw1)
  have hEroot : ∀ α ∈ F4.fixedOrbitRoots j, IsRoot F4.tag α :=
    fun α hα => (mem_fixedOrbitRoots_iff.1 hα).1
  have hnegroot : ∀ α ∈ Neg.neg '' F4.fixedOrbitRoots j, IsRoot F4.tag α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.neg (hEroot β hβ)
  have hTU : ∀ h ∈ F4.reeFixedTorus K a, ∀ u ∈ F4.reeFixedPosUnipotent K a,
      h * u * h⁻¹ ∈ F4.reeFixedPosUnipotent K a := fun h hh u hu =>
    (mem_normalizer_iff.mp
      (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (reeFixedTorus_le_reeFixedBorel hh))
      u).mp hu
  have hTY : ∀ h ∈ F4.reeFixedTorus K a, ∀ y ∈ F4.reeFixedOrbitNegUnipotent K a j,
      h * y * h⁻¹ ∈ F4.reeFixedOrbitNegUnipotent K a j := by
    intro h hh y hy
    obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.mp
      (torusGroup_le_normalizer_rootSpan hnegroot hhT) y).mp hyS,
      mul_mem (mul_mem hhΓ hyΓ) (inv_mem hhΓ)⟩
  have hYA : F4.reeFixedOrbitNegUnipotent K a j ≤ A := by
    intro y hy
    have hy₁ := hTY h₁ hh₁ y hy
    obtain ⟨hy₁S, hy₁Γ⟩ := Subgroup.mem_inf.1 hy₁
    set T := (fun α => w⁻¹ • α) '' (Neg.neg '' F4.fixedOrbitRoots j) with hT
    have hTroot : ∀ α ∈ T, IsRoot F4.tag α := by
      rintro _ ⟨β, hβ, rfl⟩
      exact IsRoot.smul (hnegroot β hβ) w⁻¹
    have himg : (fun α => w • α) '' T = Neg.neg '' F4.fixedOrbitRoots j := by
      rw [hT, Set.image_image]
      simp only [smul_inv_smul, Set.image_id']
    have hmap := (canonical_weyl_root_transport F4.tag K).1 w T hTroot
    rw [himg] at hmap
    rw [← hmap] at hy₁S
    obtain ⟨v, hvT, hv⟩ := hy₁S
    have hvy : n⁻¹ * (h₁ * y * h₁⁻¹) * n = v := by
      rw [← hv]
      change n⁻¹ * (n * v * n⁻¹) * n = v
      group
    have hvU : v ∈ F4.reeFixedPosUnipotent K a := by
      refine Subgroup.mem_inf.2 ⟨rootSpan_mono (fun α hα => ?_) hvT, ?_⟩
      · obtain ⟨_, ⟨β, hβ, rfl⟩, rfl⟩ := hα
        refine ⟨IsRoot.smul (IsRoot.neg (hEroot β hβ)) w⁻¹, ?_⟩
        have h1 := hj β hβ
        show 0 < height (w⁻¹ • -β)
        rw [smul_neg, height_neg]
        omega
      · rw [← hvy]
        exact mul_mem (mul_mem (inv_mem hnΓ) hy₁Γ) hnΓ
    have hu' := hTU h₂⁻¹ (inv_mem hh₂) v hvU
    have hy' : y = m * (h₂⁻¹ * v * h₂⁻¹⁻¹) * m⁻¹ := by
      rw [← hvy, hm]
      group
    rw [hy']
    exact mul_mem (mul_mem hmA (hUA hu')) (inv_mem hmA)
  have hMA : F4.reeLocalBlock K a j ≤ A :=
    sup_le ((reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j).trans hUA) hYA
  have hMs : Group.IsSolvable (F4.reeLocalBlock K a j) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMA)
      (Subgroup.inclusion_injective hMA)
  obtain ⟨⟨h0, -, -⟩, ⟨h1, -, -⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  fin_cases j
  · obtain ⟨hs, x, y, hxy⟩ := LargeReeInvolution.isSimpleGroup_rankOneGroupOne ha hK
    rw [h0] at hMs
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hMs x y)
  · obtain ⟨hs, x, y, hxy⟩ := LargeReeInvolution.isSimpleGroup_rankOneGroupTwo ha hK
    rw [h1] at hMs
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hMs x y)

theorem solvOver_of_is2F4
    {S : Type} [Group S] [Finite S]
    {k : ℕ} (h : CFSG.Quasithin.Is2F4 k S) {P : Subgroup S} (hP : IsSylowTwoOf P ⊤) :
    SolvOver S P := by
  obtain ⟨-, -, -, -, ⟨a, ha, hka⟩, hiso⟩ := large_Ree_model_Schreier S 2 k h
  obtain ⟨-, a', hka', ⟨K, _, _, hK, he⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := k) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  have haa' : a' = a := by omega
  subst haa'
  obtain ⟨e⟩ := hiso a' K hka' hK he
  have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hka']
  have : Fact (Nat.Prime F4.prime) := ⟨Nat.prime_two⟩
  set Γ := F4.reeGamma K a' with hΓ
  have hU₀ : IsSylowTwoOf ((F4.reeFixedPosUnipotent K a').subgroupOf Γ) ⊤ := by
    refine ⟨le_top, isPGroup_reeFixedPosUnipotent_subgroupOf, ?_⟩
    rw [show (((F4.reeFixedPosUnipotent K a').subgroupOf Γ).subgroupOf ⊤).index =
      ((F4.reeFixedPosUnipotent K a').subgroupOf Γ).index from relIndex_top_right _]
    exact not_dvd_index_reeFixedPosUnipotent
  have hsol : SolvOver Γ ((F4.reeFixedPosUnipotent K a').subgroupOf Γ) := by
    intro X hUX hX
    have hAΓ : X.map Γ.subtype ≤ Γ := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hUA : F4.reeFixedPosUnipotent K a' ≤ X.map Γ.subtype := fun u hu =>
      ⟨⟨u, reeFixedPosUnipotent_le_reeGamma hu⟩, hUX (mem_subgroupOf.2 hu), rfl⟩
    have hAs : Group.IsSolvable (X.map Γ.subtype) :=
      Group.isSolvable_of_surjective (f := (X.equivMapOfInjective Γ.subtype
        Γ.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    have hAB := le_reeFixedBorel_of_isSolvable ha hK' hAΓ hUA hAs
    intro x hx
    have hxB : (x : ModGL F4.tag K) ∈ F4.reeFixedBorel K a' := hAB ⟨x, hx, rfl⟩
    rw [mem_normalizer_iff]
    intro y
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (reeFixedBorel_le_normalizer_reeFixedPosUnipotent hxB) y
  exact solvOver_of_sylow hsol hU₀ e.symm hP

end CFSG.Quasithin.H13.NQCat.BN
