module

public import CFSG.Walter.Bender1970.S1.QdNotInvolved
public import CFSG.Adapters.GlaubermanZJ
public import CFSG.Walter.W67.Section5.Lemma53
public import CFSG.Walter.W67.Section5.P56Series

public section

namespace CFSG.Walter.W67

open scoped commutatorElement

namespace Sec56

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_ZJ (S : Subgroup G) :
    S ≤ Subgroup.normalizer ((Glauberman.ZJ (G := G) S : Subgroup G) : Set G) := by
  intro g hg
  apply Sec53.mem_normalizer_of_conj_le
  have h1 := Adapters.thompsonCenter_map_mulEquiv S (MulAut.conj g)
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem hg hy) (S.inv_mem hg)
  have hS : S.map (MulAut.conj g).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [hS] at h1
  intro z hz
  have : g * z * g⁻¹ ∈ (thompsonCenter (G := G) S).map (MulAut.conj g).toMonoidHom :=
    ⟨z, hz, rfl⟩
  rw [h1] at this
  exact this

theorem eq_bot_of_commutator_eq_top {p : ℕ} [Fact p.Prime] {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (h : commutator Q = ⊤) : (⊤ : Subgroup Q) = ⊥ := by
  have h' : ⁅(⊤ : Subgroup Q), ⊤⁆ = ⊤ := h
  refine eq_bot_of_lpcStep_eq (Nat.card Q) Q rfl hQ ⊤ inferInstance
    (le_antisymm (lpcStep_le p ⊤) ?_)
  calc (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), ⊤⁆ := h'.symm
    _ ≤ lpcStep p ⊤ := le_sup_left

theorem hallPResidual_eq_top_of_sylow_le_commutator {N : Type} [Group N] [Finite N] {p : ℕ}
    [Fact p.Prime] (P : Sylow p N) (hP : (P : Subgroup N) ≤ commutator N) :
    BenderSuzuki.External.hallPResidual p N = ⊤ := by
  let : (BenderSuzuki.External.hallPResidual p N).Normal :=
    BenderSuzuki.External.hallPResidual_normal p N
  have hQ3 : IsPGroup p (N ⧸ BenderSuzuki.External.hallPResidual p N) :=
    BenderSuzuki.External.hallPResidual_quotient_isPGroup p
  have hsup := BenderSuzuki.External.hall_sup_hallPResidual_eq_top_of_sylow_le p P
    (commutator N) hP
  have h1 : (commutator N).map
      (QuotientGroup.mk' (BenderSuzuki.External.hallPResidual p N)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hy : y ∈ commutator N ⊔ BenderSuzuki.External.hallPResidual p N := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    refine ⟨a, ha, ?_⟩
    have hb1 : QuotientGroup.mk' (BenderSuzuki.External.hallPResidual p N) b = 1 :=
      (QuotientGroup.eq_one_iff b).mpr hb
    rw [map_mul, hb1, mul_one]
  have h2 : (commutator N).map
      (QuotientGroup.mk' (BenderSuzuki.External.hallPResidual p N)) =
      commutator (N ⧸ BenderSuzuki.External.hallPResidual p N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hQ1 := eq_bot_of_commutator_eq_top hQ3 (h2 ▸ h1)
  rw [eq_top_iff]
  intro y _
  have : (QuotientGroup.mk' (BenderSuzuki.External.hallPResidual p N) y) ∈
      (⊤ : Subgroup (N ⧸ BenderSuzuki.External.hallPResidual p N)) := Subgroup.mem_top _
  rw [hQ1, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff y).mp this

theorem subgroupOf_le_commutator_ZJ
    (hperf : commutator G = ⊤) (hab2 : HasAbelianSylowTwo G)
    (S : Sylow 3 G) :
    (S : Subgroup G).subgroupOf (Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G)) ≤
      commutator (Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hqd := qd_not_involved_of_hasAbelianSylowTwo hab2 (p := 3) (by norm_num)
  have hB := Glauberman.theoremB (by norm_num : (3 : ℕ) ≠ 2) S hqd
  have hSN := le_normalizer_ZJ (S : Subgroup G)
  have hfoc := sylow_inf_derivedSubgroup_eq_focalSubgroup 3 S
  have hder : derivedSubgroup G = ⊤ := by
    change derivedSeries G 1 = ⊤
    rw [derivedSeries_one]
    exact hperf
  rw [hder, inf_top_eq] at hfoc
  intro s hs
  have hs' : (s : G) ∈ (S : Subgroup G) := hs
  replace hs' := hfoc.le hs'
  have key : Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G,
      y ∈ (S : Subgroup G) ∧ IsConj x y ∧ z = x⁻¹ * y} ≤
      (commutator (Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G))).map
        (Subgroup.normalizer
          ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G)).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c₁, hc₁⟩ := isConj_iff.mp hxy
    have hW : Glauberman.conjSubset c₁⁻¹ ({x} : Set G) ⊆ (S : Subgroup G) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [inv_inv, hc₁]
      exact hy
    obtain ⟨c, n, hc, hn, hcn⟩ := hB {x} ⟨x, rfl⟩ (Set.singleton_subset_iff.mpr hx) c₁⁻¹ hW
    have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc x rfl).symm
    have hy' : y = n⁻¹ * x * n := by
      have h1 : c₁ = n⁻¹ * c⁻¹ := by
        have := congrArg (·⁻¹) hcn
        simpa using this
      rw [← hc₁, h1]
      calc n⁻¹ * c⁻¹ * x * (n⁻¹ * c⁻¹)⁻¹ = n⁻¹ * (c⁻¹ * (x * c)) * n := by group
        _ = n⁻¹ * (c⁻¹ * (c * x)) * n := by rw [hcx]
        _ = n⁻¹ * x * n := by group
    have hxN := hSN hx
    refine ⟨⁅(⟨x⁻¹, Subgroup.inv_mem _ hxN⟩ : Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G)),
        (⟨n⁻¹, Subgroup.inv_mem _ hn⟩ : Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G))⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
    rw [hy']
    change x⁻¹ * n⁻¹ * x⁻¹⁻¹ * n⁻¹⁻¹ = x⁻¹ * (n⁻¹ * x * n)
    group
  obtain ⟨t, ht, hts⟩ := key hs'
  have : t = s := Subtype.ext hts
  rw [← this]
  exact ht

theorem hallPResidual_normalizer_ZJ_eq
    (hperf : commutator G = ⊤) (hab2 : HasAbelianSylowTwo G)
    (S : Sylow 3 G) :
    (BenderSuzuki.External.hallPResidual 3 (Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G))).map
      (Subgroup.normalizer
        ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G)).subtype =
      Subgroup.normalizer ((Glauberman.ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSN := le_normalizer_ZJ (S : Subgroup G)
  have h1 := hallPResidual_eq_top_of_sylow_le_commutator (S.subtype hSN)
    (by rw [Sylow.coe_subtype]; exact subgroupOf_le_commutator_ZJ hperf hab2 S)
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Sec56

end CFSG.Walter.W67
