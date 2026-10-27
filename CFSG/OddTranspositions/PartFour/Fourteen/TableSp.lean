module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Lin
import CFSG.ClassicalGroups.Alternating.RT1SpBasic

public section

namespace CFSG.OddTranspositions.PartFour.Fourteen

open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic

theorem exists_ne_zero_ne_one {F : Type} [Field F] [Finite F] (hF : 2 < Nat.card F) :
    ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set F) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (h x hx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 : ({0, 1} : Set F).ncard ≤ 2 :=
    (Set.ncard_insert_le 0 {1}).trans (by rw [Set.ncard_singleton])
  omega

theorem meetsSq_of_isSymplecticTransvection {G : Type} [Group G] {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hZ : Subgroup.center G = ⊥) {s : G} (hs : s ∈ D)
    {m f : ℕ} (hf : 2 ≤ f)
    (hsp : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection G m f s) :
    ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D := by
  classical
  obtain ⟨k, -, F, _, _, hcard, e, hrank⟩ := hsp
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  set ψ : G →* Gsp (spForm k F) :=
    ((spEquiv (m := k) (K := F)).toMonoidHom.comp e.toMonoidHom).comp
      (QuotientGroup.mk' (Subgroup.center G)) with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center G) a = QuotientGroup.mk' (Subgroup.center G) b :=
      e.injective ((spEquiv (m := k) (K := F)).injective hab)
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    (spEquiv (m := k) (K := F)).surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨u, c, hu, hc, huc⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_spEquiv_eq_Tsp_of_rank_eq_one _ hrank
  have hψs : ψ s = Tsp (spForm_isAlt (m := k) (K := F)) u c := huc
  have hconj : ∀ d : F, d ≠ 0 → ∃ g : G, g * s * g⁻¹ ∈ D ∧
      ψ (g * s * g⁻¹) = Tsp (spForm_isAlt (m := k) (K := F)) u d := by
    intro d hd
    obtain ⟨g', hg'⟩ := exists_gsp_conj_Tsp_eq spForm_isAlt spForm_nondegenerate hu hu hc hd
    obtain ⟨g, rfl⟩ := hψsurj g'
    refine ⟨g, ?_, ?_⟩
    · obtain ⟨d₀, hD⟩ := hcls
      rw [hD] at hs ⊢
      exact (show IsConj d₀ s from hs).trans (isConj_iff.mpr ⟨g, rfl⟩)
    · rw [map_mul, map_mul, map_inv, hψs, hg']
  have hcardF : 2 < Nat.card F := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one hcardF
  have hl1' : 1 + l ≠ 0 := fun h => hl1 (by
    have h' := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at h')
  obtain ⟨g₁, hg₁D, hg₁⟩ := hconj (l * c) (mul_ne_zero hl0 hc)
  obtain ⟨g₂, hg₂D, hg₂⟩ := hconj ((1 + l) * c) (mul_ne_zero hl1' hc)
  refine ⟨s, hs, g₁ * s * g₁⁻¹, hg₁D, fun h => ?_, ?_, ?_⟩
  ·
    have h' := congrArg ψ h
    rw [hψs, hg₁] at h'
    have h1 : Tsp (spForm_isAlt (m := k) (K := F)) u c *
        Tsp (spForm_isAlt (m := k) (K := F)) u (l * c) = 1 := by
      rw [← h', Tsp_mul_self]
    rw [Tsp_mul_Tsp, Tsp_eq_one_iff spForm_isAlt spForm_nondegenerate] at h1
    rcases h1 with h1 | h1
    · exact hu h1
    · exact mul_ne_zero hl1' hc (by rw [← h1]; ring)
  ·
    apply hψinj
    rw [map_mul ψ s (g₁ * s * g₁⁻¹), map_mul ψ (g₁ * s * g₁⁻¹) s, hψs, hg₁]
    exact Tsp_comm spForm_isAlt (spForm_isAlt u) c (l * c)
  ·
    have hprod : s * (g₁ * s * g₁⁻¹) = g₂ * s * g₂⁻¹ := by
      apply hψinj
      rw [map_mul ψ s (g₁ * s * g₁⁻¹), hψs, hg₁, hg₂, Tsp_mul_Tsp]
      congr 1
      ring
    rw [hprod]
    exact hg₂D

end CFSG.OddTranspositions.PartFour.Fourteen

end
