module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverSpec

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_cover_of_data_pow {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (S : Sylow p K) (T : List K) (hT : ∀ x ∈ (S : Subgroup K), x ∈ T) (reps : List K)
    (hreps : ∀ r ∈ reps, ∀ x : K, IsConj r x → SporKRestGenerating p x)
    (hcensus : ∀ t ∈ T, t ≠ 1 → t ^ p = 1 → ∃ r ∈ reps, ∃ g : K, g⁻¹ * r * g = t) :
    SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hE hcard
  have hlt : 1 < Nat.card E := by
    rw [hcard]
    nlinarith [hp.two_le]
  have hbot : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp hlt
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hbot
  obtain ⟨x, hxE, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial E
  have hEp : IsPGroup p ↥E := IsPGroup.of_card hcard
  have hzp : IsPGroup p ↥(Subgroup.zpowers x) :=
    hEp.to_le (Subgroup.zpowers_le.mpr hxE)
  obtain ⟨Q, hxQ⟩ := hzp.exists_le_sylow
  have hxQmem : x ∈ Q := hxQ (Subgroup.mem_zpowers x)
  letI : MulAction.IsPretransitive K (Sylow p K) :=
    Sylow.isPretransitive_of_finite (p := p) (G := K)
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := K) S Q
  have hxS : g⁻¹ * x * g ∈ (S : Subgroup K) := by
    have hxg : x ∈ ((g • S : Sylow p K) : Subgroup K) := by rw [hg]; exact hxQmem
    rw [Sylow.coe_subgroup_smul] at hxg
    refine (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj g)
      (S := (S : Subgroup K)) (x := g⁻¹ * x * g)).mp ?_
    have hax : (MulAut.conj g) • (g⁻¹ * x * g) = x := by
      change (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group
    rw [hax]
    exact hxg
  have htT : g⁻¹ * x * g ∈ T := hT _ hxS
  have ht1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have htpow : (g⁻¹ * x * g) ^ p = 1 := by
    have hxp : x ^ p = 1 := hE.2 x hxE
    have hconj : (g⁻¹ * x * g) ^ p = g⁻¹ * x ^ p * g := by
      have h := conj_pow (a := g⁻¹) (b := x) (i := p)
      rwa [inv_inv] at h
    rw [hconj, hxp]
    group
  obtain ⟨r, hr, g', hg'⟩ := hcensus _ htT ht1 htpow
  refine ⟨x, hxE, hx1, hreps r hr x ?_⟩
  rw [isConj_iff]
  refine ⟨g * g'⁻¹, ?_⟩
  calc (g * g'⁻¹) * r * (g * g'⁻¹)⁻¹
      = g * (g'⁻¹ * r * g') * g⁻¹ := by group
    _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hg']
    _ = x := by group

end CFSG.StandardType.SporadicShape
