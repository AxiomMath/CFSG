module

public import CFSG.LieType.RootSystem.Basic
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
import CFSG.LocalAnalysis.StandardType.GGA2Conj
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

private theorem orthEdge_parabolic_conj {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (J : Finset ι) (u : (coxeterMatrix hC).Group)
    {t w : (coxeterMatrix hC).Group} {r : ι} (ht : t = w * (coxeterMatrix hC).simple r * w⁻¹)
    (hsupp : ∀ k ∉ J, weylAction hC u (weylAction hC w (Pi.single r 1)) k = 0) :
    ∃ z ∈ (coxeterMatrix hC).toCoxeterSystem.parabolic J, ∃ m ∈ J,
      u * t * u⁻¹ = z⁻¹ * (coxeterMatrix hC).simple m * z := by
  obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_support hC (J : Set ι) (u * w) r
    fun k hk => by
      rw [weylAction_mul_apply]
      exact hsupp k (mt Finset.mem_coe.2 hk)
  have h := ggWeyl_conj_simple_eq_of_root_smul hC (z * (u * w)) 1 r m one_ne_zero (by
    rw [weylAction_mul_apply, hzm]
    simp)
  simp only [CoxeterMatrix.toCoxeterSystem_simple, mul_one, one_mul, inv_one] at h
  refine ⟨z, hz, m, Finset.mem_coe.1 hm, ?_⟩
  rw [ht, ← h]
  group

theorem ggOrth_edge {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) (hsl : GGSimplyLaced (coxeterMatrix hC))
    {t t' : (coxeterMatrix hC).Group}
    (ht : ∃ (w : (coxeterMatrix hC).Group) (i : ι), t = w * (coxeterMatrix hC).simple i * w⁻¹)
    (ht' : ∃ (w : (coxeterMatrix hC).Group) (i : ι), t' = w * (coxeterMatrix hC).simple i * w⁻¹)
    (hne : t ≠ t') (hcomm : t * t' = t' * t) :
    ∃ (a b : ι) (w : (coxeterMatrix hC).Group), (coxeterMatrix hC).M a b = 2 ∧
      w * (coxeterMatrix hC).simple a * w⁻¹ = t ∧ w * (coxeterMatrix hC).simple b * w⁻¹ = t' := by
  obtain ⟨w₁, r₁, ht₁⟩ := ht
  obtain ⟨w₂, r₂, ht₂⟩ := ht'
  have hγ₁ : weylAction hC w₁ (Pi.single r₁ 1) ∈ roots hC (∅ : Set ι) := Or.inl ⟨w₁, r₁, rfl⟩
  have hγ₂ : weylAction hC w₂ (Pi.single r₂ 1) ∈ roots hC (∅ : Set ι) := Or.inl ⟨w₂, r₂, rfl⟩
  obtain ⟨u, J, hJ, hsupp⟩ := exists_weylAction_support_subset hC (∅ : Set ι) hγ₁ hγ₂
  obtain ⟨z₁, hz₁, m, hm, hx⟩ :=
    orthEdge_parabolic_conj hC J u ht₁ (hsupp _ hγ₁ ⟨1, 0, fun k => by simp⟩)
  obtain ⟨z₂, hz₂, m', hm', hy⟩ :=
    orthEdge_parabolic_conj hC J u ht₂ (hsupp _ hγ₂ ⟨0, 1, fun k => by simp⟩)
  have hne' : u * t * u⁻¹ ≠ u * t' * u⁻¹ := fun h => hne (mul_left_cancel (mul_right_cancel h))
  by_cases h3 : ∃ j ∈ J, ∃ k ∈ J, (coxeterMatrix hC).M j k = 3
  ·
    exfalso
    obtain ⟨j, hj, k, hk, hjk⟩ := h3
    have hjk' : j ≠ k := by
      rintro rfl
      have := (coxeterMatrix hC).diagonal j
      omega
    have hJjk : ∀ i ∈ J, i = j ∨ i = k := fun i hi => by
      by_contra hc
      obtain ⟨hij, hik⟩ := not_or.1 hc
      exact absurd (Finset.two_lt_card_iff.2 ⟨j, k, i, hj, hk, hi, hjk', Ne.symm hij,
        Ne.symm hik⟩) (by omega)
    have ha : (coxeterMatrix hC).simple j * (coxeterMatrix hC).simple j = 1 :=
      (coxeterMatrix hC).toCoxeterSystem.simple_mul_simple_self j
    have hb : (coxeterMatrix hC).simple k * (coxeterMatrix hC).simple k = 1 :=
      (coxeterMatrix hC).toCoxeterSystem.simple_mul_simple_self k
    have hab : ((coxeterMatrix hC).simple j * (coxeterMatrix hC).simple k) ^ 3 = 1 := by
      rw [← hjk]
      exact (coxeterMatrix hC).toCoxeterSystem.simple_mul_simple_pow j k
    have hP : (coxeterMatrix hC).toCoxeterSystem.parabolic J ≤
        Subgroup.closure {(coxeterMatrix hC).simple j, (coxeterMatrix hC).simple k} :=
      (coxeterMatrix hC).toCoxeterSystem.parabolic_le_iff.2 fun i hi => by
        rcases hJjk i (Finset.mem_coe.1 hi) with rfl | rfl <;>
          exact Subgroup.subset_closure (by simp)
    have hmem : ∀ (z : (coxeterMatrix hC).Group) (n : ι),
        z ∈ (coxeterMatrix hC).toCoxeterSystem.parabolic J → n ∈ J →
          (z⁻¹ * (coxeterMatrix hC).simple n * z = (coxeterMatrix hC).simple j ∨
            z⁻¹ * (coxeterMatrix hC).simple n * z = (coxeterMatrix hC).simple k ∨
            z⁻¹ * (coxeterMatrix hC).simple n * z = (coxeterMatrix hC).simple j *
              (coxeterMatrix hC).simple k * (coxeterMatrix hC).simple j) := by
      intro z n hz hn
      have h := ggDihedral_conj_mem ha hb hab (inv_mem (hP hz))
        (k := (coxeterMatrix hC).simple n) (by rcases hJjk n hn with rfl | rfl <;> simp)
      rwa [inv_inv] at h
    obtain ⟨v, hvj, hvk⟩ := ggDihedral_pair ha hb hab (by rw [hx]; exact hmem _ _ hz₁ hm)
      (by rw [hy]; exact hmem _ _ hz₂ hm') hne'
    apply ggSimplyLaced_simple_noncomm hsl hjk
    calc (coxeterMatrix hC).simple j * (coxeterMatrix hC).simple k
        = v⁻¹ * ((v * (coxeterMatrix hC).simple j * v⁻¹) *
            (v * (coxeterMatrix hC).simple k * v⁻¹)) * v := by group
      _ = v⁻¹ * ((u * t * u⁻¹) * (u * t' * u⁻¹)) * v := by rw [hvj, hvk]
      _ = v⁻¹ * ((u * t' * u⁻¹) * (u * t * u⁻¹)) * v := by
        rw [show (u * t * u⁻¹) * (u * t' * u⁻¹) = u * (t * t') * u⁻¹ by group, hcomm]
        group
      _ = (coxeterMatrix hC).simple k * (coxeterMatrix hC).simple j := by
        rw [← hvj, ← hvk]
        group
  ·
    have hfix : ∀ (z : (coxeterMatrix hC).Group) (n : ι),
        z ∈ (coxeterMatrix hC).toCoxeterSystem.parabolic J → n ∈ J →
          z⁻¹ * (coxeterMatrix hC).simple n * z = (coxeterMatrix hC).simple n := by
      intro z n hz hn
      have hle : (coxeterMatrix hC).toCoxeterSystem.parabolic J ≤
          Subgroup.centralizer {(coxeterMatrix hC).simple n} :=
        (coxeterMatrix hC).toCoxeterSystem.parabolic_le_iff.2 fun i hi => by
          show (coxeterMatrix hC).simple i ∈ _
          refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
          rw [Set.mem_singleton_iff.1 hg]
          by_cases hni : n = i
          · rw [hni]
          · exact ggSimplyLaced_simple_comm ((hsl n i hni).resolve_right
              fun h => h3 ⟨n, hn, i, Finset.mem_coe.1 hi, h⟩)
      rw [mul_assoc, Subgroup.mem_centralizer_iff.1 (hle hz) _ (Set.mem_singleton _),
        ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hfix _ _ hz₁ hm] at hx
    rw [hfix _ _ hz₂ hm'] at hy
    have hmm : m ≠ m' := fun h => hne' (by rw [hx, hy, h])
    refine ⟨m, m', u⁻¹, (hsl m m' hmm).resolve_right fun h => h3 ⟨m, hm, m', hm', h⟩, ?_, ?_⟩
    · rw [← hx]
      group
    · rw [← hy]
      group

end CFSG.StandardType

end
