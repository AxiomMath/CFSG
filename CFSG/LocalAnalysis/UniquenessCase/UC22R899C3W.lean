module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c3_exists_centralizesBar_sq {K : Subgroup G} {n p : ℕ}
    (hL2 : IsL2 (Bar2 K) n) (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G}
    (hB : IsElemAbelian p B) (hBN : B ≤ normalizer (K : Set G)) :
    ∃ C : Subgroup G, C ≤ B ∧ (∀ c ∈ C, CentralizesBar c K) ∧
      Nat.card B ≤ p ^ 2 * Nat.card C := by
  let φ : ↥B →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hBN)
  have hX := (P22fin.isL2Ev_of_isL2 hL2).1
  have hexp : ∀ b : ↥B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hB.2 _ b.2)
  have hcyc : ∀ (H : Type) [Group H] [IsCyclic H], (∀ x : H, x ^ p = 1) → Nat.card H ≤ p :=
    fun H _ _ h => Nat.le_of_dvd hp.pos
      ((IsCyclic.exponent_eq_card (α := H)) ▸ Monoid.exponent_dvd_of_forall_pow_eq_one h)
  have hrpow : ∀ y ∈ φ.range, y ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, hexp, map_one]
  let ψ : ↥φ.range →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K))).comp
      φ.range.subtype
  have hker : Nat.card ψ.ker ≤ p := by
    haveI := P22y.isCyclic_range_inf_inner hX hp hp2 hexp φ
    have hle : ψ.ker.map φ.range.subtype ≤
        φ.range ⊓ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have h1 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (Bar2 K)) (y : MulAut (Bar2 K)) = 1 := hy
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    rw [← Subgroup.card_map_of_injective φ.range.subtype_injective]
    refine (Subgroup.card_le_of_le hle).trans (hcyc _ ?_)
    rintro ⟨x, hx, -⟩
    exact Subtype.ext (by rw [Subgroup.coe_pow, hrpow x hx]; rfl)
  have hran : Nat.card ψ.range ≤ p := by
    haveI := P22y.isCyclic_outer_of_isL2Ev hX
    refine hcyc _ ?_
    rintro ⟨_, y, rfl⟩
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, show y ^ p = 1 from Subtype.ext (hrpow y y.2), map_one]
      rfl)
  have hrange : Nat.card φ.range ≤ p ^ 2 := by
    rw [← Subgroup.card_ker_mul_card_range ψ, sq]
    exact Nat.mul_le_mul hker hran
  refine ⟨φ.ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨hBN b.2, fun l hl => ?_⟩
    have h1 : UC6S846.rhoL K (Subgroup.inclusion hBN b) = 1 := hb
    have h2 : UC6S846.rhoL K (Subgroup.inclusion hBN b) (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h1, MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K _ ⟨l, hl⟩).1 h2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_ker_mul_card_range φ,
      mul_comm (p ^ 2)]
    exact Nat.mul_le_mul_left _ hrange

theorem uc22r899c3_comm_mem_pCoreOf_map_conj {M K : Subgroup G} {c g : G} (hgM : g ∈ M)
    (hcg : g * c = c * g) (h : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M) :
    ∀ k ∈ K.map (MulAut.conj g).toMonoidHom, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M := by
  rintro _ ⟨k, hk, rfl⟩
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  have h1 := (Subgroup.mem_normalizer_iff.1 (hMO hgM) _).1 (h k hk)
  have h3 : g⁻¹ * c⁻¹ = c⁻¹ * g⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcg]
  have e : c * (g * k * g⁻¹) * c⁻¹ * (g * k * g⁻¹)⁻¹ = g * (c * k * c⁻¹ * k⁻¹) * g⁻¹ :=
    calc c * (g * k * g⁻¹) * c⁻¹ * (g * k * g⁻¹)⁻¹
        = (c * g) * k * (g⁻¹ * c⁻¹) * g * k⁻¹ * g⁻¹ := by group
      _ = (g * c) * k * (c⁻¹ * g⁻¹) * g * k⁻¹ * g⁻¹ := by rw [hcg, h3]
      _ = g * (c * k * c⁻¹ * k⁻¹) * g⁻¹ := by group
  change c * (g * k * g⁻¹) * c⁻¹ * (g * k * g⁻¹)⁻¹ ∈ pCoreOf 2 M
  rw [e]
  exact h1

theorem uc22r899c3_exists_eq_map_conj {M L : Subgroup G} (hc3 : (conjSetOf M L).ncard = 3)
    {w : G} (hwM : w ∈ M) (hw3 : w ^ 3 = 1) (hwL : w ∉ normalizer (L : Set G))
    {K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    ∃ j : ℕ, K = L.map (MulAut.conj (w ^ j)).toMonoidHom := by
  set C : ℕ → Subgroup G := fun j => L.map (MulAut.conj (w ^ j)).toMonoidHom with hC
  have hmem : ∀ j, C j ∈ conjSetOf M L := fun j => ⟨w ^ j, M.pow_mem hwM j, rfl⟩
  have hC0 : C 0 = L := by
    simp only [hC, pow_zero]
    ext x
    simp
  have hmap : ∀ i j, (C i).map (MulAut.conj (w ^ j)).toMonoidHom = C (j + i) := fun i j => by
    simp only [hC]
    rw [uc22p22d_map_conj_map_conj, ← pow_add]
  have hw4 : w ^ 4 = w := by
    calc w ^ 4 = w ^ 3 * w := pow_succ w 3
      _ = w := by rw [hw3, one_mul]
  have hC4 : C 4 = C 1 := by simp only [hC, hw4, pow_one]
  have hC3 : C 3 = C 0 := by simp only [hC, hw3, pow_zero]
  have h1 : C 1 ≠ L := fun h => hwL (by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [hC] using h)
  have h2 : C 2 ≠ L := fun h => hwL (by
    have hw2 : w ^ 2 ∈ normalizer (L : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h
    have := Subgroup.pow_mem _ hw2 2
    rwa [← pow_mul, hw4] at this)
  have h12 : C 2 ≠ C 1 := fun h => h1 (by
    calc C 1 = C 4 := hC4.symm
      _ = (C 2).map (MulAut.conj (w ^ 2)).toMonoidHom := (hmap 2 2).symm
      _ = (C 1).map (MulAut.conj (w ^ 2)).toMonoidHom := by rw [h]
      _ = C 3 := hmap 1 2
      _ = L := hC3.trans hC0)
  have hs : ({L, C 1, C 2} : Set (Subgroup G)) = conjSetOf M L := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro N hN
      rcases hN with hN | hN | hN
      · rw [hN]
        exact ⟨1, M.one_mem, by ext x; simp⟩
      · rw [hN]
        exact hmem 1
      · rw [Set.mem_singleton_iff.1 hN]
        exact hmem 2
    · rw [hc3, Set.ncard_eq_three.2 ⟨L, C 1, C 2, h1.symm, h2.symm, h12.symm, rfl⟩]
  rw [← hs] at hK
  rcases hK with hK | hK | hK
  · exact ⟨0, hK.trans hC0.symm⟩
  · exact ⟨1, hK⟩
  · exact ⟨2, Set.mem_singleton_iff.1 hK⟩

theorem uc22r899c3_exists_third {M L K₁ K₂ : Subgroup G} (hc3 : (conjSetOf M L).ncard = 3) :
    ∃ K₃ ∈ conjSetOf M L, K₃ ≠ K₁ ∧ K₃ ≠ K₂ := by
  by_contra h
  have hsub : conjSetOf M L ⊆ {K₁, K₂} := fun K hK => by
    by_cases h1 : K = K₁
    · exact Or.inl h1
    · by_cases h2 : K = K₂
      · exact Or.inr h2
      · exact absurd ⟨K, hK, h1, h2⟩ h
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({K₁, K₂} : Set (Subgroup G)).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
