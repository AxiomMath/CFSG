module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case1A

public section

namespace CFSG.Quasithin.F146Field.Case1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem relIndex_normalizer_eq_two {K T : Subgroup G} {t : G} (ht : t ∈ T)
    (hne : cjSub t K ≠ K) (horb : ∀ s ∈ T, cjSub s K = K ∨ cjSub s K = cjSub t K) :
    (T ⊓ Subgroup.normalizer (K : Set G)).relIndex T = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, ht⟩, fun b => ?_⟩
  have htn : t ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hne (mem_normalizer_iff_cjSub_eq.mp h)
  have hbT : (b : G) ∈ T := b.2
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  by_cases hg : (b : G) ∈ Subgroup.normalizer (K : Set G)
  · right
    refine ⟨⟨hbT, hg⟩, fun h => htn ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) h.2
    simpa using this
  · left
    refine ⟨⟨T.mul_mem hbT ht, ?_⟩, fun h => hg h.2⟩
    rw [mem_normalizer_iff_cjSub_eq]
    have hgK : cjSub (b : G) K = cjSub t K := by
      rcases horb b hbT with h | h
      · exact absurd (mem_normalizer_iff_cjSub_eq.mpr h) hg
      · exact h
    rcases horb ((b : G) * t) (T.mul_mem hbT ht) with h | h
    · exact h
    · exfalso
      rw [← cjSub_cjSub_mul] at h
      have h2 : cjSub (b : G) (cjSub t K) = cjSub (b : G) K := by rw [h, hgK]
      exact hne (cjSub_injective _ h2)

theorem le_normalizer_inf_of_orbit {K T : Subgroup G} {t : G} (ht : t ∈ T)
    (hne : cjSub t K ≠ K) (horb : ∀ s ∈ T, cjSub s K = K ∨ cjSub s K = cjSub t K) :
    T ≤ Subgroup.normalizer ((K ⊓ cjSub t K : Subgroup G) : Set G) := by
  intro s hs
  rw [mem_normalizer_iff_cjSub_eq]
  have h1 := horb s hs
  have h2 : cjSub s (cjSub t K) = K ∨ cjSub s (cjSub t K) = cjSub t K := by
    rw [cjSub_cjSub_mul]
    exact horb (s * t) (T.mul_mem hs ht)
  have hinf : cjSub s (K ⊓ cjSub t K) = cjSub s K ⊓ cjSub s (cjSub t K) := by
    ext x
    simp [mem_cjSub]
  rw [hinf]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (cjSub_injective s (h1.trans h2.symm)).symm hne
  · rw [h1, h2]
  · rw [h1, h2, inf_comm]
  · exact absurd (cjSub_injective s (h1.trans h2.symm)).symm hne

variable [Finite G]

theorem oTwoUpper_eq_sup {K T H : Subgroup G} (hK : K ∈ cComp H) (hT : IsPGroup 2 T)
    (hHK : H = K ⊔ T) {t : G} (ht : t ∈ T)
    (horb : ∀ s ∈ T, cjSub s K = K ∨ cjSub s K = cjSub t K) :
    oTwoUpper H = K ⊔ cjSub t K := by
  have hTH : T ≤ H := by rw [hHK]; exact le_sup_right
  apply le_antisymm
  · refine (oTwoUpper_le_conjClosure hT hHK).trans (conjClosure_le fun h hh z hz => ?_)
    have hconj : ∀ A : Subgroup G, cjSub h K = A → h * z * h⁻¹ ∈ A := fun A hA => by
      rw [← hA, mem_cjSub]
      have : h⁻¹ * (h * z * h⁻¹) * h = z := by group
      rw [this]
      exact hz
    rcases horb h hh with h1 | h1
    · exact Subgroup.mem_sup_left (hconj K h1)
    · exact Subgroup.mem_sup_right (hconj _ h1)
  · refine sup_le (le_oTwoUpper hK) (fun x hx => ?_)
    rw [mem_cjSub] at hx
    have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH ht)) _).mp
        (le_oTwoUpper hK hx)
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [h2] at h1

theorem inf_cjSub_le_pCoreOf {M₀ H K T : Subgroup G} (hmin : MinParabolic H T M₀)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T) (hker : kerIn M₀ H = pCoreOf 2 H) {t : G} (ht : t ∈ T)
    (hne : cjSub t K ≠ K) (horb : ∀ s ∈ T, cjSub s K = K ∨ cjSub s K = cjSub t K) :
    K ⊓ cjSub t K ≤ pCoreOf 2 H := by
  have hTH : T ≤ H := hmin.isSylow.1
  have hK' : cjSub t K ∈ cComp H := cjSub_mem_cComp_of_mem hK (hTH ht)
  set C := K ⊓ cjSub t K with hC
  have hKN' : K ≤ Subgroup.normalizer (cjSub t K : Set G) := le_normalizer_of_mem_cComp hK' hK
  have hCK : K ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hKN' hx⟩
  have hCT := le_normalizer_inf_of_orbit ht hne horb
  have hCH : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [hHK]
    exact sup_le hCK hCT
  by_cases hX : C ⊔ T = H
  · exfalso
    have h2 := B6.isTwoQuotient_of_sup_eq hmin.isSylow.2.1 hCH (by rw [sup_comm]; exact hX)
    have hKC : K ≤ C := (le_oTwoUpper hK).trans (oTwoUpper_le_of_pow_mem h2)
    have heq : K = cjSub t K :=
      Subgroup.eq_of_le_of_card_ge (hKC.trans inf_le_right) (by rw [card_cjSub])
    exact hne heq.symm
  · have hlt : C ⊔ T < H :=
      lt_of_le_of_ne (sup_le (inf_le_left.trans (le_of_mem_cComp hK)) hTH) hX
    obtain ⟨N, hN, hXN⟩ := exists_isMaxSubgroupIn hlt
    have hNM : N = M₀ := hmin.eq_of_maximal hN (le_sup_right.trans hXN)
    have hCM : C ≤ M₀ := hNM ▸ (le_sup_left.trans hXN)
    rw [← hker]
    intro x hx
    rw [mem_kerIn]
    intro b hb
    exact hCM ((Subgroup.mem_normalizer_iff.mp (hCH hb) x).mp hx)

end CFSG.Quasithin.F146Field.Case1
