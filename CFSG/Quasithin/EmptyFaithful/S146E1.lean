module

public import CFSG.Quasithin.EmptyFaithful.S146D8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Three

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem le_normalizer_of_forall_conjSub_le {H X : Subgroup G}
    (h : ∀ g ∈ H, conjSub g X ≤ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h g hg (mul_mem_conjSub hx)
  · intro hx
    have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ X := by
      have := h g⁻¹ (H.inv_mem hg) (mul_mem_conjSub hx)
      simpa using this
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h1

theorem Setting146.exists_normal_of_cComp_le (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (S : Setting146 G T M) {H K : Subgroup G} (hH : IsHTM T M H) (hK : K ∈ cComp H) (hKM : K ≤ M) :
    ∃ N : Subgroup G, K ≤ N ∧ N ≤ M ⊓ H ∧ H ≤ Subgroup.normalizer (N : Set G) := by
  have hTH : T ≤ H := hH.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hpc : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hKH : K ≤ H := le_of_mem_cComp hK
  by_cases hKT : ∀ t ∈ T, t ∈ Subgroup.normalizer (K : Set G)
  · have hn := lemma_1_2_4_normal S.hyp.qtke S.hyp.simple S.hyp.nonabelian h37 h38 hpc hTsyl
      (cComp_subset_lFamily hTH hK) le_rfl hK hKT
    exact ⟨K, le_rfl, le_inf hKM hKH,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn⟩
  push Not at hKT
  obtain ⟨t, ht, htn⟩ := hKT
  rcases lemma_1_2_1_three S.hyp.qtke S.hyp.simple S.hyp.nonabelian h37 h38 hpc hK with
    hKn | ⟨hcard, -⟩
  · exact ⟨K, le_rfl, le_inf hKM hKH, (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn⟩
  · have hne : conjSub t K ≠ K := fun h => htn (A38.map_conj_eq_iff.mp h)
    have hK₁ : K ∈ conjSubgroupsBy H K := ⟨1, H.one_mem, (conjSub_one K).symm⟩
    have hK₂ : conjSub t K ∈ conjSubgroupsBy H K := ⟨t, hTH ht, rfl⟩
    have hpair : ({K, conjSub t K} : Set (Subgroup G)) = conjSubgroupsBy H K := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · rintro x (rfl | rfl)
        · exact hK₁
        · exact hK₂
      · rw [Set.ncard_pair hne.symm, hcard]
    refine ⟨K ⊔ conjSub t K, le_sup_left, ?_, ?_⟩
    · refine le_inf (sup_le hKM ?_) (sup_le hKH ?_)
      · intro x hx
        have h1 : t⁻¹ * x * t ∈ K := mem_conjSub.mp hx
        have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
        rw [e]
        exact M.mul_mem (M.mul_mem (hTM ht) (hKM h1)) (M.inv_mem (hTM ht))
      · intro x hx
        have h1 : t⁻¹ * x * t ∈ K := mem_conjSub.mp hx
        have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (hTH ht) (hKH h1)) (H.inv_mem (hTH ht))
    · refine le_normalizer_of_forall_conjSub_le fun g hg => ?_
      rw [conjSub_sup]
      refine sup_le ?_ ?_
      · have : conjSub g K ∈ ({K, conjSub t K} : Set (Subgroup G)) := by
          rw [hpair]
          exact ⟨g, hg, rfl⟩
        rcases this with h | h
        · rw [h]; exact le_sup_left
        · rw [h]; exact le_sup_right
      · have : conjSub g (conjSub t K) ∈ ({K, conjSub t K} : Set (Subgroup G)) := by
          rw [hpair, ← conjSub_mul]
          exact ⟨g * t, H.mul_mem hg (hTH ht), rfl⟩
        rcases this with h | h
        · rw [h]; exact le_sup_left
        · rw [h]; exact le_sup_right

theorem Setting146.not_le_M_of_cComp (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (S : Setting146 G T M) {H K : Subgroup G} (hH : IsHTM T M H) (hK : K ∈ cComp H) :
    ¬ K ≤ M := by
  intro hKM
  obtain ⟨N, hKN, hNMH, hHN⟩ := S.exists_normal_of_cComp_le h37 h38 hH hK hKM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hNZ : Subgroup.normalizer (Zz : Set G) = mcOf T := S.normalizer_Z
  have hHZ : ∀ g ∈ H, g ∈ Subgroup.normalizer (Zz : Set G) := fun g hg => by
    rw [hNZ]; exact hHG hg
  have hUW : conjClosure (VZ T M) H ≤ centralizerMod Zz (conjClosure (VZ T M) H) N := by
    refine conjClosure_le fun h hh v hv => ?_
    have hhU : h * v * h⁻¹ ∈ conjClosure (VZ T M) H := mem_conjClosure hh hv
    refine ⟨hhU, S.conjClosure_le_normalizer_Z hH hhU, fun n hn => ?_⟩
    have hn' : h⁻¹ * n * h ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hh)) n).mp hn
      simpa using this
    have hb := S.commutator_VZ_mem (hNMH hn').1 (hHG (hNMH hn').2) hv
    have hb' : v * (h⁻¹ * n * h) * v⁻¹ * (h⁻¹ * n * h)⁻¹ ∈ Zz := by
      have := (quasithinOmegaOneCenter T).inv_mem hb
      have e : ((h⁻¹ * n * h) * v * (h⁻¹ * n * h)⁻¹ * v⁻¹)⁻¹ =
          v * (h⁻¹ * n * h) * v⁻¹ * (h⁻¹ * n * h)⁻¹ := by group
      rwa [e] at this
    have h3 := (Subgroup.mem_normalizer_iff.mp (hHZ h hh) _).mp hb'
    have e2 : h * (v * (h⁻¹ * n * h) * v⁻¹ * (h⁻¹ * n * h)⁻¹) * h⁻¹ =
        (h * v * h⁻¹) * n * (h * v * h⁻¹)⁻¹ * n⁻¹ := by group
    rwa [e2] at h3
  have hNC : N ≤ centralizerMod Zz H (conjClosure (VZ T M) H) := by
    intro n hn
    refine ⟨(hNMH hn).2, hHZ n (hNMH hn).2, fun u hu => ?_⟩
    have h1 := (hUW hu).2.2 n hn
    have h2 := (quasithinOmegaOneCenter T).inv_mem h1
    have e : (u * n * u⁻¹ * n⁻¹)⁻¹ = n * u * n⁻¹ * u⁻¹ := by group
    rwa [e] at h2
  rw [S.lemma_14_5_15_four hH] at hNC
  have hKP : K ≤ pCoreOf 2 H := hKN.trans hNC
  have : Group.IsSolvable ↥(pCoreOf 2 H) := isSolvable_pCoreOf_two H
  exact not_isSolvable_of_mem_cComp hK
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKP)
      (Subgroup.inclusion_injective hKP))

end Three

theorem stage1461Three_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Stage1461Three := by
  intro G _ _ T M S H hH K hK
  exact S.not_le_M_of_cComp h37 h38 hH hK

end CFSG.Quasithin
