module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Thm4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

theorem isSylowTwoOf_map_hom' {G K : Type*} [Group G] [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem centralizer_Z₁_le_normalizer_K (h5114 : Stmt5_1_14_first) :
    Subgroup.centralizer (Z₁ : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)).trans
    ((h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.2 z
      (s.Z₁_le_Z hz) hz1)

theorem tildeOf_pCoreOf_K_le_centralizer (h5114 : Stmt5_1_14_first) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    tildeOf Z₁ (pCoreOf 2 (oTwoUpper H)) ≤ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :
        Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHG₁ := s.H_le_centralizer h5114
  have h21 := (h521 G T M L V H B D D₃ Z₁ (Subgroup.centralizer (Z₁ : Set G)) n s.hyp.hyp
    s.hyp.notation59 s.hyp.module s.hyp.l34 hnot s.le_D s.card_D₃ s.z1 hHG₁ le_rfl).1
  have hOK : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ((oTwoUpper_le H).trans hHG₁))
      ((s.centralizer_Z₁_le_normalizer_K h5114).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
  have hc : (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ ∈ Z₁ :=
    h21 (Subgroup.commutator_mem_commutator hu (hOK hx))
  have h1 : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (u * x * u⁻¹ * x⁻¹) = 1 := by
    rw [secMk_eq_one_iff]; simpa using hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ x) h1
  simp only [one_mul, inv_mul_cancel_right] at this
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ u) this
  simpa [mul_assoc] using this

end Setup521

end CFSG.Quasithin.H13
