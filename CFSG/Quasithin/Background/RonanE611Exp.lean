module

public import CFSG.Quasithin.Background.RonanE611Cent

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.E6.E68Proof CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Bar

variable {G : Type} [Group G] {L S : Subgroup G}

theorem piBar_mem_normalizer (hZS : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ S) {g : G} (hgL : g ∈ L)
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    piBar L ⟨g, hgL⟩ ∈
      Subgroup.normalizer ((((S.subgroupOf L).map (piBar L) : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
        Set (↥L ⧸ Subgroup.center ↥L))) := by
  have hker : (piBar L).ker ≤ S.subgroupOf L := by
    rw [ker_piBar]
    intro z hz
    exact hZS z hz
  have hcomap : ∀ u : ↥L, piBar L u ∈ (S.subgroupOf L).map (piBar L) ↔ u ∈ S.subgroupOf L := by
    intro u
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨u, rfl⟩ := piBar_surjective y
  rw [← map_inv, ← map_mul, ← map_mul, hcomap, hcomap, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.1 hg (u : G)

end Bar

section Lin3

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G}

theorem pow_card_sub_one_mem_of_lin3 {n : ℕ} (hn : 2 ≤ n)
    (hL : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n)
    (hZ : IsPGroup 2 (Subgroup.center ↥L)) (hS : IsSylowTwoOf S L) {g : G}
    (hg : g ∈ L ⊓ Subgroup.normalizer (S : Set G)) : g ^ (2 ^ n - 1) ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS := center_le_of_isSylowTwoOf hS hZ
  have hSbar : IsSylowTwoOf ((S.subgroupOf L).map (piBar L)) ⊤ := isSylowTwoOf_map_piBar hS hZS
  obtain ⟨K, _, _, _, φ, hK, hφ⟩ := exists_unitriangular_iso hL hSbar
  have hN := piBar_mem_normalizer hZS hg.1 hg.2
  have hmem : ∀ y : ↥L ⧸ Subgroup.center ↥L, φ y ∈ projUnitriangular 3 K ↔
      y ∈ (S.subgroupOf L).map (piBar L) := by
    intro y
    rw [← hφ]
    exact (Subgroup.mem_map_equiv (f := φ) (K := (S.subgroupOf L).map (piBar L))).trans
      (by simp)
  have hNφ : φ (piBar L ⟨g, hg.1⟩) ∈ Subgroup.normalizer
      ((projUnitriangular 3 K : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro w
    obtain ⟨y, rfl⟩ := φ.surjective w
    rw [hmem, ← map_inv, ← map_mul, ← map_mul, hmem]
    exact hN y
  have h1 := pow_card_sub_one_mem_projUnitriangular hNφ
  rw [hK, ← map_pow] at h1
  have h2 : (piBar L ⟨g, hg.1⟩) ^ (2 ^ n - 1) ∈ (S.subgroupOf L).map (piBar L) := (hmem _).1 h1
  have hker : (piBar L).ker ≤ S.subgroupOf L := by
    rw [ker_piBar]
    intro z hz
    exact hZS z hz
  rw [← map_pow, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker, Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem exists_pow_eq_one_of_lin3 {n : ℕ} (hn : 2 ≤ n)
    (hL : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n)
    (hZ : IsPGroup 2 (Subgroup.center ↥L)) (hS : IsSylowTwoOf S L) {g : G}
    (hg : g ∈ L ⊓ Subgroup.normalizer (S : Set G)) : ∃ k : ℕ, (g ^ (2 ^ n - 1)) ^ (2 ^ k) = 1 := by
  have h := pow_card_sub_one_mem_of_lin3 hn hL hZ hS hg
  obtain ⟨k, hk⟩ := hS.2.1 ⟨_, h⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Lin3

end CFSG.Quasithin.RonanE611
