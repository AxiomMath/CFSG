module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockSup
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAInv
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open CFSG.RankThreeCoreUniqueness.Helpers

variable {W Y : Type} [Group W] [Group Y]

section Hom

variable (π : W →* Y)

theorem isSolvable_of_map [Finite W] (hk : IsPGroup 2 π.ker) {A : Subgroup W}
    (h : Group.IsSolvable ↥(A.map π)) : Group.IsSolvable ↥A := by
  have h2 : IsPGroup 2 ↥(π.ker.subgroupOf A) := hk.comap_subtype
  have : Group.IsSolvable ↥(π.ker.subgroupOf A) := by
    have := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (π.ker.subgroupOf A).subtype (π.subgroupMap A)
    (by rw [Subgroup.ker_subgroupMap, Subgroup.range_subtype])

theorem isSolvable_map {A : Subgroup W} (h : Group.IsSolvable ↥A) : Group.IsSolvable ↥(A.map π) :=
  Group.isSolvable_of_surjective (f := π.subgroupMap A) (π.subgroupMap_surjective A)

theorem ker_le_sylow [Finite W] (hk : IsPGroup 2 π.ker) {S : Subgroup W} (hS : IsSylowTwoOf S ⊤) :
    π.ker ≤ S := by
  have hsub : S ≤ Subgroup.normalizer (π.ker : Set W) := by
    intro x _
    exact Subgroup.mem_normalizer_iff.mpr fun h => by
      refine ⟨fun hh => π.normal_ker.conj_mem h hh x, fun hh => ?_⟩
      have := π.normal_ker.conj_mem _ hh x⁻¹
      simpa [mul_assoc] using this
  have hsup : IsPGroup 2 ↥(S ⊔ π.ker) :=
    hS.2.1.to_sup_of_normal_right' hk hsub
  have := (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _ le_top hsup le_sup_left
  exact le_sup_right.trans this

theorem mem_normalizer_iff_comap (hπ : Function.Surjective π) {S : Subgroup W} (hker : π.ker ≤ S)
    {x : W} :
    x ∈ Subgroup.normalizer (S : Set W) ↔
      π x ∈ Subgroup.normalizer ((S.map π : Subgroup Y) : Set Y) := by
  have hmem : ∀ w, π w ∈ S.map π ↔ w ∈ S := fun w => by
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker]
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    obtain ⟨w, rfl⟩ := hπ y
    rw [hmem, ← map_inv, ← map_mul, ← map_mul, hmem]
    exact h w
  · intro h w
    have := h (π w)
    rwa [hmem, ← map_inv, ← map_mul, ← map_mul, hmem] at this

theorem comap_pCoreOf_inf_le (hk : IsPGroup 2 π.ker) (A : Subgroup W) :
    (pCoreOf 2 (A.map π)).comap π ⊓ A ≤ pCoreOf 2 A := by
  have hp : IsPGroup 2 ↥((pCoreOf 2 (A.map π)).comap π) :=
    (pCoreOf_isPGroup 2 (A.map π)).comap_of_ker_isPGroup π hk
  refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right (fun a ha => ?_)
    (hp.to_le inf_le_left)
  refine mem_normalizer_inf ?_ (Subgroup.le_normalizer ha)
  have h1 : π a ∈ Subgroup.normalizer ((pCoreOf 2 (A.map π) : Subgroup Y) : Set Y) :=
    localGroup_le_normalizer_pCoreOf 2 (A.map π) ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff] at h1 ⊢
  intro w
  have := h1 (π w)
  simpa [Subgroup.mem_comap, map_mul, map_inv] using this

theorem map_pCoreOf_le (hπ : Function.Surjective π) (A : Subgroup W) :
    (pCoreOf 2 A).map π ≤ pCoreOf 2 (A.map π) := by
  refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
    (Subgroup.map_mono (pCoreOf_le 2 A)) (fun y hy => ?_) ((pCoreOf_isPGroup 2 A).map π)
  obtain ⟨a, ha, rfl⟩ := hy
  have h1 : a ∈ Subgroup.normalizer (pCoreOf 2 A : Set W) := localGroup_le_normalizer_pCoreOf 2 A ha
  have h2 : a ∈ Subgroup.normalizer (π.ker : Set W) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr π.normal_ker]
    exact Subgroup.mem_top _
  have hsup := mem_normalizer_sup h1 h2
  have hmem : ∀ w, π w ∈ (pCoreOf 2 A).map π ↔ w ∈ pCoreOf 2 A ⊔ π.ker := fun w => by
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨w, rfl⟩ := hπ y
  rw [hmem, ← map_inv, ← map_mul, ← map_mul, hmem]
  exact Subgroup.mem_normalizer_iff.mp hsup w

theorem charTwo_comap (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker) {P : Subgroup Y}
    (hP : CharTwo P) : CharTwo (P.comap π) := by
  intro g ⟨hgP, hgC⟩
  have hmapP : (P.comap π).map π = P := Subgroup.map_comap_eq_self_of_surjective hπ P
  have hinf := comap_pCoreOf_inf_le π hk (P.comap π)
  rw [hmapP] at hinf
  have hg2 : π g ∈ Subgroup.centralizer (pCoreOf 2 P : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrP : r ∈ (P.comap π).map π := by rw [hmapP]; exact pCoreOf_le 2 P hr
    obtain ⟨w, hw, rfl⟩ := hrP
    have hwQ : w ∈ pCoreOf 2 (P.comap π) := hinf ⟨hr, hw⟩
    have := Subgroup.mem_centralizer_iff.mp hgC w hwQ
    simpa [map_mul] using congrArg π this
  exact hinf ⟨hP ⟨hgP, hg2⟩, hgP⟩

end Hom

end CFSG.Quasithin.GoldMLB
