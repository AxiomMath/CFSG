module

public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

open CFSG.Open CFSG.LieType.BorelTits

namespace CFSG.Quasithin

section Dich

variable {G : Type} [Group G] [Finite G]

theorem perfect_le_of_le_sup_pGroup {L N P : Subgroup G} (hLp : ⁅L, L⁆ = L) (hNL : N ≤ L)
    (hNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hP : IsPGroup 2 P) (hPL : P ≤ L)
    (hle : L ≤ N ⊔ P) : L ≤ N := by
  classical
  have hNnormal : (N.subgroupOf L).Normal := ⟨fun n hn l => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn l l.2 n hn⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hQ2 : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxN : x ∈ N.subgroupOf L ⊔ P.subgroupOf L := by
      rw [← Subgroup.subgroupOf_sup hNL hPL]
      exact hle x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
    have hPpL : IsPGroup 2 (P.subgroupOf L) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    obtain ⟨k, hk⟩ := hPpL ⟨z, hz⟩
    refine ⟨k, ?_⟩
    have e : (QuotientGroup.mk x : ↥L ⧸ N.subgroupOf L) = QuotientGroup.mk z := by
      rw [← hyz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul]
    rw [e, ← QuotientGroup.mk_pow]
    have : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, QuotientGroup.mk_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (↥L ⧸ N.subgroupOf L) := hQ2.isNilpotent
  have hsub : Subsingleton (↥L ⧸ N.subgroupOf L) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N.subgroupOf L) ‹_›
  intro x hx
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ N.subgroupOf L) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem perfect_normal_dichotomy {L N : Subgroup G} (hLp : ⁅L, L⁆ = L) (hLs : IsSimpleGroup (KBar L))
    (hNL : N ≤ L) (hNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) :
    N ≤ pCoreOf 2 L ∨ L ≤ N := by
  classical
  have hNnormal : (N.subgroupOf L).Normal := ⟨fun n hn l => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn l l.2 n hn⟩
  set π : ↥L →* KBar L := QuotientGroup.mk' ((pCoreOf 2 L).subgroupOf L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNn' : ((N.subgroupOf L).map π).Normal := Subgroup.Normal.map hNnormal π hπs
  rcases hLs.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map π) with hbot | htop
  · left
    intro n hn
    have h1 : π ⟨n, hNL hn⟩ ∈ (N.subgroupOf L).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hn)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  · right
    refine perfect_le_of_le_sup_pGroup hLp hNL hNn (pCoreOf_isPGroup 2 L) (pCoreOf_le 2 L) ?_
    intro x hx
    have h1 : π ⟨x, hx⟩ ∈ (N.subgroupOf L).map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp h1
    have hp : ((n : ↥L) : G)⁻¹ * x ∈ pCoreOf 2 L :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hnx)
    have hnN : ((n : ↥L) : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have e : x = ((n : ↥L) : G) * (((n : ↥L) : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right hp)

end Dich

end CFSG.Quasithin
