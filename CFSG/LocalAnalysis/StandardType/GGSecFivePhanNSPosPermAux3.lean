module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.ClassicalGroups.Unitary.Perfect
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniMark

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA_commute_of_scalar_commutator {d : ℕ} {K : Type} [Field K]
    {H : Subgroup (GL (Fin d) K)} (hperf : Group.IsPerfect ↥H)
    (X : Subgroup.normalizer (H : Set (GL (Fin d) K)))
    (hX : ∀ h : ↥H, (X : GL (Fin d) K) * (h : GL (Fin d) K) * (X : GL (Fin d) K)⁻¹ *
      (h : GL (Fin d) K)⁻¹ ∈ LargeEvenScalars (Fin d) K) :
    ∀ g ∈ H, (X : GL (Fin d) K) * g = g * (X : GL (Fin d) K) := by
  classical
  have hker := CFSG.LocalAnalysis.GLTheoremA.K155X.l154_ker_projMk_le_center H
  have h : ∀ u : ↥H, LargeEvenProjMk H (H.normalizerMonoidHom X u) = LargeEvenProjMk H u := by
    intro u
    let zh : ↥H := (H.normalizerMonoidHom X u) * u⁻¹
    have hzu : (zh : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := hX u
    have hzu_eq : H.normalizerMonoidHom X u = zh * u := by
      apply Subtype.ext
      change (X : GL (Fin d) K) * (u : GL (Fin d) K) * (X : GL (Fin d) K)⁻¹ =
        ((X : GL (Fin d) K) * (u : GL (Fin d) K) * (X : GL (Fin d) K)⁻¹ *
          (u : GL (Fin d) K)⁻¹) * (u : GL (Fin d) K)
      group
    have hzh1 : LargeEvenProjMk H zh = 1 := by
      apply (MonoidHom.mem_ker).mp
      rw [show (LargeEvenProjMk H).ker = (LargeEvenScalars (Fin d) K).subgroupOf H from
        QuotientGroup.ker_mk' _]
      exact (Subgroup.mem_subgroupOf).mpr hzu
    rw [hzu_eq, map_mul, hzh1, one_mul]
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq (LargeEvenProjMk H) hker hperf
    ((H.normalizerMonoidHom X).toMonoidHom) (MonoidHom.id ↥H) h
  intro g hg
  have h2 := congrArg Subtype.val (key ⟨g, hg⟩)
  change (X : GL (Fin d) K) * g * (X : GL (Fin d) K)⁻¹ = g at h2
  calc (X : GL (Fin d) K) * g = (X : GL (Fin d) K) * g * (X : GL (Fin d) K)⁻¹ *
        (X : GL (Fin d) K) := by group
    _ = g * (X : GL (Fin d) K) := by rw [h2]


theorem su_coe_mem_largeEvenScalars_of_mem_center {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) {u : Su K 2 f n}
    (hu : u ∈ Subgroup.center (Su K 2 f n)) :
    (u : GL (Fin n) K) ∈ LargeEvenScalars (Fin n) K := by
  have hu2 : (u : GL (Fin n) K) ∈ StatedSU n (2 ^ f) K := by
    rw [← SUid_eq_statedSU hK n]; exact u.2
  let u' : ↥(StatedSU n (2 ^ f) K) := ⟨(u : GL (Fin n) K), hu2⟩
  have hcenter' : u' ∈ Subgroup.center ↥(StatedSU n (2 ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subgroup.mem_center_iff] at hu
    have hg : (g : GL (Fin n) K) ∈ SUid (unitaryInvolution K 2 f) n := by
      rw [SUid_eq_statedSU hK n]; exact g.2
    refine Subtype.coe_injective.eq_iff.mp ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact congrArg Subtype.val (hu ⟨(g : GL (Fin n) K), hg⟩)
  have hsc := center_statedSU_le_scalars hK hn hcenter'
  have : (u : GL (Fin n) K) ∈ StatedScalars (Fin n) K := hsc
  rwa [← largeEvenScalars_eq_statedScalars] at this

theorem ggNSPosPA_scalar_of_mem_center {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {u : Su K 2 f n}
    (hu : u ∈ Subgroup.center (Su K 2 f n)) :
    (u : GL (Fin n) K) ∈ LargeEvenScalars (Fin n) K :=
  su_coe_mem_largeEvenScalars_of_mem_center h.card h.four_le hu

end CFSG.StandardType

end
