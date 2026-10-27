module

public import CFSG.LocalAnalysis.SteinbergCCCComponentSubnormalSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup

theorem le_solvableRadical_of_normal_ne_top {L : Type*} [Group L] [Finite L]
    (hL : CFSG.IsCComponent (⊤ : Subgroup L)) {N : Subgroup L} [N.Normal] (hN : N ≠ ⊤) :
    N ≤ CFSG.solvableRadical L := by
  have hsub : (N.subgroupOf (⊤ : Subgroup L)).IsSubnormal := by
    have : (N.subgroupOf (⊤ : Subgroup L)).Normal := inferInstance
    exact this.isSubnormal
  have hs := CFSG.LocalAnalysis.Ccomponent_proper_subnormal_solvable hL (lt_top_iff_ne_top.2 hN)
    hsub
  exact (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).2.2.1 N
    inferInstance hs

theorem nq_Ccomponent_representation_kernel_commutator {M : Type*} [Group M] [Finite M]
    {L : Subgroup M} [L.Normal] (hL : CFSG.IsCComponent (⊤ : Subgroup L)) {A : Type*} [Group A]
    (φ : M →* A) (hφ : φ.comp L.subtype ≠ 1) :
    ⁅L, φ.ker⁆ ≤ (CFSG.solvableRadical L).map L.subtype := by
  have hne : φ.ker.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hφ
    ext x
    have hx : x ∈ φ.ker.subgroupOf L := by rw [htop]; exact mem_top x
    rw [mem_subgroupOf, MonoidHom.mem_ker] at hx
    simpa using hx
  have hle := le_solvableRadical_of_normal_ne_top hL hne
  refine (commutator_le_inf L φ.ker).trans fun x hx => ?_
  obtain ⟨hxL, hxK⟩ := mem_inf.1 hx
  exact ⟨⟨x, hxL⟩, hle (show (⟨x, hxL⟩ : L) ∈ φ.ker.subgroupOf L from hxK), rfl⟩

theorem nontrivial_Ccomponent_images_retain_radical_quotient_Sylow_noncyclicity {L : Type*}
    [Group L] [Finite L] [(CFSG.solvableRadical L).Normal]
    (hL : CFSG.IsCComponent (⊤ : Subgroup L)) {F : Type*} [Group F]
    (α : L →* F) (hα : α ≠ 1) {r : ℕ} (hr : r.Prime) (H : Subgroup L) (S : Sylow r H)
    (hB : ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ H.map (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧ IsPGroup r B ∧ ¬ IsCyclic B) :
    ¬ IsCyclic ((S : Subgroup H).map (α.comp H.subtype)) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  set R := CFSG.solvableRadical L with hR
  set π := QuotientGroup.mk' R with hπ
  have hker : α.ker ≤ R := by
    refine le_solvableRadical_of_normal_ne_top hL fun htop => hα ?_
    ext x
    have hx : x ∈ α.ker := by rw [htop]; exact mem_top x
    simpa using hx
  intro hcyc
  obtain ⟨⟨_, ⟨s₀, hs₀, rfl⟩⟩, hgen⟩ := hcyc.exists_generator
  set f : H →* H.map π := π.subgroupMap H with hf
  have hfs : Function.Surjective f := π.subgroupMap_surjective H
  set Sb : Sylow r (H.map π) := S.mapSurjective hfs with hSb
  have hSbcyc : IsCyclic (Sb : Subgroup (H.map π)) := by
    refine ⟨⟨⟨f s₀, by rw [hSb, Sylow.coe_mapSurjective]; exact ⟨s₀, hs₀, rfl⟩⟩, fun x => ?_⟩⟩
    obtain ⟨y, hy⟩ := x
    rw [hSb, Sylow.coe_mapSurjective] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hgen ⟨(α.comp H.subtype) s, ⟨s, hs, rfl⟩⟩)
    refine mem_zpowers_iff.2 ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hk' : α (s₀ ^ k : H) = α s := by
      have := congrArg Subtype.val hk
      simpa using this
    have hR' : ((s₀ ^ k : H) : L)⁻¹ * s ∈ R :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hk', ← map_inv, ← map_mul,
        inv_mul_cancel, map_one])
    have := (QuotientGroup.eq (s := R)).2 hR'
    simpa [hf, hπ] using this
  obtain ⟨B, hBH, hBr, hBcyc⟩ := hB
  have hB' : IsPGroup r (B.subgroupOf (H.map π)) := hBr.comap_subtype
  obtain ⟨P, hP⟩ := hB'.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (H.map π) Sb P
  apply hBcyc
  have hPcyc : IsCyclic ((h • Sb : Sylow r (H.map π)) : Subgroup (H.map π)) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact isCyclic_of_surjective _ ((MulDistribMulAction.toMonoidEnd (MulAut (H.map π))
      (H.map π) (MulAut.conj h)).subgroupMap_surjective (Sb : Subgroup (H.map π)))
  have hBsub : IsCyclic (B.subgroupOf (H.map π)) :=
    Subgroup.isCyclic_of_le hP
  exact isCyclic_of_surjective (subgroupOfEquivOfLe hBH).toMonoidHom
    (subgroupOfEquivOfLe hBH).surjective

end CFSG.Quasithin.H13.NQSetup
