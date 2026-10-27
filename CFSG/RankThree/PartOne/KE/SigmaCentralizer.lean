module

public import CFSG.RankThree.PartOne.KE.A1Centralizer
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem rootRankOneGroup_le_rootSpan {S : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h1 : α ∈ S) (h2 : -α ∈ S) :
    rootRankOneGroup τ L α ≤ rootSpan τ L S := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ L hα).1]
  exact sup_le (le_iSup₂_of_le α h1 le_rfl) (le_iSup₂_of_le (-α) h2 le_rfl)

theorem torusGroup_le_normalizer_rootSpan {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) :
    torusGroup τ L ≤ Subgroup.normalizer (rootSpan τ L S : Set (ModGL τ L)) := by
  have h1 : torusGroup τ L ≤ ⨅ α : S, Subgroup.normalizer
      (rootSubgroup τ L α.1 : Set (ModGL τ L)) :=
    le_iInf fun α => torusGroup_le_normalizer_rootSubgroup (hS α.1 α.2)
  refine h1.trans ((Subgroup.iInf_normalizer_le_normalizer_iSup fun α : S =>
    rootSubgroup τ L α.1).trans ?_)
  have h2 : (⨆ α : S, rootSubgroup τ L α.1) = rootSpan τ L S := by
    rw [rootSpan, iSup_subtype']
  rw [h2]

theorem toralCentralizer_le_sup_rootSpan {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    (hSn : ∀ α ∈ S, -α ∈ S) (hker : rootCharKernel a ⊆ S) :
    toralCentralizer τ L a ≤ torusGroup τ L ⊔ rootSpan τ L S := by
  classical
  set Q := rootSpan τ L S with hQ
  set H := torusGroup τ L with hH
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ L a).2.2.2]
  refine sup_le (sup_le le_sup_left ?_) ?_
  · exact (rootSpan_mono hker).trans le_sup_right
  ·
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hwcl := rootCharStabilizer_subset_closure hp hord hap ha1 hw
    let N := monomialSubgroup τ L
    let π := weylQuotientHom τ L
    let Wsub : Subgroup (WeylGroup τ) := ((H ⊔ Q).subgroupOf N).map π
    have hgen : ∀ α ∈ S, rootReflection α ∈ Wsub := by
      intro α hα
      have hαr := hS α hα
      obtain ⟨hmem, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hαr).2.2.1 1
      refine ⟨⟨rootWeylSL2 τ L α 1, hmem⟩, ?_, hπ⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_sup_right ?_
      exact rootRankOneGroup_le_rootSpan hαr hα (hSn α hα) ⟨_, rfl⟩
    have hclW : Subgroup.closure {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} ≤ Wsub := by
      rw [Subgroup.closure_le]
      rintro _ ⟨α, hα, rfl⟩
      exact hgen α (hker hα)
    obtain ⟨m, hm, hmπ⟩ := hclW hwcl
    have hcanN : canonicalRep (coxeterSystem τ) L w ∈ N := canonicalRep_mem_monomialSubgroup L w
    obtain ⟨ρ, -, hρ, -, -, hρker⟩ := (Weyl_normalizer_quotient τ L).2.1
    have hρπ : ∀ g : N, ρ g = π g := fun g =>
      (hρ g).unique (mapsRootLines_weylQuotientHom g)
    have hcan : π ⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ = w :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)
    have hker1 : (⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ * m⁻¹ : N) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρπ, hρπ, hcan, hmπ, mul_inv_cancel]
    rw [hρker, Subgroup.mem_subgroupOf] at hker1
    have hker2 : canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹ ∈ H := hker1
    have hmQ : (m : ModGL τ L) ∈ H ⊔ Q := hm
    have hc : canonicalRep (coxeterSystem τ) L w =
        (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) := by group
    have h3 : (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) ∈
        H ⊔ Q := mul_mem (Subgroup.mem_sup_left hker2) hmQ
    rw [← hc] at h3
    exact h3

theorem mem_torus_mul_rootSpan_of_commute {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    (hSn : ∀ α ∈ S, -α ∈ S) (hker : rootCharKernel a ⊆ S) {y : ModGL τ L}
    (hy : y ∈ adjointGroup τ L) (hcomm : y * rootDiagUnit τ a = rootDiagUnit τ a * y) :
    y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L)) := by
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootSpan hS)]
  refine toralCentralizer_le_sup_rootSpan hp hord hap ha1 hS hSn hker ?_
  exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩

end CFSG.RankThree.PartOne.KE
