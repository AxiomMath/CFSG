module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint

namespace ExcNonsplit

theorem largeEvenHalfSplit_mono {p : ℕ} {lab : LargeEvenLabel} {c₁ c₂ : Prop}
    (h : c₁ → c₂) (hc : LargeEvenHalfSplit p lab c₁) : LargeEvenHalfSplit p lab c₂ := by
  unfold LargeEvenHalfSplit at hc ⊢
  rcases hc with h | h | h | ⟨h1, h2, h3, h4, h5⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h h4, h5⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem subgroupMap_ker_le_center (π : G →* G') (hker : π.ker ≤ Subgroup.center G)
    (K : Subgroup G) : (π.subgroupMap K).ker ≤ Subgroup.center ↥K := by
  intro j hj
  rw [Subgroup.ker_subgroupMap] at hj
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hj) (k : G)

end Transport

theorem ggNbrClauseFiveMarking_map_of_central {G G' : Type} [Group G] [Group G'] (π : G →* G')
    (hker : π.ker ≤ Subgroup.center G) {p : ℕ} {x : G} {K : Subgroup G}
    (hnorm : ∀ j ∈ K, x⁻¹ * j * x ∈ K) (h : GGNbrClauseFiveMarking p x K) :
    GGNbrClauseFiveMarking p (π x) (K.map π) := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h
  have hφ : Function.Surjective (π.subgroupMap K) := MonoidHom.subgroupMap_surjective π K
  have hkerφ : (π.subgroupMap K).ker ≤ Subgroup.center ↥K := subgroupMap_ker_le_center π hker K
  haveI : Group.IsPerfect ↥K := ⟨hcomm⟩
  let e : ↥K ⧸ Subgroup.center ↥K ≃* ↥(K.map π) ⧸ Subgroup.center ↥(K.map π) :=
    CFSG.SeitzReduction.F4Pilot.centerQuotientEquivOfSurjective (π.subgroupMap K) hφ hkerφ
  have he : ∀ j : ↥K, e (QuotientGroup.mk' (Subgroup.center ↥K) j) =
      QuotientGroup.mk' (Subgroup.center ↥(K.map π)) (π.subgroupMap K j) :=
    fun j => CFSG.SeitzReduction.F4Pilot.centerQuotientEquivOfSurjective_mk
      (π.subgroupMap K) hφ hkerφ j
  have hcomm' : commutator ↥(K.map π) = ⊤ :=
    Group.isPerfect_def.mp
      (Group.IsPerfect.ofSurjective (f := π.subgroupMap K) hφ)
  refine ⟨hcomm', lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hsimp, hna, θ, hP⟩
  refine ⟨hsimp, hna, e.symm.trans θ, ?_⟩
  rcases hP with hHS | ⟨h3, f, hf, u, hu, hord, hind⟩
  · left
    refine largeEvenHalfSplit_mono (fun hZ => ?_) hHS
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨k, rfl⟩ := hφ y
    have hmk : QuotientGroup.mk' (Subgroup.center ↥K) k = 1 := by
      apply e.injective
      rw [map_one, he k]
      exact (QuotientGroup.eq_one_iff (π.subgroupMap K k)).mpr hy
    have hk : k ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff k).mp hmk
    rw [hZ] at hk
    rw [Subgroup.mem_bot] at hk
    rw [hk, map_one]
  · right
    refine ⟨h3, f, hf, u, hu, hord, ?_⟩
    intro y y' hyy'
    obtain ⟨j, rfl⟩ := hφ y
    obtain ⟨j', rfl⟩ := hφ y'
    let j₁ : ↥K := ⟨x⁻¹ * (j : G) * x, hnorm j j.2⟩
    have hφj₁ : (π.subgroupMap K) j₁ = (π.subgroupMap K) j' := by
      apply Subtype.ext
      change π (x⁻¹ * (j : G) * x) = π (j' : G)
      rw [map_mul, map_mul, map_inv]
      exact hyy'.symm
    have hmem : j₁⁻¹ * j' ∈ (π.subgroupMap K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφj₁, inv_mul_cancel]
    have hcen : j₁⁻¹ * j' ∈ Subgroup.center ↥K := hkerφ hmem
    have hmk : QuotientGroup.mk' (Subgroup.center ↥K) j₁ =
        QuotientGroup.mk' (Subgroup.center ↥K) j' := by
      rw [QuotientGroup.mk'_eq_mk']
      exact ⟨j₁⁻¹ * j', hcen, by group⟩
    have hθ' : ∀ m : ↥K, (e.symm.trans θ)
        (QuotientGroup.mk' (Subgroup.center ↥(K.map π)) (π.subgroupMap K m)) =
        θ (QuotientGroup.mk' (Subgroup.center ↥K) m) := by
      intro m
      rw [MulEquiv.trans_apply, ← he m, MulEquiv.symm_apply_apply]
    have hind1 : (u * f * u⁻¹) (θ (QuotientGroup.mk' (Subgroup.center ↥K) j)) =
        θ (QuotientGroup.mk' (Subgroup.center ↥K) j₁) :=
      hind j j₁ rfl
    calc (u * f * u⁻¹) ((e.symm.trans θ)
            (QuotientGroup.mk' (Subgroup.center ↥(K.map π)) (π.subgroupMap K j)))
        = (u * f * u⁻¹) (θ (QuotientGroup.mk' (Subgroup.center ↥K) j)) := by rw [hθ' j]
      _ = θ (QuotientGroup.mk' (Subgroup.center ↥K) j₁) := hind1
      _ = θ (QuotientGroup.mk' (Subgroup.center ↥K) j') := by rw [hmk]
      _ = (e.symm.trans θ)
            (QuotientGroup.mk' (Subgroup.center ↥(K.map π)) (π.subgroupMap K j')) := by
          rw [hθ' j']

end ExcNonsplit

end CFSG.StandardType
