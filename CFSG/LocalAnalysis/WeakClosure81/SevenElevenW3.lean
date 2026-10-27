module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

section Sections

variable {G : Type} [Group G]

theorem hasQuotShape_centerPre_of_isBarMap {K N : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K N φ) {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : P (X ⧸ Subgroup.center X)) : HasQuotShape K (centerPre K N) P := by
  refine ⟨X ⧸ Subgroup.center X, inferInstance,
    (QuotientGroup.mk' (Subgroup.center X)).comp φ, ?_, ?_, hP⟩
  · exact (QuotientGroup.mk'_surjective _).comp hφ.surjective
  · intro k
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff]
    change (∀ g : X, g * φ k = φ k * g) ↔
      (k : G) ∈ K ∧ ∀ x ∈ K, (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ N
    constructor
    · intro hk
      refine ⟨k.2, fun x hx => ?_⟩
      have h1 : φ (k * (⟨x, hx⟩ : ↥K) * k⁻¹ * (⟨x, hx⟩ : ↥K)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hk (φ ⟨x, hx⟩)]
        group
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (hφ.ker_iff _).mp h1
    · rintro ⟨-, hx⟩ g
      obtain ⟨y, rfl⟩ := hφ.surjective g
      have h1 : φ (k * y * k⁻¹ * y⁻¹) = 1 := by
        refine (hφ.ker_iff _).mpr ?_
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hx (y : G) y.2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem isBarMap_mk_pCore (K : Subgroup G) :
    IsBarMap K (pCoreOf 2 K) (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
  refine ⟨QuotientGroup.mk'_surjective _, fun k => ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm

end Sections

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

end CFSG.LocalAnalysis.WeakClosure81
