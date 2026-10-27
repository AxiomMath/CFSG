module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvMap

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem imageSub_mono {K D₁ D₂ : Subgroup G} (h : D₁ ≤ D₂) : imageSub K D₁ ≤ imageSub K D₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem imageSub_sup {K D₁ D₂ : Subgroup G} (h₁ : D₁ ≤ K) (h₂ : D₂ ≤ K) :
    imageSub K (D₁ ⊔ D₂) = imageSub K D₁ ⊔ imageSub K D₂ := by
  simp only [imageSub, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem imageSub_zpowers {K : Subgroup G} (k : K) :
    imageSub K (Subgroup.zpowers (k : G)) =
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) := by
  have h : (Subgroup.zpowers (k : G)).subgroupOf K = Subgroup.zpowers k := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers]
    exact inf_eq_left.mpr (Subgroup.zpowers_le.mpr k.2)
  rw [imageSub, h, MonoidHom.map_zpowers]

theorem mk_mem_imageSub {K D : Subgroup G} {x : K} (hx : (x : G) ∈ D) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 K) x ∈ imageSub K D :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)

theorem mem_normalizer_of_conj_mem {M : Type*} [Group M] [Finite M] {D : Subgroup M} {w : M}
    (h : ∀ y ∈ D, w * y * w⁻¹ ∈ D) : w ∈ Subgroup.normalizer (D : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  let f : D → D := fun x => ⟨w * x * w⁻¹, h x x.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : w * (a : M) * w⁻¹ = w * (b : M) * w⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w * y * w⁻¹, hy⟩
  have h2 : w * (x : M) * w⁻¹ = w * y * w⁻¹ := congrArg Subtype.val hx
  have hxy : (x : M) = y := by simpa using h2
  rw [← hxy]
  exact x.2

end CFSG.RankThree.PartTwo.Sec8.Hering611
