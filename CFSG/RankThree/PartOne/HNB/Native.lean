module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def NativeData (M : Type) [Group M] : Prop :=
  ∃ (f t : M) (K Y : Subgroup M),
    orderOf f = 5 ∧ K ≤ Subgroup.centralizer ({f} : Set M) ∧
    (K.subgroupOf (Subgroup.centralizer ({f} : Set M))).Normal ∧
    Subgroup.zpowers f ⊓ K = ⊥ ∧ IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧
    StatedClassicalModel K .PSU 3 5 1 ∧ Y ≤ K ∧
    Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
    t ∈ Y ∧ orderOf t = 2 ∧ ∀ y ∈ Y, y * t = t * y

@[expose] def HNNativeFive : Prop :=
  IsSimpleGroup (Carrier .HN) ∧ (∃ a b : Carrier .HN, a * b ≠ b * a) ∧ NativeData (Carrier .HN)

structure NativeIn (G : Type) [Group G] (L : Subgroup G) where
  x : G
  t : G
  K : Subgroup G
  Y : Subgroup G
  hxL : x ∈ L
  hx5 : orderOf x = 5
  hKL : K ≤ L
  hKx : K ≤ Subgroup.centralizer ({x} : Set G)
  hKnorm : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (K : Set G)
  hxK : Subgroup.zpowers x ⊓ K = ⊥
  hKsimple : IsSimpleGroup K
  hKnonab : ∃ a b : K, a * b ≠ b * a
  hKmodel : StatedClassicalModel K .PSU 3 5 1
  hYK : Y ≤ K
  hYsl : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  htY : t ∈ Y
  ht2 : orderOf t = 2
  htc : ∀ y ∈ Y, y * t = t * y

theorem nativeIn_of_nativeData {M : Type} [Group M] (hN : NativeData M) {G : Type} [Group G]
    {L : Subgroup G} (e : M ≃* L) : Nonempty (NativeIn G L) := by
  obtain ⟨f, t, K, Y, hf5, hKf, hKn, hfK, hKs, hKna, hKm, hYK, hYsl, htY, ht2, htc⟩ := hN
  set φ : M →* G := L.subtype.comp e.toMonoidHom with hφ
  have hinj : Function.Injective φ := L.subtype_injective.comp e.injective
  have hφapp : ∀ g, φ g = ((e g : L) : G) := fun g => rfl
  have eK : K ≃* K.map φ := K.equivMapOfInjective φ hinj
  have eY : Y ≃* Y.map φ := Y.equivMapOfInjective φ hinj
  refine ⟨⟨φ f, φ t, K.map φ, Y.map φ, (e f).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩⟩
  · rw [orderOf_injective φ hinj f]
    exact hf5
  · rintro _ ⟨k, hk, rfl⟩
    exact (e k).2
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKf hk)
    rw [← map_mul, ← map_mul]
    exact congrArg φ this
  · rintro g ⟨hgL, hgc⟩
    set g₀ : M := e.symm ⟨g, hgL⟩ with hg₀
    have hφg : φ g₀ = g := by rw [hφapp, hg₀, MulEquiv.apply_symm_apply]
    have hcomm : g₀ * f = f * g₀ := by
      apply hinj
      rw [map_mul, map_mul, hφg]
      exact Subgroup.mem_centralizer_singleton_iff.mp hgc
    have hg₀C : g₀ ∈ Subgroup.centralizer ({f} : Set M) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have key : ∀ g' : Subgroup.centralizer ({f} : Set M), ∀ k ∈ K,
        (g' : M) * k * (g' : M)⁻¹ ∈ K := by
      intro g' k hk
      have h1 := hKn.conj_mem ⟨k, hKf hk⟩ (Subgroup.mem_subgroupOf.mpr hk) g'
      exact Subgroup.mem_subgroupOf.mp h1
    have hg₀N : g₀ ∈ Subgroup.normalizer (K : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        exact key ⟨g₀, hg₀C⟩ k hk
      · intro hk
        have := key ⟨g₀, hg₀C⟩⁻¹ _ hk
        simpa [mul_assoc] using this
    rw [← hφg]
    exact Subgroup.le_normalizer_map φ ⟨g₀, hg₀N, rfl⟩
  · rw [← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ φ hinj, hfK, Subgroup.map_bot]
  · exact eK.isSimpleGroup_congr.mp hKs
  · obtain ⟨a, b, hab⟩ := hKna
    exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul, h]))⟩
  · exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv eK.symm hKm
  · exact Subgroup.map_mono hYK
  · obtain ⟨σ⟩ := hYsl
    exact ⟨eY.symm.trans σ⟩
  · exact Subgroup.mem_map_of_mem φ htY
  · rw [orderOf_injective φ hinj t]
    exact ht2
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, htc y hy]

end CFSG.RankThree.PartOne.HNB
