module

public import CFSG.Assembly.Defs
public import CFSG.LieType.Chevalley.RankOneGaussian
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.SteinbergCAOddResidualOrderFacts

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open Subgroup CFSG.LieType.Chevalley

theorem isComponentOf_map_of_normal_simple {G : Type*} [Group G] {X : Subgroup G}
    (S : Subgroup X) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) : CFSG.Assembly.IsComponentOf (S.map X.subtype) X := by
  have hle : S.map X.subtype ≤ X := map_subtype_le S
  have hof : (S.map X.subtype).subgroupOf X = S :=
    comap_map_eq_self_of_injective X.subtype_injective S
  have hn : ((S.map X.subtype).subgroupOf X).Normal := by
    rw [hof]
    exact hSn
  refine ⟨hle, CFSG.Assembly.IsSubnormal.step hle hn (CFSG.Assembly.IsSubnormal.refl X),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 ?_⟩
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (S.equivMapOfInjective X.subtype X.subtype_injective)).1
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1

theorem map_subtype_le_of_commutator_le {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : ⁅X, X⁆ ≤ N) (S : Subgroup X) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) : S.map X.subtype ≤ N := by
  have hperf : commutator S = ⊤ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1.1.commutator_eq_top
  set f : S →* G := X.subtype.comp S.subtype
  have hrange : f.range = S.map X.subtype := by
    rw [MonoidHom.range_comp, range_subtype]
  have hle : f.range ≤ X := hrange ▸ map_subtype_le S
  have hc : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hperf]
  calc S.map X.subtype = f.range := hrange.symm
    _ = ⁅f.range, f.range⁆ := hc.symm
    _ ≤ ⁅X, X⁆ := commutator_mono hle hle
    _ ≤ N := hXN

theorem le_map_subtype_of_normal_of_le {G : Type*} [Group G] {X N : Subgroup G} (hNX : N ≤ X)
    (hNs : IsSimpleGroup N) (S : Subgroup X) (hSn : S.Normal) (hS1 : S ≠ ⊥)
    (hSN : S.map X.subtype ≤ N) : N ≤ S.map X.subtype := by
  set T : Subgroup N := (S.map X.subtype).subgroupOf N
  have hTn : T.Normal := ⟨fun t ht n => by
    obtain ⟨s, hs, hst⟩ := mem_subgroupOf.1 ht
    refine mem_subgroupOf.2 ⟨⟨n, hNX n.2⟩ * s * ⟨n, hNX n.2⟩⁻¹, hSn.conj_mem s hs _, ?_⟩
    simp only [coe_subtype, coe_mul, coe_inv] at hst ⊢
    rw [hst]⟩
  rcases hNs.eq_bot_or_eq_top_of_normal T with h | h
  · exfalso
    apply hS1
    rw [eq_bot_iff]
    intro s hs
    have hsN : ((s : G)) ∈ N := hSN ⟨s, hs, rfl⟩
    have hT : (⟨s, hsN⟩ : N) ∈ T := mem_subgroupOf.2 ⟨s, hs, rfl⟩
    rw [h, mem_bot] at hT
    have h1 : ((s : X) : G) = 1 := congrArg Subtype.val hT
    exact (mem_bot).2 (Subtype.ext h1)
  · intro x hx
    have hT : (⟨x, hx⟩ : N) ∈ T := h ▸ mem_top _
    exact mem_subgroupOf.1 hT

theorem exists_injective_of_normal_simple_of_commutator_le {G H : Type*} [Group G] [Group H]
    {X N : Subgroup G} (hXN : ⁅X, X⁆ ≤ N) (hNX : N ≤ X) (hNs : IsSimpleGroup N) (ρ : H →* G)
    (hρ : Function.Injective ρ) (hρN : ∀ h, ρ h ∈ N) (S : Subgroup X) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    ∃ φ : H →* S, Function.Injective φ := by
  have hS1 : S ≠ ⊥ := by
    have := hSs.toNontrivial
    exact (nontrivial_iff_ne_bot S).1 this
  have hle := le_map_subtype_of_normal_of_le hNX hNs S hSn hS1
    (map_subtype_le_of_commutator_le hXN S hSs hSnab)
  have hmem : ∀ h, (⟨ρ h, hNX (hρN h)⟩ : X) ∈ S := fun h => by
    obtain ⟨s, hs, hsρ⟩ := hle (hρN h)
    have : s = ⟨ρ h, hNX (hρN h)⟩ := Subtype.ext hsρ
    rw [← this]
    exact hs
  refine ⟨((ρ.codRestrict X fun h => hNX (hρN h)).codRestrict S hmem), fun a b hab => hρ ?_⟩
  have h1 := congrArg (fun y : S => ((y : X) : G)) hab
  exact h1

theorem SL2_map_injective {k K : Type*} [Field k] [Field K] (f : k →+* K) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := fun A B h =>
  Subtype.ext (Matrix.ext fun i j => f.injective (by
    have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
      (M : Matrix (Fin 2) (Fin 2) K) i j) h
    simpa using this))

theorem false_of_injective_SL2_of_mulEquiv {G : Type*} [Group G] {S : Subgroup G} {k : Type*}
    [Field k] [Finite k] (hk : ringChar k ≠ 2) (φ : SL2 k →* S) (hφ : Function.Injective φ)
    {K : Type*} [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have : Fintype k := Fintype.ofFinite k
  have : CharP k (ringChar k) := ringChar.charP k
  obtain ⟨n, hp, -⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  have hinj : Function.Injective (S.subtype.comp φ) := S.subtype_injective.comp hφ
  refine CFSG.LocalAnalysis.SteinbergCA.false_of_mulEquiv_SL2_of_hom eS hk (S.subtype.comp φ)
    (fun A => (φ A).2) (fun h => ?_) (fun h => ?_)
  ·
    have h1 := hinj (h.trans (map_one _).symm)
    have h2 := congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    exact Ring.neg_one_ne_one_of_char_ne_two hk h2
  · exact CFSG.LocalAnalysis.SteinbergCA.uSL_one_ne_one_and_ne_neg_one.1
      (hinj (h.trans (map_one _).symm))

end CFSG.LocalAnalysis.SteinbergBM
