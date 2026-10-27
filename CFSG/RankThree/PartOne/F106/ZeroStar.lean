module

public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.N143 (SectionListBound)

theorem zeroStar_quotient_list (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hSLB : SectionListBound) {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {K : Subgroup G} (hK : K ∈ sectionTenZeroStar p A) :
    CFSG.RankThree.PartOne.Census3.TheoremThreeList (↥K ⧸ center ↥K) := by
  have hKq : CFSG.IsQuasisimple ↥K :=
    section_ten_maximal_moving_theta_components_quasisimple hS hTwo G p A h K hK
  obtain ⟨hsimple, hnonab, hKP, -, -, -, -, -, -, -⟩ := id h
  have : IsSimpleGroup G := hsimple
  have he3 : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq h).le
  obtain ⟨c, -, hc1, hKc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p A).2.2.1 hK.2)
  have hKC : K ≤ centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hKc).1
  have hne : centralizer ({c} : Set G) ≠ ⊤ :=
    EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hc1
  have hCK : CFSG.IsKGroup ↥(centralizer ({c} : Set G)) := hKP _ hne
  have hCe : evenRank ↥(centralizer ({c} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans he3
  exact (hSLB _ hCK hCe (K.subgroupOf (centralizer ({c} : Set G))) ↥K hKq
    (Subgroup.subgroupOfEquivOfLe hKC).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hKC).surjective).1

theorem zeroStar_simple_quotient (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hI : InSec10Seven) (hSLB : SectionListBound) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} (h : SteinbergBM.SectionTenSetup G p A) {K : Subgroup G}
    (hK : K ∈ sectionTenZeroStar p A) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (φ : ↥K →* X), Function.Surjective φ ∧
      φ.ker ≤ center ↥K ∧ IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧
      CFSG.Blueprint.EvenLieType X ∧ CFSG.RankThree.PartOne.Census3.TheoremThreeList X := by
  have hKq : CFSG.IsQuasisimple ↥K :=
    section_ten_maximal_moving_theta_components_quasisimple hS hTwo G p A h K hK
  exact ⟨↥K ⧸ center ↥K, inferInstance, inferInstance, QuotientGroup.mk' (center ↥K),
    QuotientGroup.mk'_surjective _, fun x hx => (QuotientGroup.eq_one_iff x).mp hx, hKq.2.1,
    hKq.2.2, hI G p A h K hK, zeroStar_quotient_list hS hTwo hSLB h hK⟩

theorem conj_mem_thetaComponentsAt_cent {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {d x : G}
    (hx : x ∈ centralizer ({d} : Set G)) {K : Subgroup G} (hK : K ∈ thetaComponentsAt p d) :
    K.map (MulAut.conj x).toMonoidHom ∈ thetaComponentsAt p d := by
  set H := centralizer ({d} : Set G)
  obtain ⟨K', hK', rfl⟩ := hK
  refine ⟨K'.map (MulAut.conj (⟨x, hx⟩ : H)).toMonoidHom,
    map_mulEquiv_mem_thetaComponents hp (MulAut.conj (⟨x, hx⟩ : H)) hK', ?_⟩
  show (K'.map (MulAut.conj (⟨x, hx⟩ : H)).toMonoidHom).map H.subtype =
    (K'.map H.subtype).map (MulAut.conj x).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_normalizer_of_perfect_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A K' V : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hK' : K' ∈ thetaComponentFamily p A) (hV : V ≠ ⊥) (hVp : Group.IsPerfect V) (hVK : V ≤ K')
    (hAV : A ≤ normalizer (V : Set G)) : A ≤ normalizer (K' : Set G) := by
  intro b hb
  obtain ⟨c, hcA, -, hK'c⟩ := mem_thetaComponentFamily_iff.mp hK'
  have hbc : b ∈ centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc b hb c hcA)
  have hK'' := conj_mem_thetaComponentsAt_cent hp hbc hK'c
  have hVK'' : V ≤ K'.map (MulAut.conj b).toMonoidHom := by
    intro v hv
    have hv' : b⁻¹ * v * b ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hAV (A.inv_mem hb)) v).mp hv
      simpa using this
    exact ⟨b⁻¹ * v * b, hVK hv', by simp [MulAut.conj_apply, mul_assoc]⟩
  have heq : K' = K'.map (MulAut.conj b).toMonoidHom :=
    EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp hK'c hK'' hV hVp hVK hVK''
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : b * h * b⁻¹ ∈ K'.map (MulAut.conj b).toMonoidHom := ⟨h, hh, by simp [MulAut.conj_apply]⟩
    rwa [← heq] at this
  · intro hh
    rw [heq] at hh
    obtain ⟨h', hh', hh'e⟩ := hh
    have : h' = h := by simpa [MulAut.conj_apply] using hh'e
    rwa [this] at hh'

end CFSG.RankThree.PartOne.F106
