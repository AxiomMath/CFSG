module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2b
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL3e
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2S5

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem exists_mem_calP_commutator_ne_bot (hH : hP ρ = ⊤) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) : ∃ A ∈ calP ρ, ⁅L, A⁆ ≠ ⊥ := by
  by_contra hne
  have hle : hP ρ ≤ Subgroup.centralizer (L : Set G) := iSup₂_le fun A hA => by
    have h : ⁅L, A⁆ = ⊥ := Classical.byContradiction fun h => hne ⟨A, hA, h⟩
    rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  rw [hH] at hle
  have hc : Subgroup.center ↥L = ⊤ := by
    refine eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_
    exact (Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top (y : G))) x x.2).symm
  obtain ⟨a, b, hab⟩ := hL.2.2.2.exists_pair_ne
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (QuotientGroup.eq.2 (by rw [hc]; exact Subgroup.mem_top _))


theorem component_dichotomy [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hH : hP ρ = ⊤) {L : Subgroup G} (hL : IsComponentOf L ⊤)
    (hshape : (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨
      (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2)))) :
    ((∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u) ∧
        Shape148 ρ L (commOn ρ L ⊤) (fixSub ρ L)) ∨
      (commOn ρ L ⊤ ⊓ fixSub ρ L = ⊥ ∧ ∃ a : G, a * a = 1 ∧
        a ∈ Subgroup.normalizer (L : Set G) ∧ a ∉ L ∧
        SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥) := by
  obtain ⟨A, hA, hLA⟩ := exists_mem_calP_commutator_ne_bot hH hL
  have hmem : ∀ g : G, g ∈ hP ρ := fun g => by rw [hH]; exact Subgroup.mem_top g
  rcases hshape with ⟨n, hn, hX⟩ | ⟨hX, -⟩
  · haveI : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
    obtain ⟨B, hinv, hBA, -, -, -, -, hT, F, _, _, _, _, hF, α, hout⟩ :=
      exists_componentOffenderOutput hρ hL hn hX hA hLA
    rcases dichotomy_of_componentOffenderOutput hρ hL hX hA hLA hBA hinv hT hF hout with
      ⟨hnat, -⟩ | ⟨-, hZ, a, haB, haL, hS5, -⟩
    · obtain ⟨hUL, hnt⟩ := commOn_facts_of_mem_calP hρ hL hA hLA
      have hin := exists_eq_apply_of_natL2_of_mem_hP hρ hL hUL hnt (by omega) hnat
      exact Or.inl ⟨fun g => hin g (hmem g), Or.inl ⟨n, by omega, hnat⟩⟩
    · have ha2 : a * a = 1 := by
        rw [← pow_two]
        exact ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1
          (isElementaryAbelian_of_mem_calP hA)).2 a (hBA haB)
      exact Or.inr ⟨hZ, a, ha2, le_normalizer_of_mem_calP hρ hL hA (hBA haB), haL, hS5⟩
  · obtain ⟨-, -, hsh, hin⟩ := l3_component_identification hρ hL hX hA hLA
    refine Or.inl ⟨fun g => hin g (hmem g), ?_⟩
    rcases hsh with h3 | ⟨hZ, hsum⟩
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl (by rw [hZ]; exact hsum)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
