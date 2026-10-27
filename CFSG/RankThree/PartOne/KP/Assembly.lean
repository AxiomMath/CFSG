module

public import CFSG.RankThree.PartOne.KP.Basic
public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree.LocalRank
open CFSG.Blueprint (Catalog)
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def CatalogCoprimeAutomorphismRankOneOrJ4BM : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Catalog T → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card T →
      Nonempty (T ≃* Carrier .J4) ∨ Nonempty (T ≃* Carrier .B) ∨ Nonempty (T ≃* Carrier .M) ∨
        ElementaryRankAtMostOne p (MulAut T)

@[expose] def J4CoprimeNormalizedComponentCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ¬ p ∣ Nat.card (L ⧸ Subgroup.center L) →
    Nonempty ((L ⧸ Subgroup.center L) ≃* Carrier .J4) →
    E ≤ Subgroup.normalizer (L : Set G) →
    ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ ≤
      Subgroup.normalizer (L : Set G) →
    E ≤ Subgroup.centralizer (L : Set G) ∧ ComponentLocalCoreCentralizes p E t L

theorem original_coprime_catalog_component_local_core_centralization_of_inputs
    (hrank : CatalogCoprimeAutomorphismRankOneOrJ4BM)
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour)
    (hJ4 : J4CoprimeNormalizedComponentCentralization) :
    OriginalCoprimeCatalogComponentLocalCoreCentralization := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL hcat hpT hEL hXL
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have hnab := hL.1.2.2
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  rcases hrank (L ⧸ Subgroup.center L) hnab hcat p hp hp5 hpT with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | hrk
  · obtain ⟨hEC, hD⟩ := hJ4 (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL hpT ⟨e⟩ hEL hXL
    refine ⟨?_, hD⟩
    rw [inf_eq_left.mpr hEC, hEc]
    exact Nat.le_self_pow (by norm_num) p
  · exfalso
    obtain ⟨H, K, hK, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup N L
    have h4 := hB X H K ⟨φ.trans e⟩
    omega
  · exfalso
    obtain ⟨H, K, hK, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup N L
    have h4 := hM X H K (L ⧸ Subgroup.center L) hnab ⟨φ⟩ ⟨e⟩
    omega
  · exact component_local_core_centralizes_of_rank_le_one hp (by omega) hE hEc ht ht1 hL hEL hXL
      hrk

end CFSG.RankThree.PartOne
