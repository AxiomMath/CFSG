module

public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec19.Item1912
public import CFSG.RankThree.PartTwo.Sec19.Step1913Omega
public import CFSG.RankThree.PartTwo.Sec17.Item1730Split
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

variable {G : Type} [Group G] [Finite G]

theorem rank3II_19_13_of_hj' (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h135 : Item135Simple) (h1730 : Sec17.Item1730HJ) (hmult : KFacts.KS18Mult)
    (hΩ : Step1913Omega) : Step1913 := by
  intro G _ _ A c L E M hctx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hiso : aschbacherSolvableCore 3 L = CFSG.pCore 2 L →
      (L ⧸ CFSG.pCore 2 L ≃* L ⧸ aschbacherSolvableCore 3 L) :=
    fun h => QuotientGroup.quotientMulEquivOfEq h.symm
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
  have hexcl : (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22)) →
      False := by
    intro hS
    set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
    have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
    have hE := isE27_of_mem_partTwoE hctx.mem_partTwoT.1
    have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
    have hAH : A ≤ H := (le_centralizer_of_mem hA.1.1 hcA).trans
      (centralizer_le_normalizer_zpowers c)
    have hEH : E ≤ H := hctx.le_centralizer.trans (centralizer_le_normalizer_zpowers c)
    obtain ⟨Q, hAQ⟩ := (hA.isPGroup.comap_subtype (K := H)).exists_le_sylow
    have hP : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup H).map H.subtype) H := ⟨Q, rfl⟩
    have hAP : A ≤ (Q : Subgroup H).map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hAH]
      exact Subgroup.map_mono hAQ
    have hΩP := hΩ G A c L hD hctx.hypS hctx.chosen136 hS _ hP hAP
    obtain ⟨g, hg⟩ := exists_map_conj_le_sylow (hE.isPGroup.comap_subtype (K := H)) Q
    have hEg : E.map (MulAut.conj (g : G)).toMonoidHom ≤ (Q : Subgroup H).map H.subtype := by
      rw [← map_subtype_map_conj_subgroupOf hEH g]
      exact Subgroup.map_mono hg
    have hEA : E.map (MulAut.conj (g : G)).toMonoidHom ≤ A := by
      rw [← hΩP]
      rintro x hx
      refine Subgroup.subset_closure ⟨hEg hx, ?_⟩
      obtain ⟨e, he, rfl⟩ := hx
      change ((g : G) * e * (g : G)⁻¹) ^ 3 = 1
      rw [conj_pow, hE.1.2 e he, mul_one, mul_inv_cancel]
    have hEeq : E.map (MulAut.conj (g : G)).toMonoidHom = A :=
      Subgroup.eq_of_le_of_card_ge hEA
        (by rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hE.2, hA.2])
    exact hctx.not_mem_partTwoT
      (hEeq ▸ (map_mem_partTwoT_iff (MulAut.conj (g : G))).mpr hctx.mem_partTwoT)
  rcases cases131 h131 ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ hSLC hD with
    ⟨-, -, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · rcases hcase with ⟨hL3, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact Or.inl (isLThreePi_of_mulEquiv (hiso (theta_eq_pCore_two_of_mult hmult
        (h135 G A c L hD (Or.inl hL3)) (Or.inl hL3))) hL3)
    · exact absurd (Or.inl ⟨φ⟩) (fun h => hexcl h)
    · exact absurd (Or.inr ⟨φ⟩) (fun h => hexcl h)
  · rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact Or.inr ⟨(hiso (theta_eq_pCore_two_of_mult hmult
        (h135 G A c L hD (Or.inr (Or.inl ⟨ψ⟩))) (Or.inr (Or.inl ⟨ψ⟩)))).trans ψ⟩
    · exfalso
      obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      have hθ := theta_eq_pCore_two_of_mult hmult (h135 G A c L hD (Or.inr (Or.inr ⟨ψ⟩)))
        (Or.inr (Or.inr (Or.inl ⟨ψ⟩)))
      exact (h1730 G hst hctx.partTwoS_eq A hctx.mem_partTwoE hctx.not_mem_partTwoT c
        hctx.zpowers_mem_omegaA L hctx.mem_lA).false ((hiso hθ).trans ψ)
  · obtain ⟨hL3, -, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
    exact Or.inl (isLThreePi_of_mulEquiv (hiso (theta_eq_pCore_two_of_mult hmult
      (h135 G A c L hD (Or.inl hL3)) (Or.inl hL3))) hL3)
  · exact absurd hcL' hcL

theorem rank3II_19_13_of_kfacts_hj' (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (h135 : Item135Simple) (h1730 : Sec17.Item1730HJ)
    (hmult : KFacts.KS18Mult) (hA7 : KFacts.KS18A7M22) : Step1913 :=
  rank3II_19_13_of_hj' h131 hspor hSLC h135 h1730 hmult (rank3II_19_13_omega_of hA7)

end CFSG.RankThree.PartTwo.Sec19
