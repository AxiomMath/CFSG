module

public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.GH74.GLS.Balance.Bender.Ambient
import CFSG.GH74.GLS.Balance.Bender.T59
import CFSG.GroupTheory.CardSupInf
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GH74.GLS.Balance.Bender.AuxSylow
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial

theorem ggF4TWP_false_of_component {G : Type} [Group G] [Finite G] {J C : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J C) (hZ : Subgroup.center J = ⊥)
    (h13 : 13 ∣ Nat.card J) (h17J : ¬ 17 ∣ Nat.card J) (h169 : ¬ 13 ^ 2 ∣ Nat.card C)
    (hN : ∀ P : Subgroup G, P ≤ J → Nat.card P = 13 → ∀ u ∈ C,
      u ∈ Subgroup.normalizer (P : Set G) → u ^ 17 = 1 → u = 1)
    {u : G} (hu : u ∈ C) (hu17 : u ^ 17 = 1) (hu1 : u ≠ 1) : False := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hCnorm : C ≤ Subgroup.normalizer (J : Set G) := by
    intro c hc
    by_contra hcN
    have hconj_ne : conjSub c J ≠ J := fun h =>
      hcN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hJc : CFSG.Assembly.IsComponentOf (conjSub c J) C := by
      have h := isComponentOf_map_conj hJ c
      rw [show C.map (MulAut.conj c).toMonoidHom = C from
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hc)] at h
      simpa [conjSub] using h
    have hcomm : ⁅J, conjSub c J⁆ = ⊥ :=
      (isComponentOf_eq_or_commute hJ hJc).resolve_left fun h => hconj_ne h.symm
    have hcent : J ≤ Subgroup.centralizer (conjSub c J : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
    have hdisj : J ⊓ conjSub c J = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxJ, hxK⟩ := Subgroup.mem_inf.mp hx
      have hxcenter : (⟨x, hxJ⟩ : J) ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hcent y.2) x hxK).symm
      rw [hZ] at hxcenter
      simpa using congrArg Subtype.val hxcenter
    have hcardK : Nat.card (conjSub c J) = Nat.card J :=
      Subgroup.card_map_of_injective (K := J) (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective
    have hnormK : J ≤ Subgroup.normalizer (conjSub c J : Set G) :=
      hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hdisjK : Disjoint (conjSub c J) J := by
      rw [disjoint_iff, inf_comm]
      exact hdisj
    have hcard_sup : Nat.card (J ⊔ conjSub c J : Subgroup G) = Nat.card J * Nat.card J := by
      rw [sup_comm]
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (conjSub c J) J
        hnormK hdisjK, hcardK]
    have hdvd : 13 ^ 2 ∣ Nat.card C := by
      have hdvdJ : 13 ^ 2 ∣ Nat.card J * Nat.card J := by
        obtain ⟨k, hk⟩ := h13
        exact ⟨k * k, by rw [hk]; ring⟩
      have hdvd_sup : 13 ^ 2 ∣ Nat.card (J ⊔ conjSub c J : Subgroup G) := by
        rw [hcard_sup]
        exact hdvdJ
      exact dvd_trans hdvd_sup (Subgroup.card_dvd_of_le (sup_le hJ.1 hJc.1))
    exact h169 hdvd
  have hJnormal : (J.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.1).mpr hCnorm
  have hcardJ_dvd_C : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_le hJ.1
  have h169J : ¬ 13 ^ 2 ∣ Nat.card J := fun h => h169 (h.trans hcardJ_dvd_C)
  have hcardJ_ne0 : Nat.card J ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, J.one_mem⟩, inferInstance⟩
  have hfac : Nat.factorization (Nat.card J) 13 = 1 := by
    have hge : 1 ≤ Nat.factorization (Nat.card J) 13 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 13)
        hcardJ_ne0).mp (by simpa using h13)
    have hlt : Nat.factorization (Nat.card J) 13 < 2 := by
      by_contra h2
      exact h169J ((Nat.Prime.pow_dvd_iff_le_factorization
        (by norm_num : Nat.Prime 13) hcardJ_ne0).mpr (le_of_not_gt h2))
    omega
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 13 J))
  let P : Subgroup G := (S : Subgroup J).map J.subtype
  have hPJ : P ≤ J := Subgroup.map_subtype_le _
  have hPsyl : CFSG.GH74.GLS.Balance.IsSylowIn 13 P J :=
    CFSG.GH74.GLS.Balance.isSylowIn_of_sylow 13 S
  have hScard : Nat.card S = 13 := by
    rw [Sylow.card_eq_multiplicity S, hfac]
    norm_num
  have hPcard : Nat.card P = 13 := by
    show Nat.card ((S : Subgroup J).map J.subtype) = 13
    rw [Subgroup.card_map_of_injective (K := (S : Subgroup J)) (f := J.subtype)
      J.subtype_injective]
    exact hScard
  set N : Subgroup G := C ⊓ Subgroup.normalizer (P : Set G) with hNdef
  have hNleC : N ≤ C := inf_le_left
  have hfrattini : C ≤ J ⊔ N := by
    have h := CFSG.GH74.GLS.Balance.t59_frattini (X := C) (N := J) (P := P)
      hJ.1 hJnormal hPsyl
    simpa [N, hNdef] using h
  have hsup : J ⊔ N = C := le_antisymm (sup_le hJ.1 hNleC) hfrattini
  have huord : orderOf u = 17 := orderOf_eq_prime hu17 hu1
  have h17C : 17 ∣ Nat.card C := by
    have h := orderOf_dvd_natCard (⟨u, hu⟩ : C)
    rwa [Subgroup.orderOf_mk, huord] at h
  have hNnorm : N ≤ Subgroup.normalizer (J : Set G) := hNleC.trans hCnorm
  have hcard_eq : Nat.card C * Nat.card (N ⊓ J : Subgroup G) = Nat.card N * Nat.card J := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := N) (K := J) hNnorm
    rw [sup_comm N J, hsup] at h
    exact h
  have h17N : 17 ∣ Nat.card N := by
    have hdvd : 17 ∣ Nat.card N * Nat.card J := by
      have h : 17 ∣ Nat.card C * Nat.card (N ⊓ J : Subgroup G) :=
        dvd_mul_of_dvd_left h17C _
      rwa [hcard_eq] at h
    exact ((by norm_num : Nat.Prime 17).dvd_mul.mp hdvd).resolve_right h17J
  obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card' (G := N) 17 h17N
  have hvC : (v : G) ∈ C := hNleC v.2
  have hvP : (v : G) ∈ Subgroup.normalizer (P : Set G) :=
    (inf_le_right : N ≤ Subgroup.normalizer (P : Set G)) v.2
  have hv17 : (v : G) ^ 17 = 1 := by
    have h : (v : N) ^ 17 = 1 := by
      rw [← hvord]
      exact pow_orderOf_eq_one v
    simpa using congrArg Subtype.val h
  have hv1 : (v : G) = 1 := hN P hPJ hPcard (v : G) hvC hvP hv17
  have hv_eq_one : v = 1 := Subtype.ext (by simpa using hv1)
  have hcontr : orderOf v = 1 := by
    rw [hv_eq_one]
    simp
  omega

end CFSG.StandardType
