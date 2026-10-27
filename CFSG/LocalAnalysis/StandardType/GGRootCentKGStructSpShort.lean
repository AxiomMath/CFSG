module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutUCenter
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSummand
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAlt
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Perfect
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PerfectEight
import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple

public section

namespace CFSG.StandardType.KGSp

open Subgroup CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.SeitzReduction.SymplecticPilot
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement Pointwise

theorem exists_kgPieces_twoCentralElt {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ}
    (hF : Nat.card F = 2 ^ f) (hm : 1 ≤ m) {G : Type} [Group G] [Finite G]
    (ψ : StatedSp (m + 3) F →* G) (hψ : Function.Injective ψ) {E : Subgroup G}
    (hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (twoCentralElt (m + 3) 1 2 (0 : F) 1)}) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G,
        P ≤ ψ.range ⊓ Subgroup.centralizer {ψ (twoCentralElt (m + 3) 1 2 (0 : F) 1)} →
        ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece
        (ψ.range ⊓ Subgroup.centralizer {ψ (twoCentralElt (m + 3) 1 2 (0 : F) 1)}) E J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x₀ : StatedSp (m + 3) F := twoCentralElt (m + 3) 1 2 (0 : F) 1 with hx₀
  set C₀ : Subgroup G := ψ.range ⊓ Subgroup.centralizer {ψ x₀} with hC₀def
  set QW : Subgroup (StatedSp (m + 3) F) := wRadical F (1 : Fin (m + 3)) 2
  set S : Subgroup (StatedSp (m + 3) F) :=
    (shortBlock F (one_ne_two_fin (n := m))).range
  set T : Subgroup (StatedSp (m + 3) F) := spCompl12 F m
  set Q : Subgroup G := QW.map ψ with hQdef
  set S' : Subgroup G := S.map ψ with hS'def
  set T' : Subgroup G := T.map ψ with hT'def
  obtain ⟨hC, hSQ, hTQ, hST⟩ := RCSTSp.centralizer_a2_facts (F := F) (n := m)
  have hC₀ : C₀ = Q ⊔ (S' ⊔ T') := by
    rw [hC₀def, RCSTSp.range_inf_centralizer_of_injective hψ x₀, hx₀, hC,
      Subgroup.map_sup, Subgroup.map_sup, hQdef, hS'def, hT'def]
  have hpQ : pCoreOf 2 C₀ = Q := by
    rw [hC₀def, pCoreOf_range_inf_centralizer hψ x₀, hx₀,
      pCoreOf_centralizer_twoCentralElt (F := F) (m := m) hm, hQdef]
  have hdQST : Disjoint QW (S ⊔ T) := RCSTSp2.disjoint_wRadical_levi (F := F) (n := m)
  have hdQS : Q ⊓ S' = ⊥ := by
    have hbot : QW ⊓ S = ⊥ := disjoint_iff.mp (hdQST.mono_right le_sup_left)
    rw [hQdef, hS'def, ← Subgroup.map_inf QW S ψ hψ, hbot, Subgroup.map_bot]
  have hdQT : Q ⊓ T' = ⊥ := by
    have hbot : QW ⊓ T = ⊥ := disjoint_iff.mp (hdQST.mono_right le_sup_right)
    rw [hQdef, hT'def, ← Subgroup.map_inf QW T ψ hψ, hbot, Subgroup.map_bot]
  have hS'Q : S' ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hS'def, hQdef]
    exact ggRCST_map_le_normalizer ψ hSQ
  have hT'Q : T' ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hT'def, hQdef]
    exact ggRCST_map_le_normalizer ψ hTQ
  have hS'T' : S' ≤ Subgroup.centralizer (T' : Set G) := by
    rw [hS'def, hT'def]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp (hST hs) t ht
    rw [← map_mul, ← map_mul, h]
  have hT'S' : T' ≤ Subgroup.centralizer (S' : Set G) :=
    Subgroup.le_centralizer_iff.mp hS'T'
  rcases LayerCores.card_eq_two_or_four_le (D := F) with hcard | hcard
  ·
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    ·
      obtain rfl : m = 1 := by omega
      have hpcore : CFSG.Quasithin.perfectCore C₀ = Q ⊔ ⁅T', T'⁆ := by
        rw [hC₀def, RCSTSp.range_inf_centralizer_of_injective hψ x₀, hx₀,
          ← CFSG.Quasithin.map_perfectCore,
          perfectCore_centralizer_twoCentralElt_one_two hcard (Or.inl rfl),
          Subgroup.map_sup, ← Subgroup.map_commutator, hQdef]
      have hperf : ⁅Q ⊔ ⁅T', T'⁆, Q ⊔ ⁅T', T'⁆⁆ = Q ⊔ ⁅T', T'⁆ := by
        rw [hQdef, hT'def, ← Subgroup.map_commutator, ← Subgroup.map_sup,
          ← Subgroup.map_commutator,
          commutator_wRadical_sup_commutator_spCompl12_of_perfect (K := F) (n := 1) le_rfl
            (commutator_commutator_spCompl12_one hcard)]
      have hNL : T' ≤ Subgroup.normalizer ((⁅T', T'⁆ : Subgroup G) : Set G) := by
        have h := CFSG.commutator_normal_in_sup T' T'
        rw [sup_idem] at h
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.commutator_le_self T')).mp h
      have hC₀' : C₀ = Q ⊔ (T' ⊔ S') := by
        rw [hC₀, sup_comm (S') (T')]
      have eT : ↥T' ≃* ↥(StatedSp 2 F) :=
        (T.equivMapOfInjective ψ hψ).symm.trans (spCompl12Equiv F 1).symm
      obtain ⟨hLq, hLm⟩ :=
        isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two hcard eT
      have hJ : GGRCSKGPiece C₀ E (Q ⊔ ⁅T', T'⁆) :=
        ggRCSKGPiece_of_summand_normal hC₀' hpQ (Subgroup.commutator_le_self T') hNL hT'Q hS'Q
          hT'S' hdQT hperf hLq hLm hE
      refine ⟨{Q ⊔ ⁅T', T'⁆}, ?_, ?_⟩
      · intro P hP hPperf
        have h1 : P ≤ CFSG.Quasithin.perfectCore C₀ :=
          CFSG.Quasithin.le_perfectCore_of_perfect hP hPperf
        rw [hpcore] at h1
        simpa using h1
      · intro J hJmem
        rw [Set.mem_singleton_iff] at hJmem
        subst hJmem
        exact hJ
    ·
      have hpcore : CFSG.Quasithin.perfectCore C₀ = Q ⊔ T' := by
        rw [hC₀def, RCSTSp.range_inf_centralizer_of_injective hψ x₀, hx₀,
          ← CFSG.Quasithin.map_perfectCore,
          perfectCore_centralizer_twoCentralElt_two hcard hm2 (Or.inl rfl),
          Subgroup.map_sup, hQdef, hT'def]
      have hperf : ⁅Q ⊔ T', Q ⊔ T'⁆ = Q ⊔ T' := by
        rw [hQdef, hT'def, ← Subgroup.map_sup, ← Subgroup.map_commutator,
          commutator_wRadical_sup_spCompl12_two (K := F) (n := m) hcard hm2,
          Subgroup.map_sup]
      have hmf : (m + 1, 2 ^ f) ≠ (2, 2) := by
        rintro h
        have h1 : m + 1 = 2 := congrArg Prod.fst h
        omega
      have eT : ↥T' ≃* ↥(StatedSp (m + 1) F) :=
        (T.equivMapOfInjective ψ hψ).symm.trans (spCompl12Equiv F m).symm
      obtain ⟨hLq, hLm⟩ :=
        isQuasisimple_largeEvenMarking_of_equiv_statedSp hF (by omega : 2 ≤ m + 1) hmf eT
      have hC₀' : C₀ = Q ⊔ (T' ⊔ S') := by
        rw [hC₀, sup_comm (S') (T')]
      have hJ : GGRCSKGPiece C₀ E (Q ⊔ T') :=
        ggRCSKGPiece_of_summand hC₀' hpQ hT'Q hS'Q hT'S' hdQT hperf hLq hLm hE
      refine ⟨{Q ⊔ T'}, ?_, ?_⟩
      · intro P hP hPperf
        have h1 : P ≤ CFSG.Quasithin.perfectCore C₀ :=
          CFSG.Quasithin.le_perfectCore_of_perfect hP hPperf
        rw [hpcore] at h1
        simpa using h1
      · intro J hJmem
        rw [Set.mem_singleton_iff] at hJmem
        subst hJmem
        exact hJ
  ·
    have hf2 : 2 ≤ f := by
      rcases Nat.lt_or_ge f 2 with hlt | hge
      · interval_cases f
        · rw [pow_zero] at hF
          omega
        · rw [pow_one] at hF
          omega
      · exact hge
    have hJ1 : GGRCSKGPiece C₀ E (Q ⊔ S') := by
      have hperf : ⁅Q ⊔ S', Q ⊔ S'⁆ = Q ⊔ S' := by
        rw [hQdef, hS'def, ← Subgroup.map_sup, ← Subgroup.map_commutator,
          commutator_wRadical_sup_shortBlock (F := F) (m := m) hcard, Subgroup.map_sup]
      have eS : ↥S' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (S.equivMapOfInjective ψ hψ).symm.trans
          (MonoidHom.ofInjective (shortBlock_injective (one_ne_two_fin (n := m)))).symm
      obtain ⟨hLq, hLm⟩ := isQuasisimple_largeEvenMarking_of_equiv_SL2 hF hf2 eS
      exact ggRCSKGPiece_of_summand hC₀ hpQ hS'Q hT'Q hS'T' hdQS hperf hLq hLm hE
    have hJ2 : GGRCSKGPiece C₀ E (Q ⊔ T') := by
      have hperf : ⁅Q ⊔ T', Q ⊔ T'⁆ = Q ⊔ T' := by
        rw [hQdef, hT'def, ← Subgroup.map_sup, ← Subgroup.map_commutator,
          commutator_wRadical_sup_spCompl12 (K := F) (n := m) hcard, Subgroup.map_sup]
      have hmf : (m + 1, 2 ^ f) ≠ (2, 2) := by
        rintro h
        have h2f : 2 ^ f ≠ 2 := by
          intro h2
          rw [hF, h2] at hcard
          norm_num at hcard
        exact h2f (congrArg Prod.snd h)
      have eT : ↥T' ≃* ↥(StatedSp (m + 1) F) :=
        (T.equivMapOfInjective ψ hψ).symm.trans (spCompl12Equiv F m).symm
      obtain ⟨hLq, hLm⟩ :=
        isQuasisimple_largeEvenMarking_of_equiv_statedSp hF (by omega : 2 ≤ m + 1) hmf eT
      have hC₀' : C₀ = Q ⊔ (T' ⊔ S') := by
        rw [hC₀, sup_comm (S') (T')]
      exact ggRCSKGPiece_of_summand hC₀' hpQ hT'Q hS'Q hT'S' hdQT hperf hLq hLm hE
    refine ⟨{Q ⊔ S', Q ⊔ T'}, ?_, ?_⟩
    · intro P hP hPperf
      have hle : P ≤ C₀ := hP
      rw [hC₀] at hle
      refine hle.trans ?_
      rw [sSup_pair]
      exact sup_le (le_sup_left.trans le_sup_left)
        (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
    · intro J hJmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hJmem
      rcases hJmem with rfl | rfl
      · exact hJ1
      · exact hJ2

end CFSG.StandardType.KGSp
