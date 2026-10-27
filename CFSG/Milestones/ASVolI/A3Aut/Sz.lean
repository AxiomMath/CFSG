module

public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SteinbergBR
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki


section SzFamily

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem burnsideAut_map_szFieldAut_U
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : RingAut K) :
    (suzukiU a K).map (szFieldAut a K σ).toMonoidHom = suzukiU a K := by
  have hle : ∀ τ : RingAut K, (suzukiU a K).map (szFieldAut a K τ).toMonoidHom ≤ suzukiU a K := by
    intro τ
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    change szFieldAut a K τ (suzukiSElt a K u v) ∈ suzukiU a K
    rw [szFieldAut_S]
    exact suzukiSElt_mem_suzukiU a K _ _
  refine Subgroup.eq_of_le_of_card_ge (hle σ) ?_
  rw [Subgroup.card_map_of_injective (szFieldAut a K σ).injective]

theorem burnsideAut_suzukiU_isSylowTwoOf
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (suzukiU a K) ⊤ := by
  refine ⟨le_top, isPGroup_suzukiU hK, ?_⟩
  have h1 : ((suzukiU a K).subgroupOf ⊤).index = (suzukiU a K).index :=
    Subgroup.relIndex_top_right _
  rw [h1]
  exact not_two_dvd_index_suzukiU hK

theorem burnsideAut_isSz_suzukiGroup (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Quasithin.IsSz (2 * a + 1) ↥(suzukiGroup a K) :=
  ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩

theorem burnsideAut_sz_solvBorel (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    burnsideAut_SolvBorel ↥(suzukiGroup a K) (suzukiU a K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(suzukiGroup a K) := CFSG.LieType.Simplicity.finite_suzukiGroup a K
  have hB := CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz (burnsideAut_isSz_suzukiGroup ha hK)
  haveI hs : IsSimpleGroup ↥(suzukiGroup a K) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  haveI : Group.IsPerfect ↥(suzukiGroup a K) := (suzuki_perfect ha hK).2
  let Q : Sylow 2 ↥(suzukiGroup a K) :=
    (isPGroup_suzukiU hK).toSylow (not_two_dvd_index_suzukiU hK)
  intro Y hUY hY
  have hQ : (Q : Subgroup _) = suzukiU a K := rfl
  have h1 := CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB Q (hQ ▸ hUY)
    (burnsideAut_ne_top_of_isSolvable hY)
  rwa [hQ] at h1

theorem burnsideAut_sz_aut_mem (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (α : MulAut ↥(suzukiGroup a K)) :
    α ∈ (MulAut.conj : ↥(suzukiGroup a K) →* MulAut ↥(suzukiGroup a K)).range ⊔
      (szFieldAut a K).range := by
  obtain ⟨g, σ, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK α
  exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨σ, rfl⟩

theorem burnsideAut_a315_Sz {G : Type} [Group G]
    {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hL : CFSG.Quasithin.IsSz n ↥L) :
    ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl hL))))))
  obtain ⟨-, a, ha, K, _, _, hn, hK, ⟨e₀⟩⟩ := id hL
  subst hn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(suzukiGroup a K) := CFSG.LieType.Simplicity.finite_suzukiGroup a K
  have hUsyl := burnsideAut_suzukiU_isSylowTwoOf (a := a) (K := K) hK
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow e₀ (burnsideAut_isSylowTwoOf_subgroupOf h.sylow)
    hUsyl
  haveI : Group.IsPerfect ↥(suzukiGroup a K) := (suzuki_perfect ha hK).2
  have hB := CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz (burnsideAut_isSz_suzukiGroup ha hK)
  haveI hs : IsSimpleGroup ↥(suzukiGroup a K) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hMZ : Subgroup.center ↥(suzukiGroup a K) = ⊥ :=
    burnsideAut_center_eq_bot burnsideAut_nonabelian_of_perfect
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK)
  refine burnsideAut_case5_of_model2 h (2 * a + 1) (by omega) hLie hMZ e he hUsyl
    (IM := (MulAut.conj : ↥(suzukiGroup a K) →* MulAut ↥(suzukiGroup a K)).range)
    (ΦM := (szFieldAut a K).range) le_rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (burnsideAut_sz_solvBorel ha hK) ?_
  · exact burnsideAut_inn_relIndex_self _
  · exact burnsideAut_map_inn_le_innDiag e
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  · haveI := burnsideAut_inn_normal' ↥(suzukiGroup a K)
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rw [eq_bot_iff]
    rintro φ ⟨hφI, hφΦ⟩
    exact (CFSG.RankThree.PartTwo.KFacts.stdPinnedSz_separated ha hK).field_inter φ hφΦ hφI
  · rintro _ ⟨σ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (burnsideAut_map_szFieldAut_U hK σ)
  · intro b _
    exact burnsideAut_sz_aut_mem ha hK _
  · intro ε hε F hF _ _
    obtain ⟨hcyc, hdvd, σ, -, hpin⟩ := burnsideAut_pinned_of_field (szFieldAut a K)
      szFieldAut_injective hcard.2 (MulEquiv.refl _) hUsyl (burnsideAut_map_szFieldAut_U hK)
      (fun σ mg => ∀ g : ↥(suzukiGroup a K), ∃ g' : ↥(suzukiGroup a K),
        (g' : GL (Fin 4) K) = ChA.glMapAut σ (g : GL (Fin 4) K) ∧ mg g = g')
      (fun σ g => ⟨szFieldAut a K σ g, Units.ext (coe_szFieldAut σ g), rfl⟩) ε hε F hF
    refine ⟨hcyc, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, K, inferInstance, inferInstance, ε.trans (MulEquiv.refl _), σ, rfl, hK, hpin⟩))))⟩
    rwa [hcard.1] at hdvd

end SzFamily

end CFSG.ASVolI
