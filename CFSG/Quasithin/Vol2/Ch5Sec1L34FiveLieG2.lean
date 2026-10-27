module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieGen
public import CFSG.Quasithin.H13.NQCatBNG2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace CFSG.Quasithin.H13.FiveNorm.LieG2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.QuasithinUnique

variable {K : Type} [Field K]

theorem powOver_g2
    [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) :
    PowOver (adjointGroup .G2 K) (posUnipotent (g2Datum K)) (Nat.card K - 1) := by
  intro H hUH hH x hx
  have hB := NQCat.BN.le_borel_of_isSolvable (g2_isCTGroupDatum K) (g2_steinbergExtras K)
    (NQCat.BN.rankOne_not_solvable_g2 hK4) hUH hH hx
  have hB' := NQCat.BN.borel_adjDatum_le .G2 hB
  rw [NQCat.BN.posUnipotent_adjDatum]
  exact pow_mem_of_mem_sup RootGroupData.H_le_normalizer_U
    (fun t ht => (nativeRootSubgroups .G2 K).pow_card_sub_one_eq_one ht) hB'

theorem fiveRigid_g2
    [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) : FiveRigid (adjointGroup .G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form le_rfl K
      hK
  have hinn : FiveInner (adjointGroup .G2 K) := by
    refine fiveInner_of_hom Θ (fun α hα => ?_) (fun σ hσ => ?_)
    · have hmem : α ∈ Θ.ker := hα
      rw [hker] at hmem
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, hx.symm⟩
    · have h2 := ringEquiv_pow_eq_one (by norm_num) hK σ
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 5)
        (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hσ))
  have hK4 := NQCat.exists_finset_card_four_of_card (k := 2) le_rfl hK
  obtain ⟨Q, hQ⟩ := NQCat.BN.exists_sylow_posUnipotent_g2 hK4
  have hU : IsSylowTwoOf (posUnipotent (g2Datum K)) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  exact ⟨center_adjointGroup_eq_bot, hinn,
    noFiveOver_of_powOver hU (by rw [hK]; norm_num) (powOver_g2 hK4)⟩

theorem fiveRigid_quot_of_isG2
    {X : Type} [Group X]
    (hX : CFSG.Quasithin.IsG2 2 2 X) : FiveRigid (X ⧸ Subgroup.center X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  have hP := fiveRigid_g2 hK
  let ψ : X ≃* adjointGroup .G2 K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot)
  obtain ⟨-, ⟨e'⟩⟩ := nonempty_quotCenter_equiv ψ hP.1
  exact fiveRigid_of_mulEquiv e'.symm hP

end CFSG.Quasithin.H13.FiveNorm.LieG2
