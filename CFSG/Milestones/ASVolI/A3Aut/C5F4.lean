module

public import CFSG.Milestones.ASVolI.A3Aut.C5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBF4
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LocalAnalysis.ComponentInitial

section C5F4


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideAut_c5F4_map_fieldAut_U (σ : K ≃+* K) :
    ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map
        (F4.reeGammaFieldAutHom K a σ).toMonoidHom =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := by
  have hle : ∀ τ : K ≃+* K, ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map
      (F4.reeGammaFieldAutHom K a τ).toMonoidHom ≤
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := by
    intro τ
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := hu
    show ((F4.reeGammaFieldAut K a τ u : F4.reeGamma K a) : ModGL F4.tag K) ∈
      F4.reeFixedPosUnipotent K a
    have h := map_reeFixedPosUnipotent_exactEntrywiseAut (t := F4) (K := K) (a := a) τ
    rw [coe_reeGammaFieldAut, ← h]
    exact ⟨(u : ModGL F4.tag K), hu', rfl⟩
  refine le_antisymm (hle σ) fun x hx => ?_
  refine ⟨F4.reeGammaFieldAutHom K a σ⁻¹ x, hle σ⁻¹ ⟨x, hx, rfl⟩, ?_⟩
  change (F4.reeGammaFieldAutHom K a σ * F4.reeGammaFieldAutHom K a σ⁻¹) x = x
  rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem burnsideAut_c5F4_fieldAut_injective (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (F4.reeGammaFieldAutHom K a) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine (CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK).2 σ ?_
  rw [← reeGammaFieldAutHom_apply, hσ]
  exact ⟨1, map_one _⟩

theorem burnsideAut_a315_2F4 {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hodd : Odd n) (h3 : 3 ≤ n)
    (hL : CFSG.Quasithin.Is2F4 n ↥L) : ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL))))))
  obtain ⟨-, a, hna, K, _, _, hK, ⟨e₀⟩⟩ := id hL
  subst hna
  have ha : 1 ≤ a := by omega
  haveI : CharP K 2 := burnsideA26_charP_two hK
  haveI : CharP K F4.prime := (inferInstance : CharP K 2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  set H : Subgroup (ModGL Tag.F4 K) :=
    reeFixedGroup Tag.F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)
    with hHdef
  have hH : F4.reeGamma K a = H := reeGamma_eq_reeFixedGroup (t := F4)
  have hperf : ⁅F4.reeGamma K a, F4.reeGamma K a⁆ = F4.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, (ree_generic_fixed_group_perfect F4 a ha K hK).2.1,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hHC : ⁅H, H⁆ = F4.reeGamma K a := by
    rw [← hH]
    exact hperf
  have hZ := large_Ree_fixed_group_center_trivial a K hK
  obtain ⟨κ, hκ⟩ : ∃ κ : DerivedCentralQuotient H ≃* ↥(F4.reeGamma K a),
      ∀ g : ↥⁅H, H⁆, ((κ (QuotientGroup.mk g)).1 : ModGL Tag.F4 K) = (g.1 : ModGL Tag.F4 K) :=
    ⟨burnsideA26_dcqEquiv H (F4.reeGamma K a) hHC hZ,
      burnsideA26_dcqEquiv_mk H (F4.reeGamma K a) hHC hZ⟩
  have hP : ∀ σ : RingAut K, ∀ g : ↥⁅H, H⁆, ∃ g' : ↥⁅H, H⁆,
      (g' : ModGL Tag.F4 K) = Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.F4 K) ∧
      MulAut.congr κ.symm (F4.reeGammaFieldAutHom K a σ) (QuotientGroup.mk g) =
        QuotientGroup.mk g' := by
    intro σ g
    obtain ⟨y, hy⟩ : ∃ y : ↥(F4.reeGamma K a),
        y = F4.reeGammaFieldAutHom K a σ (κ (QuotientGroup.mk g)) := ⟨_, rfl⟩
    have hmem : (y.1 : ModGL Tag.F4 K) ∈ ⁅H, H⁆ := by
      rw [hHC]
      exact y.2
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · show (y.1 : ModGL Tag.F4 K) = _
      rw [hy, reeGammaFieldAutHom_apply, coe_reeGammaFieldAut, hκ]
      rfl
    · rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
        ← hy]
      apply κ.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hκ]
  have hUsyl := burnsideAut_isSylowTwoOf_reeFixedPosUnipotent (K := K) a
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow (e₀.trans κ)
    (burnsideAut_isSylowTwoOf_subgroupOf h.sylow) hUsyl
  have hMZ := burnsideAut_c5_center_eq_bot h e
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  have hNF := CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK
  refine burnsideAut_case5_of_model2 h (2 * a + 1) (by omega) hLie hMZ e he hUsyl
    (IM := (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range)
    (ΦM := (F4.reeGammaFieldAutHom K a).range) le_rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (burnsideAut_solvBorel_largeRee ha hK) ?_
  · exact burnsideAut_inn_relIndex_self _
  · exact burnsideAut_map_inn_le_innDiag e
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  · haveI := burnsideAut_inn_normal' (F4.reeGamma K a)
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rw [eq_bot_iff]
    rintro _ ⟨hI, ⟨σ, rfl⟩⟩
    rw [hNF.2 σ hI, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨σ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (burnsideAut_c5F4_map_fieldAut_U σ)
  · intro b _
    obtain ⟨x, β, hxβ⟩ := hNF.1 (MulAut.congr e (MulAut.conjNormal b))
    rw [hxβ]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨β, rfl⟩
  · intro ε hε F hF _ _
    obtain ⟨hcyc, hdvd, σ, -, hpin⟩ := burnsideAut_pinned_of_field (F4.reeGammaFieldAutHom K a)
      (burnsideAut_c5F4_fieldAut_injective ha hK) hcard.2 κ.symm hUsyl
      burnsideAut_c5F4_map_fieldAut_U
      (fun σ mg => ∀ g : ↥⁅H, H⁆, ∃ g' : ↥⁅H, H⁆,
          (g' : ModGL Tag.F4 K) = Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.F4 K) ∧
          mg (QuotientGroup.mk g) = QuotientGroup.mk g')
      hP ε hε F hF
    refine ⟨hcyc, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨a, K, inferInstance, inferInstance, ε.trans κ.symm, σ, rfl, hK, hpin⟩))))))⟩
    rwa [hcard.1] at hdvd

end C5F4

end CFSG.ASVolI
