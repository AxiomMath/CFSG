module

public import CFSG.Milestones.ASVolI.A3Aut.C5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBG2
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (g2FieldHom coe_g2FieldHom g2_automorphism_normal_form)

section C5G2


variable {K : Type} [Field K]

theorem burnsideAut_c5G2_map_fieldAut_U (σ : K ≃+* K) :
    ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
        (g2FieldHom K σ).toMonoidHom =
      (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
  have hle : ∀ τ : K ≃+* K, ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      (g2FieldHom K τ).toMonoidHom ≤ (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    intro τ
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K := hu
    show ((g2FieldHom K τ u : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K
    rw [coe_g2FieldHom]
    have h := map_exactEntrywiseAut (τ := Tag.G2) τ (H := posUnipotent Tag.G2 K)
      (Or.inr (Or.inl rfl))
    rw [← h]
    exact ⟨(u : ModGL Tag.G2 K), hu', rfl⟩
  refine le_antisymm (hle σ) fun x hx => ?_
  refine ⟨g2FieldHom K σ⁻¹ x, hle σ⁻¹ ⟨x, hx, rfl⟩, ?_⟩
  change (g2FieldHom K σ * g2FieldHom K σ⁻¹) x = x
  rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem burnsideAut_c5G2_fieldAut_injective [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    Function.Injective (g2FieldHom K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  exact (g2_automorphism_normal_form hK3 hK4).2 σ (by rw [hσ]; exact ⟨1, map_one _⟩)

theorem burnsideAut_a315_G2 {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hn : 2 ≤ n)
    (hL : CFSG.Quasithin.IsG2 2 n ↥L) : ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hL
  haveI : CharP K 2 := burnsideA26_charP_two hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hZ := center_adjointGroup_eq_bot (τ := Tag.G2) (K := K)
  set κ : AdjointQuotient Tag.G2 K ≃* adjointGroup Tag.G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with hκdef
  have hκ : ∀ g : adjointGroup Tag.G2 K, κ.symm g = QuotientGroup.mk g := fun g => by
    apply κ.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hUsyl := burnsideAut_isSylowTwoOf_posUnipotent (τ := Tag.G2) (K := K)
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow (e₀.trans κ)
    (burnsideAut_isSylowTwoOf_subgroupOf h.sylow) hUsyl
  have hMZ := burnsideAut_c5_center_eq_bot h e
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  have hNF := g2_automorphism_normal_form hK3 hK4
  refine burnsideAut_case5_of_model2 h n hn hLie hMZ e he hUsyl
    (IM := (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range)
    (ΦM := (g2FieldHom K).range) le_rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (burnsideAut_solvBorel_chevalley hK4) ?_
  · exact burnsideAut_inn_relIndex_self _
  · exact burnsideAut_map_inn_le_innDiag e
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  · haveI := burnsideAut_inn_normal' (adjointGroup Tag.G2 K)
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rw [eq_bot_iff]
    rintro _ ⟨hI, ⟨σ, rfl⟩⟩
    rw [hNF.2 σ hI, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨σ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (burnsideAut_c5G2_map_fieldAut_U σ)
  · intro b _
    obtain ⟨g, σ, hgσ⟩ := hNF.1 (MulAut.congr e (MulAut.conjNormal b))
    rw [hgσ]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨σ, rfl⟩
  · intro ε hε F hF _ _
    obtain ⟨hcyc, hdvd, σ, -, hpin⟩ := burnsideAut_pinned_of_field (g2FieldHom K)
      (burnsideAut_c5G2_fieldAut_injective hK4) hcard.2 κ.symm hUsyl
      burnsideAut_c5G2_map_fieldAut_U
      (fun σ mg => ∀ g : ↥(adjointGroup Tag.G2 K), ∃ g' : ↥(adjointGroup Tag.G2 K),
          (g' : ModGL Tag.G2 K) = Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.G2 K) ∧
          mg (QuotientGroup.mk g) = QuotientGroup.mk g')
      (fun σ g => ⟨g2FieldHom K σ g, coe_g2FieldHom σ g, by
        have h1 : κ (QuotientGroup.mk g) = g := by
          rw [← hκ g]
          exact κ.apply_symm_apply g
        rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
          h1, hκ]⟩) ε hε F hF
    refine ⟨hcyc, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨K, inferInstance, inferInstance, ε.trans κ.symm, σ, hK, hpin⟩)))))⟩
    rwa [hcard.1] at hdvd

end C5G2

end CFSG.ASVolI
