module

public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTwist
public import CFSG.Sporadic.Schreier.LySylow
public import CFSG.Sporadic.Schreier.LyGroupLemmas
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly
open CFSG.ComponentClassification.OuterAutomorphisms

theorem bs_zGroup_map
    (β : MulAut lyC) (hβ : β zC = zC) :
    zGroup.map (β : lyC →* lyC) = zGroup := by
  rw [zGroup, MonoidHom.map_zpowers]
  change Subgroup.zpowers (β zC) = Subgroup.zpowers zC
  rw [hβ]

@[expose] def bsInduced
    (β : MulAut lyC) (hβ : β zC = zC) : MulAut (alternatingGroup (Fin 11)) :=
  (lyCoverEquiv.symm.trans (QuotientGroup.congr zGroup zGroup β (bs_zGroup_map β hβ))).trans
    lyCoverEquiv

theorem bsInduced_imgC
    (β : MulAut lyC) (hβ : β zC = zC) (x : lyC) :
    (bsInduced β hβ (lyCoverEquiv (x : lyC ⧸ zGroup)) : Equiv.Perm (Fin 11)) = imgC (β x) := by
  simp only [bsInduced, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]
  rw [imgC_apply]

theorem bs_exists_perm
    (β : MulAut lyC) (hβ : β zC = zC) :
    ∃ σ : Equiv.Perm (Fin 11), ∀ x : lyC, imgC (β x) = σ * imgC x * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 11) (Or.inr (by norm_num)) (bsInduced β hβ)
  exact ⟨σ, fun x => by rw [← bsInduced_imgC β hβ x, hσ, imgC_apply]⟩

theorem bs_imgC_surj
    {τ : Equiv.Perm (Fin 11)} (hτ : τ ∈ alternatingGroup (Fin 11)) :
    ∃ c : lyC, imgC c = τ := by
  obtain ⟨q, hq⟩ := lyCoverEquiv.surjective ⟨τ, hτ⟩
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨c, by rw [imgC_apply, hq]⟩

theorem bs_mem_inner_of_fix
    (hC : lyC = Subgroup.centralizer ({lyz} : Set J)) (α : MulAut J)
    (β : MulAut lyC) (hαβ : ∀ x : lyC, (β x : J) = α x) (hαz : α lyz = lyz) :
    β ∈ inner lyC := by
  have hβz : β zC = zC := Subtype.ext (by rw [hαβ]; exact hαz)
  obtain ⟨σ, hσ⟩ := bs_exists_perm β hβz
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  ·
    obtain ⟨c, hc⟩ := bs_imgC_surj (Equiv.Perm.mem_alternatingGroup.2 hs)
    have h1 : MulAut.conj c⁻¹ * β = 1 := by
      refine eq_one_of_trivial_on_quotient zGroup zGroup_le_center commutator_lyC _ fun x => ?_
      rw [← imgC_eq_one_iff, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
      simp only [map_mul, map_inv, hσ, hc]
      group
    refine ⟨c, ?_⟩
    have h2 : β = (MulAut.conj c⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right (α := MulAut lyC) h1
    rw [h2, map_inv, inv_inv]
  ·
    exfalso
    have hτ : Equiv.swap (8 : Fin 11) 9 * σ⁻¹ ∈ alternatingGroup (Fin 11) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs,
        Equiv.Perm.sign_swap (by decide)]
      decide
    obtain ⟨c, hc⟩ := bs_imgC_surj hτ
    have h : (c : J) ∈ Subgroup.centralizer ({lyz} : Set J) := by
      rw [← hC]
      exact c.2
    have hcz := Subgroup.mem_centralizer_singleton_iff.1 h
    refine bs_no_swap_twist hC (MulAut.conj (c : J) * α) (MulAut.conj c * β) (fun x => ?_) ?_
      (fun x => ?_)
    · rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.mul_apply, MulAut.conj_apply,
        Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hαβ]
    · rw [MulAut.mul_apply, MulAut.conj_apply, hαz, hcz, mul_assoc, mul_inv_cancel, mul_one]
    · rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hσ, hc, mul_inv_rev,
        inv_inv, Equiv.swap_inv]
      group

end CFSG.Sporadic.LySchreier
