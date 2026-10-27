module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213Setup

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem SemisimpleAction.not_isNilpotent_cenIn
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ¬ Group.IsNilpotent ↥(cenIn J (norIn A J)) := by
  intro hnil
  obtain ⟨x, hx, c, hc, hne⟩ := h.exists_noncomm_cenIn hJ
  have hF : cenIn J (norIn A J) ≤ CFSG.fittingSubgroupOf (cenIn J (norIn A J)) :=
    Thm210.le_fittingSubgroupOf_of_nilpotent le_rfl Subgroup.le_normalizer hnil
  have := h.isMulCommutative_fittingSubgroupOf_kJ hJ
  have hcomm : IsMulCommutative ↥(CFSG.fittingSubgroupOf (cenIn J (norIn A J))) :=
    Thm210.isMulCommutative_of_le (h.fittingSubgroupOf_cenIn_le_kJ hJ)
  have h1 := congrArg Subtype.val
    (mul_comm' (⟨c, hF hc⟩ : ↥(CFSG.fittingSubgroupOf (cenIn J (norIn A J)))) ⟨x, hx⟩)
  apply hne
  rw [mul_inv_eq_iff_eq_mul]
  exact h1

end CFSG.SignalizerFunctorTheorem.McBride.Near

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G W : Subgroup Γ}

namespace Hyp

variable (H : Hyp p A G W)

include H

theorem k1_eq_cenIn_k2
    : k1 G W = cenIn (kOf G) ((k2 G W : Subgroup Γ) : Set Γ) := by
  rw [H.k2_eq, cenIn_sSup_eq H.hK (fun J hJ => simple_of_mem_lcal hJ) (tTwo_subset G W),
    H.tTwo_eq_diff, Set.sdiff_sdiff_cancel_left (tOne_subset G W), H.k1_eq]

theorem nilpotent_projIn_iff
    {Z₀ : Subgroup Γ} (hadm₀ : Admits (cenIn G A ⊔ A) Z₀)
    (hD : Z₀ ⊓ kOf G ⊓ cenIn G A = cenIn (k1 G W) A) {J : Subgroup Γ}
    (hJ : J ∈ lcal (kOf G)) :
    Group.IsNilpotent ↥(projIn (lcal (kOf G)) J (Z₀ ⊓ kOf G)) ↔ J ∈ tTwo G W := by
  have hSA := H.semisimpleAction
  have hcen : cenIn (kOf G) (A : Set Γ) ≤ cenIn G A := inf_le_inf_right _ (kOf_le G)
  have hQ : cenIn (kOf G) (A : Set Γ) ⊔ A ≤ cenIn G A ⊔ A := sup_le_sup_right hcen A
  constructor
  · intro hnil
    by_contra hJ2
    have hJ1 : J ∈ tOne G W := by
      by_contra hJ1
      apply hJ2
      rw [H.tTwo_eq_diff]
      exact ⟨hJ, hJ1⟩
    have hsm : smear J A ≤ Z₀ ⊓ kOf G := by
      have h1 : smear J A ≤ cenIn (k1 G W) A :=
        le_inf (H.smear_le_k1 hJ1) (smear_le_centralizer J A)
      rw [← hD] at h1
      exact h1.trans inf_le_left
    have hle : cenIn J (norIn A J) ≤ projIn (lcal (kOf G)) J (Z₀ ⊓ kOf G) := by
      rw [← hSA.projIn_smear hJ]
      exact Thm210.projIn_mono J hsm
    exact hSA.not_isNilpotent_cenIn hJ
      (Thm210.isNilpotent_of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle))
  · intro hJ2
    by_contra hnn
    have hX : Admits (cenIn (kOf G) A ⊔ A) (Z₀ ⊓ kOf G) :=
      Thm210g.admits_inf (hQ.trans hadm₀) (hQ.trans H.admits_DA_kOf)
    have hF := thm210h hSA (inf_le_right : Z₀ ⊓ kOf G ≤ kOf G) hX hJ hnn
    have hFs : CFSG.fittingSubgroupOf (smear J A) ≤ smear J A := Subgroup.map_subtype_le _
    have hFD : CFSG.fittingSubgroupOf (smear J A) ≤ cenIn G A := hFs.trans
      ((hSA.smear_le_cenIn hJ).trans hcen)
    have hFK1 : CFSG.fittingSubgroupOf (smear J A) ≤ k1 G W := by
      have : CFSG.fittingSubgroupOf (smear J A) ≤ cenIn (k1 G W) A := hD ▸ le_inf hF hFD
      exact this.trans inf_le_left
    have hFK2 : CFSG.fittingSubgroupOf (smear J A) ≤ k2 G W :=
      hFs.trans ((H.smear_le_W hJ2).trans H.le_k2)
    have hbot : CFSG.fittingSubgroupOf (smear J A) ≤ ⊥ := by
      rw [← H.isDirectPair.inf_eq_bot]
      exact le_inf hFK1 hFK2
    exact hSA.fittingSubgroupOf_smear_ne_bot hJ (le_bot_iff.1 hbot)

theorem admits_k2_of_normal
    {Z₀ Z : Subgroup Γ} (hZ : Z ≤ G) (hZ₀ : IsNormalIn Z₀ Z)
    (hadm₀ : Admits (cenIn G A ⊔ A) Z₀)
    (hD : Z₀ ⊓ kOf G ⊓ cenIn G A = cenIn (k1 G W) A) : Admits Z (k2 G W) := by
  have hK := H.hK
  rw [H.k2_eq]
  refine Thm210.le_normalizer_of_conj_mem fun z hz x hx => ?_
  have hzG : z ∈ G := hZ hz
  have hzN : z ∈ Subgroup.normalizer (kOf G : Set Γ) :=
    mem_normalizer_kOf H.sol_eq (Subgroup.le_normalizer hzG)
  have hperm : ∀ J ∈ lcal (kOf G), J.map (MulAut.conj z).toMonoidHom ∈ lcal (kOf G) :=
    fun J hJ => map_conj_mem_lcal hJ hzN
  have hperm' : ∀ J ∈ lcal (kOf G), J.map (MulAut.conj z⁻¹).toMonoidHom ∈ lcal (kOf G) :=
    fun J hJ => map_conj_mem_lcal hJ (inv_mem hzN)
  have hzX : z ∈ Subgroup.normalizer ((Z₀ ⊓ kOf G : Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hZ₀.2 hz, hzN⟩
  have hle : sSup (tTwo G W) ≤ (sSup (tTwo G W)).comap (MulAut.conj z).toMonoidHom := by
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hJz : J.map (MulAut.conj z).toMonoidHom ∈ tTwo G W := by
      have hJnil := (H.nilpotent_projIn_iff hadm₀ hD hJ.1).2 hJ
      refine (H.nilpotent_projIn_iff hadm₀ hD (hperm J hJ.1)).1 ?_
      have hle1 := projIn_map_conj_le hK hperm hperm' hzX hJ.1
      have := hJnil
      have hnil2 : Group.IsNilpotent ↥((projIn (lcal (kOf G)) J (Z₀ ⊓ kOf G)).map
          (MulAut.conj z).toMonoidHom) :=
        Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj z).injective)
      exact Thm210.isNilpotent_of_injective (Subgroup.inclusion hle1)
        (Subgroup.inclusion_injective hle1)
    exact le_sSup hJz
  simpa using hle hx

theorem admits_k1_of_normal
    {Z₀ Z : Subgroup Γ} (hZ : Z ≤ G) (hZ₀ : IsNormalIn Z₀ Z)
    (hadm₀ : Admits (cenIn G A ⊔ A) Z₀)
    (hD : Z₀ ⊓ kOf G ⊓ cenIn G A = cenIn (k1 G W) A) : Admits Z (k1 G W) := by
  rw [H.k1_eq_cenIn_k2]
  exact admits_cenIn (fun z hz => mem_normalizer_kOf H.sol_eq (Subgroup.le_normalizer (hZ hz)))
    (H.admits_k2_of_normal hZ hZ₀ hadm₀ hD)

end Hyp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213
