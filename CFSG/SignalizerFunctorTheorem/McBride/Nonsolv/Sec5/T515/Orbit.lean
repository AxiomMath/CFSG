module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Core
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab

variable {Γ : Type*} [Group Γ]

theorem mem_lcal_mono {X Y J : Subgroup Γ} (hJ : J ∈ lcal Y) (hJX : J ≤ X) (hXY : X ≤ Y) :
    J ∈ lcal X := by
  obtain ⟨-, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  refine mem_lcal_iff.mpr ⟨hJX, ?_, hs, hnc⟩
  have heq : (J.subgroupOf Y).comap (Subgroup.inclusion hXY) = J.subgroupOf X := by
    ext t
    rfl
  exact heq ▸ hsub.comap (Subgroup.inclusion hXY)

theorem ne_bot_of_not_isMulCommutative {F : Subgroup Γ} (hnc : ¬ IsMulCommutative F) : F ≠ ⊥ := by
  rintro rfl
  exact hnc inferInstance

variable [Finite Γ]

theorem eq_bot_of_isSolvable_of_normalized {G N : Subgroup Γ} (hsol : sol G = ⊥)
    (hNK : N ≤ kOf G) (hN : kOf G ≤ Subgroup.normalizer (N : Set Γ))
    (hs : Group.IsSolvable N) : N = ⊥ := by
  have hK := isDirectProduct_lcal_kOf hsol
  have hcent : ∀ J ∈ lcal G, N ≤ Subgroup.centralizer (J : Set Γ) := by
    intro J hJ n hn
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    obtain ⟨-, -, hjs, hjnc⟩ := mem_lcal_iff.mp hJ
    have hJK : J ≤ kOf G := hK.le hJ
    have hnJ : n * j * n⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hK.le_normalizer hJ (hNK hn)) j).mp hj
    have hjN : j * n⁻¹ * j⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hN (hJK hj)) n⁻¹).mp (inv_mem hn)
    have hc : n * j * n⁻¹ * j⁻¹ ∈ N ⊓ J := by
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem hnJ (inv_mem hj)⟩
      have := mul_mem hn hjN
      simpa [mul_assoc] using this
    have hNJ : ((N ⊓ J).subgroupOf J).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro u v hu hv
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hN (hJK hv)) u).mp (Subgroup.mem_inf.mp hu).1,
          mul_mem (mul_mem hv (Subgroup.mem_inf.mp hu).2) (inv_mem hv)⟩
    have := hjs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ J).subgroupOf J) with h | h
    · have h1 : (⟨n * j * n⁻¹ * j⁻¹, (Subgroup.mem_inf.mp hc).2⟩ : ↥J) ∈
          (N ⊓ J).subgroupOf J := hc
      rw [h, Subgroup.mem_bot] at h1
      have h2 : n * j * n⁻¹ * j⁻¹ = 1 := congrArg Subtype.val h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · exfalso
      have hJN : J ≤ N := fun x hx => by
        have : (⟨x, hx⟩ : ↥J) ∈ (N ⊓ J).subgroupOf J := by rw [h]; trivial
        exact (Subgroup.mem_inf.mp this).1
      exact not_isSolvable_of_not_isMulCommutative hjnc (isSolvable_of_le hJN hs)
  refine eq_bot_iff.mpr fun n hn => ?_
  have hn' : n ∈ G ⊓ Subgroup.centralizer (kOf G : Set Γ) := by
    refine Subgroup.mem_inf.mpr ⟨kOf_le G (hNK hn), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have : kOf G ≤ Subgroup.centralizer ({n} : Set Γ) := by
      rw [← hK.sSup_eq]
      refine sSup_le fun J hJ y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hcent J hJ hn) y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hk)
  rwa [centralizer_kOf_eq_bot hsol] at hn'

section Orbit

variable {A G J : Subgroup Γ}

theorem orbitClosure_le_of_mem_lcal (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) : orbitClosure J A ≤ G :=
  (orbitClosure_le_kOf hAG hsol hJ).trans (kOf_le G)

theorem kOf_le_normalizer_orbitClosure (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    kOf G ≤ Subgroup.normalizer (orbitClosure J A : Set Γ) := by
  rw [← (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).sup_eq]
  exact sup_le Subgroup.le_normalizer
    ((outsideOrbit_le_centralizer hAG hsol hJ).trans (Subgroup.centralizer_le_normalizer _))

theorem sol_orbitClosure_eq_bot (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥)
    (hJ : J ∈ lcal G) : sol (orbitClosure J A) = ⊥ :=
  eq_bot_of_isSolvable_of_normalized hsol
    ((sol_le _).trans (orbitClosure_le_kOf hAG hsol hJ))
    ((kOf_le_normalizer_orbitClosure hAG hsol hJ).trans (SolQuot.normalizer_le_nrm_sol _))
    (isSolvable_sol _)

theorem orbitClosure_inf_centralizer_eq_bot (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    orbitClosure J A ⊓ Subgroup.centralizer (orbitClosure J A : Set Γ) = ⊥ := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
  have hle : kOf G ≤ Subgroup.centralizer ({g} : Set Γ) := by
    rw [← hdp.sup_eq]
    refine sup_le (fun l hl => ?_) (fun m hm => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hgC l hl
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hdp.commute g hgL m hm).eq.symm
  have hg' : g ∈ G ⊓ Subgroup.centralizer (kOf G : Set Γ) := by
    refine Subgroup.mem_inf.mpr ⟨orbitClosure_le_of_mem_lcal hAG hsol hJ hgL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  rwa [centralizer_kOf_eq_bot hsol] at hg'

theorem kSetting_orbitClosure {p : ℕ} (h : KSetting p A G) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    KSetting p A (orbitClosure J A) where
  prime := h.prime
  elemAbelian := h.elemAbelian
  normalizes := fun _ ha => mem_normalizer_orbitClosure ha
  hypB := hypB_of_le h.hypB (orbitClosure_le_of_mem_lcal h.normalizes hsol hJ)

theorem mem_lcalA_orbitClosure (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥)
    (hJ : J ∈ lcalA G A) : J ∈ lcalA (orbitClosure J A) A :=
  ⟨mem_lcal_mono hJ.1 (le_orbitClosure J A) (orbitClosure_le_of_mem_lcal hAG hsol hJ.1), hJ.2⟩

theorem fitting_smear_ne_bot
    {p : ℕ} (h : KSetting p A G) (hJ : J ∈ lcalA G A) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≠ ⊥ :=
  ne_bot_of_not_isMulCommutative (smear_fitting_isSimple h hJ).2

theorem eq_bot_of_le_centralizer_of_mem_conjOrbit (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hJ : J ∈ lcal G) {E F : Subgroup Γ} (hE : E ∈ conjOrbit A J)
    (hFL : F ≤ smear J A) (hFE : F ≤ Subgroup.centralizer (E : Set Γ)) : F = ⊥ := by
  have hL := isDirectProduct_conjOrbit hAG hJ
  have hEl : E ∈ lcal G := conjOrbit_subset_lcal hAG hJ hE
  obtain ⟨-, -, hEs, hEnc⟩ := mem_lcal_iff.mp hEl
  have hdp := hL.isDirectPair hE
  have hA : ∀ a ∈ A, ∀ K ∈ conjOrbit A J, K.map (MulAut.conj a).toMonoidHom ∈ conjOrbit A J :=
    fun a ha K hK => map_conj_mem_conjOrbit hK ha
  have hbot := inf_centralizer_inf_sSup_eq_bot_of_transitive hL hA hE
    (fun K hK => exists_conj_of_mem_conjOrbit hE hK)
  refine eq_bot_iff.mpr fun f hf => ?_
  have hfL : f ∈ orbitClosure J A := smear_le_orbitClosure J A (hFL hf)
  have hfA : f ∈ Subgroup.centralizer (A : Set Γ) := smear_le_centralizer J A (hFL hf)
  rw [← hdp.sup_eq] at hfL
  obtain ⟨e, he, l, hl, hel⟩ := (mem_sup_iff_of_commute hdp.commute).mp hfL
  have hfE := Subgroup.mem_centralizer_iff.mp (hFE hf)
  have hec : ∀ y ∈ E, y * e = e * y := by
    intro y hy
    have h1 := hfE y hy
    have h2 := (hL.commute_sSup_diff hE y hy l hl).eq
    rw [← hel] at h1
    have : y * e * l = e * y * l := by
      calc y * e * l = y * (e * l) := mul_assoc _ _ _
        _ = e * l * y := h1
        _ = e * (l * y) := mul_assoc _ _ _
        _ = e * (y * l) := by rw [← h2]
        _ = e * y * l := (mul_assoc _ _ _).symm
    exact mul_right_cancel this
  have he1 : e = 1 := by
    have := hEs
    exact eq_one_of_forall_commute hEnc he hec
  rw [he1, one_mul] at hel
  have hfl : f ∈ sSup (conjOrbit A J \ {E}) := hel ▸ hl
  have hmem : f ∈ orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ) ⊓
      sSup (conjOrbit A J \ {E}) := by
    refine ⟨⟨?_, hfA⟩, hfl⟩
    rw [← hdp.sup_eq]
    exact hel ▸ Subgroup.mem_sup_right hl
  rw [hbot] at hmem
  exact hmem

end Orbit

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab
