module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Core
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66.Normalizer
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Sol

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T66

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem kOf_inf_centralizer_le_sSup_diff {X : Subgroup Γ} (hsol : sol X = ⊥)
    {T : Set (Subgroup Γ)} (hT : T ⊆ lcal X) :
    kOf X ⊓ Subgroup.centralizer ((sSup T : Subgroup Γ) : Set Γ) ≤ sSup (lcal X \ T) := by
  have hK := isDirectProduct_lcal_kOf hsol
  have hcomm : ∀ x ∈ sSup T, ∀ y ∈ sSup (lcal X \ T), Commute x y :=
    L514.commute_of_forall_commute_sSup fun J₁ hJ₁ J₂ hJ₂ x hx y hy =>
      hK.commute J₁ (hT hJ₁) J₂ hJ₂.1 (fun h => hJ₂.2 (h ▸ hJ₁)) x hx y hy
  have hsup : kOf X = sSup T ⊔ sSup (lcal X \ T) := by
    rw [← hK.sSup_eq, ← sSup_union, Set.union_sdiff_cancel hT]
  rintro z ⟨hzK, hzC⟩
  rw [hsup] at hzK
  obtain ⟨t, ht, u, hu, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hzK
  have htT : t ∈ Subgroup.centralizer ((sSup T : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hzC y hy
    have h2 := (hcomm y hy u hu).eq
    have h3 : y * t * u = t * y * u := by
      calc y * t * u = y * (t * u) := mul_assoc _ _ _
        _ = t * u * y := h1
        _ = t * (u * y) := mul_assoc _ _ _
        _ = t * (y * u) := by rw [← h2]
        _ = t * y * u := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  have htK : t ∈ kOf X := by
    rw [hsup]
    exact Subgroup.mem_sup_left ht
  have hle : kOf X ≤ Subgroup.centralizer ({t} : Set Γ) := by
    rw [hsup]
    refine sup_le (fun y hy => ?_) fun y hy => ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp htT y hy
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm t ht y hy).eq.symm
  have htC : t ∈ Subgroup.centralizer (kOf X : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  have h4 : t ∈ X ⊓ Subgroup.centralizer (kOf X : Set Γ) :=
    ⟨kOf_le X htK, htC⟩
  rw [centralizer_kOf_eq_bot hsol, Subgroup.mem_bot] at h4
  rw [h4, one_mul]
  exact hu

omit [Finite Γ] in
theorem kUp_eq_sSup_lcalA {A X : Subgroup Γ} (hsol : sol X = ⊥) :
    kUp X A = sSup (lcalA X A) := by
  have h : mcalA X A = lcalA X A := by
    unfold mcalA lcalA
    rw [mcal_eq_lcal_of_sol_eq_bot hsol]
  unfold kUp
  rw [h, sSup_eq_iSup]

theorem isSolvable_kDown_inf_kOf_inf_centralizer_of_sol_eq_bot {p : ℕ} {A X : Subgroup Γ}
    (h : KSetting p A X) (hsol : sol X = ⊥) :
    Group.IsSolvable (kDown X A ⊓ kOf X ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) := by
  have h1 : kDown X A ⊓ kOf X ≤ sSup (lcal X \ lcalA X A) := by
    refine le_trans (le_inf inf_le_right fun z hz => ?_)
      (kOf_inf_centralizer_le_sSup_diff hsol (lcalA_subset X A))
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (T515ab.mul_comm_of_mem_kDown hsol hz.1 ((kUp_eq_sSup_lcalA hsol).symm ▸ hk)).symm
  have hdp : IsDirectProduct (lcal X \ lcalA X A) (sSup (lcal X \ lcalA X A)) :=
    isDirectProduct_of_subset (isDirectProduct_lcal_kOf hsol) Set.sdiff_subset
  have hsolv := isSolvable_inf_centralizer_of_isDirectProduct hdp
    (fun a ha _ hJ' => map_conj_mem_lcal_diff_lcalA hJ' (h.normalizes ha) (Or.inl ha))
    (fun J' hJ' => (isSolvable_inf_centralizer_iff_smear h.normalizes hJ'.1).mpr (by
      by_contra hns
      exact hJ'.2 ⟨hJ'.1, hns⟩))
  exact isSolvable_of_le (inf_le_inf_right _ h1) hsolv

theorem isSolvable_kDown_inf_kOf_inf_centralizer {p : ℕ} {A X : Subgroup Γ}
    (h : KSetting p A X) :
    Group.IsSolvable (kDown X A ⊓ kOf X ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) := by
  have hq := SolQuot.qSetting_sol h
  have hYX : kDown X A ⊓ kOf X ≤ X := inf_le_left.trans (kDown_le X A)
  have hAY : A ≤ Subgroup.normalizer ((kDown X A ⊓ kOf X : Subgroup Γ) : Set Γ) := fun a ha =>
    mem_normalizer_kDown_inf_kOf (h.normalizes ha) (Or.inl ha)
  refine (hq.isSolvable_qimg_inf_centralizer_iff hYX hAY).mp ?_
  have hbar : AChief.qimg (sol X) (kDown X A ⊓ kOf X) =
      kDown (AChief.qimg (sol X) X) (AChief.qimg (sol X) A) ⊓ kOf (AChief.qimg (sol X) X) := by
    rw [SolQuot.qimg_inf_of_le ((kOf_le X).trans (SolQuot.le_nrm_sol X)) (sol_le_kOf X),
      SolQuot.kDown_qimg_sol h, SolQuot.kOf_qimg_sol le_rfl]
  rw [hbar]
  exact isSolvable_kDown_inf_kOf_inf_centralizer_of_sol_eq_bot (SolQuot.kSetting_qimg_sol h)
    (SolQuot.sol_qimg_sol X)

theorem kDown_inf_kOf_mem_nsSet {p : ℕ} {A X : Subgroup Γ} (h : KSetting p A X) :
    kDown X A ⊓ kOf X ∈ nsSet p A X := by
  have hYX : kDown X A ⊓ kOf X ≤ X := inf_le_left.trans (kDown_le X A)
  refine ⟨hYX, fun d hd => ?_, fun a ha => ?_, h.elemAbelian, L514.hypB_of_le h.hypB hYX,
    isSolvable_kDown_inf_kOf_inf_centralizer h⟩
  · exact mem_normalizer_kDown_inf_kOf (Subgroup.le_normalizer hd.1) (Or.inr hd.2)
  · exact mem_normalizer_kDown_inf_kOf (h.normalizes ha) (Or.inl ha)

theorem kDown_eq_bot_of_kDown_inf_kOf_eq_bot {A X : Subgroup Γ}
    (h1 : kDown X A ⊓ kOf X = ⊥) : kDown X A = ⊥ := by
  have hsol : sol X = ⊥ := le_bot_iff.mp (h1 ▸ le_inf (sol_le_kDown X A) (sol_le_kOf X))
  have hK := isDirectProduct_lcal_kOf hsol
  have hall : lcal X ⊆ lcalA X A := by
    intro J hJ
    by_contra hJA
    have hc : ∀ x ∈ sSup ({J} : Set (Subgroup Γ)), ∀ y ∈ sSup (lcalA X A), Commute x y :=
      L514.commute_of_forall_commute_sSup fun J₁ hJ₁ J₂ hJ₂ x hx y hy => by
        rw [Set.mem_singleton_iff] at hJ₁
        subst hJ₁
        exact hK.commute J₁ hJ J₂ (lcalA_subset X A hJ₂) (fun hh => hJA (hh ▸ hJ₂)) x hx y hy
    rw [sSup_singleton] at hc
    have hJk : J ≤ kDown X A := fun x hx => by
      refine mem_kDown_iff.mpr ⟨lcal_le hJ hx, fun k hk => ?_⟩
      rw [hsol, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hc x hx k ((kUp_eq_sSup_lcalA hsol).symm ▸ hk)).eq
    exact ne_bot_of_not_isMulCommutative (mem_lcal_iff.mp hJ).2.2.2
      (le_bot_iff.mp (h1 ▸ le_inf hJk (hK.le hJ)))
  have hkUp : kUp X A = kOf X := by
    rw [kUp_eq_sSup_lcalA hsol, ← hK.sSup_eq]
    exact congrArg sSup (Set.Subset.antisymm (lcalA_subset X A) hall)
  refine eq_bot_iff.mpr fun g hg => ?_
  have hgC : g ∈ Subgroup.centralizer (kOf X : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (T515ab.mul_comm_of_mem_kDown hsol hg (hkUp.symm ▸ hk)).symm
  have h2 := centralizer_kOf_eq_bot hsol
  rw [eq_bot_iff] at h2
  exact h2 ⟨kDown_le X A hg, hgC⟩

theorem kDown_eq_bot_of_forall_nsSet {p : ℕ} {A X : Subgroup Γ} (h : KSetting p A X)
    (hN : ∀ Y ∈ nsSet p A X, Y = ⊥) : kDown X A = ⊥ :=
  kDown_eq_bot_of_kDown_inf_kOf_eq_bot (hN _ (kDown_inf_kOf_mem_nsSet h))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T66
