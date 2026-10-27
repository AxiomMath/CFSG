module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515cd.Decomp

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515cd

variable {Γ : Type*} [Group Γ] {A G : Subgroup Γ}

theorem kUp_eq_sSup_lcalA (hsol : sol G = ⊥) : kUp G A = sSup (lcalA G A) := by
  have h : mcalA G A = lcalA G A := by
    unfold mcalA lcalA
    rw [mcal_eq_lcal_of_sol_eq_bot hsol]
  unfold kUp
  rw [h, sSup_eq_iSup]

section Finite

variable [Finite Γ]

theorem exists_mem_kUp_of_mem_kOf (hsol : sol G = ⊥) {x : Γ} (hx : x ∈ kOf G) :
    ∃ y ∈ kUp G A, y⁻¹ * x ∈ Subgroup.centralizer (kUp G A : Set Γ) := by
  have hK := isDirectProduct_lcal_kOf hsol
  have hsub : lcalA G A ⊆ lcal G := lcalA_subset G A
  have hcomm : ∀ u ∈ sSup (lcalA G A), ∀ v ∈ sSup (lcal G \ lcalA G A), Commute u v :=
    commute_of_forall_commute_sSup fun J₁ hJ₁ J₂ hJ₂ u hu v hv =>
      hK.commute J₁ (hsub hJ₁) J₂ hJ₂.1 (fun h => hJ₂.2 (h ▸ hJ₁)) u hu v hv
  have hsup : kOf G = sSup (lcalA G A) ⊔ sSup (lcal G \ lcalA G A) := by
    rw [← hK.sSup_eq, ← sSup_union, Set.union_sdiff_cancel hsub]
  rw [hsup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
  refine ⟨y, (kUp_eq_sSup_lcalA hsol).symm ▸ hy, ?_⟩
  rw [inv_mul_cancel_left, Subgroup.mem_centralizer_iff]
  exact fun k hk => (hcomm k ((kUp_eq_sSup_lcalA hsol) ▸ hk) z hz).eq

theorem exists_mem_kUp_of_sol_eq_bot
    {p : ℕ} {X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hsol : sol G = ⊥) (hK : kOf X = X) :
    ∀ x ∈ X, ∃ y ∈ kUp G A, y⁻¹ * x ∈ kDown G A := by
  set X₁ := X ⊓ kOf G with hX₁
  have hX₁X : X₁ ≤ X := inf_le_left
  have hXn : X ≤ Subgroup.normalizer (X₁ : Set Γ) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (le_normalizer_kOf G (hX.1 hg))
  have hAk : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf G : Set Γ) := fun a ha =>
    mem_normalizer_kOf_of_mem_normalizer (h.normalizes ha)
  have hDk : ∀ d ∈ G ⊓ Subgroup.centralizer (A : Set Γ),
      d ∈ Subgroup.normalizer (kOf G : Set Γ) := fun d hd => le_normalizer_kOf G hd.1
  have hX₂ : IsDAInvariant A G (secCentralizer X X₁) :=
    ⟨(secCentralizer_le X X₁).trans hX.1,
      fun d hd => mem_normalizer_secCentralizer (hX.2.1 hd)
        (mem_normalizer_inf (hX.2.1 hd) (hDk d hd)),
      fun a ha => mem_normalizer_secCentralizer (hX.2.2 ha)
        (mem_normalizer_inf (hX.2.2 ha) (hAk a ha))⟩
  have hcent : ∀ J ∈ lcalA G A, secCentralizer X X₁ ≤ Subgroup.centralizer (J : Set Γ) := by
    intro J hJ
    rcases lemma_5_14 h hX₂ hsol hJ with hF | hC
    · exfalso
      obtain ⟨hs, hnc⟩ := smear_fitting_isSimple h hJ
      have hFk : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ kOf G :=
        ((Subgroup.map_subtype_le _).trans (smear_le_orbitClosure J A)).trans
          (orbitClosure_le_kOf h.normalizes hsol hJ.1)
      have hFsol : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ sol X := fun z hz =>
        mem_sol_of_mem_secCentralizer hK hX₁X hXn
          (Subgroup.mem_inf.mpr ⟨secCentralizer_le X X₁ (hF hz), hFk hz⟩) (hF hz)
      have : Group.IsSolvable ↥(sol X) := isSolvable_sol X
      exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hFsol)
          (Subgroup.inclusion_injective hFsol))))
    · exact hC
  have hcentK : secCentralizer X X₁ ≤ Subgroup.centralizer (kUp G A : Set Γ) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hle : kUp G A ≤ Subgroup.centralizer ({z} : Set Γ) := by
      rw [kUp_eq_sSup_lcalA hsol]
      refine sSup_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hcent J hJ hz) j hj
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  intro x hx
  obtain ⟨x₁, hx₁, hx₂⟩ := exists_mem_of_kOf_eq_self hK hX₁X hXn hx
  obtain ⟨y, hy, hyc⟩ := exists_mem_kUp_of_mem_kOf (A := A) hsol (Subgroup.mem_inf.mp hx₁).2
  refine ⟨y, hy, mem_kDown_iff.mpr ⟨mul_mem (inv_mem (kUp_le G A hy)) (hX.1 hx), fun k hk => ?_⟩⟩
  rw [hsol, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have e : y⁻¹ * x = (y⁻¹ * x₁) * (x₁⁻¹ * x) := by group
  rw [e]
  have h1 : Commute k (y⁻¹ * x₁) := Subgroup.mem_centralizer_iff.mp hyc k hk
  have h2 : Commute k (x₁⁻¹ * x) := Subgroup.mem_centralizer_iff.mp (hcentK hx₂) k hk
  exact (h1.mul_right h2).eq.symm

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515cd
