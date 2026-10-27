module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515cd.Core

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem le_normalizer_kUp_of_kOf_eq_self
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hK : kOf X = X) : X ≤ Subgroup.normalizer (kUp G A : Set Γ) := by
  have hkh : khat X = X := khat_eq_self_of_kOf_eq_self hK
  have hn : ∀ J ∈ mcalA G A, ∀ g ∈ X, g ∈ Subgroup.normalizer (J : Set Γ) := fun J hJ =>
    theorem_5_15_b h hX hJ hkh
  intro g hg
  have hconj : ∀ g ∈ X, ∀ J ∈ mcalA G A, J.map (MulAut.conj g).toMonoidHom ∈ mcalA G A :=
    fun g hg J hJ => (map_conj_eq_of_mem_normalizer (hn J hJ g hg)).symm ▸ hJ
  have : kUp G A = sSup (mcalA G A) := (sSup_eq_iSup).symm
  rw [this]
  exact mem_normalizer_sSup (hconj g hg) (hconj g⁻¹ (inv_mem hg))

theorem theorem_5_15_c
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hK : kOf X = X) :
    X ≤ Subgroup.normalizer (kUp G A : Set Γ) ∧ ∀ x ∈ X, ∃ y ∈ kUp G A, y⁻¹ * x ∈ kDown G A := by
  refine ⟨le_normalizer_kUp_of_kOf_eq_self h hX hK, ?_⟩
  have hKbar : kOf (AChief.qimg (sol G) X) = AChief.qimg (sol G) X := by
    rw [SolQuot.kOf_qimg_sol hX.1, hK]
  exact SolQuot.exists_mem_kUp_of_qimg_sol h hX.1
    (T515cd.exists_mem_kUp_of_sol_eq_bot (SolQuot.kSetting_qimg_sol h)
      (SolQuot.isDAInvariant_qimg_sol h hX) (SolQuot.sol_qimg_sol G) hKbar)

theorem theorem_5_15_d
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hK : kOf X = X) :
    ∀ x ∈ X, ∃ y ∈ kUp G A, ∃ z ∈ kDown G A, x = y * z := by
  intro x hx
  obtain ⟨y, hy, hz⟩ := (theorem_5_15_c h hX hK).2 x hx
  exact ⟨y, hy, y⁻¹ * x, hz, by group⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
