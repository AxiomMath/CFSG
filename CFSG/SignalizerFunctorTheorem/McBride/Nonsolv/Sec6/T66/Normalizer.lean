module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KHat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.CentralizerK.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T66

variable {Γ : Type*} [Group Γ] {A X M : Subgroup Γ}

theorem inv_mem_or {g : Γ} (hg : g ∈ A ∨ g ∈ Subgroup.centralizer (A : Set Γ)) :
    g⁻¹ ∈ A ∨ g⁻¹ ∈ Subgroup.centralizer (A : Set Γ) :=
  hg.imp inv_mem inv_mem

variable [Finite Γ]

theorem map_conj_mem_mcalA {g : Γ} (hgX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hg : g ∈ A ∨ g ∈ Subgroup.centralizer (A : Set Γ)) (hM : M ∈ mcalA X A) :
    M.map (MulAut.conj g).toMonoidHom ∈ mcalA X A := by
  refine ⟨map_conj_mem_mcal hM.1 hgX, fun hs => hM.2 ?_⟩
  rcases inv_mem_or hg with hg' | hg'
  · have h := smear_map_conj_of_mem (J := M.map (MulAut.conj g).toMonoidHom) (A := A) hg'
    rw [L514.map_conj_map_conj_inv] at h
    rwa [h]
  · have h := isSolvable_smear_map_conj_of_mem_centralizer hg' hs
    rwa [L514.map_conj_map_conj_inv] at h

theorem mem_normalizer_kUp {g : Γ} (hgX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hg : g ∈ A ∨ g ∈ Subgroup.centralizer (A : Set Γ)) :
    g ∈ Subgroup.normalizer (kUp X A : Set Γ) := by
  have hkUp : kUp X A = sSup (mcalA X A) := by
    unfold kUp
    rw [sSup_eq_iSup]
  rw [hkUp]
  exact L514.mem_normalizer_sSup (fun _ hJ => map_conj_mem_mcalA hgX hg hJ)
    fun _ hJ => map_conj_mem_mcalA (inv_mem hgX) (inv_mem_or hg) hJ

theorem mem_normalizer_kDown {g : Γ} (hgX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hgK : g ∈ Subgroup.normalizer (kUp X A : Set Γ)) :
    g ∈ Subgroup.normalizer (kDown X A : Set Γ) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  obtain ⟨htX, ht⟩ := mem_kDown_iff.mp ht
  refine mem_kDown_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgX t).mp htX, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ kUp X A := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
  have h1 := (Subgroup.mem_normalizer_iff.mp (SolQuot.normalizer_le_nrm_sol X hgX) _).mp
    (ht _ hk')
  have e : ⁅g * t * g⁻¹, k⁆ = g * ⁅t, g⁻¹ * k * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem mem_normalizer_kDown_inf_kOf {g : Γ} (hgX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hg : g ∈ A ∨ g ∈ Subgroup.centralizer (A : Set Γ)) :
    g ∈ Subgroup.normalizer ((kDown X A ⊓ kOf X : Subgroup Γ) : Set Γ) :=
  L514.mem_normalizer_inf (mem_normalizer_kDown hgX (mem_normalizer_kUp hgX hg))
    (mem_normalizer_kOf_of_mem_normalizer hgX)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T66
