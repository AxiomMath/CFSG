module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimTheta
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem exists_swap_of_isOmegaPlus_six {X : Type} [Group X] [Finite X] (hX : IsOmegaPlus X 6 1)
    {Y : Subgroup X} (hY : IsCentralizerOfTransvectionIn X 3 Y) :
    ∃ (e : X ≃* alternatingGroup (Fin 8)) (a b : Fin 8), a ≠ b ∧
      Y.map e.toMonoidHom =
        (Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin 8)))).comap
          (alternatingGroup (Fin 8)).subtype := by
  obtain ⟨τ, hτ2, hτout, hYfix, hYcard⟩ := hY
  have hYcard' : Nat.card Y = 720 := by simpa using hYcard
  obtain ⟨e₀⟩ := s15k_omp6_isAlt8 hX
  let σ : Equiv.Perm (Fin 8) :=
    CFSG.QuasithinUnique.Claim2526.conjEquiv8.symm (MulAut.congr e₀ τ)
  have hσconj : MulAut.conjNormal σ = MulAut.congr e₀ τ := by
    change MulAut.conjNormal (CFSG.QuasithinUnique.Claim2526.conjEquiv8.symm
      (MulAut.congr e₀ τ)) = MulAut.congr e₀ τ
    exact MulEquiv.ofBijective_apply_symm_apply _ _
  have hσspec : ∀ x : X,
      ((e₀ (τ x) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        σ * (e₀ x : Equiv.Perm (Fin 8)) * σ⁻¹ := by
    intro x
    have h1 : MulAut.congr e₀ τ (e₀ x) = e₀ (τ x) := by
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    have h2 := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => f (e₀ x)) hσconj
    rw [h1] at h2
    have h3 := congrArg (fun z : alternatingGroup (Fin 8) =>
      (z : Equiv.Perm (Fin 8))) h2
    rw [MulAut.conjNormal_apply] at h3
    exact h3.symm
  have hσmul : σ * σ = 1 := by
    change CFSG.QuasithinUnique.Claim2526.conjEquiv8.symm (MulAut.congr e₀ τ) *
        CFSG.QuasithinUnique.Claim2526.conjEquiv8.symm (MulAut.congr e₀ τ) = 1
    rw [← map_mul, ← map_mul, hτ2, map_one, map_one]
  have hσsq : σ ^ 2 = 1 := by rw [pow_two]; exact hσmul
  have hodd : Equiv.Perm.sign σ = -1 := by
    by_contra hne
    have hsign1 : Equiv.Perm.sign σ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · exact h1
      · exact absurd h1 hne
    have hmem : σ ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 hsign1
    let g : alternatingGroup (Fin 8) := ⟨σ, hmem⟩
    have hinner : τ = MulAut.conj (e₀.symm g) := by
      ext x
      apply e₀.injective
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      change ((e₀ (τ x) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        σ * ((e₀ x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) * σ⁻¹
      exact hσspec x
    exact hτout ⟨e₀.symm g, hinner.symm⟩
  have hmap : Y.map e₀.toMonoidHom =
      (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))).comap
        (alternatingGroup (Fin 8)).subtype := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      change (e₀ x : Equiv.Perm (Fin 8)) * σ = σ * (e₀ x : Equiv.Perm (Fin 8))
      have hxfix : τ x = x := (hYfix x).mp hx
      have h := hσspec x
      rw [hxfix] at h
      nth_rewrite 1 [h]
      group
    · intro hg
      rw [Subgroup.mem_map]
      refine ⟨e₀.symm g, ?_, e₀.apply_symm_apply g⟩
      rw [hYfix]
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      have hg' : (g : Equiv.Perm (Fin 8)) * σ = σ * (g : Equiv.Perm (Fin 8)) := hg
      have h := hσspec (e₀.symm g)
      rw [MulEquiv.apply_symm_apply] at h
      rw [h, ← hg']
      group
  have hcardCmap : Nat.card ↥((Subgroup.centralizer
      ({σ} : Set (Equiv.Perm (Fin 8)))).comap (alternatingGroup (Fin 8)).subtype) = 720 := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective e₀.injective).trans hYcard'
  have hcard_inf : Nat.card ↥(alternatingGroup (Fin 8) ⊓
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) = 720 := by
    have hmap_inf : ((Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))).comap
        (alternatingGroup (Fin 8)).subtype).map (alternatingGroup (Fin 8)).subtype =
        Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8))) ⊓
          alternatingGroup (Fin 8) := by
      rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]
    rw [inf_comm, ← hmap_inf,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective (alternatingGroup (Fin 8)))]
    exact hcardCmap
  have hσcycle : σ.cycleType = {2} :=
    CFSG.EvenSporadicStandard.HNRecog.Section3.s7_sym8_cycleType_of_card hσsq hodd hcard_inf
  have hσisSwap : σ.IsSwap := Equiv.Perm.isSwap_iff_cycleType.mpr hσcycle
  obtain ⟨a, b, hab, hσab⟩ := hσisSwap
  exact ⟨e₀, a, b, hab, by rw [← hσab]; exact hmap⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
