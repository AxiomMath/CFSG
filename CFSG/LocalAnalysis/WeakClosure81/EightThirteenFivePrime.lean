module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFive

public section

open Finset

namespace CFSG.LocalAnalysis.WeakClosure81.Five

theorem five_point_const' {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [CommGroup W]
    (hcard : Fintype.card Ω = 5) (hW2 : ∀ w : W, w * w = 1) (f : Ω → W) (ω₁ : Ω)
    (htrans : ∀ ω₀ : Ω, ∃ (φ : W ≃* W) (π : Equiv.Perm Ω), π ω₁ = ω₀ ∧
      ∀ ω, f (π ω) = φ (f ω))
    (σa σb : Equiv.Perm Ω) (θa θb : W ≃* W)
    (hfa : ∀ ω, f (σa ω) = θa (f ω)) (hfb : ∀ ω, f (σb ω) = θb (f ω))
    (hσa : σa * σa = 1) (hcomm : σa * σb = σb * σa)
    (ha1 : σa ω₁ = ω₁) (hb1 : σb ω₁ = ω₁)
    (hua : ∀ ω, σa ω = ω → ω = ω₁) (hub : ∀ ω, σb ω = ω → ω = ω₁)
    (huab : ∀ ω, (σa * σb) ω = ω → ω = ω₁)
    (hfixed : ∀ ω, θb (f ω * θa (f ω)) = f ω * θa (f ω)) :
    ∀ ω, f ω = f ω₁ := by
  classical
  have haa : ∀ ω : Ω, σa (σa ω) = ω := fun ω => by
    have := congrArg (fun σ : Equiv.Perm Ω => σ ω) hσa
    simpa [Equiv.Perm.mul_apply] using this
  have hab_apply : ∀ ω, (σa * σb) ω = σa (σb ω) := fun ω => rfl
  have hba_apply : ∀ ω, (σa * σb) ω = σb (σa ω) := fun ω => by
    rw [hcomm]; rfl
  have hrel : ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f ω = 1 := by
    have hne : ∃ ω₂ : Ω, ω₂ ≠ ω₁ := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => by
        rw [hcon x, hcon y])
      omega
    obtain ⟨ω₂, hω₂⟩ := hne
    have hfa' : σa ω₂ ≠ ω₂ := fun h => hω₂ (hua ω₂ h)
    have hfb' : σb ω₂ ≠ ω₂ := fun h => hω₂ (hub ω₂ h)
    have hfab' : (σa * σb) ω₂ ≠ ω₂ := fun h => hω₂ (huab ω₂ h)
    have h12 : σa ω₂ ≠ σb ω₂ := by
      intro h
      apply hfab'
      rw [hab_apply, ← h, haa]
    have h13 : σa ω₂ ≠ (σa * σb) ω₂ := by
      intro h
      rw [hab_apply] at h
      exact hfb' (σa.injective h).symm
    have h23 : σb ω₂ ≠ (σa * σb) ω₂ := by
      intro h
      rw [hba_apply] at h
      exact hfa' (σb.injective h).symm
    have hne1a : σa ω₂ ≠ ω₁ := fun h => hω₂ (σa.injective (h.trans ha1.symm))
    have hne1b : σb ω₂ ≠ ω₁ := fun h => hω₂ (σb.injective (h.trans hb1.symm))
    have hne1ab : (σa * σb) ω₂ ≠ ω₁ := by
      intro h
      apply hω₂
      have h' : (σa * σb) ω₂ = (σa * σb) ω₁ := by
        rw [h, hab_apply, hb1, ha1]
      exact (σa * σb).injective h'
    set S : Finset Ω := {ω₂, σa ω₂, σb ω₂, (σa * σb) ω₂} with hS
    have hSsub : S ⊆ (Finset.univ : Finset Ω).erase ω₁ := by
      intro x hx
      rw [hS] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact hω₂
      · exact hne1a
      · exact hne1b
      · exact hne1ab
    have hScard : S.card = 4 := by
      rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using h23
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hfa'.symm, hfb'.symm, hfab'.symm⟩
    have herase : (Finset.univ : Finset Ω).erase ω₁ = S := by
      refine (Finset.eq_of_subset_of_card_le hSsub ?_).symm
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard, hScard]
    rw [herase, hS]
    rw [Finset.prod_insert, Finset.prod_insert, Finset.prod_insert, Finset.prod_singleton]
    · set u : W := f ω₂ * f (σa ω₂) with hu
      have hbu : θb u = u := by
        rw [hu, hfa]
        exact hfixed ω₂
      have hbu' : θb u = f (σb ω₂) * f ((σa * σb) ω₂) := by
        rw [hu, map_mul, ← hfb, ← hfb, hba_apply]
      have h4 : f ω₂ * (f (σa ω₂) * (f (σb ω₂) * f ((σa * σb) ω₂))) = u * u := by
        have h5 : u * (f (σb ω₂) * f ((σa * σb) ω₂)) = u * u := by rw [← hbu', hbu]
        rw [← h5, hu, mul_assoc]
      rw [h4, hW2]
    · simp only [Finset.mem_singleton]
      exact h23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfa'.symm, hfb'.symm, hfab'.symm⟩
  have hrel' : ∀ ω₀ : Ω, ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₀, f ω = 1 := by
    intro ω₀
    obtain ⟨φ, π, hπ, hfπ⟩ := htrans ω₀
    have hprod : ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f (π ω) =
        ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₀, f ω := by
      refine Finset.prod_equiv π ?_ ?_
      · intro i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rw [← hπ]
        exact not_congr π.injective.eq_iff.symm
      · intro i _
        rfl
    rw [← hprod]
    have h1 : ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f (π ω) =
        φ (∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f ω) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun ω _ => hfπ ω
    rw [h1, hrel, map_one]
  intro ω
  have h1 := Finset.mul_prod_erase (Finset.univ : Finset Ω) f (Finset.mem_univ ω)
  have h2 := Finset.mul_prod_erase (Finset.univ : Finset Ω) f (Finset.mem_univ ω₁)
  rw [hrel' ω, mul_one] at h1
  rw [hrel' ω₁, mul_one] at h2
  rw [h1, h2]

end CFSG.LocalAnalysis.WeakClosure81.Five

end
