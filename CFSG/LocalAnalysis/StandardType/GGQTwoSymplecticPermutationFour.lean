module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticTorusActions
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticMovingBlock
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix CFSG.Open CFSG.StandardType.WitSpNs
open scoped commutatorElement
open CFSG.SeitzReduction.SymplecticPilot (permSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)


theorem four_dvd_of_klein_permutations_in_full_frame
    {K : Type} [Field K] [Finite K] {n : ℕ}
    {E J : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    {π ρ : Equiv.Perm (Fin n)} (hπ2 : π ^ 2 = 1) (hρ2 : ρ ^ 2 = 1)
    (hcomm : π * ρ = ρ * π) (hπ1 : π ≠ 1) (hρ1 : ρ ≠ 1) (hne : π ≠ ρ)
    (hπJ : A₀ * permSp K π * A₀⁻¹ ∈ J) (hρJ : A₀ * permSp K ρ * A₀⁻¹ ∈ J) :
    4 ∣ Nat.card (ggAutomizer J E) := by
  let f : Equiv.Perm (Fin n) →* StatedSp n K :=
    { toFun := fun σ => A₀ * permSp K σ * A₀⁻¹
      map_one' := by rw [permSp_one_of_injective, mul_one, mul_inv_cancel]
      map_mul' := fun σ τ => by rw [permSp_mul_of_injective]; group }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply eq_one_of_permSp_frame_centralizes hframe hsurj σ
    intro g hg
    change f σ * g * (f σ)⁻¹ = g
    rw [hσ]
    simp
  have hg2 : f π * f π = 1 := by rw [← _root_.pow_two, ← map_pow, hπ2, map_one]
  have hh2 : f ρ * f ρ = 1 := by rw [← _root_.pow_two, ← map_pow, hρ2, map_one]
  have hgh : f π * f ρ = f ρ * f π := by rw [← map_mul, ← map_mul, hcomm]
  have hg1 : f π ≠ 1 := by
    intro h
    apply hπ1
    apply hf
    simpa only [map_one] using h
  have hh1 : f ρ ≠ 1 := by
    intro h
    apply hρ1
    apply hf
    simpa only [map_one] using h
  have hghne : f π ≠ f ρ := fun h => hne (hf h)
  have hNπ : f π ∈ Subgroup.normalizer (E : Set (StatedSp n K)) :=
    permSp_mem_normalizer_of_full_frame hframe hsurj π
  have hNρ : f ρ ∈ Subgroup.normalizer (E : Set (StatedSp n K)) :=
    permSp_mem_normalizer_of_full_frame hframe hsurj ρ
  have hkernel : ∀ g ∈ Subgroup.closure ({f π, f ρ} : Set (StatedSp n K)),
      (∀ a ∈ E, g * a * g⁻¹ = a) → g = 1 := by
    have hle : Subgroup.closure ({f π, f ρ} : Set (StatedSp n K)) ≤ f.range :=
      (Subgroup.closure_le (K := f.range)).mpr (by
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact ⟨π, rfl⟩
        · exact ⟨ρ, rfl⟩)
    intro g hg hcen
    obtain ⟨σ, rfl⟩ := hle hg
    have hσ : σ = 1 := eq_one_of_permSp_frame_centralizes hframe hsurj σ hcen
    rw [hσ, map_one]
  exact QTwoCav.four_dvd_ggAutomizer_of_two_independent_involutions
    hπJ hρJ hNπ hNρ hg2 hh2 hgh hg1 hh1 hghne hkernel


theorem exists_klein_commutator_permutations {n : ℕ} (i : Fin 4 → Fin n)
    (hi : Function.Injective i) :
    ∃ p q r s g h : Equiv.Perm (Fin n),
      (∀ π ∈ ({p, q, r, s} : Set (Equiv.Perm (Fin n))), ∀ j ∉ Set.range i, π j = j) ∧
      g = ⁅p, q⁆ ∧ h = ⁅r, s⁆ ∧ g ^ 2 = 1 ∧ h ^ 2 = 1 ∧
      g * h = h * g ∧ g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h := by
  let ι : Fin 4 ↪ Fin n := ⟨i, hi⟩
  let f : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin n) := Equiv.Perm.viaEmbeddingHom ι
  let p : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  let q : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  let r : Equiv.Perm (Fin 4) := Equiv.swap 0 2
  let s : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  let g : Equiv.Perm (Fin 4) := ⁅p, q⁆
  let h : Equiv.Perm (Fin 4) := ⁅r, s⁆
  have hg2 : g ^ 2 = 1 := by decide +kernel
  have hh2 : h ^ 2 = 1 := by decide +kernel
  have hcomm : g * h = h * g := by decide +kernel
  have hg1 : g ≠ 1 := by decide +kernel
  have hh1 : h ≠ 1 := by decide +kernel
  have hne : g ≠ h := by decide +kernel
  have hf : Function.Injective f := Equiv.Perm.viaEmbeddingHom_injective ι
  have hfix : ∀ π : Equiv.Perm (Fin 4), ∀ j ∉ Set.range i, f π j = j := by
    intro π j hj
    exact Equiv.Perm.viaEmbedding_apply_of_notMem π ι j hj
  have hgp : f g = ⁅f p, f q⁆ := by simp only [g, commutatorElement_def, map_mul, map_inv]
  have hhr : f h = ⁅f r, f s⁆ := by simp only [h, commutatorElement_def, map_mul, map_inv]
  refine ⟨f p, f q, f r, f s, f g, f h, ?_, hgp, hhr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π hπ j hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
    rcases hπ with rfl | rfl | rfl | rfl <;> exact hfix _ j hj
  · rw [← map_pow, hg2, map_one]
  · rw [← map_pow, hh2, map_one]
  · rw [← map_mul, ← map_mul, hcomm]
  · intro h
    apply hg1
    apply hf
    simpa only [map_one] using h
  · intro h
    apply hh1
    apply hf
    simpa only [map_one] using h
  · exact fun h => hne (hf h)

end CFSG.StandardType.QTwoSymplecticCav

end
