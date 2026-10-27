module

public import CFSG.Quasithin.Background.G118Inputs
public import CFSG.Quasithin.Background.P3Sp44Rank
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Equiv CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank Matrix

theorem sp44_commutator_eq (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    ⁅StatedSp 2 K, StatedSp 2 K⁆ = StatedSp 2 K := by
  have := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := ⟨Finset.univ, by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]⟩
  have hp := CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 K (Or.inl h4)
  exact Subgroup.isPerfect_iff.1 hp

theorem sp44RankInput : Sp44RankInput := by
  intro I _ _ _ H' hnat A hA hnorm hex
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨φ, ψ, hψ⟩ := hnat
  have hcomm := sp44_commutator_eq (GaloisField 2 2) hK
  have hsurj : ∀ g : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2), g ∈ StatedSp 2 (GaloisField 2 2) →
      ∃ h : H', ((φ h : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2))) = g := by
    intro g hg
    have hg' : g ∈ ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ := by
      rw [hcomm]
      exact hg
    obtain ⟨h, hh⟩ := φ.surjective ⟨g, hg'⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  let Ψ : GLV I →* Equiv.Perm (Fin 2 ⊕ Fin 2 → GaloisField 2 2) :=
    { toFun := fun g => ψ.symm.toEquiv.trans (g.toEquiv.trans ψ.toEquiv)
      map_one' := by
        ext v
        simp
      map_mul' := fun g h => by
        ext v
        simp }
  have hΨ : ∀ (g : GLV I) v, Ψ g v = ψ (g (ψ.symm v)) := fun g v => rfl
  have hΨinj : Function.Injective Ψ := by
    intro g g' h
    apply LinearEquiv.ext
    intro u
    have := congrArg (fun m : Equiv.Perm (Fin 2 ⊕ Fin 2 → GaloisField 2 2) => m (ψ u)) h
    simp only [hΨ, LinearEquiv.symm_apply_apply] at this
    exact ψ.injective this
  obtain ⟨hAcomm, hAsq⟩ := hA
  have hcommA : ∀ g h : GLV I, g ∈ A → h ∈ A → g * h = h * g := fun g h hg hh =>
    congrArg Subtype.val (hAcomm.is_comm.comm (⟨g, hg⟩ : A) ⟨h, hh⟩)
  have hsqA : ∀ g : GLV I, g ∈ A → g * g = 1 := fun g hg => by
    rw [← sq]
    exact hAsq g hg
  obtain ⟨α, hαA, f, hfE, hne⟩ := hex
  have hcentr : ∀ h ∈ H', ∀ u, h (f u) = f (h u) := by
    intro h hh u
    have := (Subalgebra.mem_centralizer_iff _).1 hfE (h : I →ₗ[ZMod 2] I) ⟨h, hh, rfl⟩
    have := congrArg (fun m : Module.End (ZMod 2) I => m u) this
    exact this
  let f' : (Fin 2 ⊕ Fin 2 → GaloisField 2 2) →+ (Fin 2 ⊕ Fin 2 → GaloisField 2 2) :=
    AddMonoidHom.mk' (fun v => ψ (f (ψ.symm v))) (fun v w => by simp [map_add])
  have hf'apply : ∀ v, f' v = ψ (f (ψ.symm v)) := fun v => rfl
  have hf' : ∀ g : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2), g ∈ StatedSp 2 (GaloisField 2 2) → ∀ v,
      f' ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) *ᵥ v) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) *ᵥ f' v := by
    intro g hg v
    obtain ⟨h, rfl⟩ := hsurj g hg
    obtain ⟨u, rfl⟩ := ψ.surjective v
    rw [hf'apply, hf'apply, LinearEquiv.symm_apply_apply, ← hψ h u, LinearEquiv.symm_apply_apply,
      ← hψ h (f u), hcentr h h.2 u]
  have hne' : ∃ v, Ψ α (f' v) ≠ f' (Ψ α v) := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply LinearMap.ext
    intro u
    have := hcon (ψ u)
    simp only [hΨ, hf'apply, LinearEquiv.symm_apply_apply] at this
    exact ψ.injective this
  have hcardA : Nat.card A = Nat.card (A.map Ψ) :=
    Nat.card_congr (Subgroup.equivMapOfInjective A Ψ hΨinj).toEquiv
  have hcore := sp44_core hK (A.map Ψ) ?_ ?_ ?_ ?_ (Ψ α) (Subgroup.mem_map_of_mem Ψ hαA) f' hf' hne'
  · rw [hcardA]
    simpa using hcore
  · rintro a ha v w
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
    simp [hΨ, map_add]
  · rintro a ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_mul, hsqA g hg, map_one]
  · rintro a b ha hb
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_mul, ← map_mul, hcommA g h hg hh]
  · rintro a ha g hg
    obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨h, rfl⟩ := hsurj g hg
    have hh' : β * (h : GLV I) * β⁻¹ ∈ H' := hnorm β hβ h h.2
    refine ⟨(φ ⟨β * h * β⁻¹, hh'⟩ : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2)), ?_, ?_⟩
    · exact hcomm.le (φ ⟨β * h * β⁻¹, hh'⟩).2
    · intro v
      obtain ⟨u, rfl⟩ := ψ.surjective v
      rw [← hψ h u, hΨ, hΨ, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
        ← hψ ⟨β * h * β⁻¹, hh'⟩ (β u)]
      simp

end G118

end G11

end CFSG.Quasithin
