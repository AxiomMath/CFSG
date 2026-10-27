module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Model

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace A7Mod

abbrev pA7 : Subgroup (V7 ≃ₗ[ZMod 2] V7) := (alternatingGroup (Fin 7)).map pAct

@[expose] def StabCount : Prop :=
  ∀ v : V7, Nat.card ↥(pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) v) = 360 ↔ ∃ p, v = f p

theorem card_stabilizer_eq {γ : V7 ≃ₗ[ZMod 2] V7}
    (hγ : γ ∈ Subgroup.normalizer (pA7 : Set (V7 ≃ₗ[ZMod 2] V7))) (v : V7) :
    Nat.card ↥(pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) (γ v)) =
      Nat.card ↥(pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) v) := by
  have h : pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) (γ v) =
      (pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) v).map (MulAut.conj γ).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨hx, hxv⟩
      refine ⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.1 hγ (γ⁻¹ * x * γ)).2
        apply h1
        have e : γ * (γ⁻¹ * x * γ) * γ⁻¹ = x := by group
        rw [e]
        exact hx
      · have hxv' : x (γ v) = γ v := hxv
        change γ.symm (x (γ v)) = v
        rw [hxv', LinearEquiv.symm_apply_apply]
      · show γ * (γ⁻¹ * x * γ) * γ⁻¹ = x
        group
    · rintro ⟨y, ⟨hy, hyv⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hγ y).1 hy, ?_⟩
      have hyv' : y v = v := hyv
      change γ (y (γ.symm (γ v))) = γ v
      rw [LinearEquiv.symm_apply_apply, hyv']
  rw [h, Subgroup.card_map_of_injective (MulAut.conj γ).injective]

theorem eq_pAct_of_mem_normalizer (hK : StabCount) {γ : V7 ≃ₗ[ZMod 2] V7}
    (hγ : γ ∈ Subgroup.normalizer (pA7 : Set (V7 ≃ₗ[ZMod 2] V7))) :
    ∃ π : Equiv.Perm (Fin 7), γ = pAct π := by
  classical
  have hf : ∀ p, ∃ q, γ (f p) = f q := fun p =>
    (hK (γ (f p))).1 ((card_stabilizer_eq hγ (f p)).trans ((hK (f p)).2 ⟨p, rfl⟩))
  choose π hπ using hf
  have hπinj : Function.Injective π := fun p q h =>
    f_injective (γ.injective (by rw [hπ, hπ, h]))
  let πe : Equiv.Perm (Fin 7) := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj)
  refine ⟨πe, LinearEquiv.ext fun x => ?_⟩
  rw [eq_sum_smul_f x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, hπ, pAct_f]
  rfl

theorem eq_map_of_le_normalizer (hK : StabCount) {Γ : Subgroup (V7 ≃ₗ[ZMod 2] V7)}
    (h1 : pA7 ≤ Γ) (h2 : Γ ≤ Subgroup.normalizer (pA7 : Set (V7 ≃ₗ[ZMod 2] V7))) :
    ∃ K : Subgroup (Equiv.Perm (Fin 7)), (K = alternatingGroup (Fin 7) ∨ K = ⊤) ∧
      Γ = K.map pAct := by
  set K := Γ.comap pAct with hKdef
  have hrange : Γ ≤ pAct.range := fun γ hγ => by
    obtain ⟨π, rfl⟩ := eq_pAct_of_mem_normalizer hK (h2 hγ)
    exact ⟨π, rfl⟩
  have hΓ : Γ = K.map pAct := by
    rw [hKdef, Subgroup.map_comap_eq, inf_eq_right.2 hrange]
  refine ⟨K, ?_, hΓ⟩
  have hAK : alternatingGroup (Fin 7) ≤ K := fun σ hσ => by
    rw [hKdef, Subgroup.mem_comap]
    exact h1 ⟨σ, hσ, rfl⟩
  have hdvd : K.index ∣ 2 := by
    have h := Subgroup.index_dvd_of_le hAK
    rwa [alternatingGroup.index_eq_two] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · right
    exact Subgroup.index_eq_one.1 h
  · left
    exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h

end A7Mod

end CFSG.Quasithin.H13
