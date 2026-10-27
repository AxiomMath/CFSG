module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModS18
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.G7.A

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S43.Even
  CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem eq_one_of_fixed (w : orth.W) (h : ∀ σ : Perm (Fin 5), orth.act σ w = w) : w = 1 := by
  have key : ∀ w : orth.W, (∀ σ : Perm (Fin 5), orth.act σ w = w) → w = 1 := by
    decide +kernel
  exact key w h

theorem exists_section (M : Model 5) (hf : M.Faithful) {t : Perm (Fin 5)} (ht : idx M t = 2)
    (π : M.W →* orth.W) (hsurj : Function.Surjective π)
    (hπ : ∀ (σ : Perm (Fin 5)) (m : M.W), π (M.act σ m) = orth.act σ (π m)) :
    ∃ s : orth.W →* M.W, (∀ σ w, s (orth.act σ w) = M.act σ (s w)) ∧ (∀ w, π (s w) = w) ∧
      ∀ m, π m = 1 → ∀ σ, M.act σ m = m := by
  obtain ⟨-, -, -, hcompl, -, -, ⟨e⟩⟩ := S18_model M hf ht
  have hFinv := isInvSub_commW_top M
  set C := fixW M ⊤ with hC
  set F := commW M ⊤ ⊤ with hF
  set ι := EvenMod.restrictIncl M F hFinv with hι
  set τ : orth.W →* orth.W := π.comp (ι.comp e.symm.toMulEquiv.toMonoidHom) with hτ
  have hτapp : ∀ w, τ w = π (ι (e.symm.toMulEquiv w)) := fun w => rfl
  have hes : ∀ x, e.symm.toMulEquiv (e.toMulEquiv x) = x := fun x =>
    e.toMulEquiv.symm_apply_apply x
  have hτact : ∀ σ w, τ (orth.act σ w) = orth.act σ (τ w) := by
    intro σ w
    rw [hτapp, hτapp, e.symm.map_act, EvenMod.restrictIncl_act, hπ]
  have hsup : C ⊔ F = ⊤ := codisjoint_iff.mp hcompl.codisjoint
  have hπC : ∀ c ∈ C, π c = 1 := by
    intro c hc
    apply eq_one_of_fixed
    intro σ
    rw [← hπ, mem_fixW.mp hc σ (Subgroup.mem_top σ)]
  have hdec : ∀ m : M.W, ∃ y ∈ C, ∃ z ∈ F, y * z = m := by
    intro m
    have : m ∈ C ⊔ F := by rw [hsup]; trivial
    exact Subgroup.mem_sup.mp this
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hker : ∀ σ : Perm (Fin 5), ∀ y ∈ τ.ker, orth.act σ y ∈ τ.ker := by
      intro σ y hy
      rw [MonoidHom.mem_ker] at hy ⊢
      rw [hτact, hy, map_one]
    rcases irreducible_orth _ hker with h | h
    · exact h
    · exfalso
      have h1 : ∀ m : M.W, π m = 1 := by
        intro m
        obtain ⟨y, hy, z, hz, rfl⟩ := hdec m
        have hz' : τ (e.toMulEquiv ⟨z, hz⟩) = 1 := by
          rw [← MonoidHom.mem_ker, h]; trivial
        have : π z = 1 := by
          rw [hτapp] at hz'
          erw [hes] at hz'
          exact hz'
        rw [map_mul, hπC y hy, this, one_mul]
      obtain ⟨m, hm⟩ := hsurj (vp 0)
      exact vp_ne_one 0 (hm.symm.trans (h1 m))
  have hτsurj : Function.Surjective τ := Finite.injective_iff_surjective.mp hτinj
  set T : orth.W ≃* orth.W := MulEquiv.ofBijective τ ⟨hτinj, hτsurj⟩ with hT
  have hTapp : ∀ w, T w = τ w := fun w => rfl
  refine ⟨ι.comp (e.symm.toMulEquiv.toMonoidHom.comp T.symm.toMonoidHom), ?_, ?_, ?_⟩
  · intro σ w
    have hTs : T.symm (orth.act σ w) = orth.act σ (T.symm w) := by
      apply T.injective
      rw [MulEquiv.apply_symm_apply, hTapp, hτact, ← hTapp, MulEquiv.apply_symm_apply]
    show ι (e.symm.toMulEquiv (T.symm (orth.act σ w))) =
      M.act σ (ι (e.symm.toMulEquiv (T.symm w)))
    rw [hTs, e.symm.map_act, EvenMod.restrictIncl_act]
  · intro w
    have : τ (T.symm w) = w := by
      rw [← hTapp, MulEquiv.apply_symm_apply]
    rwa [hτapp] at this
  · intro m hm σ
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec m
    rw [map_mul, hπC y hy, one_mul] at hm
    have hz1 : τ (e.toMulEquiv ⟨z, hz⟩) = 1 := by
      rw [hτapp]; erw [hes]; exact hm
    have hz2 : z = 1 := by
      have := hτinj (hz1.trans (map_one τ).symm)
      have := e.toMulEquiv.map_eq_one_iff.mp this
      exact congrArg Subtype.val this
    subst hz2
    rw [mul_one]
    exact mem_fixW.mp hy σ (Subgroup.mem_top σ)

end CFSG.Quasithin.F53.Stellmacher.S35.G7.A
