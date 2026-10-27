module

public import CFSG.Quasithin.H13.AS91Sec8Perm3
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.H13.AS91

theorem perm5_stab2_aux {M X : Type*} [Group M] [Finite X] (hX : Nat.card X = 5)
    (ρ : M →* Equiv.Perm X) (a b : X) (hab : a ≠ b)
    (hfix : ∀ m, ρ m a = a ∧ ρ m b = b)
    (hsurj : ∀ σ : Equiv.Perm X, σ a = a → σ b = b → ∃ m, ρ m = σ) :
    derivedSeries M 2 ≤ ρ.ker ∧
      ∀ P : Subgroup M, P.Normal → IsPGroup 2 P → P ≤ ρ.ker := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hpres : ∀ (m : M) (x : X), (ρ m x ≠ a ∧ ρ m x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
    intro m x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h]; exact (hfix m).1),
        fun h => h2 (by rw [h]; exact (hfix m).2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 ((ρ m).injective (h.trans (hfix m).1.symm)),
        fun h => h2 ((ρ m).injective (h.trans (hfix m).2.symm))⟩
  let ψ : M →* Equiv.Perm {q : X // q ≠ a ∧ q ≠ b} :=
    MonoidHom.mk' (fun m => (ρ m).subtypePerm (p := fun q : X => q ≠ a ∧ q ≠ b) (hpres m))
      (by
        intro m n
        refine Equiv.ext fun q => Subtype.ext ?_
        show ρ (m * n) q.1 = ρ m (ρ n q.1)
        rw [map_mul, Equiv.Perm.mul_apply])
  have hψapply : ∀ (m : M) (q : {q : X // q ≠ a ∧ q ≠ b}), (ψ m q).1 = ρ m q.1 :=
    fun _ _ => rfl
  have hker : ∀ m, ψ m = 1 → ρ m = 1 := by
    intro m hm
    ext q
    by_cases ha : q = a
    · rw [ha, Equiv.Perm.one_apply, (hfix m).1]
    by_cases hb : q = b
    · rw [hb, Equiv.Perm.one_apply, (hfix m).2]
    have hq : q ≠ a ∧ q ≠ b := ⟨ha, hb⟩
    have h2 : ψ m ⟨q, hq⟩ = ⟨q, hq⟩ := by
      rw [hm, Equiv.Perm.one_apply]
    have h3 : ρ m q = q := by
      have := congrArg Subtype.val h2
      rw [hψapply] at this
      exact this
    rw [Equiv.Perm.one_apply, h3]
  have hψsurj : Function.Surjective ψ := by
    intro τ
    obtain ⟨m, hm⟩ := hsurj (Equiv.Perm.ofSubtype τ)
      (Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun h => h.1 rfl))
      (Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun h => h.2 rfl))
    refine ⟨m, Equiv.ext fun q => Subtype.ext ?_⟩
    rw [hψapply, hm, Equiv.Perm.ofSubtype_apply_of_mem τ q.2]
  have hcard : Fintype.card {q : X // q ≠ a ∧ q ≠ b} = 3 := by
    have h1 : Fintype.card {q : X // q ≠ a ∧ q ≠ b} = (Finset.univ \ {a, b}).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext q
      simp
    rw [h1, Finset.card_univ_diff, Finset.card_pair hab, ← Nat.card_eq_fintype_card, hX]
  have hψ2 : derivedSeries (Equiv.Perm {q : X // q ≠ a ∧ q ≠ b}) 2 = ⊥ :=
    perm3_derivedSeries_two hcard
  refine ⟨?_, fun P hPn hPp => ?_⟩
  ·
    intro x hx
    apply MonoidHom.mem_ker.2
    apply hker x
    have hle : (derivedSeries M 2).map ψ ≤
        derivedSeries (Equiv.Perm {q : X // q ≠ a ∧ q ≠ b}) 2 :=
      map_derivedSeries_le_derivedSeries (f := ψ) 2
    rw [hψ2] at hle
    exact Subgroup.mem_bot.1 (hle (Subgroup.mem_map_of_mem ψ hx))
  ·
    haveI : (P.map ψ).Normal := hPn.map ψ hψsurj
    have hbot : P.map ψ = ⊥ :=
      perm3_eq_bot_of_normal_pGroup hcard (P.map ψ) (hPp.map ψ)
    intro x hx
    have hmem : ψ x ∈ P.map ψ := Subgroup.mem_map_of_mem ψ hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.2 (hker x hmem)

end CFSG.Quasithin.H13.AS91
