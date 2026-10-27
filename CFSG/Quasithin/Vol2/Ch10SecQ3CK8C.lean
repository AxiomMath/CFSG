module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8

open Equiv

theorem card_compl_support_le {σ : Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7))
    (h1 : σ ≠ 1) {k : ℕ} (hk : σ ^ 2 ^ k = 1) : σ.supportᶜ.card ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Perm.card_compl_support_modEq (p := 2) hk
  have hsum : σ.supportᶜ.card + σ.support.card = 7 := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ σ.support
    rw [Fintype.card_fin] at this
    omega
  have h0 : σ.support.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, Perm.support_eq_empty_iff]
    exact h1
  have h1' := Perm.card_support_ne_one σ
  have h2 : σ.support.card ≠ 2 := by
    intro h
    have hs := (Perm.card_support_eq_two.1 h).sign_eq
    rw [Perm.mem_alternatingGroup] at hσ
    rw [hσ] at hs
    exact absurd hs (by decide)
  unfold Nat.ModEq at hmod
  rw [Fintype.card_fin] at hmod
  omega

theorem card_fixedBy_eq {P : Subgroup (Perm (Fin 7))} (g : P) :
    Nat.card (MulAction.fixedBy (Fin 7) g) = (g : Perm (Fin 7)).supportᶜ.card := by
  have hset : MulAction.fixedBy (Fin 7) g = ((g : Perm (Fin 7)).supportᶜ : Finset (Fin 7)) := by
    ext i
    simp [MulAction.mem_fixedBy, Subgroup.smul_def, Perm.smul_def]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem card_orbits_le {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 7)) (h4 : 4 ≤ Nat.card P) :
    Nat.card (Quotient (MulAction.orbitRel P (Fin 7))) ≤ 4 := by
  classical
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P (Fin 7)
  have hle : ∀ g : P, Fintype.card (MulAction.fixedBy (Fin 7) g) ≤
      3 + if g = 1 then 4 else 0 := by
    intro g
    rw [← Nat.card_eq_fintype_card, card_fixedBy_eq]
    split_ifs with hg
    · subst hg
      simp
    · obtain ⟨k, hk⟩ := hP g
      have hk' : (g : Perm (Fin 7)) ^ 2 ^ k = 1 := by
        rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
      have hne : (g : Perm (Fin 7)) ≠ 1 := fun h => hg (Subtype.ext h)
      have := card_compl_support_le (hPA g.2) hne hk'
      omega
  have hsum : ∑ g : P, Fintype.card (MulAction.fixedBy (Fin 7) g) ≤
      3 * Fintype.card P + 4 := by
    calc ∑ g : P, Fintype.card (MulAction.fixedBy (Fin 7) g)
        ≤ ∑ g : P, (3 + if g = 1 then 4 else 0) := Finset.sum_le_sum fun g _ => hle g
      _ = 3 * Fintype.card P + 4 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Finset.sum_ite_eq']
        simp [mul_comm]
  rw [hB] at hsum
  rw [Nat.card_eq_fintype_card] at h4 ⊢
  by_contra hlt
  have h5 : 5 * Fintype.card P ≤
      Fintype.card (Quotient (MulAction.orbitRel P (Fin 7))) * Fintype.card P :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem card_fixVec_le {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 7)) (h4 : 4 ≤ Nat.card P) :
    Nat.card {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i} ≤ 16 := by
  have hΩ := card_orbits_le hP hPA h4
  let f : {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i} →
      (Quotient (MulAction.orbitRel P (Fin 7)) → ZMod 2) := fun x q => x.1 q.out
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hq : (Quotient.mk (MulAction.orbitRel P (Fin 7)) i).out ∈ MulAction.orbit P i :=
      MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq _))
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hq
    have key : ∀ z : {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i},
        f z (Quotient.mk _ i) = z.1 i := by
      intro z
      show z.1 (Quotient.mk (MulAction.orbitRel P (Fin 7)) i).out = z.1 i
      rw [← hg, Subgroup.smul_def, Perm.smul_def]
      have := z.2 (g : Perm (Fin 7))⁻¹ (P.inv_mem g.2) i
      rwa [inv_inv] at this
    rw [← key x, ← key y, hxy]
  calc Nat.card {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i}
      ≤ Nat.card (Quotient (MulAction.orbitRel P (Fin 7)) → ZMod 2) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 ^ Nat.card (Quotient (MulAction.orbitRel P (Fin 7))) := by
        rw [Nat.card_fun, Nat.card_zmod]
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hΩ
    _ = 16 := by norm_num

theorem card_fixVec_even_le {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 7)) (h4 : 4 ≤ Nat.card P) :
    Nat.card {x : Fin 7 → ZMod 2 // (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0} ≤ 8 := by
  have hF := card_fixVec_le hP hPA h4
  let E := {x : Fin 7 → ZMod 2 // (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0}
  let F := {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i}
  have hodd : ∀ y : E, ∑ i, (y.1 + 1) i = 1 := by
    intro y
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, y.2.2]
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide
  let g : E ⊕ E → F := Sum.elim (fun x => ⟨x.1, x.2.1⟩)
    (fun x => ⟨x.1 + 1, fun σ hσ i => by
      simp only [Pi.add_apply, Pi.one_apply]
      rw [x.2.1 σ hσ i]⟩)
  have hg : Function.Injective g := by
    rintro (x | x) (y | y) h
    · have h1 := congrArg Subtype.val h
      exact congrArg Sum.inl (Subtype.ext h1)
    · exfalso
      have h1 : x.1 = y.1 + 1 := congrArg Subtype.val h
      have h2 := hodd y
      rw [← h1, x.2.2] at h2
      exact absurd h2 (by decide)
    · exfalso
      have h1 : x.1 + 1 = y.1 := congrArg Subtype.val h
      have h2 := hodd x
      rw [h1, y.2.2] at h2
      exact absurd h2 (by decide)
    · have h1 : x.1 + 1 = y.1 + 1 := congrArg Subtype.val h
      exact congrArg Sum.inr (Subtype.ext (add_right_cancel h1))
  have h := Nat.card_le_card_of_injective g hg
  rw [Nat.card_sum] at h
  change Nat.card F ≤ 16 at hF
  change Nat.card E ≤ 8
  omega

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
