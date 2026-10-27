module

public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.Monster

theorem eq_one_of_fourGroup_fixedPointFree {N E : Type*} [Group N] [Finite N] [Group E]
    (hE : Nat.card E = 4) (hexp : ∀ e : E, e * e = 1) (φ : E →* MulAut N)
    (hfree : ∀ e : E, e ≠ 1 → ∀ n : N, φ e n = n → n = 1) (n : N) : n = 1 := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have := Fintype.ofFinite E
  have hcard : 1 < ((Finset.univ : Finset E).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hE]
    norm_num
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.1 hcard
  have he1 : e ≠ 1 := (Finset.mem_erase.1 he).1
  have hf1 : f ≠ 1 := (Finset.mem_erase.1 hf).1
  have hinv : ∀ x : E, x ≠ 1 → ∀ m : N, φ x m = m⁻¹ := by
    intro x hx m
    have hfp : MonoidHom.FixedPointFree (φ x) := fun g hg => hfree x hx g hg
    have hinvol : Function.Involutive (φ x) := by
      intro g
      rw [← MulAut.mul_apply, ← map_mul, hexp x, map_one, MulAut.one_apply]
    rw [hfp.coe_eq_inv_of_involutive hinvol]
  have hef1 : e * f ≠ 1 := by
    intro h
    apply hef
    have : e = f⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right (hexp f)]
  apply hfree (e * f) hef1 n
  rw [map_mul, MulAut.mul_apply, hinv f hf1, hinv e he1, inv_inv]

theorem eq_bot_of_inf_centralizer_eq_bot {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : Nat.card E = 4) (hexp : ∀ e ∈ E, e * e = 1) {z : G}
    (hconj : ∀ e ∈ E, e ≠ 1 → IsConj z e) {N : Subgroup G} [hN : N.Normal]
    (hNH : N ⊓ Subgroup.centralizer {z} = ⊥) : N = ⊥ := by
  let φ : E →* MulAut N := (MulAut.conjNormal (H := N)).comp E.subtype
  have hφ : ∀ (e : E) (n : N), ((φ e n : N) : G) = (e : G) * n * (e : G)⁻¹ := fun e n => by
    simp [φ, MulAut.conjNormal_apply]
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  have key := eq_one_of_fourGroup_fixedPointFree (N := N) (E := E) hE
    (fun e => Subtype.ext (hexp e e.2)) φ ?_ ⟨n, hn⟩
  · exact congrArg Subtype.val key
  intro e he1 m hm
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj e e.2 he1')
  have hme : (e : G) * m * (e : G)⁻¹ = m := by rw [← hφ e m, hm]
  have hmem : c⁻¹ * (m : G) * c ∈ N ⊓ Subgroup.centralizer {z} := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa using hN.conj_mem m m.2 c⁻¹
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (e : G) * m = m * e := by
        calc (e : G) * m = (e : G) * m * (e : G)⁻¹ * e := by group
          _ = m * e := by rw [hme]
      rw [← hc] at h1
      calc c⁻¹ * (m : G) * c * z = c⁻¹ * (m * (c * z * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z * c⁻¹) * m) * c := by rw [h1]
        _ = z * (c⁻¹ * (m : G) * c) := by group
  rw [hNH, Subgroup.mem_bot] at hmem
  apply Subtype.ext
  change (m : G) = 1
  calc (m : G) = c * (c⁻¹ * m * c) * c⁻¹ := by group
    _ = 1 := by rw [hmem]; group

end CFSG.Monster
