module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open Equiv

private def shift (v : Fin 5 → ZMod 2) : Perm (Fin 5 × ZMod 2) where
  toFun p := (p.1, p.2 + v p.1)
  invFun p := (p.1, p.2 + v p.1)
  left_inv p := by
    have h : v p.1 + v p.1 = 0 := CharTwo.add_self_eq_zero (v p.1)
    simp only [add_assoc, h, add_zero]
  right_inv p := by
    have h : v p.1 + v p.1 = 0 := CharTwo.add_self_eq_zero (v p.1)
    simp only [add_assoc, h, add_zero]

private theorem shift_zero : shift 0 = 1 := by
  ext p <;> simp [shift, Pi.zero_apply]

private theorem shift_add (v w : Fin 5 → ZMod 2) : shift v * shift w = shift (v + w) := by
  ext p <;> simp [shift, Pi.add_apply] <;> abel

private theorem shift_sq (v : Fin 5 → ZMod 2) : shift v * shift v = 1 := by
  rw [shift_add]
  have hv : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [hv, shift_zero]

private theorem shift_inj {v : Fin 5 → ZMod 2} (h : shift v = 1) : v = 0 := by
  funext i
  have hp := congrArg (fun σ : Perm (Fin 5 × ZMod 2) => σ (i, 0)) h
  simpa [shift] using hp

private def t : Perm (Fin 5 × ZMod 2) where
  toFun p := (finRotate 5 p.1, p.2)
  invFun p := ((finRotate 5).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

private theorem sign_shift (v : Fin 5 → ZMod 2) (hv : ∑ i, v i = 0) :
    Equiv.Perm.sign (shift v) = 1 := by
  revert v
  decide +kernel

private theorem sign_t : Equiv.Perm.sign t = 1 := by
  decide +kernel

private theorem conj_shift_inv : ∀ (v : Fin 5 → ZMod 2),
    t⁻¹ * shift v * t = shift (fun i => v (finRotate 5 i)) := by
  decide +kernel

private theorem conj_shift : ∀ (v : Fin 5 → ZMod 2),
    t * shift v * t⁻¹ = shift (fun i => v ((finRotate 5).symm i)) := by
  decide +kernel

private theorem conj_fixed : ∀ (k : Fin 4) (v : Fin 5 → ZMod 2), (∑ i, v i = 0) →
    t ^ (k.val + 1) * shift v * (t ^ (k.val + 1))⁻¹ = shift v → v = 0 := by
  decide +kernel

private def S0 : Subgroup (Perm (Fin 5 × ZMod 2)) where
  carrier := {g | ∃ v : Fin 5 → ZMod 2, (∑ i, v i = 0) ∧ g = shift v}
  one_mem' := ⟨0, by simp, shift_zero.symm⟩
  mul_mem' := by
    rintro a b ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, by simp [Finset.sum_add_distrib, hv, hw], shift_add v w⟩
  inv_mem' := by
    rintro a ⟨v, hv, rfl⟩
    exact ⟨v, hv, inv_eq_of_mul_eq_one_right (shift_sq v)⟩

private def altS : Subgroup (alternatingGroup (Fin 5 × ZMod 2)) :=
  S0.subgroupOf (alternatingGroup (Fin 5 × ZMod 2))

private theorem mem_altS {g : alternatingGroup (Fin 5 × ZMod 2)} :
    g ∈ altS ↔ ∃ v : Fin 5 → ZMod 2,
      (∑ i, v i = 0) ∧ (g : Perm (Fin 5 × ZMod 2)) = shift v :=
  Iff.rfl

private def vTwo : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

private theorem sum_vTwo : ∑ i, vTwo i = 0 := by
  decide +kernel

private theorem vTwo_ne_zero : vTwo ≠ 0 := by
  decide +kernel

private theorem shift_vTwo_ne_one : shift vTwo ≠ 1 :=
  fun h => vTwo_ne_zero (shift_inj h)

private theorem fixedFreeFive_prod : FixedFreeFive 2 (alternatingGroup (Fin 5 × ZMod 2)) := by
  refine ⟨altS, ?_, ?_, ?_, ⟨t, sign_t⟩, ?_, ?_⟩
  · intro s
    obtain ⟨v, hv, hsv⟩ := mem_altS.mp s.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show (s.1.1 : Perm _) ^ (2 ^ 1) = 1
    rw [pow_one, hsv, pow_two, shift_sq]
  · intro hbot
    have hle : altS ≤ ⊥ := by rw [hbot]
    let s : altS := ⟨⟨shift vTwo, sign_shift vTwo sum_vTwo⟩, by
      rw [mem_altS]
      exact ⟨vTwo, sum_vTwo, rfl⟩⟩
    have hs1 : s = 1 := Subtype.ext (Subgroup.mem_bot.mp (hle s.2))
    have hshift : shift vTwo = 1 := by
      simpa [s] using congrArg (fun x : altS => (x.1.1 : Perm _)) hs1
    exact shift_vTwo_ne_one hshift
  · intro a ha b hb
    obtain ⟨v, hv, hav⟩ := mem_altS.mp ha
    obtain ⟨w, hw, hbw⟩ := mem_altS.mp hb
    apply Subtype.ext
    change (a.1 : Perm (Fin 5 × ZMod 2)) * b.1 = b.1 * a.1
    rw [hav, hbw, shift_add, shift_add]
    congr 1
    exact add_comm v w
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨v, hv, hhv⟩ := mem_altS.mp hh
      rw [mem_altS]
      refine ⟨fun i => v ((finRotate 5).symm i), ?_, ?_⟩
      · rw [Equiv.sum_comp (finRotate 5).symm v]
        exact hv
      · show t * (h : Perm _) * t⁻¹ = shift (fun i => v ((finRotate 5).symm i))
        rw [hhv]
        exact conj_shift v
    · intro hh
      obtain ⟨w, hw, hhw⟩ := mem_altS.mp hh
      rw [mem_altS]
      refine ⟨fun i => w (finRotate 5 i), ?_, ?_⟩
      · rw [Equiv.sum_comp (finRotate 5) w]
        exact hw
      · have hh' : t * (h : Perm _) * t⁻¹ = shift w := by
          simpa using hhw
        show (h : Perm _) = shift (fun i => w (finRotate 5 i))
        calc (h : Perm _) = t⁻¹ * (t * (h : Perm _) * t⁻¹) * t := by group
          _ = t⁻¹ * shift w * t := by rw [hh']
          _ = shift (fun i => w (finRotate 5 i)) := conj_shift_inv w
  · intro k hk0 hk5 s hs hfix
    obtain ⟨v, hv, hsv⟩ := mem_altS.mp hs
    apply Subtype.ext
    have h : t ^ k * shift v * (t ^ k)⁻¹ = shift v := by
      have hc := congrArg (fun x : alternatingGroup _ => (x.1 : Perm _)) hfix
      simpa only [hsv, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv] using hc
    have hklt : k - 1 < 4 := by omega
    let k' : Fin 4 := ⟨k - 1, hklt⟩
    have hk_eq : k = k'.val + 1 := by simp [k']; omega
    rw [hk_eq] at h
    have hv0 := conj_fixed k' v hv h
    rw [hsv, hv0, shift_zero]
    rfl

private noncomputable def altMulEquiv :
    alternatingGroup (Fin 5 × ZMod 2) ≃* alternatingGroup (Fin 10) :=
  Equiv.altCongrHom (Fintype.equivFinOfCardEq (by simp))

private noncomputable def altEmb {n : ℕ} (hn : 10 ≤ n) :
    alternatingGroup (Fin 10) →* alternatingGroup (Fin n) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)).comp
    (alternatingGroup (Fin 10)).subtype).codRestrict _ (by
      intro a
      rw [Equiv.Perm.mem_alternatingGroup, MonoidHom.comp_apply, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
      exact Equiv.Perm.mem_alternatingGroup.mp a.2)

private theorem altEmb_injective {n : ℕ} (hn : 10 ≤ n) : Function.Injective (altEmb hn) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun x : alternatingGroup (Fin n) => (x : Perm (Fin n))) hab
  simp only [altEmb, MonoidHom.codRestrict_apply, MonoidHom.comp_apply] at h
  exact Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn) h

theorem fixedFreeFive_alternatingGroup_ten : FixedFreeFive 2 (alternatingGroup (Fin 10)) :=
  FixedFreeFive.of_mulEquiv altMulEquiv fixedFreeFive_prod

theorem fixedFreeFive_alternatingGroup {n : ℕ} (hn : 10 ≤ n) :
    FixedFreeFive 2 (alternatingGroup (Fin n)) :=
  FixedFreeFive.of_injective (altEmb hn) (altEmb_injective hn) fixedFreeFive_alternatingGroup_ten

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
