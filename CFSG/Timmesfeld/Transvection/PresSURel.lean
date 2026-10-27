module

public import CFSG.Timmesfeld.Transvection.PresSUModel

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

structure SURelations (r : ℕ) {F : Type*} [Field F] (σ : F ≃+* F) (G : Type*) [Group G] where
  ξ : Fin r ⊕ Fin r → Fin r ⊕ Fin r → F → G
  ξL : Fin r ⊕ Fin r → F → G
  swap : ∀ a b, idx a ≠ idx b → ∀ c, ξ b a c = ξ a b (σ c)
  add : ∀ a b, idx a ≠ idx b → ∀ s t, ξ a b (s + t) = ξ a b s * ξ a b t
  addL : ∀ a s t, σ s = s → σ t = t → ξL a (s + t) = ξL a s * ξL a t
  short : ∀ a b d, idx a ≠ idx b → idx b ≠ idx d → idx a ≠ idx d → ∀ s t,
    ⁅ξ a b s, ξ (Sum.swap b) d t⁆ = ξ a d (s * t)
  shortLong : ∀ a b, idx a ≠ idx b → ∀ s t, σ t = t →
    ⁅ξ a b s, ξL (Sum.swap b) t⁆ = ξ a (Sum.swap b) (s * t) * ξL a (σ s * s * t)
  trace : ∀ a b, idx a ≠ idx b → ∀ s t,
    ⁅ξ a b s, ξ a (Sum.swap b) t⁆ = ξL a (s * σ t + σ s * t)
  commLL : ∀ a c, c ≠ Sum.swap a → ∀ s t, σ s = s → σ t = t → ⁅ξL a s, ξL c t⁆ = 1
  commLS : ∀ a c d, idx c ≠ idx d → c ≠ Sum.swap a → d ≠ Sum.swap a → ∀ s t, σ s = s →
    ⁅ξL a s, ξ c d t⁆ = 1
  commSS : ∀ a b c d, idx a ≠ idx b → idx c ≠ idx d → c ≠ Sum.swap a → c ≠ Sum.swap b →
    d ≠ Sum.swap a → d ≠ Sum.swap b → ∀ s t, ⁅ξ a b s, ξ c d t⁆ = 1

namespace SURelations

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]
  (R : SURelations r σ G)

@[expose] def eval (e : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) : G :=
  if e.2.1 = e.1 then R.ξL e.1 e.2.2 else R.ξ e.1 e.2.1 e.2.2

@[expose] def evalO : Option ((Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) → G
  | none => 1
  | some e => R.eval e

@[simp] theorem evalO_none : R.evalO none = 1 := rfl

@[simp] theorem evalO_some (e : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) :
    R.evalO (some e) = R.eval e := rfl

theorem eval_long (a : Fin r ⊕ Fin r) (c : F) : R.eval (a, a, c) = R.ξL a c := by
  simp [eval]

theorem eval_short {a b : Fin r ⊕ Fin r} (h : b ≠ a) (c : F) : R.eval (a, b, c) = R.ξ a b c := by
  simp [eval, h]

theorem map_zero {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) : R.ξ a b 0 = 1 := by
  have h := R.add a b hab 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem mapL_zero (a : Fin r ⊕ Fin r) : R.ξL a 0 = 1 := by
  have h := R.addL a 0 0 (_root_.map_zero σ) (_root_.map_zero σ)
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem eq_commutator_trace {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (s : F) :
    R.ξL a (s + σ s) = ⁅R.ξ a b s, R.ξ a (Sum.swap b) 1⁆ := by
  have h := R.trace a b hab s 1
  simp only [map_one, mul_one] at h
  exact h.symm

variable [CharP F 2]

theorem inv_eq {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (c : F) :
    (R.ξ a b c)⁻¹ = R.ξ a b c := by
  have h := R.add a b hab c c
  rw [CharTwo.add_self_eq_zero, R.map_zero hab] at h
  exact inv_eq_of_mul_eq_one_left h.symm

theorem invL_eq (a : Fin r ⊕ Fin r) {c : F} (hc : σ c = c) : (R.ξL a c)⁻¹ = R.ξL a c := by
  have h := R.addL a c c hc hc
  rw [CharTwo.add_self_eq_zero, R.mapL_zero a] at h
  exact inv_eq_of_mul_eq_one_left h.symm

theorem longShort (hσ : ∀ c, σ (σ c) = c) {a d : Fin r ⊕ Fin r} (had : idx a ≠ idx d) {s : F}
    (hs : σ s = s) (t : F) :
    ⁅R.ξL a s, R.ξ (Sum.swap a) d t⁆ = R.ξ a d (s * t) * R.ξL d (s * σ t * t) := by
  have hda : idx d ≠ idx (Sum.swap a) := by rw [idx_swap]; exact had.symm
  have hda' : idx (Sum.swap a) ≠ idx d := hda.symm
  have h := R.shortLong d (Sum.swap a) hda (σ t) s hs
  rw [Sum.swap_swap] at h
  have v2 : a ≠ Sum.swap d := ne_swap_of_idx_ne had.symm
  have v3 : d ≠ Sum.swap a := ne_swap_of_idx_ne had
  have hfix : σ (σ (σ t) * σ t * s) = σ (σ t) * σ t * s := by
    rw [map_mul, map_mul, hσ, hs, mul_comm (σ (σ t)) (σ t), hσ]
  have hcomm : ⁅R.ξ d a (σ t * s), R.ξL d (σ (σ t) * σ t * s)⁆ = 1 := by
    rw [← commutatorElement_inv, R.commLS d d a had.symm (swap_ne_self d).symm v2 _ _ hfix,
      inv_one]
  rw [commutatorElement_eq_one_iff_mul_comm] at hcomm
  calc ⁅R.ξL a s, R.ξ (Sum.swap a) d t⁆ = ⁅R.ξ (Sum.swap a) d t, R.ξL a s⁆⁻¹ := by
        rw [commutatorElement_inv]
    _ = (R.ξ d a (σ t * s) * R.ξL d (σ (σ t) * σ t * s))⁻¹ := by
        rw [← h, R.swap _ _ hda]
    _ = R.ξL d (σ (σ t) * σ t * s) * R.ξ d a (σ t * s) := by
        rw [_root_.mul_inv_rev, R.invL_eq d hfix, R.inv_eq had.symm]
    _ = R.ξ a d (s * t) * R.ξL d (s * σ t * t) := by
        rw [← hcomm, R.swap _ _ had, map_mul, hσ, hs, mul_comm t s,
          show t * σ t * s = s * σ t * t by ring]

theorem eq_commutator_shortLong (hσ : ∀ c, σ (σ c) = c) {a b : Fin r ⊕ Fin r}
    (hab : idx a ≠ idx b) (s : F) :
    R.ξ a (Sum.swap b) s = ⁅R.ξ a b s, R.ξL (Sum.swap b) 1⁆ * R.ξL a (σ s * s) := by
  have hfix : σ (σ s * s) = σ s * s := by rw [map_mul, hσ, mul_comm]
  have h := R.shortLong a b hab s 1 (map_one σ)
  simp only [mul_one] at h
  rw [h, mul_assoc, ← R.addL a _ _ hfix hfix, CharTwo.add_self_eq_zero, R.mapL_zero, mul_one]

end SURelations

@[expose] def RElValid {r : ℕ} {F : Type*} [Field F] (σ : F ≃+* F)
    (e : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) : Prop :=
  e.2.1 ≠ Sum.swap e.1 ∧ (e.2.1 = e.1 → σ e.2.2 = e.2.2)

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) [CharP F 2] (m : ℕ)

@[expose] noncomputable def suRelationsModel : SURelations (m / 2) σ (SU σ m) where
  ξ := suElt σ hσ
  ξL := suLong σ
  swap _ _ hab c := by rw [suElt_swap hσ hab, CharTwo.neg_eq]
  add _ _ _ s t := suElt_add hσ s t
  addL a _ _ hs ht := suLong_add a (add_map_eq_zero_iff.2 hs) (add_map_eq_zero_iff.2 ht)
  short _ _ _ hab hbd had s t := suElt_comm_short hσ hab hbd had s t
  shortLong _ _ hab s _ ht := suElt_comm_shortLong hσ hab s ht
  trace _ _ hab s t := suElt_comm_trace hσ hab s t
  commLL _ _ hca _ _ hs ht := suLong_comm_long hca hs ht
  commLS _ _ _ hcd hca hda _ t hs := suLong_comm_shortGen hσ hcd hca hda hs t
  commSS _ _ _ _ hab hcd hca hcb hda hdb s t := suElt_comm_shortGen hσ hab hcd hca hcb hda hdb s t

theorem suRelationsModel_ξ : (suRelationsModel hσ m).ξ = suElt σ hσ := rfl

theorem suRelationsModel_ξL : (suRelationsModel hσ m).ξL = suLong σ := rfl

end CFSG.Timmesfeld.Transvection
