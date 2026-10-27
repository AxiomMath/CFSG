module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.Quasithin.S1567

variable {U : Type*} [CommGroup U]

@[expose] def fixSub (σ : U ≃* U) : Subgroup U where
  carrier := {u | σ u = u}
  one_mem' := map_one σ
  mul_mem' := fun {a b} ha hb => by
    show σ (a * b) = a * b
    rw [map_mul, show σ a = a from ha, show σ b = b from hb]
  inv_mem' := fun {a} ha => by
    show σ a⁻¹ = a⁻¹
    rw [map_inv, show σ a = a from ha]

@[expose] def formMap (ε : U ≃* U) (W : Subgroup U) : W × W →* U where
  toFun p := (p.1 : U) * ε (p.2 : U)
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
    ac_rfl

theorem formMap_apply (ε : U ≃* U) (W : Subgroup U) (p : W × W) :
    formMap ε W p = (p.1 : U) * ε (p.2 : U) := rfl

@[expose] def normW (ω : U ≃* U) : U →* U :=
  MonoidHom.mk' (fun u => u * ω u * ω (ω u)) (by
    intro a b
    simp only [map_mul]
    ac_rfl)

theorem normW_apply (ω : U ≃* U) (u : U) : normW ω u = u * ω u * ω (ω u) := rfl

theorem normW_comp (ω : U ≃* U) (h3 : ∀ u, ω (ω (ω u)) = u) (u : U) :
    normW ω (ω u) = normW ω u := by
  simp only [normW_apply, h3]
  ac_rfl

theorem normW_pow_apply (ω : MulAut U) (h3 : ∀ u, ω (ω (ω u)) = u) (u : U) (i : ℕ) :
    normW ω ((ω ^ i) u) = normW ω u := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', MulAut.mul_apply, normW_comp ω h3, ih]

theorem normW_eq_one_of_generated (hU : ∀ u : U, u ^ 2 = 1) (ω : MulAut U)
    (h3 : ∀ u, ω (ω (ω u)) = u) (S : Set U) (hS : ∀ u ∈ S, ∃ (v : U) (i : ℕ), u = v * (ω ^ i) v)
    (hgen : Subgroup.closure S = ⊤) (u : U) : normW ω u = 1 := by
  have hle : Subgroup.closure S ≤ (normW ω).ker := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨v, i, rfl⟩ := hS x hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, normW_pow_apply ω h3, ← sq]
    exact hU _
  have hu : u ∈ Subgroup.closure S := by
    rw [hgen]
    exact Subgroup.mem_top u
  exact MonoidHom.mem_ker.mp (hle hu)

section Form

variable (hU : ∀ u : U, u ^ 2 = 1) (ε σ : U ≃* U)
  (hnorm : ∀ u, u * ε u * ε (ε u) = 1) (hε3 : ∀ u, ε (ε (ε u)) = u)
  (hσε : ∀ u, σ (ε u) = ε (ε (σ u)))

include hU hnorm hε3 hσε

theorem formMap_injective : Function.Injective (formMap ε (fixSub σ)) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  rintro ⟨a, b⟩ hab
  have h1 : (a : U) * ε (b : U) = 1 := hab
  have hεb : ε (b : U) = (a : U)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have ha : σ (a : U) = a := a.2
  have hb : σ (b : U) = b := b.2
  have hσεb : σ (ε (b : U)) = ε (b : U) := by
    rw [hεb, map_inv, ha]
  rw [hσε, hb] at hσεb
  have h3 : (b : U) = ε (b : U) := by
    have := congrArg ε hσεb
    rw [hε3] at this
    exact this.trans hσεb
  have hb1 : (b : U) = 1 := by
    have := hnorm (b : U)
    rw [← h3, ← h3] at this
    have h2 := hU (b : U)
    rw [pow_two] at h2
    calc (b : U) = (b : U) * ((b : U) * (b : U)) := by rw [h2, mul_one]
      _ = 1 := by rw [← mul_assoc]; exact this
  have ha1 : (a : U) = 1 := by
    have : (a : U) * ε (b : U) = 1 := h1
    rw [hb1, map_one, mul_one] at this
    exact this
  exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)

omit hε3 in
theorem formMap_surjective (hσ2 : ∀ x, σ (σ x) = x) : Function.Surjective (formMap ε (fixSub σ)) := by
  intro u
  have haW : u * σ u ∈ fixSub σ := by
    show σ (u * σ u) = u * σ u
    rw [map_mul, hσ2, mul_comm]
  have hcW : ε u * σ (ε u) ∈ fixSub σ := by
    show σ (ε u * σ (ε u)) = ε u * σ (ε u)
    rw [map_mul, hσ2, mul_comm]
  refine ⟨(⟨(u * σ u) * (ε u * σ (ε u)), (fixSub σ).mul_mem haW hcW⟩, ⟨u * σ u, haW⟩), ?_⟩
  rw [formMap_apply]
  have h2 : ε u * ε u = 1 := by
    have := hU (ε u)
    rwa [pow_two] at this
  have h3 := hnorm (σ u)
  show (u * σ u) * (ε u * σ (ε u)) * ε (u * σ u) = u
  rw [map_mul, hσε]
  have e : (u * σ u) * (ε u * ε (ε (σ u))) * (ε u * ε (σ u)) =
      u * (σ u * ε (σ u) * ε (ε (σ u))) * (ε u * ε u) := by ac_rfl
  rw [e, h3, h2]
  simp

theorem formMap_bijective (hσ2 : ∀ x, σ (σ x) = x) :
    Function.Bijective (formMap ε (fixSub σ)) :=
  ⟨formMap_injective hU ε σ hnorm hε3 hσε, formMap_surjective hU ε σ hnorm hσε hσ2⟩

theorem card_eq_sq [Finite U] (hσ2 : ∀ x, σ (σ x) = x) :
    Nat.card U = Nat.card (fixSub σ) ^ 2 := by
  have hbij := formMap_bijective hU ε σ hnorm hε3 hσε hσ2
  calc Nat.card U = Nat.card (↥(fixSub σ) × ↥(fixSub σ)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card (fixSub σ) ^ 2 := by rw [Nat.card_prod, sq]

@[expose] def fixSet (S : Set (U ≃* U)) : Subgroup U where
  carrier := {u | ∀ g ∈ S, g u = u}
  one_mem' := fun g _ => map_one g
  mul_mem' := fun {a b} ha hb g hg => by
    show g (a * b) = a * b
    rw [map_mul, show g a = a from ha g hg, show g b = b from hb g hg]
  inv_mem' := fun {a} ha g hg => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, show g a = a from ha g hg]

theorem card_fixSet_eq_sq [Finite U] (hσ2 : ∀ x, σ (σ x) = x) (S : Set (U ≃* U))
    (hS : ∀ g ∈ S, (∀ u, g (ε u) = ε (g u)) ∧ (∀ u, g (σ u) = σ (g u))) :
    Nat.card (fixSet S) = Nat.card (fixSub σ ⊓ fixSet S : Subgroup U) ^ 2 := by
  have hbij := formMap_bijective hU ε σ hnorm hε3 hσε hσ2
  set W := fixSub σ with hW
  set C : Subgroup U := W ⊓ fixSet S with hC
  set C' : Subgroup ↥W := C.subgroupOf W with hC'
  have himg : Subgroup.map (formMap ε W) (C'.prod C') = fixSet S := by
    ext u
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      have ha : (a : U) ∈ fixSet S := (Subgroup.mem_subgroupOf.mp hab.1).2
      have hb : (b : U) ∈ fixSet S := (Subgroup.mem_subgroupOf.mp hab.2).2
      intro g hg
      rw [formMap_apply]
      show g ((a : U) * ε (b : U)) = (a : U) * ε (b : U)
      rw [map_mul, (hS g hg).1, show g (a : U) = a from ha g hg, show g (b : U) = b from hb g hg]
    · intro hu
      obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 u
      have hgW : ∀ g ∈ S, ∀ w : W, g (w : U) ∈ W := by
        intro g hg w
        show σ (g (w : U)) = g (w : U)
        rw [← (hS g hg).2, show σ (w : U) = w from w.2]
      have hfix : ∀ g ∈ S, g (a : U) = a ∧ g (b : U) = b := by
        intro g hg
        have hgab : formMap ε W (⟨g a, hgW g hg a⟩, ⟨g b, hgW g hg b⟩) = formMap ε W (a, b) := by
          rw [hab, formMap_apply]
          show g (a : U) * ε (g (b : U)) = u
          rw [← (hS g hg).1, ← map_mul, show (a : U) * ε (b : U) = u from hab]
          exact hu g hg
        have h2 := hbij.1 hgab
        exact ⟨congrArg (fun p : W × W => (p.1 : U)) h2, congrArg (fun p : W × W => (p.2 : U)) h2⟩
      exact ⟨(a, b), ⟨Subgroup.mem_subgroupOf.mpr ⟨a.2, fun g hg => (hfix g hg).1⟩,
        Subgroup.mem_subgroupOf.mpr ⟨b.2, fun g hg => (hfix g hg).2⟩⟩, hab⟩
  have hCC : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ W)).toEquiv
  rw [← himg, Subgroup.card_map_of_injective hbij.1,
    Nat.card_congr (Subgroup.prodEquiv C' C').toEquiv, Nat.card_prod, hCC, sq]

end Form

end CFSG.Quasithin.S1567
