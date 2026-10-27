module

public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin

theorem L3.eq_of_basis {f g : L3.Vec → L3.Vec} (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b) (h : ∀ j : Fin 3, f (Pi.single j 1) = g (Pi.single j 1))
    (v : L3.Vec) : f v = g v := by
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hg0 : g 0 = 0 := by
    have := hg 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hs : ∀ j : Fin 3, ∀ a : ZMod 2, f (Pi.single j a) = g (Pi.single j a) := by
    intro j a
    have ha : a = 0 ∨ a = 1 := by revert a; decide
    rcases ha with rfl | rfl
    · rw [Pi.single_zero, hf0, hg0]
    · exact h j
  have hv : v = (Pi.single (0 : Fin 3) (v 0) : L3.Vec) + (Pi.single (1 : Fin 3) (v 1) : L3.Vec) +
      (Pi.single (2 : Fin 3) (v 2) : L3.Vec) := by
    funext i
    fin_cases i <;> simp
  rw [hv, hf, hf, hg, hg, hs, hs, hs]

theorem L3.exists_act_eq {f : L3.Vec → L3.Vec} (hf : ∀ a b, f (a + b) = f a + f b)
    (hinj : Function.Injective f) : ∃ δ : L3.Γ, ∀ v, L3.act δ v = f v := by
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  set M : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => f (Pi.single j 1) i with hM
  have hMv : ∀ v, M.mulVec v = f v := by
    refine L3.eq_of_basis (fun a b => Matrix.mulVec_add M a b) hf fun j => ?_
    funext i
    simp [hM, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdet : M.det = 1 := by
    have hne : M.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      apply hinj
      rw [← hMv, hv, hf0]
    generalize M.det = d at hne ⊢
    revert d
    decide
  exact ⟨⟨M, hdet⟩, fun v => hMv v⟩

theorem L3.fixS_card_le_two : ∀ γ : L3.Γ, γ ≠ 1 → ¬ L3.IsInvol γ → (L3.fixS γ).card ≤ 2 := by
  decide +kernel

theorem L3.eq_top_of_invariant {K : Subgroup (Multiplicative L3.Vec)}
    (hK : ∀ γ : L3.Γ, ∀ v ∈ K, Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd v)) ∈ K)
    (hK1 : K ≠ ⊥) : K = ⊤ := by
  obtain ⟨⟨k, hk⟩, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK1
  have hk0 : Multiplicative.toAdd k ≠ 0 := fun h0 => hk1 (Subtype.ext (by simpa using h0))
  rw [eq_top_iff]
  intro v _
  by_cases hv : Multiplicative.toAdd v = 0
  · have : v = 1 := by simpa using hv
    rw [this]
    exact K.one_mem
  · obtain ⟨γ, hγ⟩ := L3.act_trans _ _ hk0 hv
    have := hK γ k hk
    rwa [hγ, ofAdd_toAdd] at this

section Coord

variable {W : Type*} [CommGroup W] {Gr : Subgroup (MulAut W)} {Z : Subgroup W}

@[expose] def bvec (D : L3Data Gr ⊤ Z) (w : W) : L3.Vec :=
  Multiplicative.toAdd (D.β ⟨w, Subgroup.mem_top w⟩)

theorem bvec_mul (D : L3Data Gr ⊤ Z) (a b : W) : bvec D (a * b) = bvec D a + bvec D b := by
  unfold bvec
  rw [show (⟨a * b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
    ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ from rfl, map_mul, toAdd_mul]

theorem bvec_inv (D : L3Data Gr ⊤ Z) (a : W) : bvec D a⁻¹ = - bvec D a := by
  unfold bvec
  rw [show (⟨a⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
    (⟨a, Subgroup.mem_top _⟩)⁻¹ from rfl, map_inv, toAdd_inv]

theorem bvec_eq_zero_iff (D : L3Data Gr ⊤ Z) (w : W) : bvec D w = 0 ↔ w ∈ Z := by
  unfold bvec
  rw [toAdd_eq_zero]
  exact D.ker_β ⟨w, Subgroup.mem_top w⟩

theorem bvec_surj (D : L3Data Gr ⊤ Z) (v : L3.Vec) : ∃ w, bvec D w = v := by
  obtain ⟨⟨w, hw0⟩, hw⟩ := D.β_surj (Multiplicative.ofAdd v)
  exact ⟨w, by unfold bvec; rw [hw]; rfl⟩

theorem bvec_rho (D : L3Data Gr ⊤ Z) (γ : L3.Γ) (w : W) :
    bvec D (D.rho γ w) = L3.act γ (bvec D w) := by
  unfold bvec
  rw [D.β_rho γ w (Subgroup.mem_top w) (Subgroup.mem_top _)]
  rfl

@[expose] def bhom (D : L3Data Gr ⊤ Z) : W →* Multiplicative L3.Vec where
  toFun w := D.β ⟨w, Subgroup.mem_top w⟩
  map_one' := map_one D.β
  map_mul' a b := map_mul D.β ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩

theorem ker_bhom (D : L3Data Gr ⊤ Z) : (bhom D).ker = Z := by
  ext w
  rw [MonoidHom.mem_ker]
  exact D.ker_β ⟨w, Subgroup.mem_top w⟩

theorem exists_act_of_preserves (D : L3Data Gr ⊤ Z) {x : MulAut W} (hxZ : ∀ z ∈ Z, x z ∈ Z)
    (hxZ' : ∀ z ∈ Z, x⁻¹ z ∈ Z) : ∃ δ : L3.Γ, ∀ w, bvec D (x w) = L3.act δ (bvec D w) := by
  classical
  choose lift hlift using bvec_surj D
  have hdep : ∀ a b : W, bvec D a = bvec D b → bvec D (x a) = bvec D (x b) := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ Z := by
      rw [← bvec_eq_zero_iff D, bvec_mul, bvec_inv, hab]
      exact neg_add_cancel _
    have h2 := hxZ _ h1
    rw [map_mul, map_inv, ← bvec_eq_zero_iff D, bvec_mul, bvec_inv] at h2
    exact neg_add_eq_zero.mp h2
  have hfw : ∀ w, bvec D (x (lift (bvec D w))) = bvec D (x w) := fun w => hdep _ _ (hlift _)
  have hadd : ∀ a b, bvec D (x (lift (a + b))) =
      bvec D (x (lift a)) + bvec D (x (lift b)) := by
    intro a b
    have h1 : bvec D (lift a * lift b) = a + b := by rw [bvec_mul, hlift, hlift]
    rw [← h1, hfw, map_mul, bvec_mul]
  have hinj : Function.Injective fun v => bvec D (x (lift v)) := by
    intro a b hab
    have hab' : bvec D (x (lift a)) = bvec D (x (lift b)) := hab
    have h1 : (x (lift a))⁻¹ * x (lift b) ∈ Z := by
      rw [← bvec_eq_zero_iff D, bvec_mul, bvec_inv, hab']
      exact neg_add_cancel _
    have h2 := hxZ' _ h1
    rw [map_mul, map_inv, MulAut.inv_apply_self, MulAut.inv_apply_self] at h2
    rw [← bvec_eq_zero_iff D, bvec_mul, bvec_inv, hlift, hlift] at h2
    exact neg_add_eq_zero.mp h2
  obtain ⟨δ, hδ⟩ := L3.exists_act_eq hadd hinj
  exact ⟨δ, fun w => by rw [← hfw, ← hδ (bvec D w)]⟩

end Coord

end CFSG.Quasithin.Vol2.Ch10.SecD
