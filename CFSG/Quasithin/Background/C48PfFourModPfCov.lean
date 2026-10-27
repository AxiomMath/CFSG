module

public import CFSG.Quasithin.Background.F918F2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.Quasithin.JonesParshall

theorem addHom_eq_dotProduct {d : ℕ} (ℓ : (Fin d → ZMod 2) →+ ZMod 2) (x : Fin d → ZMod 2) :
    ℓ x = (fun j => ℓ (Pi.single j 1)) ⬝ᵥ x := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hsc : ∀ (j : Fin d) (c : ZMod 2), ℓ (Pi.single j c) = c * ℓ (Pi.single j 1) := by
    intro j c
    rcases h01 c with rfl | rfl
    · simp
    · simp
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsc j (x j), mul_comm]

variable {W : Type*} [CommGroup W]

theorem exists_section {L : Subgroup W} (hL2 : ∀ u ∈ L, u ^ 2 = 1)
    (q : ↥L →* Multiplicative (Fin 6 → ZMod 2)) (hq : Function.Surjective q) :
    ∃ s : Multiplicative (Fin 6 → ZMod 2) →* ↥L, ∀ y, q (s y) = y := by
  classical
  choose u hu using fun j : Fin 6 => hq (Multiplicative.ofAdd (Pi.single j 1))
  have hpw : ∀ (x : ↥L) (a b : ZMod 2), x ^ (a + b).val = x ^ a.val * x ^ b.val := by
    intro x a b
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hL2 x x.2)
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
    · simp
    · simp
    · simp
    · show x ^ (0 : ℕ) = x ^ 1 * x ^ 1
      rw [← pow_add, hx2, pow_zero]
  refine ⟨{ toFun := fun y => ∏ j, u j ^ (Multiplicative.toAdd y j).val
            map_one' := by simp
            map_mul' := fun y y' => by
              simp only [toAdd_mul, Pi.add_apply, hpw, Finset.prod_mul_distrib] }, fun y => ?_⟩
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_pow, hu]
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  simp only [toAdd_pow, toAdd_ofAdd]
  conv_rhs => rw [← Finset.univ_sum_single (Multiplicative.toAdd y)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]


theorem minors4_inv_mulVec (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (y : Fin 6 → ZMod 2) :
    minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← minors4_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, minors4_one, Matrix.one_mulVec]

theorem minors4_mulVec_inv (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (y : Fin 6 → ZMod 2) :
    minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        y) = y := by
  rw [Matrix.mulVec_mulVec, ← minors4_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, minors4_one, Matrix.one_mulVec]

variable {ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut W} {L : Subgroup W}

@[expose] noncomputable def twist (ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut W)
    (s : Multiplicative (Fin 6 → ZMod 2) →* ↥L) (γ : SpecialLinearGroup (Fin 4) (ZMod 2))
    (y : Fin 6 → ZMod 2) : W :=
  ρ γ ((s (Multiplicative.ofAdd (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y)) : ↥L) : W) * ((s (Multiplicative.ofAdd y) : ↥L) : W)⁻¹

section Twist

variable {Z : Subgroup W} (hLinv : ∀ γ, ∀ u ∈ L, ρ γ u ∈ L) (hZfix : ∀ γ, ∀ w ∈ Z, ρ γ w = w)
  {q : ↥L →* Multiplicative (Fin 6 → ZMod 2)} (hqker : ∀ u : ↥L, q u = 1 ↔ (u : W) ∈ Z)
  (hqe : ∀ (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (u : ↥L) (hu : ρ γ u ∈ L),
    Multiplicative.toAdd (q ⟨ρ γ u, hu⟩) =
      minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (q u))
  {s : Multiplicative (Fin 6 → ZMod 2) →* ↥L} (hs : ∀ y, q (s y) = y)

include hLinv hqker hqe hs in
theorem twist_mem (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (y : Fin 6 → ZMod 2) :
    twist ρ s γ y ∈ Z := by
  set u := s (Multiplicative.ofAdd (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y)) with hu
  have hmem : ρ γ (u : W) ∈ L := hLinv γ _ u.2
  have h1 : q (⟨ρ γ u, hmem⟩ * (s (Multiplicative.ofAdd y))⁻¹) = 1 := by
    rw [map_mul, map_inv, hs]
    apply mul_inv_eq_one.2
    apply Multiplicative.toAdd.injective
    rw [hqe γ u hmem, hu, hs, toAdd_ofAdd, minors4_mulVec_inv, toAdd_ofAdd]
  exact (hqker _).1 h1

theorem twist_add (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (y y' : Fin 6 → ZMod 2) :
    twist ρ s γ (y + y') = twist ρ s γ y * twist ρ s γ y' := by
  have key : ∀ a b c d : W, a * b * (c * d)⁻¹ = a * c⁻¹ * (b * d⁻¹) := by
    intro a b c d
    rw [_root_.mul_inv_rev, mul_comm d⁻¹, mul_mul_mul_comm]
  simp only [twist, Matrix.mulVec_add, ofAdd_add, map_mul, Subgroup.coe_mul]
  exact key _ _ _ _

include hLinv hZfix hqker hqe hs in
theorem twist_mul (γ δ : SpecialLinearGroup (Fin 4) (ZMod 2)) (y : Fin 6 → ZMod 2) :
    twist ρ s (γ * δ) y = twist ρ s γ y * twist ρ s δ (minors4 ((γ⁻¹ :
      SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) := by
  set y' := minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y with hy'
  have hδ : ρ δ ((s (Multiplicative.ofAdd (minors4 ((δ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y')) : ↥L) : W) =
      twist ρ s δ y' * ((s (Multiplicative.ofAdd y') : ↥L) : W) := by
    simp only [twist, inv_mul_cancel_right]
  have hγ : ρ γ ((s (Multiplicative.ofAdd y') : ↥L) : W) =
      twist ρ s γ y * ((s (Multiplicative.ofAdd y) : ↥L) : W) := by
    simp only [twist, hy', inv_mul_cancel_right]
  have hinv : ((γ * δ)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) = δ⁻¹ * γ⁻¹ :=
    _root_.mul_inv_rev γ δ
  have hmv : minors4 (((γ * δ)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y = minors4 ((δ⁻¹ : SpecialLinearGroup (Fin 4)
        (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y' := by
    rw [hinv, Matrix.SpecialLinearGroup.coe_mul, minors4_mul, ← Matrix.mulVec_mulVec]
  have hz := twist_mem hLinv hqker hqe hs δ y'
  have hL : twist ρ s (γ * δ) y = ρ γ (ρ δ ((s (Multiplicative.ofAdd (minors4 ((δ⁻¹ :
      SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y')) : ↥L) :
        W)) * ((s (Multiplicative.ofAdd y) : ↥L) : W)⁻¹ := by
    show ρ (γ * δ) _ * _ = _
    rw [hmv, map_mul, MulAut.mul_apply]
  rw [hL, hδ, map_mul, hZfix γ _ hz, hγ, ← mul_assoc, mul_inv_cancel_right, mul_comm]

end Twist


theorem exists_eq_of_card_two {Z : Subgroup W} (hZ2 : Nat.card Z = 2) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ w ∈ Z, w = 1 ∨ w = z := by
  obtain ⟨⟨z, hz⟩, hz1, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).1 hZ2
  refine ⟨z, hz, fun h => hz1 (Subtype.ext h), fun w hw => ?_⟩
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  · exact Or.inr (congrArg Subtype.val (hu ⟨w, hw⟩ fun h => hw1 (congrArg Subtype.val h)))

theorem pow_val_add {z : W} (hz2 : z ^ 2 = 1) (a b : ZMod 2) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
  · simp
  · simp
  · simp
  · show z ^ (0 : ℕ) = z ^ 1 * z ^ 1
    rw [← pow_add, hz2, pow_zero]

open SteinbergCB.I16 in
theorem cover_fixed_le (hW2 : ∀ w : W, w ^ 2 = 1) {Z : Subgroup W} (hZL : Z ≤ L)
    (hZ2 : Nat.card Z = 2) (hLinv : ∀ γ, ∀ u ∈ L, ρ γ u ∈ L) (hZfix : ∀ γ, ∀ w ∈ Z, ρ γ w = w)
    {q : ↥L →* Multiplicative (Fin 6 → ZMod 2)} (hq : Function.Surjective q)
    (hqker : ∀ u : ↥L, q u = 1 ↔ (u : W) ∈ Z)
    (hqe : ∀ (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (u : ↥L) (hu : ρ γ u ∈ L),
      Multiplicative.toAdd (q ⟨ρ γ u, hu⟩) =
        minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (q u))
    (hcomm : L ≤ Subgroup.closure {c | ∃ γ, ∃ u ∈ L, ρ γ u * u⁻¹ = c})
    (Ys : Fin 3 → SpecialLinearGroup (Fin 4) (ZMod 2)) (σs : Fin 3 → ↥(alternatingGroup (Fin 8)))
    (hσY : ∀ φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2),
      (∀ k, φ (CFSG.ComponentClassification.PresentationLocal.carmichaelCycle k) =
        CFSG.GH74.Exceptional.l42Gen k) →
      ∀ i, φ (σs i) = Matrix.SpecialLinearGroup.toGL (Ys i))
    (hcheck : ∀ w : Fin 6 → ZMod 2,
      (∀ i, minors4 ((Ys i : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w) →
      (∀ i, (alt8WedgeBInv *ᵥ coords8.f0 0 ((σs i : ↥(alternatingGroup (Fin 8))) :
        Equiv.Perm (Fin 8))) ⬝ᵥ w = 0) → w = 0)
    {v : W} (hv : v ∈ L) (hfix : ∀ i, ρ (Ys i) v = v) : v ∈ Z := by
  classical
  obtain ⟨z, hz, hz1, hZ⟩ := exists_eq_of_card_two hZ2
  have hz2 : z ^ 2 = 1 := hW2 z
  have hL2 : ∀ u ∈ L, u ^ 2 = 1 := fun u _ => hW2 u
  obtain ⟨s, hs⟩ := exists_section hL2 q hq
  let toZ : W → ZMod 2 := fun w => if w = 1 then 0 else 1
  have hzz : z * z = 1 := by rw [← pow_two, hz2]
  have htoZ1 : toZ 1 = 0 := by simp [toZ]
  have htoZz : toZ z = 1 := by simp [toZ, hz1]
  have htoZ : ∀ a ∈ Z, ∀ b ∈ Z, toZ (a * b) = toZ a + toZ b := by
    intro a ha b hb
    rcases hZ a ha with h | h <;> rcases hZ b hb with h' | h' <;> rw [h, h']
    · simp [htoZ1]
    · simp [htoZ1]
    · simp [htoZ1]
    · rw [hzz, htoZ1, htoZz]
      decide
  have hzpow : ∀ w ∈ Z, w = z ^ (toZ w).val := by
    intro w hw
    rcases hZ w hw with h | h <;> rw [h]
    · simp [htoZ1]
    · rw [htoZz]
      show z = z ^ 1
      rw [pow_one]
  have htw := twist_mem (ρ := ρ) hLinv hqker hqe hs
  let ℓ : SpecialLinearGroup (Fin 4) (ZMod 2) → (Fin 6 → ZMod 2) →+ ZMod 2 := fun γ =>
    { toFun := fun y => toZ (twist ρ s γ y)
      map_zero' := by simp [toZ, twist]
      map_add' := fun y y' => by
        rw [twist_add]
        exact htoZ _ (htw γ y) _ (htw γ y') }
  have hℓ : ∀ γ y, (ℓ γ) y = toZ (twist ρ s γ y) := fun γ y => rfl
  let fv : SpecialLinearGroup (Fin 4) (ZMod 2) → Fin 6 → ZMod 2 := fun γ j =>
    ℓ γ (Pi.single j 1)
  have hfv : ∀ γ y, toZ (twist ρ s γ y) = fv γ ⬝ᵥ y := fun γ y => by
    rw [← hℓ]
    exact addHom_eq_dotProduct (ℓ γ) y
  have hcoc : ∀ γ δ, fv (γ * δ) = fv γ + (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *ᵥ fv δ := by
    intro γ δ
    funext j
    have h1 := twist_mul hLinv hZfix hqker hqe hs γ δ (Pi.single j 1)
    show toZ (twist ρ s (γ * δ) (Pi.single j 1)) = _
    rw [h1, htoZ _ (htw _ _) _ (htw _ _), hfv δ, Pi.add_apply, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose]
    simp [fv, ℓ, dotProduct_single]
  obtain ⟨φ, hφ⟩ := exists_iso_alt8_carm
  have hdet : ∀ g : GL (Fin 4) (ZMod 2), (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 := by
    intro g
    have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hu (Matrix.GeneralLinearGroup.det g),
      Units.val_one]
  let toSL : GL (Fin 4) (ZMod 2) →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    { toFun := fun g => ⟨(g : Matrix (Fin 4) (Fin 4) (ZMod 2)), hdet g⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun g h => Subtype.ext rfl }
  have htoSL : ∀ γ, toSL (Matrix.SpecialLinearGroup.toGL γ) = γ := fun γ => Subtype.ext rfl
  have hdual : ∀ g : GL (Fin 4) (ZMod 2), alt8WedgeDual g = (minors4 (((toSL g)⁻¹ :
      SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ := by
    intro g
    rw [← map_inv]
    rfl
  let F : ↥(alternatingGroup (Fin 8)) → Fin 6 → ZMod 2 := fun σ =>
    alt8WedgeB *ᵥ fv (toSL (φ σ))
  have hint : ∀ (σ : ↥(alternatingGroup (Fin 8))) (x : Fin 6 → ZMod 2),
      alt8WedgeB *ᵥ (alt8WedgeDual (φ σ) *ᵥ x) = coords8.actA σ (alt8WedgeB *ᵥ x) :=
    alt8WedgeDual_intertwine φ.toMonoidHom hφ
  have hF : F ∈ JonesParshall.Z1A coords8.actA := by
    intro σ τ
    show alt8WedgeB *ᵥ fv (toSL (φ (σ * τ))) =
      alt8WedgeB *ᵥ fv (toSL (φ σ)) + coords8.actA σ (alt8WedgeB *ᵥ fv (toSL (φ τ)))
    rw [map_mul, map_mul, hcoc, Matrix.mulVec_add, ← hint, hdual]
  have hcl := classify_Z1A closure_gens8 cols8_lt act8 rels8_eq (coords8.f0_mem 0) f0_gens8 class8
  have hback : ∀ γ, fv γ = alt8WedgeBInv *ᵥ F (φ.symm (Matrix.SpecialLinearGroup.toGL γ)) := by
    intro γ
    show fv γ = alt8WedgeBInv *ᵥ (alt8WedgeB *ᵥ fv (toSL (φ (φ.symm
      (Matrix.SpecialLinearGroup.toGL γ)))))
    rw [MulEquiv.apply_symm_apply, htoSL, Matrix.mulVec_mulVec, alt8WedgeBInv_mul,
      Matrix.one_mulVec]
  have hbinv : ∀ (σ : ↥(alternatingGroup (Fin 8))) (x : Fin 6 → ZMod 2),
      alt8WedgeBInv *ᵥ coords8.actA σ x = alt8WedgeDual (φ σ) *ᵥ (alt8WedgeBInv *ᵥ x) := by
    intro σ x
    have h1 := hint σ (alt8WedgeBInv *ᵥ x)
    have hBB : alt8WedgeB *ᵥ (alt8WedgeBInv *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, alt8WedgeB_mul_inv, Matrix.one_mulVec]
    rw [hBB] at h1
    rw [← h1, Matrix.mulVec_mulVec, alt8WedgeBInv_mul, Matrix.one_mulVec]
  have hdualγ : ∀ γ, alt8WedgeDual (φ (φ.symm (Matrix.SpecialLinearGroup.toGL γ))) =
      (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ := by
    intro γ
    rw [MulEquiv.apply_symm_apply, hdual, htoSL]
  have hcob : ∀ (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (l w : Fin 6 → ZMod 2),
      minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w →
      ((minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *ᵥ l - l) ⬝ᵥ w = 0 := by
    intro γ l w hw
    have hw' : minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w := by
      conv_lhs => rw [← hw]
      exact minors4_inv_mulVec γ w
    rw [sub_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hw', sub_self]
  rcases hcl F hF with ⟨x, hx⟩ | ⟨x, hx⟩
  ·
    exfalso
    set l := alt8WedgeBInv *ᵥ x with hl
    have hfvl : ∀ γ, fv γ = (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *ᵥ l - l := by
      intro γ
      rw [hback, ← hx]
      show alt8WedgeBInv *ᵥ (coords8.actA _ x - x) = _
      rw [Matrix.mulVec_sub, hbinv, hdualγ]
    have hzL : z ∈ L := hZL hz
    set zL : ↥L := ⟨z, hzL⟩ with hzLdef
    have hzL2 : zL ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    have hqz : q zL = 1 := (hqker zL).2 hz
    let s' : Multiplicative (Fin 6 → ZMod 2) →* ↥L :=
      { toFun := fun y => s y * zL ^ (l ⬝ᵥ Multiplicative.toAdd y).val
        map_one' := by simp
        map_mul' := fun y y' => by
          simp only [map_mul, toAdd_mul, dotProduct_add]
          rw [pow_val_add hzL2, mul_mul_mul_comm] }
    have hs'q : ∀ y, q (s' y) = y := fun y => by
      show q (s y * zL ^ _) = y
      rw [map_mul, map_pow, hqz, one_pow, mul_one, hs]
    have hsub : ∀ a b : ZMod 2, a - b + a = b := by decide
    have hs'eq : ∀ γ (y : Multiplicative (Fin 6 → ZMod 2)), ρ γ ((s' y : ↥L) : W) =
        ((s' (Multiplicative.ofAdd (minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd y)) : ↥L) : W) := by
      intro γ y
      set y₁ := minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd y with hy₁
      have htw1 : twist ρ s γ y₁ =
          ρ γ ((s y : ↥L) : W) * ((s (Multiplicative.ofAdd y₁) : ↥L) : W)⁻¹ := by
        show ρ γ ((s (Multiplicative.ofAdd (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y₁)) : ↥L) : W) * _ = _
        rw [hy₁, minors4_inv_mulVec, ofAdd_toAdd]
      have hval : toZ (twist ρ s γ y₁) = l ⬝ᵥ Multiplicative.toAdd y - l ⬝ᵥ y₁ := by
        rw [hfv, hfvl, sub_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hy₁,
          minors4_inv_mulVec]
      have hρs : ρ γ ((s y : ↥L) : W) = z ^ (l ⬝ᵥ Multiplicative.toAdd y - l ⬝ᵥ y₁).val *
          ((s (Multiplicative.ofAdd y₁) : ↥L) : W) := by
        rw [← hval, ← hzpow _ (htw γ y₁), htw1, inv_mul_cancel_right]
      show ρ γ ((s y * zL ^ (l ⬝ᵥ Multiplicative.toAdd y).val : ↥L) : W) =
        ((s (Multiplicative.ofAdd y₁) * zL ^ (l ⬝ᵥ y₁).val : ↥L) : W)
      rw [Subgroup.coe_mul, map_mul, hρs, Subgroup.coe_pow, map_pow,
        show ((zL : ↥L) : W) = z from rfl, hZfix γ z hz, Subgroup.coe_mul, Subgroup.coe_pow,
        show ((zL : ↥L) : W) = z from rfl,
        mul_comm (z ^ _) ((s (Multiplicative.ofAdd y₁) : ↥L) : W), mul_assoc,
        ← pow_val_add hz2, hsub]
    have hS : L ≤ (s'.range).map L.subtype := by
      refine hcomm.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨γ, u, hu, rfl⟩
      set y := q ⟨u, hu⟩ with hy
      have hc : u * ((s' y : ↥L) : W)⁻¹ ∈ Z := by
        have : q (⟨u, hu⟩ * (s' y)⁻¹) = 1 := by rw [map_mul, map_inv, hs'q, mul_inv_cancel]
        exact (hqker _).1 this
      have hu' : u = ((s' y : ↥L) : W) * (u * ((s' y : ↥L) : W)⁻¹) := by
        rw [mul_comm u, mul_inv_cancel_left]
      refine ⟨s' (Multiplicative.ofAdd (minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        Multiplicative.toAdd y)) * (s' y)⁻¹, ⟨Multiplicative.ofAdd (minors4 (γ : Matrix (Fin 4)
          (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd y) * y⁻¹, by rw [map_mul, map_inv]⟩, ?_⟩
      conv_rhs => rw [hu']
      rw [map_mul (ρ γ), hs'eq, hZfix γ _ hc]
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    obtain ⟨x', ⟨y, rfl⟩, hxz⟩ := hS hzL
    have h1 : s' y = zL := Subtype.ext hxz
    have h2 : y = 1 := by rw [← hs'q y, h1, hqz]
    rw [h2, map_one] at h1
    exact hz1 (congrArg Subtype.val h1).symm
  ·
    set l := alt8WedgeBInv *ᵥ x with hl
    have hfvl : ∀ γ, fv γ = (minors4 ((γ⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *ᵥ l - l + alt8WedgeBInv *ᵥ coords8.f0 0
          ((φ.symm (Matrix.SpecialLinearGroup.toGL γ) : ↥(alternatingGroup (Fin 8))) :
            Equiv.Perm (Fin 8)) := by
      intro γ
      set σ := φ.symm (Matrix.SpecialLinearGroup.toGL γ) with hσdef
      have h1 := congrFun hx σ
      have h2 : F σ = coords8.actA σ x - x + coords8.f0 0 (σ : Equiv.Perm (Fin 8)) :=
        (sub_eq_iff_eq_add.1 h1.symm)
      rw [hback, ← hσdef, h2, Matrix.mulVec_add, Matrix.mulVec_sub, hbinv, hσdef, hdualγ]
    set w := Multiplicative.toAdd (q ⟨v, hv⟩) with hw
    have hwfix : ∀ i, minors4 ((Ys i : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w := by
      intro i
      have h1 := hqe (Ys i) ⟨v, hv⟩ (hLinv _ v hv)
      have h2 : (⟨ρ (Ys i) v, hLinv _ v hv⟩ : ↥L) = ⟨v, hv⟩ := Subtype.ext (hfix i)
      rw [h2] at h1
      exact h1.symm
    have hσ : ∀ i, φ.symm (Matrix.SpecialLinearGroup.toGL (Ys i)) = σs i := fun i => by
      rw [MulEquiv.symm_apply_eq]
      exact (hσY φ hφ i).symm
    have hpair : ∀ i, (alt8WedgeBInv *ᵥ coords8.f0 0 ((σs i : ↥(alternatingGroup (Fin 8))) :
        Equiv.Perm (Fin 8))) ⬝ᵥ w = 0 := by
      intro i
      have hc : v * ((s (Multiplicative.ofAdd w) : ↥L) : W)⁻¹ ∈ Z := by
        have : q (⟨v, hv⟩ * (s (Multiplicative.ofAdd w))⁻¹) = 1 := by
          rw [map_mul, map_inv, hs, hw, ofAdd_toAdd, mul_inv_cancel]
        exact (hqker _).1 this
      have hinvw : minors4 (((Ys i)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w := by
        conv_lhs => rw [← hwfix i]
        exact minors4_inv_mulVec _ w
      have hsfix : ρ (Ys i) ((s (Multiplicative.ofAdd w) : ↥L) : W) =
          ((s (Multiplicative.ofAdd w) : ↥L) : W) := by
        have h1 := hfix i
        have hv' : v = ((s (Multiplicative.ofAdd w) : ↥L) : W) *
            (v * ((s (Multiplicative.ofAdd w) : ↥L) : W)⁻¹) := by
          rw [mul_comm v, mul_inv_cancel_left]
        rw [hv', map_mul, hZfix _ _ hc] at h1
        exact mul_right_cancel h1
      have htw1 : twist ρ s (Ys i) w = 1 := by
        show ρ (Ys i) ((s (Multiplicative.ofAdd (minors4 (((Ys i)⁻¹ :
          SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w)) : ↥L) :
            W) * _ = 1
        rw [hinvw, hsfix, mul_inv_cancel]
      have h0 := hfv (Ys i) w
      rw [htw1, htoZ1, hfvl, add_dotProduct, hcob _ _ _ (hwfix i), zero_add, hσ] at h0
      exact h0.symm
    have hw0 := hcheck w hwfix hpair
    have : q ⟨v, hv⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact hw0
    exact (hqker _).1 this

section Parabolics

open CFSG.ComponentClassification.PresentationLocal CFSG.GH74.Exceptional SteinbergCB.I16

@[expose] def cperm (j : Fin 6) : ↥(alternatingGroup (Fin 8)) :=
  carmichaelCycle ⟨⟨(j : ℕ) + 2, by omega⟩, by simp⟩

theorem phi_cperm (φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    (hφ : ∀ k, φ (carmichaelCycle k) = l42Gen k) (j : Fin 6) : φ (cperm j) = l42Unit j := by
  rw [cperm, hφ]
  show l42Unit (carmichaelIndexToFin6 _) = l42Unit j
  congr 1

theorem phi_wordEval (φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    (hφ : ∀ k, φ (carmichaelCycle k) = l42Gen k) :
    ∀ w : List (Fin 6), φ (wordEval cperm w) = wordEval l42Unit w
  | [] => map_one φ
  | j :: w => by
    show φ (cperm j * wordEval cperm w) = l42Unit j * wordEval l42Unit w
    rw [map_mul, phi_cperm φ hφ, phi_wordEval φ hφ w]

theorem val_wordEval_l42 : ∀ w : List (Fin 6),
    ((wordEval l42Unit w : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      wordEvalM l42Mat w
  | [] => rfl
  | j :: w => by
    show (l42Unit j : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      ((wordEval l42Unit w : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        l42Mat j * wordEvalM l42Mat w
    rw [val_wordEval_l42 w]
    rfl

abbrev tv4 (k l : Fin 4) (h : k ≠ l) : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  SpecialLinearGroup.transvection h (1 : ZMod 2)

@[expose] def Y031 : Fin 3 → SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ![tv4 0 3 (by decide), tv4 1 3 (by decide), tv4 2 3 (by decide)]

@[expose] def Y130 : Fin 3 → SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ![tv4 0 1 (by decide), tv4 0 2 (by decide), tv4 0 3 (by decide)]

@[expose] def W031 : Fin 3 → List (Fin 6) :=
  ![[2, 4, 5, 1, 2, 3, 0, 1], [4, 2, 1, 3, 5, 2, 1, 0], [3, 5, 2, 0, 4, 1, 2, 0]]

@[expose] def W130 : Fin 3 → List (Fin 6) :=
  ![[2, 5, 4, 0, 2, 3, 1, 0], [4, 3, 1, 5, 2, 3, 1, 0], [2, 4, 5, 1, 2, 3, 0, 1]]

theorem wordEvalM_W031 : ∀ i, wordEvalM l42Mat (W031 i) =
    ((Y031 i : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  decide +kernel

theorem wordEvalM_W130 : ∀ i, wordEvalM l42Mat (W130 i) =
    ((Y130 i : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  decide +kernel

@[expose] def v031 : Fin 3 → Fin 6 → ZMod 2 :=
  ![![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 1, 1], ![1, 0, 1, 0, 0, 1]]

@[expose] def v130 : Fin 3 → Fin 6 → ZMod 2 :=
  ![![1, 0, 0, 1, 0, 1], ![0, 1, 0, 0, 1, 1], ![0, 0, 1, 1, 1, 0]]

theorem f0_W031 : ∀ i, alt8WedgeBInv *ᵥ coords8.f0 0 ((wordEval cperm (W031 i) :
    ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) = v031 i := by
  decide +kernel

theorem f0_W130 : ∀ i, alt8WedgeBInv *ᵥ coords8.f0 0 ((wordEval cperm (W130 i) :
    ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) = v130 i := by
  decide +kernel

theorem check031 : ∀ w : Fin 6 → ZMod 2,
    (∀ i, minors4 ((Y031 i : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w) → (∀ i, v031 i ⬝ᵥ w = 0) → w = 0 := by
  decide +kernel

theorem check130 : ∀ w : Fin 6 → ZMod 2,
    (∀ i, minors4 ((Y130 i : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w) → (∀ i, v130 i ⬝ᵥ w = 0) → w = 0 := by
  decide +kernel

variable {Z : Subgroup W} (hW2 : ∀ w : W, w ^ 2 = 1) (hZL : Z ≤ L) (hZ2 : Nat.card Z = 2)
  (hLinv : ∀ γ, ∀ u ∈ L, ρ γ u ∈ L) (hZfix : ∀ γ, ∀ w ∈ Z, ρ γ w = w)
  {q : ↥L →* Multiplicative (Fin 6 → ZMod 2)} (hq : Function.Surjective q)
  (hqker : ∀ u : ↥L, q u = 1 ↔ (u : W) ∈ Z)
  (hqe : ∀ (γ : SpecialLinearGroup (Fin 4) (ZMod 2)) (u : ↥L) (hu : ρ γ u ∈ L),
    Multiplicative.toAdd (q ⟨ρ γ u, hu⟩) =
      minors4 (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (q u))
  (hcomm : L ≤ Subgroup.closure {c | ∃ γ, ∃ u ∈ L, ρ γ u * u⁻¹ = c})

include hW2 hZL hZ2 hLinv hZfix hq hqker hqe hcomm

theorem cover_fixed_031 {v : W} (hv : v ∈ L) (hfix : ∀ i, ρ (Y031 i) v = v) : v ∈ Z :=
  cover_fixed_le hW2 hZL hZ2 hLinv hZfix hq hqker hqe hcomm Y031
    (fun i => wordEval cperm (W031 i))
    (fun φ hφ i => Units.ext (by rw [phi_wordEval φ hφ, val_wordEval_l42, wordEvalM_W031]; rfl))
    (fun w h1 h2 => check031 w h1 fun i => by rw [← f0_W031 i]; exact h2 i) hv hfix

theorem cover_fixed_130 {v : W} (hv : v ∈ L) (hfix : ∀ i, ρ (Y130 i) v = v) : v ∈ Z :=
  cover_fixed_le hW2 hZL hZ2 hLinv hZfix hq hqker hqe hcomm Y130
    (fun i => wordEval cperm (W130 i))
    (fun φ hφ i => Units.ext (by rw [phi_wordEval φ hφ, val_wordEval_l42, wordEvalM_W130]; rfl))
    (fun w h1 h2 => check130 w h1 fun i => by rw [← f0_W130 i]; exact h2 i) hv hfix

end Parabolics

end CFSG.Quasithin.C48Pf.FMod
