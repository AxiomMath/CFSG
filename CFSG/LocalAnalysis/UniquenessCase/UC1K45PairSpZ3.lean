module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpZ3Sub
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpRec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {B : LinearMap.BilinForm (ZMod 2) W} {a b : W ≃ₗ[ZMod 2] W}

@[expose] noncomputable def zComp (h : PairHyp B a b) (y : W ≃ₗ[ZMod 2] W) :
    Module.End (ZMod 2) ↥(commSp a) :=
  (commSp a).projectionOnto (B.orthogonal (commSp a))
      (isCompl_commSp_orth h.nondeg h.ha) ∘ₗ (y : W →ₗ[ZMod 2] W) ∘ₗ (commSp a).subtype

theorem zComp_coe (h : PairHyp B a b) (y : W ≃ₗ[ZMod 2] W) (p : commSp a) :
    ((zComp h y p : commSp a) : W) = projP h.nondeg h.ha (y p) :=
  rfl

theorem zComp_one (h : PairHyp B a b) : zComp h 1 = 1 := by
  ext p
  rw [zComp_coe]
  exact projP_of_mem h.nondeg h.ha p.2

theorem sub_projP_mem_pairR (h : PairHyp B a b) {y : W ≃ₗ[ZMod 2] W} (hy : y ∈ zStab B a b)
    {p : W} (hp : p ∈ commSp a) : y p - projP h.nondeg h.ha (y p) ∈ pairR B a b := by
  refine Submodule.mem_inf.mpr ⟨?_, sub_projP_mem h.nondeg h.ha _⟩
  have h1 : y p ∈ pairU a b := by
    have := add_mem ((mem_zStab_iff.mp hy).1 p) (Submodule.mem_sup_left hp : p ∈ pairU a b)
    simpa using this
  exact sub_mem h1 (Submodule.mem_sup_left (projP_mem h.nondeg h.ha _))

theorem zComp_mul (h : PairHyp B a b) {y y' : W ≃ₗ[ZMod 2] W} (hy : y ∈ zStab B a b)
    (hy' : y' ∈ zStab B a b) : zComp h (y * y') = zComp h y * zComp h y' := by
  ext p
  show projP h.nondeg h.ha ((y * y') p) = projP h.nondeg h.ha (y (projP h.nondeg h.ha (y' p)))
  have hrR := sub_projP_mem_pairR h hy' p.2
  have hyr := (mem_zStab_iff.mp hy).2 _ hrR
  have hπr := (projP_eq_zero_iff h.nondeg h.ha).mpr (Submodule.mem_inf.mp hrR).2
  have e : y' p = projP h.nondeg h.ha (y' p) + (y' p - projP h.nondeg h.ha (y' p)) := by abel
  rw [LinearEquiv.mul_apply]
  conv_lhs => rw [e, map_add, hyr, map_add, hπr, add_zero]

theorem zComp_a (h : PairHyp B a b) (p : commSp a) : ((zComp h a p : commSp a) : W) = a p := by
  rw [zComp_coe]
  exact projP_of_mem h.nondeg h.ha (apply_mem_commSp p.2)

theorem zComp_a_sq (h : PairHyp B a b) : zComp h a ^ 2 + zComp h a + 1 = 0 := by
  ext p
  have e : ∀ q : commSp a, ((zComp h a q : commSp a) : W) = a q := zComp_a h
  have := sq_add_add_one h.ha p.2
  simp only [LinearMap.add_apply, pow_two, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_zero, e]
  exact this

theorem sub_mem_pairR_of_zComp_eq_one (h : PairHyp B a b) {y : W ≃ₗ[ZMod 2] W}
    (hy : y ∈ zStab B a b) (h1 : zComp h y = 1) {p : W} (hp : p ∈ commSp a) :
    y p - p ∈ pairR B a b := by
  refine Submodule.mem_inf.mpr ⟨(mem_zStab_iff.mp hy).1 p, ?_⟩
  have hπ : projP h.nondeg h.ha (y p) = p := by
    have := congrArg (fun T : Module.End (ZMod 2) ↥(commSp a) => ((T ⟨p, hp⟩ : commSp a) : W)) h1
    simpa [zComp_coe] using this
  have := sub_projP_mem h.nondeg h.ha (y p)
  rwa [hπ] at this

theorem sub_projP_mem_pairR_of_mem_pairU (h : PairHyp B a b) {u : W} (hu : u ∈ pairU a b) :
    u - projP h.nondeg h.ha u ∈ pairR B a b :=
  Submodule.mem_inf.mpr ⟨sub_mem hu (Submodule.mem_sup_left (projP_mem h.nondeg h.ha u)),
    sub_projP_mem h.nondeg h.ha u⟩

theorem apply_apply_of_zComp_eq_one (h : PairHyp B a b) {y : W ≃ₗ[ZMod 2] W}
    (hy : y ∈ zStab B a b) (h1 : zComp h y = 1) {u : W} (hu : u ∈ pairU a b) :
    y (y u) = u := by
  have hrR := sub_projP_mem_pairR_of_mem_pairU h hu
  have hyr := (mem_zStab_iff.mp hy).2 _ hrR
  have hq := sub_mem_pairR_of_zComp_eq_one h hy h1 (projP_mem h.nondeg h.ha u)
  have hyq := (mem_zStab_iff.mp hy).2 _ hq
  have h2 : y (y (projP h.nondeg h.ha u)) = projP h.nondeg h.ha u := by
    rw [map_sub] at hyq
    calc y (y (projP h.nondeg h.ha u))
        = (y (y (projP h.nondeg h.ha u)) - y (projP h.nondeg h.ha u)) +
            y (projP h.nondeg h.ha u) := by abel
      _ = (y (projP h.nondeg h.ha u) - projP h.nondeg h.ha u) + y (projP h.nondeg h.ha u) := by
          rw [hyq]
      _ = (y (projP h.nondeg h.ha u) + y (projP h.nondeg h.ha u)) - projP h.nondeg h.ha u := by
          abel
      _ = projP h.nondeg h.ha u := by rw [add_self_eq_zero', zero_sub, neg_eq_self']
  have e : u = projP h.nondeg h.ha u + (u - projP h.nondeg h.ha u) := by abel
  conv_lhs => rw [e, map_add, hyr, map_add, hyr, h2]
  exact e.symm

theorem sub_one_cube_eq_zero (h : PairHyp B a b) {y : W ≃ₗ[ZMod 2] W} (hy : y ∈ zStab B a b)
    (h1 : zComp h y = 1) : ((y : W →ₗ[ZMod 2] W) - 1) ^ 3 = 0 := by
  have hN : ∀ v : W, ((y : W →ₗ[ZMod 2] W) - 1) v = y v - v := fun v => rfl
  ext x
  have hu : y x - x ∈ pairU a b := (mem_zStab_iff.mp hy).1 x
  have hv := apply_apply_of_zComp_eq_one h hy h1 hu
  rw [pow_succ, pow_succ, pow_one]
  show ((y : W →ₗ[ZMod 2] W) - 1) (((y : W →ₗ[ZMod 2] W) - 1) (((y : W →ₗ[ZMod 2] W) - 1) x)) = 0
  rw [hN x, hN (y x - x), hN _, map_sub, hv]
  calc _ = ((y x - x) + (y x - x)) - (y (y x - x) + y (y x - x)) := by abel
    _ = 0 := by rw [add_self_eq_zero', add_self_eq_zero', sub_zero]

theorem pow_four_of_zComp_eq_one (h : PairHyp B a b) {y : W ≃ₗ[ZMod 2] W}
    (hy : y ∈ zStab B a b) (h1 : zComp h y = 1) : y ^ 4 = 1 := by
  have h4 := pow_four_eq_one_of_sub_one_cube (R := Module.End (ZMod 2) W) end_two_eq_zero
    (sub_one_cube_eq_zero h hy h1)
  have h5 : ((y ^ 4 : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = 1 :=
    (map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := W)) y 4).trans
      h4
  ext x
  exact LinearMap.congr_fun h5 x

@[expose] noncomputable def zHom (h : PairHyp B a b) :
    ↥(zStab B a b) →* (Module.End (ZMod 2) ↥(commSp a))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun y => zComp h y.1
      map_one' := zComp_one h
      map_mul' := fun y y' => zComp_mul h y.2 y'.2 }

theorem zComp_b_pow_three (h : PairHyp B a b)
    (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) : zComp h b ^ 3 = 1 := by
  have hb3 : (⟨b, b_mem_zStab h hQ0⟩ : ↥(zStab B a b)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h.hb.pow_three)
  have e2 := map_pow (zHom h) (⟨b, b_mem_zStab h hQ0⟩ : ↥(zStab B a b)) 3
  rw [hb3, map_one] at e2
  have e3 := congrArg Units.val e2
  rw [Units.val_pow_eq_pow_val, Units.val_one] at e3
  exact e3.symm

theorem zComp_b_cases (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) :
    zComp h b = 1 ∨ zComp h b = zComp h a ∨ zComp h b = zComp h a ^ 2 :=
  endo_two_order_three h.ha.rank (zComp_a_sq h) (zComp_b_pow_three h hQ0)

@[expose] noncomputable def zRho (h : PairHyp B a b)
    (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) :
    ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) →*
      (Module.End (ZMod 2) ↥(commSp a))ˣ :=
  (zHom h).comp (Subgroup.inclusion (closure_le_zStab h hQ0))

theorem zRho_mem_zpowers (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥)
    (y : ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)))) :
    zRho h hQ0 y ∈ Subgroup.zpowers (zRho h hQ0 (memA a b)) := by
  refine closure_pair_induction
    (p := fun y => zRho h hQ0 y ∈ Subgroup.zpowers (zRho h hQ0 (memA a b))) ?_ ?_ ?_ ?_ ?_ y
  · exact Subgroup.mem_zpowers _
  · rcases zComp_b_cases h hQ0 with hb | hb | hb
    · have : zRho h hQ0 (memB a b) = 1 := Units.ext hb
      rw [this]; exact one_mem _
    · have : zRho h hQ0 (memB a b) = zRho h hQ0 (memA a b) := Units.ext hb
      rw [this]; exact Subgroup.mem_zpowers _
    · have : zRho h hQ0 (memB a b) = zRho h hQ0 (memA a b) ^ 2 :=
        Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hb)
      rw [this]; exact pow_mem (Subgroup.mem_zpowers _) 2
  · rw [map_one]; exact one_mem _
  · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy
  · intro x hx; rw [map_inv]; exact inv_mem hx

theorem pairShapeHom_z3 (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) :
    PairShapeHom ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) := by
  set ρ := zRho h hQ0 with hρdef
  set g := ρ (memA a b) with hgdef
  have hg3 : g ^ 3 = 1 := by
    rw [hgdef, ← map_pow]
    have : (memA a b) ^ 3 = (1 : ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)))) :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h.ha.pow_three)
    rw [this, map_one]
  have hg1 : g ≠ 1 := by
    intro hg
    have hne : commSp a ≠ ⊥ := by
      intro h0
      have := h.ha.rank
      rw [h0] at this
      simp at this
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hT : zComp h a = 1 := congrArg Units.val hg
    have := zComp_a h ⟨p, hp⟩
    rw [hT] at this
    exact apply_ne_of_mem h.nondeg h.ha hp hp0 this.symm
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  let f : ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) →* ↥(Subgroup.zpowers g) :=
    ρ.codRestrict (Subgroup.zpowers g) (zRho_mem_zpowers h hQ0)
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨(memA a b) ^ k, Subtype.ext ?_⟩
    show ρ ((memA a b) ^ k) = g ^ k
    rw [map_zpow]
  have hker : IsPGroup 2 f.ker := by
    refine isPGroup_two_ker_of_pow_four f ?_
    intro y hy
    have hρy : ρ y = 1 := congrArg Subtype.val hy
    have hz : zComp h (y : W ≃ₗ[ZMod 2] W) = 1 := congrArg Units.val hρy
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_four_of_zComp_eq_one h (closure_le_zStab h hQ0 y.2) hz)
  exact pairShapeHom_of_cyclic3 f hsurj hker inferInstance (by rw [Nat.card_zpowers]; exact hord)

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
