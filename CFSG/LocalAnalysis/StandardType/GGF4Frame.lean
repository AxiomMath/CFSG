module

public import CFSG.LocalAnalysis.StandardType.GGF4FrameData
public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
import CFSG.LocalAnalysis.StandardType.GGF4OrbCore
import CFSG.LocalAnalysis.StandardType.GGF4Rk2Core
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

@[expose] def F4Vec.toFun (v : F4Vec) : Fin 4 → ℤ := ![v.v0, v.v1, v.v2, v.v3]

theorem F4Vec.toFun_injective : Function.Injective F4Vec.toFun := by
  rintro ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩ h
  have h0 : a0 = b0 := congrFun h 0
  have h1 : a1 = b1 := congrFun h 1
  have h2 : a2 = b2 := congrFun h 2
  have h3 : a3 = b3 := congrFun h 3
  rw [h0, h1, h2, h3]

theorem M4.toMat_mulVec (x : M4) (v : F4Vec) : x.toMat.mulVec v.toFun = (x.mulv v).toFun := by
  ext i
  fin_cases i <;>
    simp [M4.toMat, M4.mulv, F4Vec.toFun, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem M4.mulv_mul (x y : M4) (v : F4Vec) : (x.mul y).mulv v = x.mulv (y.mulv v) := by
  simp only [M4.mul, M4.mulv, F4Vec.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem rho_wd_mulVec (l : List (Fin 4)) (v : F4Vec) :
    (R.ρ (R.wd l)).mulVec v.toFun = ((evalW l).mulv v).toFun := by
  rw [R.rho_wd, M4.toMat_mulVec]

theorem wd_append (l l' : List (Fin 4)) : R.wd (l ++ l') = R.wd l * R.wd l' := by
  simp [wd]

theorem inv_mulVec_mulVec (g : W) (v : Fin 4 → ℤ) : (R.ρ g⁻¹).mulVec ((R.ρ g).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (g : W) (v : Fin 4 → ℤ) : (R.ρ g).mulVec ((R.ρ g⁻¹).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem exists_orbit (z : W) : ∃ v ∈ f4ShortOrb, (R.ρ z).mulVec f4E1.toFun = v.toFun ∧
    ∃ p ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W), z = R.wd (f4OrbT v) * p := by
  have hz : z ∈ Subgroup.closure (Set.range fun k : Fin 4 => R.s (id k)) := by
    rw [show (fun k : Fin 4 => R.s (id k)) = R.s from rfl, R.gen]
    exact Subgroup.mem_top _
  obtain ⟨l, rfl⟩ := R.exists_word_of_mem_closure id hz
  rw [List.map_id]
  have key : ∀ l : List (Fin 4), (evalW l).mulv f4E1 ∈ f4ShortOrb ∧
      ∃ p ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W),
        R.wd l = R.wd (f4OrbT ((evalW l).mulv f4E1)) * p := by
    intro l
    induction l with
    | nil =>
      have h1 : (evalW []).mulv f4E1 = f4E1 := by decide +kernel
      rw [h1, f4OrbT_spec.1]
      exact ⟨f4Orb_closed.1, 1, Subgroup.one_mem _, by simp [wd]⟩
    | cons k l ih =>
      obtain ⟨hv, p, hp, hl⟩ := ih
      set v := (evalW l).mulv f4E1 with hvdef
      have hev : (evalW (k :: l)).mulv f4E1 = (Sm k).mulv v := by
        rw [hvdef, ← M4.mulv_mul]
        rfl
      rw [hev]
      refine ⟨f4Orb_closed.2 v hv k, R.wd (f4OrbPi v k) * p,
        mul_mem (R.wd_mem_closure_of_ne (f4OrbPi_spec v hv k).2 ?_) hp, ?_⟩
      · intro i hi
        fin_cases i <;> simp_all
      · have hs : R.s k * R.wd (f4OrbT v) = R.wd (f4OrbT ((Sm k).mulv v)) * R.wd (f4OrbPi v k) := by
          apply R.inj
          rw [map_mul, map_mul, R.hs, R.rho_wd, R.rho_wd, R.rho_wd, ← M4.toMat_mul,
            ← M4.toMat_mul, (f4OrbPi_spec v hv k).1]
        calc R.wd (k :: l) = R.s k * R.wd l := by simp [wd]
          _ = R.s k * R.wd (f4OrbT v) * p := by rw [hl, mul_assoc]
          _ = _ := by rw [hs, mul_assoc]
  obtain ⟨hv, p, hp, hl⟩ := key l
  exact ⟨_, hv, R.rho_wd_mulVec l f4E1, p, hp, hl⟩

theorem mulVec_e1_of_mem_closureB {z : W}
    (hz : z ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W)) :
    (R.ρ z).mulVec f4E1.toFun = f4E1.toFun := by
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;>
      · rw [R.hs, M4.toMat_mulVec]
        exact congrArg F4Vec.toFun (by decide +kernel)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, ← Matrix.mulVec_mulVec, hy, hx]
  | inv x _ hx =>
    calc (R.ρ x⁻¹).mulVec f4E1.toFun = (R.ρ x⁻¹).mulVec ((R.ρ x).mulVec f4E1.toFun) := by rw [hx]
      _ = f4E1.toFun := R.inv_mulVec_mulVec x _

theorem mem_closureB_iff (z : W) :
    z ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W) ↔
      (R.ρ z).mulVec f4E1.toFun = f4E1.toFun := by
  refine ⟨R.mulVec_e1_of_mem_closureB, fun h => ?_⟩
  obtain ⟨v, -, hv, p, hp, rfl⟩ := R.exists_orbit z
  have hve : v = f4E1 := F4Vec.toFun_injective (hv.symm.trans h)
  rw [hve, f4OrbT_spec.1]
  simpa [wd] using hp

theorem conj_mulVec_iff (g z : W) (e : Fin 4 → ℤ) :
    (R.ρ (g * z * g⁻¹)).mulVec e = e ↔ (R.ρ z).mulVec ((R.ρ g⁻¹).mulVec e) = (R.ρ g⁻¹).mulVec e := by
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    rw [← R.inv_mulVec_mulVec g ((R.ρ z).mulVec ((R.ρ g⁻¹).mulVec e)), h]
  · intro h
    rw [h, R.mulVec_inv_mulVec]

theorem mem_closure_iff_of_B {a : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 0 ∧ g * a 1 * g⁻¹ = R.s 1 ∧ g * a 2 * g⁻¹ = R.s 2) (z : W) :
    z ∈ Subgroup.closure (Set.range a) ↔
      (R.ρ z).mulVec ((R.ρ g⁻¹).mulVec f4E1.toFun) = (R.ρ g⁻¹).mulVec f4E1.toFun := by
  rw [← R.conj_mulVec_iff, ← R.mem_closureB_iff]
  constructor
  · intro hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
      rcases hk with rfl | rfl | rfl
      · rw [hg.1]; exact Subgroup.subset_closure (by simp)
      · rw [hg.2.1]; exact Subgroup.subset_closure (by simp)
      · rw [hg.2.2]; exact Subgroup.subset_closure (by simp)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  · intro hz
    have h := R.conj_mem_closure_of_B hg hz
    rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h

theorem exists_frame {a b : Fin 3 → W} {ga gb : W}
    (hga : ga * a 0 * ga⁻¹ = R.s 0 ∧ ga * a 1 * ga⁻¹ = R.s 1 ∧ ga * a 2 * ga⁻¹ = R.s 2)
    (hgb : gb * b 0 * gb⁻¹ = R.s 0 ∧ gb * b 1 * gb⁻¹ = R.s 1 ∧ gb * b 2 * gb⁻¹ = R.s 2)
    {w₀ : W} (h2 : w₀ * R.s 2 * w₀⁻¹ ∈ Subgroup.closure (Set.range a))
    (h3a : w₀ * R.s 3 * w₀⁻¹ ∉ Subgroup.closure (Set.range a))
    (h3 : w₀ * R.s 3 * w₀⁻¹ ∈ Subgroup.closure (Set.range b))
    (h2b : w₀ * R.s 2 * w₀⁻¹ ∉ Subgroup.closure (Set.range b)) :
    ∃ y a' : W,
      w₀ * y * R.s 2 * (w₀ * y)⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w₀ * y * R.s 1 * (w₀ * y)⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w₀ * y * R.s 3 * (w₀ * y)⁻¹ ∈ Subgroup.closure (Set.range b) ∧
      w₀ * y * R.s 1 * (w₀ * y)⁻¹ ∈ Subgroup.closure (Set.range b) ∧
      w₀ * a' * w₀⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      (a' * y)⁻¹ * R.s 2 * (a' * y) ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set W) ∧
      (a' * y)⁻¹ * R.s 3 * (a' * y) ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set W) ∧
      ((R.ρ (ga * (w₀ * y))⁻¹).mulVec f4E1.toFun = f4E1.toFun ∨
        (R.ρ (ga * (w₀ * y))⁻¹).mulVec f4E1.toFun = f4E1.neg.toFun ∨
        (R.ρ (ga * (w₀ * y))⁻¹).mulVec f4E1.toFun = f4E2.toFun ∨
        (R.ρ (ga * (w₀ * y))⁻¹).mulVec f4E1.toFun = f4E2.neg.toFun) := by
  obtain ⟨va, hva, hvaeq, -⟩ := R.exists_orbit (ga * w₀)⁻¹
  obtain ⟨vb, hvb, hvbeq, -⟩ := R.exists_orbit (gb * w₀)⁻¹
  have hfa : (R.ρ w₀⁻¹).mulVec ((R.ρ ga⁻¹).mulVec f4E1.toFun) = va.toFun := by
    rw [Matrix.mulVec_mulVec, ← map_mul, ← mul_inv_rev, hvaeq]
  have hfb : (R.ρ w₀⁻¹).mulVec ((R.ρ gb⁻¹).mulVec f4E1.toFun) = vb.toFun := by
    rw [Matrix.mulVec_mulVec, ← map_mul, ← mul_inv_rev, hvbeq]
  have hA : ∀ z : W, w₀ * z * w₀⁻¹ ∈ Subgroup.closure (Set.range a) ↔
      (R.ρ z).mulVec va.toFun = va.toFun := by
    intro z
    rw [R.mem_closure_iff_of_B hga, R.conj_mulVec_iff, hfa]
  have hB : ∀ z : W, w₀ * z * w₀⁻¹ ∈ Subgroup.closure (Set.range b) ↔
      (R.ρ z).mulVec vb.toFun = vb.toFun := by
    intro z
    rw [R.mem_closure_iff_of_B hgb, R.conj_mulVec_iff, hfb]
  have hsv : ∀ (k : Fin 4) (v : F4Vec), (R.ρ (R.s k)).mulVec v.toFun = v.toFun ↔
      (Sm k).mulv v = v := by
    intro k v
    rw [R.hs, M4.toMat_mulVec]
    exact F4Vec.toFun_injective.eq_iff
  have hcond : F4FrameCond va vb := by
    unfold F4FrameCond
    exact ⟨(hsv 2 va).1 ((hA _).1 h2), fun h => h3a ((hA _).2 ((hsv 3 va).2 h)),
      (hsv 3 vb).1 ((hB _).1 h3), fun h => h2b ((hB _).2 ((hsv 2 vb).2 h))⟩
  have hgood := f4Frame_spec va hva vb hvb hcond
  unfold F4FrameGood at hgood
  obtain ⟨g2, g1, g3, g1b, gap, gw2, gw3, gw2n, gw3n, gv⟩ := hgood
  set wy := (f4Frame va vb).1 with hwy
  set wa := (f4Frame va vb).2.1 with hwa
  have hconj : ∀ (k : Fin 4) (v : F4Vec),
      (R.ρ (R.wd wy * R.s k * (R.wd wy)⁻¹)).mulVec v.toFun = ((conjW wy (Sm k)).mulv v).toFun := by
    intro k v
    rw [R.rho_conj_wd wy (R.hs k), M4.toMat_mulVec]
  have hmem : ∀ (k : Fin 4) {Z : Subgroup W},
      (w₀ * (R.wd wy * R.s k * (R.wd wy)⁻¹) * w₀⁻¹ ∈ Z) →
        w₀ * R.wd wy * R.s k * (w₀ * R.wd wy)⁻¹ ∈ Z := by
    intro k Z h
    rwa [show w₀ * R.wd wy * R.s k * (w₀ * R.wd wy)⁻¹ =
      w₀ * (R.wd wy * R.s k * (R.wd wy)⁻¹) * w₀⁻¹ by group]
  have hPC : ∀ {l : List (Fin 4)}, (∀ i ∈ l, i ≠ 0) →
      R.wd l ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set W) := by
    intro l hl
    refine R.wd_mem_closure_of_ne hl fun i hi => ?_
    fin_cases i <;> simp_all
  have hay : (R.wd wa * R.wd wy)⁻¹ = R.wd (wa ++ wy).reverse := by
    rw [R.wd_reverse, R.wd_append]
  have hayc : ∀ (k : Fin 4) {l : List (Fin 4)},
      conjW (wa ++ wy).reverse (Sm k) = evalW l →
        (R.wd wa * R.wd wy)⁻¹ * R.s k * (R.wd wa * R.wd wy) = R.wd l := by
    intro k l h
    have h1 := R.conj_wd_eq (w := (wa ++ wy).reverse) (R.hs k) (R.rho_wd l) h
    rw [← hay, inv_inv] at h1
    exact h1
  refine ⟨R.wd wy, R.wd wa, hmem 2 ((hA _).2 ?_), hmem 1 ((hA _).2 ?_), hmem 3 ((hB _).2 ?_),
    hmem 1 ((hB _).2 ?_), (hA _).2 ?_, ?_, ?_, ?_⟩
  · rw [hconj]; exact congrArg F4Vec.toFun g2
  · rw [hconj]; exact congrArg F4Vec.toFun g1
  · rw [hconj]; exact congrArg F4Vec.toFun g3
  · rw [hconj]; exact congrArg F4Vec.toFun g1b
  · rw [R.rho_wd_mulVec]; exact congrArg F4Vec.toFun gap
  · rw [hayc 2 gw2]; exact hPC gw2n
  · rw [hayc 3 gw3]; exact hPC gw3n
  · have hv2 : (R.ρ (ga * (w₀ * R.wd wy))⁻¹).mulVec f4E1.toFun =
        ((evalW wy.reverse).mulv va).toFun := by
      rw [show (ga * (w₀ * R.wd wy))⁻¹ = (R.wd wy)⁻¹ * (ga * w₀)⁻¹ by group, map_mul,
        ← Matrix.mulVec_mulVec, hvaeq, ← R.wd_reverse, R.rho_wd_mulVec]
    rw [hv2]
    rcases gv with h | h | h | h
    · exact Or.inl (congrArg F4Vec.toFun h)
    · exact Or.inr (Or.inl (congrArg F4Vec.toFun h))
    · exact Or.inr (Or.inr (Or.inl (congrArg F4Vec.toFun h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg F4Vec.toFun h)))

end F4Rep

end CFSG.StandardType.F4Model

end
