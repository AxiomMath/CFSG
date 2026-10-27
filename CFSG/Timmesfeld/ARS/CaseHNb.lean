module

public import CFSG.Timmesfeld.ARS.CaseHA
public import CFSG.Timmesfeld.ARS.CaseHTF

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section SL3

variable {F : Type} [Field F] [CharP F 2]

@[expose] def sw01 : Fin 3 → Fin 3 := ![1, 0, 2]

@[expose] noncomputable def w01 : SpecialLinearGroup (Fin 3) F :=
  SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) 1 *
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1

theorem val_w01 : (w01 : SpecialLinearGroup (Fin 3) F).1 = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [w01, val_mul3, val_mul3, val_tv, val_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, h2]

theorem w01_mul_self : (w01 : SpecialLinearGroup (Fin 3) F) * w01 = 1 := by
  apply Subtype.ext
  rw [val_mul3, val_w01]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem w01_mul_tv {i j : Fin 3} (hij : i ≠ j) (h' : sw01 i ≠ sw01 j) (b : F) :
    w01 * SpecialLinearGroup.transvection hij b =
      SpecialLinearGroup.transvection h' b * w01 := by
  apply Subtype.ext
  rw [val_mul3, val_mul3, val_w01, val_tv, val_tv]
  ext a k
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (fin_cases a <;> fin_cases k <;>
        simp [sw01, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply])

theorem w01_conj_tv {i j : Fin 3} (hij : i ≠ j) (h' : sw01 i ≠ sw01 j) (b : F) :
    w01 * SpecialLinearGroup.transvection hij b * w01⁻¹ =
      SpecialLinearGroup.transvection h' b := by
  rw [w01_mul_tv hij h', mul_inv_cancel_right]

theorem conjSub_rootSubgroup_w01 {i j : Fin 3} (hij : i ≠ j) (h' : sw01 i ≠ sw01 j) :
    conjSub (SpecialLinear.rootSubgroup 2 F hij) w01 = SpecialLinear.rootSubgroup 2 F h' := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij y).1 hy
    change w01 * _ * w01⁻¹ ∈ _
    rw [w01_conj_tv hij h']
    exact SpecialLinear.transvection_mem_rootSubgroup h' u
  · intro hx
    obtain ⟨u, rfl⟩ := (SpecialLinear.mem_rootSubgroup h' x).1 hx
    exact ⟨_, SpecialLinear.transvection_mem_rootSubgroup hij u, w01_conj_tv hij h' u⟩

end SL3

theorem exists_trace3_ne_zero {E : Type} [Field E] [Finite E] [CharP E 2] (σ : E →+* E)
    (hσ3 : ∀ x, σ (σ (σ x)) = x) : ∃ x, trace3 σ x ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  let n : E →+* E :=
    { toFun := fun x => x * σ x * σ (σ x)
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul]; ring
      map_zero' := by simp
      map_add' := fun x y => by
        have := norm_add σ hσ3 x y
        rw [h, h, add_zero, add_zero] at this
        rw [this, add_comm] }
  have hsurj : Function.Surjective n := Finite.injective_iff_surjective.1 n.injective
  have hσ : ∀ y, σ y = y := fun y => by
    obtain ⟨x, rfl⟩ := hsurj y
    change σ (x * σ x * σ (σ x)) = x * σ x * σ (σ x)
    rw [map_mul, map_mul, hσ3]
    ring
  have h1 := h 1
  rw [trace3, hσ, hσ, show (1 : E) + 1 + 1 = 1 + (1 + 1) by ring, CharTwo.add_self_eq_zero,
    add_zero] at h1
  exact one_ne_zero h1

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP F 2]

@[expose] noncomputable def nb : G := c.ψ w01

theorem nb_mul_self : c.nb * c.nb = 1 := by
  rw [nb, ← map_mul, w01_mul_self, map_one]

theorem nb_inv : c.nb⁻¹ = c.nb := inv_eq_of_mul_eq_one_right c.nb_mul_self

theorem nb_conj_psi {i j : Fin 3} (hij : i ≠ j) (h' : sw01 i ≠ sw01 j) (b : F) :
    c.nb * c.ψ (SpecialLinearGroup.transvection hij b) * c.nb⁻¹ =
      c.ψ (SpecialLinearGroup.transvection h' b) := by
  rw [nb, ← map_inv, ← map_mul, ← map_mul, w01_conj_tv hij h']

theorem nb_conj_x2 (v : F) : c.nb * c.x2 v * c.nb⁻¹ = c.x4 v :=
  c.nb_conj_psi _ (by decide) v

theorem nb_conj_x4 (z : F) : c.nb * c.x4 z * c.nb⁻¹ = c.x2 z :=
  c.nb_conj_psi _ (by decide) z

theorem x4_inv (z : F) : (c.x4 z)⁻¹ = c.x4 z :=
  inv_eq_of_mul_eq_one_right (by rw [← c.x4_add, CharTwo.add_self_eq_zero, c.x4_zero])

theorem conjSub_nb {i j : Fin 3} (hij : i ≠ j) (h' : sw01 i ≠ sw01 j) {X Y : Subgroup G}
    (hX : (SpecialLinear.rootSubgroup 2 F hij).map c.ψ = X)
    (hY : (SpecialLinear.rootSubgroup 2 F h').map c.ψ = Y) : conjSub X c.nb = Y := by
  rw [← hX, nb, conjSub_map, conjSub_rootSubgroup_w01 hij h', hY]

theorem conjSub_A_nb : conjSub A c.nb = P' := c.conjSub_nb _ (by decide) c.hψA c.hψP'

theorem conjSub_P'_nb : conjSub P' c.nb = A := c.conjSub_nb _ (by decide) c.hψP' c.hψA

theorem conjSub_A₀_nb : conjSub A₀ c.nb = ⁅A₀, P⁆ := c.conjSub_nb _ (by decide) c.hψA₀ c.hψQ

theorem conjSub_Q_nb : conjSub ⁅A₀, P⁆ c.nb = A₀ := c.conjSub_nb _ (by decide) c.hψQ c.hψA₀

theorem conjSub_P_nb : conjSub P c.nb = ⁅A₀, P'⁆ := c.conjSub_nb _ (by decide) c.hψP c.hψQ'

omit [CharP F 2] in
theorem nb_mem : c.nb ∈ P ⊔ ⁅A₀, P'⁆ := by
  rw [nb, w01]
  simp only [map_mul]
  have ha := fun u => Subgroup.mem_sup_left (S := P) (T := ⁅A₀, P'⁆) (psi_tv_mem _ c.hψP u)
  have hb := fun u => Subgroup.mem_sup_right (S := P) (T := ⁅A₀, P'⁆) (psi_tv_mem _ c.hψQ' u)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ha _) (hb _)) (ha _)

omit [CharP F 2] in
theorem nb_conj_U3 {y : G} (hy : y ∈ shortRoot R P ⁅A₀, P'⁆ A) : c.nb * y * c.nb⁻¹ = y := by
  rw [Subgroup.mem_centralizer_iff.1 hy.1 _ c.nb_mem, mul_inv_cancel_right]

theorem conjSub_Xa_nb : conjSub (shortRoot R A A₀ P') c.nb = shortRoot R P' ⁅A₀, P⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_A_nb, c.conjSub_A₀_nb, c.conjSub_P'_nb]

theorem nb_conj_x1_mem (s : E) : c.nb * c.x1 s * c.nb⁻¹ ∈ shortRoot R P' ⁅A₀, P⁆ A :=
  c.conjSub_Xa_nb ▸ conj_mem_conjSub c.nb (c.x1_mem s)

@[expose] noncomputable def beta (s : E) : E :=
  Classical.choose (c.x5_surjective (c.nb_conj_x1_mem s))

theorem x5_beta (s : E) : c.x5 (c.beta s) = c.nb * c.x1 s * c.nb⁻¹ :=
  Classical.choose_spec (c.x5_surjective (c.nb_conj_x1_mem s))

variable [CharP E 2]

omit [CharP F 2] in
theorem nb_conj_x3 (r : E) : c.nb * c.x3 r * c.nb⁻¹ = c.x3 r := c.nb_conj_U3 (c.x3_mem r)

omit [CharP F 2] in
theorem T_add_left (s s' r : E) : c.T (s + s') r = c.T s r + c.T s' r := by
  have := S.hyp.finite
  apply c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  have hc : Commute (c.x1 s) ⁅c.x1 s', c.x3 r⁆ :=
    (positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP').2.1 _ (c.x1_mem s) _
      (c.comm13_mem s' r)
  rw [c.x2_add, c.x2_T, c.x2_T, c.x2_T, c.x1_add, Plane.commutatorElement_mul_left_of_commute hc]
  exact (S.hyp.root.commuting_self S.hP'.2.1 _ (c.comm13_mem s' r) _ (c.comm13_mem s r)).eq

theorem T_beta [Finite F] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1) (s r : E) :
    c.T (c.beta s) r = c.T s r := by
  have := S.hyp.finite
  have hconj : ∀ g x y : G, g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := fun g x y => by
    simp only [commutatorElement_def]
    group
  apply c.x4_injective
  have h1 : c.x4 (c.T s r) = ⁅c.x5 (c.beta s), c.x3 r⁆ := by
    rw [← c.nb_conj_x2, c.x2_T, hconj, ← c.x5_beta, c.nb_conj_x3]
  rw [h1, ← commutatorElement_inv, ← c.x4_Tp, c.x4_inv, c.Tp_eq e he]

theorem beta_eq [Finite F] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
    (hnd : ∀ d, (∀ r, c.T d r = 0) → d = 0) (s : E) : c.beta s = s := by
  have h := hnd (c.beta s + s) fun r => by
    rw [c.T_add_left, c.T_beta e he, CharTwo.add_self_eq_zero]
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination h - s * h2

omit [CharP E 2] in
theorem nb_conj_x1 (hβ : ∀ s, c.beta s = s) (s : E) : c.nb * c.x1 s * c.nb⁻¹ = c.x5 s := by
  rw [← c.x5_beta, hβ]

omit [CharP E 2] in
theorem nb_conj_x5 (hβ : ∀ s, c.beta s = s) (w : E) : c.nb * c.x5 w * c.nb⁻¹ = c.x1 w := by
  rw [← c.nb_conj_x1 hβ w, c.nb_inv]
  calc c.nb * (c.nb * c.x1 w * c.nb) * c.nb = (c.nb * c.nb) * c.x1 w * (c.nb * c.nb) := by group
    _ = c.x1 w := by rw [c.nb_mul_self, one_mul, mul_one]

variable [Finite F] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem T_nondeg_G2 (hsq : ∀ s, c.sharp s = s ^ 2) (d : E) (hd : ∀ r, c.T d r = 0) : d = 0 := by
  have h := (c.G2_structure e he hτ0 hτ hsq).2.2.2 d 1
  rw [hd, mul_zero, map_zero, mul_one] at h
  exact h.symm

theorem T_nondeg_D4 (σ : E →+* E) (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hsq : ∀ s, c.sharp s = σ s * σ (σ s)) (d : E) (hd : ∀ r, c.T d r = 0) : d = 0 := by
  by_contra hd0
  obtain ⟨x, hx⟩ := exists_trace3_ne_zero σ hσ3
  have h := (c.D4_structure e he hτ0 hτ σ hσ3 hsq).2.2.2 d (d⁻¹ * x)
  rw [hd, mul_zero, map_zero, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul] at h
  exact hx h.symm

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
