module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open scoped Matrix

section Lattice


def e8Inverse : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![4,5,7,10,8,6,4,2;
     5,8,10,15,12,9,6,3;
     7,10,14,20,16,12,8,4;
     10,15,20,30,24,18,12,6;
     8,12,16,24,20,15,10,5;
     6,9,12,18,15,12,8,4;
     4,6,8,12,10,8,6,3;
     2,3,4,6,5,4,3,2]

def e7Inverse : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![4,4,6,8,6,4,2;
     4,7,8,12,9,6,3;
     6,8,12,16,12,8,4;
     8,12,16,24,18,12,6;
     6,9,12,18,15,10,5;
     4,6,8,12,10,8,4;
     2,3,4,6,5,4,3]

theorem e8Inverse_mul_cartan : e8Inverse * Tag.cartan Tag.E8 = 1 := by decide +kernel

theorem e7Inverse_mul_cartan :
    e7Inverse * Tag.cartan Tag.E7 = 2 • (1 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ) := by
  decide +kernel

def e7InverseMod4 : Matrix (Fin 7) (Fin 7) (ZMod 4) :=
  !![0,0,2,0,2,0,2;
     0,3,0,0,1,2,3;
     2,0,0,0,0,0,0;
     0,0,0,0,2,0,2;
     2,1,0,2,3,2,1;
     0,2,0,0,2,0,0;
     2,3,0,2,1,0,3]

def e7InverseMod4Tag : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 4) := e7InverseMod4

theorem e7Inverse_map_eq_mod4 :
    e7Inverse.map (Int.cast : ℤ → ZMod 4) = e7InverseMod4Tag := by
  decide +kernel

theorem e7_quad_zmod_identity (y : Fin 7 → ZMod 4) :
    y ⬝ᵥ (e7InverseMod4 *ᵥ y) =
      3*((y 1)^2 + (y 4)^2 + (y 6)^2) + 2*(y 1*y 4 + y 1*y 6 + y 4*y 6) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  change (∑ x : Fin 7, ∑ i : Fin 7, y x * (e7InverseMod4 x i * y i)) =
      3 * (y 1 ^ 2 + y 4 ^ 2 + y 6 ^ 2) + 2 * (y 1 * y 4 + y 1 * y 6 + y 4 * y 6)
  simp only [e7InverseMod4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply,
    Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  norm_num
  have h4 : (4 : ZMod 4) = 0 := by decide
  linear_combination
    (y 0 * y 2 + y 0 * y 4 + y 0 * y 6 + y 4 * y 5 + y 4 * y 3 + y 6 * y 3 + y 1 * y 5 + y 6 * y 1) * h4

theorem three_var_zmod4 (a b c : ZMod 4) :
    (3*(a^2+b^2+c^2) + 2*(a*b+a*c+b*c) = 0) ∨
    (3*(a^2+b^2+c^2) + 2*(a*b+a*c+b*c) = 3) := by
  revert a b c
  decide +kernel

theorem e7_quadratic_form_mod_four (y : Fin Tag.E7.rank → ℤ) :
    (y ⬝ᵥ (e7Inverse *ᵥ y)) % 4 = 0 ∨ (y ⬝ᵥ (e7Inverse *ᵥ y)) % 4 = 3 := by
  have hcast : ((y ⬝ᵥ (e7Inverse *ᵥ y) : ℤ) : ZMod 4) =
      (fun j => (y j : ZMod 4)) ⬝ᵥ ((e7Inverse.map (Int.cast : ℤ → ZMod 4)) *ᵥ
        (fun j => (y j : ZMod 4))) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
    push_cast
    ring
  have hmap' : (fun j => (y j : ZMod 4)) ⬝ᵥ ((e7Inverse.map (Int.cast : ℤ → ZMod 4)) *ᵥ
        (fun j => (y j : ZMod 4))) =
      (fun j => (y j : ZMod 4)) ⬝ᵥ (e7InverseMod4Tag *ᵥ (fun j => (y j : ZMod 4))) := by
    rw [e7Inverse_map_eq_mod4]
  have hident : (fun j => (y j : ZMod 4)) ⬝ᵥ (e7InverseMod4Tag *ᵥ
        (fun j => (y j : ZMod 4))) =
      3*((y 1 : ZMod 4)^2 + (y 4 : ZMod 4)^2 + (y 6 : ZMod 4)^2) +
        2*((y 1 : ZMod 4)*(y 4 : ZMod 4) + (y 1 : ZMod 4)*(y 6 : ZMod 4) +
          (y 4 : ZMod 4)*(y 6 : ZMod 4)) := by
    change (fun j : Fin 7 => (y j : ZMod 4)) ⬝ᵥ (e7InverseMod4 *ᵥ
        (fun j : Fin 7 => (y j : ZMod 4))) =
      3*((y 1 : ZMod 4)^2 + (y 4 : ZMod 4)^2 + (y 6 : ZMod 4)^2) +
        2*((y 1 : ZMod 4)*(y 4 : ZMod 4) + (y 1 : ZMod 4)*(y 6 : ZMod 4) +
          (y 4 : ZMod 4)*(y 6 : ZMod 4))
    exact e7_quad_zmod_identity _
  have hmain : ((y ⬝ᵥ (e7Inverse *ᵥ y) : ℤ) : ZMod 4) =
      3*((y 1 : ZMod 4)^2 + (y 4 : ZMod 4)^2 + (y 6 : ZMod 4)^2) +
        2*((y 1 : ZMod 4)*(y 4 : ZMod 4) + (y 1 : ZMod 4)*(y 6 : ZMod 4) +
          (y 4 : ZMod 4)*(y 6 : ZMod 4)) := by
    rw [hcast, hmap', hident]
  have hz := three_var_zmod4 (y 1) (y 4) (y 6)
  rw [← hmain] at hz
  rcases hz with hz | hz
  · left
    have := (ZMod.intCast_eq_intCast_iff' (y ⬝ᵥ (e7Inverse *ᵥ y)) 0 4).mp hz
    simpa using this
  · right
    have := (ZMod.intCast_eq_intCast_iff' (y ⬝ᵥ (e7Inverse *ᵥ y)) 3 4).mp hz
    simpa using this

theorem dvd_of_forall_dvd_mul_of_primitive {r : ℕ} {n k : ℤ} {u : Fin r → ℤ} (hn : n ≠ 0)
    (hprim : ∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1)
    (h : ∀ i, n ∣ k * u i) : n ∣ k := by
  have hg : 0 < Int.gcd n k := Int.gcd_pos_of_ne_zero_left k hn
  obtain ⟨n', k', hcop, hn', hk'⟩ := Int.exists_gcd_one hg
  set g : ℤ := (Int.gcd n k : ℤ) with hgdef
  have hn'' : n = n' * g := by rw [hn', hgdef]
  have hk'' : k = k' * g := by rw [hk', hgdef]
  have hg_ne : g ≠ 0 := by rw [hgdef]; exact_mod_cast hg.ne'
  have hdvd : ∀ i, n' ∣ u i := by
    intro i
    have hi : n ∣ k * u i := h i
    rw [hn'', hk''] at hi
    obtain ⟨c, hc⟩ := hi
    have hcancel : k' * u i = n' * c := by
      apply mul_left_cancel₀ hg_ne
      calc g * (k' * u i) = k' * g * u i := by ring
        _ = n' * g * c := hc
        _ = g * (n' * c) := by ring
    exact Int.dvd_of_dvd_mul_right_of_gcd_one ⟨c, hcancel⟩ hcop
  rcases hprim n' hdvd with h1 | h1
  · rw [hn'', h1, one_mul]; exact Int.gcd_dvd_right n k
  · rw [hn'', h1, neg_one_mul]; exact neg_dvd.mpr (Int.gcd_dvd_right n k)

theorem even_iform_self_local {τ : Tag} (x : Fin τ.rank → ℤ) : Even (iform x x) := by
  classical
  have key : ∀ s : Finset (Fin τ.rank),
      Even (iform (∑ k ∈ s, x k • (Pi.single k 1 : Fin τ.rank → ℤ))
        (∑ k ∈ s, x k • (Pi.single k 1 : Fin τ.rank → ℤ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨0, by simp [iform]⟩
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      set y := ∑ k ∈ s, x k • (Pi.single k 1 : Fin τ.rank → ℤ)
      rw [iform_add_left, iform_add_right, iform_add_right, iform_smul_left, iform_smul_right,
        iform_smul_left, iform_smul_right, iform_single_single, iform_comm y]
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + x k * iform (Pi.single k 1) y + x k * x k * τ.symmetrizer k k, by
        rw [hm]; ring⟩
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact key Finset.univ

theorem iform_self_eq_two_of_primitive_dvd_E8 {u : Fin Tag.E8.rank → ℤ} (hu : u ≠ 0)
    (hprim : ∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1)
    (hdvd : ∀ x : Fin Tag.E8.rank → ℤ, iform u u ∣ 2 * iform u x) :
    iform u u = 2 := by
  set n : ℤ := iform u u with hn_def
  have hn_pos : 0 < n := by rw [hn_def]; exact iform_self_pos hu
  have hn_ne : n ≠ 0 := hn_pos.ne'
  set y : Fin Tag.E8.rank → ℤ := fun j => iform u (Pi.single j 1) with hy_def
  have h2y : ∀ j, n ∣ 2 * y j := by
    intro j; rw [hn_def, hy_def]; exact hdvd (Pi.single j 1)
  have hy : y = Tag.cartan Tag.E8 *ᵥ u := by
    funext j
    simp only [hy_def, Matrix.mulVec_apply_eq_sum]
    rw [iform_comm, iform_single_left]
    simp [Tag.symmetrizer]
  have hinv : e8Inverse *ᵥ y = u := by
    calc e8Inverse *ᵥ y = e8Inverse *ᵥ (Tag.cartan Tag.E8 *ᵥ u) := by rw [hy]
      _ = (e8Inverse * Tag.cartan Tag.E8) *ᵥ u := Matrix.mulVec_mulVec u e8Inverse _
      _ = (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) *ᵥ u := by rw [e8Inverse_mul_cartan]
      _ = u := Matrix.one_mulVec u
  have h2u : ∀ i, n ∣ 2 * u i := by
    intro i
    have hsum : 2 * u i = ∑ j, e8Inverse i j * (2 * y j) := by
      rw [← congrFun hinv i, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (h2y j) (e8Inverse i j)
  have hndvd2 : n ∣ 2 := dvd_of_forall_dvd_mul_of_primitive hn_ne hprim h2u
  have hn_le : n ≤ 2 := Int.le_of_dvd (by norm_num) hndvd2
  have heven : Even n := by rw [hn_def]; exact even_iform_self_local u
  have hcases : n = 1 ∨ n = 2 := by omega
  rcases hcases with h | h
  · exfalso; obtain ⟨m, hm⟩ := heven; omega
  · exact h

theorem iform_self_eq_two_of_primitive_dvd_E7 {u : Fin Tag.E7.rank → ℤ} (hu : u ≠ 0)
    (hprim : ∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1)
    (hdvd : ∀ x : Fin Tag.E7.rank → ℤ, iform u u ∣ 2 * iform u x) :
    iform u u = 2 := by
  set n : ℤ := iform u u with hn_def
  have hn_pos : 0 < n := by rw [hn_def]; exact iform_self_pos hu
  have hn_ne : n ≠ 0 := hn_pos.ne'
  set y : Fin Tag.E7.rank → ℤ := fun j => iform u (Pi.single j 1) with hy_def
  have h2y : ∀ j, n ∣ 2 * y j := by
    intro j; rw [hn_def, hy_def]; exact hdvd (Pi.single j 1)
  have hy : y = Tag.cartan Tag.E7 *ᵥ u := by
    funext j
    simp only [hy_def, Matrix.mulVec_apply_eq_sum]
    rw [iform_comm, iform_single_left]
    simp [Tag.symmetrizer]
  have hcomp_i : ∀ i, (e7Inverse *ᵥ y) i = 2 * u i := by
    intro i
    have h := congrFun (show e7Inverse *ᵥ y = 2 • u from by
      calc e7Inverse *ᵥ y = e7Inverse *ᵥ (Tag.cartan Tag.E7 *ᵥ u) := by rw [hy]
        _ = (e7Inverse * Tag.cartan Tag.E7) *ᵥ u := Matrix.mulVec_mulVec u e7Inverse _
        _ = (2 • (1 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ)) *ᵥ u := by
              rw [e7Inverse_mul_cartan]
        _ = 2 • u := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]) i
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have h4u : ∀ i, n ∣ 4 * u i := by
    intro i
    have hsum : 4 * u i = ∑ j, e7Inverse i j * (2 * y j) := by
      calc 4 * u i = 2 * (2 * u i) := by ring
        _ = 2 * ((e7Inverse *ᵥ y) i) := by rw [hcomp_i i]
        _ = ∑ j, e7Inverse i j * (2 * y j) := by
              rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (h2y j) (e7Inverse i j)
  have hndvd4 : n ∣ 4 := dvd_of_forall_dvd_mul_of_primitive hn_ne hprim h4u
  have hn_le : n ≤ 4 := Int.le_of_dvd (by norm_num) hndvd4
  have heven : Even n := by rw [hn_def]; exact even_iform_self_local u
  have hn_eq2 : n = 2 ∨ n = 4 := by
    have h14 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases h14 with h | h | h | h
    · exfalso; obtain ⟨m, hm⟩ := heven; omega
    · exact Or.inl h
    · exfalso; obtain ⟨m, hm⟩ := heven; omega
    · exact Or.inr h
  rcases hn_eq2 with h2 | h4
  · exact h2
  · exfalso
    have h2yj : ∀ j, 2 ∣ y j := by
      intro j
      have h := h2y j
      rw [h4] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨c, by omega⟩
    choose y' hy' using h2yj
    have hu_eq : u = e7Inverse *ᵥ y' := by
      funext i
      have h2 : 2 * u i = 2 * (e7Inverse *ᵥ y') i := by
        rw [← hcomp_i i, Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [hy' j]; ring
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2
    have hy2 : y = fun j => 2 * y' j := by funext j; rw [hy' j]
    have hn_eq : n = 2 * (y' ⬝ᵥ (e7Inverse *ᵥ y')) := by
      calc n = iform u u := hn_def
        _ = u ⬝ᵥ (Tag.symmetrizedCartan Tag.E7 *ᵥ u) :=
              (dotProduct_mulVec_eq_iform u u).symm
        _ = u ⬝ᵥ (Tag.cartan Tag.E7 *ᵥ u) := by
              simp [Tag.symmetrizedCartan, Tag.symmetrizer]
        _ = u ⬝ᵥ y := by rw [hy]
        _ = 2 * (u ⬝ᵥ y') := by
              rw [hy2]
              simp only [dotProduct, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring
        _ = 2 * (y' ⬝ᵥ (e7Inverse *ᵥ y')) := by rw [hu_eq, dotProduct_comm]
    have hQ : y' ⬝ᵥ (e7Inverse *ᵥ y') = 2 := by
      have h := hn_eq
      rw [h4] at h
      omega
    have hmod := e7_quadratic_form_mod_four y'
    rw [hQ] at hmod
    norm_num at hmod

theorem iform_self_eq_two_of_primitive_dvd {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {u : Fin τ.rank → ℤ} (hu : u ≠ 0) (hprim : ∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1)
    (hdvd : ∀ x : Fin τ.rank → ℤ, iform u u ∣ 2 * iform u x) : iform u u = 2 := by
  rcases hτ with rfl | rfl
  · exact iform_self_eq_two_of_primitive_dvd_E7 hu hprim hdvd
  · exact iform_self_eq_two_of_primitive_dvd_E8 hu hprim hdvd

end Lattice

end ExcFramesHalf

end CFSG.StandardType
