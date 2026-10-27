module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.E9P2.FinGen

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

variable {n : ℕ}

@[expose] def elem (i j : Fin n) (h : i < j) : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨transvection i j 1, det_transvection_of_ne i j h.ne 1⟩

theorem coe_elem (i j : Fin n) (h : i < j) :
    (elem i j h : Matrix (Fin n) (Fin n) (ZMod 2)) = transvection i j 1 := rfl

theorem elem_mul_self (i j : Fin n) (h : i < j) : elem i j h * elem i j h = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elem, transvection_mul_transvection_same i j h.ne,
    show (1 + 1 : ZMod 2) = 0 from rfl, transvection_zero, Matrix.SpecialLinearGroup.coe_one]

theorem elem_mem (i j : Fin n) (h : i < j) : elem i j h ∈ unitriangular n (ZMod 2) := by
  rw [mem_unitriangular]
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · have hne : ¬ (i = k ∧ j = l) := fun hc => absurd (hc.1 ▸ hc.2 ▸ h) (not_lt.mpr hlk.le)
    simp [coe_elem, transvection, one_apply_ne hlk.ne', hne]
  · have hne : ¬ (i = k ∧ j = k) := fun hc => h.ne (hc.1.trans hc.2.symm)
    simp [coe_elem, transvection, hne]

def supp (u : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ (u : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2 ≠ 0

theorem zmod_two_eq_one {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  revert x
  decide

theorem mul_elem_apply_of_ne (u : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (i j : Fin n)
    (h : i < j) (k : Fin n) {l : Fin n} (hl : l ≠ j) :
    ((u * elem i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) k l = (u : Matrix (Fin n) (Fin n) (ZMod 2)) k l := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elem, mul_transvection_apply_of_ne i j k l hl]

theorem mul_elem_apply_same (u : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (i j : Fin n)
    (h : i < j) (k : Fin n) :
    ((u * elem i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) k j =
        (u : Matrix (Fin n) (Fin n) (ZMod 2)) k j + (u : Matrix (Fin n) (Fin n) (ZMod 2)) k i := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elem, mul_transvection_apply_same i j k 1, one_mul]

theorem apply_col_eq_zero {u : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hu : u ∈ unitriangular n (ZMod 2)) {i j : Fin n} (hij : i < j)
    (hmin : ∀ q ∈ supp u, j ≤ q.2) {k : Fin n} (hk : k ≠ i) :
    (u : Matrix (Fin n) (Fin n) (ZMod 2)) k i = 0 := by
  rcases lt_or_gt_of_ne hk with hki | hik
  · by_contra hne
    have hmem : (k, i) ∈ supp u := by simp [supp, hki, hne]
    exact absurd (hmin _ hmem) (not_le.mpr hij)
  · exact hu.1 k i hik

theorem supp_mul_elem {u : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hu : u ∈ unitriangular n (ZMod 2)) {i j : Fin n} (hij : i < j) (hmem : (i, j) ∈ supp u)
    (hmin : ∀ q ∈ supp u, j ≤ q.2) :
    supp (u * elem i j hij) = (supp u).erase (i, j) := by
  have hu_ij : (u : Matrix (Fin n) (Fin n) (ZMod 2)) i j ≠ 0 := (Finset.mem_filter.mp hmem).2.2
  have h1 : ((u * elem i j hij : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) i j = 0 := by
    rw [mul_elem_apply_same, hu.2 i, zmod_two_eq_one hu_ij]
    rfl
  ext ⟨k, l⟩
  by_cases hkl : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := hkl
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, h1,
      not_true_eq_false, false_and, iff_false, not_and, not_false_eq_true, implies_true]
  · have hentry : ((u * elem i j hij : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) k l = (u : Matrix (Fin n) (Fin n) (ZMod 2)) k l := by
      by_cases hl : l = j
      · subst hl
        rw [mul_elem_apply_same, apply_col_eq_zero hu hij hmin fun hk => hkl ⟨hk, rfl⟩, add_zero]
      · exact mul_elem_apply_of_ne u i j hij k hl
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
      Prod.mk.injEq, hentry, hkl, not_false_eq_true]

theorem closure_involutions_unitriangular (n : ℕ) :
    Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) |
      x ∈ unitriangular n (ZMod 2) ∧ x * x = 1} = unitriangular n (ZMod 2) := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) fun u hu => ?_
  generalize hN : (supp u).card = N
  induction N using Nat.strong_induction_on generalizing u with
  | _ N ih =>
    by_cases hne : (supp u).Nonempty
    · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (supp u) (fun p => p.2) hne
      obtain ⟨i, j⟩ := p
      have hij : i < j := (Finset.mem_filter.mp hp).2.1
      have hmem : u * elem i j hij ∈ unitriangular n (ZMod 2) :=
        (unitriangular n (ZMod 2)).mul_mem hu (elem_mem i j hij)
      have hlt : (supp (u * elem i j hij)).card < N := by
        rw [supp_mul_elem hu hij hp hmin, ← hN]
        exact Finset.card_erase_lt_of_mem hp
      have h1 := ih _ hlt (u * elem i j hij) hmem rfl
      have h2 : elem i j hij ∈ Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) |
          x ∈ unitriangular n (ZMod 2) ∧ x * x = 1} :=
        Subgroup.subset_closure ⟨elem_mem i j hij, elem_mul_self i j hij⟩
      have h3 := Subgroup.mul_mem _ h1 h2
      rwa [mul_assoc, elem_mul_self, mul_one] at h3
    · have hu1 : u = 1 := by
        refine Matrix.SpecialLinearGroup.ext u 1 fun k l => ?_
        rw [Matrix.SpecialLinearGroup.coe_one]
        rcases lt_trichotomy k l with hkl | rfl | hlk
        · rw [one_apply_ne hkl.ne]
          by_contra hne'
          exact hne ⟨(k, l), by simp [supp, hkl, hne']⟩
        · rw [one_apply_eq]
          exact hu.2 k
        · rw [one_apply_ne hlk.ne']
          exact hu.1 k l hlk
      rw [hu1]
      exact Subgroup.one_mem _

theorem smul_eq_map {G : Type*} [Group G] (a : MulAut G) (S : Subgroup G) :
    a • S = S.map a.toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem closure_involutions_map {G N : Type*} [Group G] [Group N] (f : G →* N)
    (hf : Function.Injective f) (S : Subgroup G)
    (h : Subgroup.closure {x | x ∈ S ∧ x * x = 1} = S) :
    Subgroup.closure {x | x ∈ S.map f ∧ x * x = 1} = S.map f := by
  have hset : {x | x ∈ S.map f ∧ x * x = 1} = f '' {x | x ∈ S ∧ x * x = 1} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx2⟩
      refine ⟨y, ⟨hy, hf ?_⟩, rfl⟩
      rw [map_mul, hx2, map_one]
    · rintro ⟨y, ⟨hy, hy2⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [← map_mul, hy2, map_one]⟩
  rw [hset, ← MonoidHom.map_closure, h]

end CFSG.Quasithin.E9P2.FinGen

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

theorem sl2_sylow_gen_involutions (n : ℕ)
    (U : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) (hU : IsSylowTwoOf U ⊤) :
    Subgroup.closure {x | x ∈ U ∧ x * x = 1} = U := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
    have hidx : ¬ 2 ∣ U.index := by
      rw [← Subgroup.relIndex_top_right]
      exact hU.2.2
    let P : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := hU.2.1.toSylow hidx
    have := Sylow.isPretransitive_of_finite (p := 2)
      (G := Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) Q P
    have hUeq : U = MulAut.conj g • unitriangular n (ZMod 2) := by
      have h1 : ((g • Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
          Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) = U := by
        rw [hg]
        rfl
      rw [Sylow.coe_subgroup_smul, hQ] at h1
      exact h1.symm
    rw [hUeq, E9P2.FinGen.smul_eq_map]
    exact E9P2.FinGen.closure_involutions_map _ (MulAut.conj g).injective _
      (E9P2.FinGen.closure_involutions_unitriangular n)

end CFSG.Quasithin
