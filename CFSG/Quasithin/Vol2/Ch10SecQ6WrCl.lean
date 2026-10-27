module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrMN

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def wv (k : Fin 5) : Fin 5 → ZMod 2 := fun i => if i = k then 0 else 1

theorem isO_wv : ∀ k, IsO (wv k) := by decide

theorem pv_wv (σ : Perm (Fin 5)) (k : Fin 5) : pv σ (wv k) = wv (σ k) := by
  funext i
  simp only [pv, wv, Perm.inv_eq_iff_eq]

@[expose] def m0 : PMod := sumv (wv 4) (wv 4)

@[expose] def n0 : PMod := tens (wv 4) (wv 4)

theorem gP_m0 {y : SymFiveWrTwo} (hy : y ∈ Y0) : gP y m0 = m0 := by
  have h1 : y.left 1 4 = 4 := hy 1
  have hz : y.left zs 4 = 4 := hy zs
  unfold m0
  rcases zmod2_cases y.right with hr | hr
  · rw [gP_sumv_base hr, pv_wv, pv_wv, h1, hz]
  · rw [gP_sumv_swap hr, pv_wv, pv_wv, h1, hz]

theorem gP_n0 {y : SymFiveWrTwo} (hy : y ∈ Y0) : gP y n0 = n0 := by
  have h1 : y.left 1 4 = 4 := hy 1
  have hz : y.left zs 4 = 4 := hy zs
  unfold n0
  rcases zmod2_cases y.right with hr | hr
  · rw [gP_tens_base hr, pv_wv, pv_wv, h1, hz]
  · rw [gP_tens_swap hr, pv_wv, pv_wv, h1, hz]

theorem rep_right (x : Fin 5 × Fin 5) : (rep x).right = 1 := wrBaseHom_right _

theorem rep_left_one (x : Fin 5 × Fin 5) : (rep x).left 1 = swap 4 x.1 := by
  simp [rep, wrBaseHom_left]

theorem rep_left_zs (x : Fin 5 × Fin 5) : (rep x).left zs = swap 4 x.2 := by
  simp [rep, wrBaseHom_left]

@[expose] def Tv (x : Fin 5 × Fin 5) : PMod := gP (rep x) m0

@[expose] def Rv (x : Fin 5 × Fin 5) : PMod := gP (rep x) n0

theorem Tv_eq (x : Fin 5 × Fin 5) : Tv x = sumv (wv x.1) (wv x.2) := by
  rw [Tv, m0, gP_sumv_base (rep_right x), pv_wv, pv_wv, rep_left_one, rep_left_zs,
    swap_apply_left, swap_apply_left]

theorem Rv_eq (x : Fin 5 × Fin 5) : Rv x = tens (wv x.1) (wv x.2) := by
  rw [Rv, n0, gP_tens_base (rep_right x), pv_wv, pv_wv, rep_left_one, rep_left_zs,
    swap_apply_left, swap_apply_left]

theorem mul_rep_eq (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) :
    g * rep x = rep (pairAct g x) * ((rep (pairAct g x))⁻¹ * g * rep x) := by
  group

theorem gP_Tv (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) : gP g (Tv x) = Tv (pairAct g x) := by
  rw [Tv, ← gP_mul, mul_rep_eq, gP_mul, gP_m0 (rep_inv_mul_mem_Y0 g x), Tv]

theorem gP_Rv (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) : gP g (Rv x) = Rv (pairAct g x) := by
  rw [Rv, ← gP_mul, mul_rep_eq, gP_mul, gP_n0 (rep_inv_mul_mem_Y0 g x), Rv]

@[expose] def gPHom (g : SymFiveWrTwo) : PMod →+ PMod where
  toFun := gP g
  map_zero' := gP_zero g
  map_add' := gP_add g

@[expose] def Mcl : AddSubgroup PMod := AddSubgroup.closure (Set.range Tv)

@[expose] def Ncl : AddSubgroup PMod := AddSubgroup.closure (Set.range Rv)

theorem Tv_mem_Mcl (x : Fin 5 × Fin 5) : Tv x ∈ Mcl := AddSubgroup.subset_closure ⟨x, rfl⟩

theorem Rv_mem_Ncl (x : Fin 5 × Fin 5) : Rv x ∈ Ncl := AddSubgroup.subset_closure ⟨x, rfl⟩

theorem gP_mem_Mcl (g : SymFiveWrTwo) {p : PMod} (hp : p ∈ Mcl) : gP g p ∈ Mcl := by
  have hle : Mcl ≤ Mcl.comap (gPHom g) := by
    rw [Mcl, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change gP g (Tv x) ∈ Mcl
    rw [gP_Tv]
    exact Tv_mem_Mcl _
  exact hle hp

theorem gP_mem_Ncl (g : SymFiveWrTwo) {p : PMod} (hp : p ∈ Ncl) : gP g p ∈ Ncl := by
  have hle : Ncl ≤ Ncl.comap (gPHom g) := by
    rw [Ncl, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change gP g (Rv x) ∈ Ncl
    rw [gP_Rv]
    exact Rv_mem_Ncl _
  exact hle hp

theorem Mcl_le_Mmod : Mcl ≤ Mmod := by
  rw [Mcl, AddSubgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  rw [Tv_eq]
  exact sumv_mem_Mmod (isO_wv _) (isO_wv _)

theorem Ncl_le_Nmod : Ncl ≤ Nmod := by
  rw [Ncl, AddSubgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  rw [Rv_eq]
  exact tens_mem_Nmod (isO_wv _) (isO_wv _)

@[expose] def delta (x : Fin 5 × Fin 5) : PMod := fun i j => if (i, j) = x then 1 else 0

theorem delta_eq (x : Fin 5 × Fin 5) : delta x = Rv x + Tv x + fun _ _ => 1 := by
  funext i j
  rw [Rv_eq, Tv_eq]
  simp only [delta, tens, sumv, wv, Pi.add_apply, Prod.ext_iff]
  by_cases hi : i = x.1 <;> by_cases hj : j = x.2 <;> simp [hi, hj] <;> decide

set_option maxRecDepth 10000 in
theorem exists_four_wv : ∀ u : Fin 5 → ZMod 2, IsO u →
    ∃ k k' l l' : Fin 5, u = wv k + wv k' + wv l + wv l' := by
  decide +kernel

theorem zmod_four_left (a b c d e : ZMod 2) :
    a + b + c + d + 0 = a + e + (b + e) + (c + e) + (d + e) := by
  revert a b c d e
  decide

theorem zmod_four_right (a b c d e : ZMod 2) :
    0 + (a + b + c + d) = e + a + (e + b) + (e + c) + (e + d) := by
  revert a b c d e
  decide

theorem sumv_left_mem_Mcl {u : Fin 5 → ZMod 2} (hu : IsO u) : sumv u 0 ∈ Mcl := by
  obtain ⟨k, k', l, l', rfl⟩ := exists_four_wv u hu
  have h : sumv (wv k + wv k' + wv l + wv l') 0 =
      Tv (k, 4) + Tv (k', 4) + Tv (l, 4) + Tv (l', 4) := by
    funext i j
    simp only [Tv_eq, sumv, Pi.add_apply, Pi.zero_apply]
    exact zmod_four_left _ _ _ _ _
  rw [h]
  exact add_mem (add_mem (add_mem (Tv_mem_Mcl _) (Tv_mem_Mcl _)) (Tv_mem_Mcl _)) (Tv_mem_Mcl _)

theorem sumv_right_mem_Mcl {u : Fin 5 → ZMod 2} (hu : IsO u) : sumv 0 u ∈ Mcl := by
  obtain ⟨k, k', l, l', rfl⟩ := exists_four_wv u hu
  have h : sumv 0 (wv k + wv k' + wv l + wv l') =
      Tv (4, k) + Tv (4, k') + Tv (4, l) + Tv (4, l') := by
    funext i j
    simp only [Tv_eq, sumv, Pi.add_apply, Pi.zero_apply]
    exact zmod_four_right _ _ _ _ _
  rw [h]
  exact add_mem (add_mem (add_mem (Tv_mem_Mcl _) (Tv_mem_Mcl _)) (Tv_mem_Mcl _)) (Tv_mem_Mcl _)

theorem tens_add_left (a a' b : Fin 5 → ZMod 2) : tens (a + a') b = tens a b + tens a' b := by
  funext i j
  simp only [tens, Pi.add_apply, add_mul]

theorem tens_add_right (a b b' : Fin 5 → ZMod 2) : tens a (b + b') = tens a b + tens a b' := by
  funext i j
  simp only [tens, Pi.add_apply, mul_add]

theorem tens_wv_mem_Ncl (k l : Fin 5) : tens (wv k) (wv l) ∈ Ncl := by
  rw [show tens (wv k) (wv l) = Rv (k, l) from (Rv_eq (k, l)).symm]
  exact Rv_mem_Ncl _

theorem tens_mem_Ncl {u v : Fin 5 → ZMod 2} (hu : IsO u) (hv : IsO v) : tens u v ∈ Ncl := by
  obtain ⟨k, k', l, l', rfl⟩ := exists_four_wv u hu
  obtain ⟨m, m', n, n', rfl⟩ := exists_four_wv v hv
  simp only [tens_add_left, tens_add_right]
  repeat' (first | exact tens_wv_mem_Ncl _ _ | apply add_mem)

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
