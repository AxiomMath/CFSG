module

public import Mathlib

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

abbrev V2 : Type := Fin 2 → ZMod 2

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

abbrev GL2 : Type := Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)

theorem V2_add_self (v : V2) : v + v = 0 := by
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this _

theorem V2_neg (v : V2) : -v = v := by
  funext i
  have : ∀ a : ZMod 2, -a = a := by decide
  exact this _

variable {G : Type} [Group G]

structure Coord (A B : Subgroup G) (u : G → V2) : Prop where
  mul : ∀ x ∈ A, ∀ y ∈ A, u (x * y) = u x + u y
  zero : ∀ x ∈ A, u x = 0 ↔ x ∈ B
  surj : ∀ v : V2, ∃ x ∈ A, u x = v

namespace Coord

variable {A B : Subgroup G} {u : G → V2} (hc : Coord A B u)
include hc

theorem map_one : u 1 = 0 := by
  have := hc.mul 1 A.one_mem 1 A.one_mem
  rw [mul_one] at this
  simpa using this.symm

theorem map_inv {x : G} (hx : x ∈ A) : u x⁻¹ = u x := by
  have h := hc.mul x hx x⁻¹ (A.inv_mem hx)
  rw [mul_inv_cancel, hc.map_one] at h
  have h2 : u x + u x⁻¹ = 0 := h.symm
  have h3 : u x⁻¹ = - u x := eq_neg_of_add_eq_zero_right h2
  rw [h3, V2_neg]

theorem mul_inv_mem {x y : G} (hx : x ∈ A) (hy : y ∈ A) (h : u x = u y) : x * y⁻¹ ∈ B := by
  refine (hc.zero _ (A.mul_mem hx (A.inv_mem hy))).mp ?_
  rw [hc.mul x hx y⁻¹ (A.inv_mem hy), hc.map_inv hy, h, V2_add_self]

theorem eq_of_mem {x : G} (hx : x ∈ A) (hxB : x ∈ B) : u x = 0 := (hc.zero x hx).mpr hxB

end Coord

section Action

variable {A B : Subgroup G} {u : G → V2} (hc : Coord A B u) (n : G)

@[expose] noncomputable def Coord.fn : V2 → V2 := fun v =>
  u (n * Classical.choose (hc.surj v) * n⁻¹)

variable {n}

theorem Coord.fn_spec (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A) (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B)
    {x : G} (hx : x ∈ A) : u (n * x * n⁻¹) = hc.fn n (u x) := by
  obtain ⟨hy, hyu⟩ := Classical.choose_spec (hc.surj (u x))
  set y := Classical.choose (hc.surj (u x)) with hydef
  show u (n * x * n⁻¹) = u (n * y * n⁻¹)
  have hxy : x * y⁻¹ ∈ B := hc.mul_inv_mem hx hy hyu.symm
  have hxyA : x * y⁻¹ ∈ A := A.mul_mem hx (A.inv_mem hy)
  have h1 : n * (x * y⁻¹) * n⁻¹ ∈ B := hnB _ ⟨hxyA, hxy⟩
  have h2 : n * (x * y⁻¹) * n⁻¹ ∈ A := hnA _ hxyA
  have hsplit : n * x * n⁻¹ = (n * (x * y⁻¹) * n⁻¹) * (n * y * n⁻¹) := by group
  rw [hsplit, hc.mul _ h2 _ (hnA y hy), hc.eq_of_mem h2 h1, zero_add]

theorem Coord.fn_add (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A) (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B)
    (v v' : V2) : hc.fn n (v + v') = hc.fn n v + hc.fn n v' := by
  obtain ⟨x, hx, rfl⟩ := hc.surj v
  obtain ⟨x', hx', rfl⟩ := hc.surj v'
  rw [← hc.mul x hx x' hx', ← hc.fn_spec hnA hnB (A.mul_mem hx hx'),
    ← hc.fn_spec hnA hnB hx, ← hc.fn_spec hnA hnB hx']
  have : n * (x * x') * n⁻¹ = (n * x * n⁻¹) * (n * x' * n⁻¹) := by group
  rw [this, hc.mul _ (hnA x hx) _ (hnA x' hx')]

theorem Coord.fn_comp {n' : G} (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A)
    (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B) (hn'A : ∀ x ∈ A, n' * x * n'⁻¹ ∈ A)
    (hn'B : ∀ x ∈ A ⊓ B, n' * x * n'⁻¹ ∈ B) (v : V2) :
    hc.fn (n * n') v = hc.fn n (hc.fn n' v) := by
  obtain ⟨x, hx, rfl⟩ := hc.surj v
  have h1 := hc.fn_spec (n := n * n') (fun x hx => by
    have := hnA _ (hn'A x hx)
    simpa [mul_assoc] using this) (fun x hx => by
    have := hnB _ ⟨hn'A x hx.1, hn'B x hx⟩
    simpa [mul_assoc] using this) hx
  rw [← h1, ← hc.fn_spec hn'A hn'B hx, ← hc.fn_spec hnA hnB (hn'A x hx)]
  congr 1
  group

theorem Coord.fn_one (v : V2) : hc.fn (1 : G) v = v := by
  obtain ⟨x, hx, rfl⟩ := hc.surj v
  rw [← hc.fn_spec (n := 1) (fun x hx => by simpa using hx) (fun x hx => by simpa using hx.2) hx]
  simp

@[expose] noncomputable def Coord.lin (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A)
    (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B) : V2 →ₗ[ZMod 2] V2 where
  toFun := hc.fn n
  map_add' := hc.fn_add hnA hnB
  map_smul' c v := by
    have h0 : hc.fn n 0 = 0 := by
      have := hc.fn_add hnA hnB 0 0
      simpa using this
    have hc2 : c = 0 ∨ c = 1 := by
      revert c; decide
    rcases hc2 with rfl | rfl
    · simp [h0]
    · simp

@[expose] noncomputable def Coord.mat (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A)
    (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B) : M2 := LinearMap.toMatrix' (hc.lin hnA hnB)

theorem Coord.mat_mulVec (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A) (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B)
    (v : V2) : hc.mat hnA hnB *ᵥ v = hc.fn n v := by
  rw [Coord.mat, LinearMap.toMatrix'_mulVec]
  rfl

theorem Coord.u_conj (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A) (hnB : ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B)
    {x : G} (hx : x ∈ A) : u (n * x * n⁻¹) = hc.mat hnA hnB *ᵥ u x := by
  rw [hc.mat_mulVec, hc.fn_spec hnA hnB hx]

end Action

section Hom

variable {A B : Subgroup G} {u : G → V2} (hc : Coord A B u) (N : Subgroup G)
  (hA : ∀ n ∈ N, ∀ x ∈ A, n * x * n⁻¹ ∈ A) (hB : ∀ n ∈ N, ∀ x ∈ A ⊓ B, n * x * n⁻¹ ∈ B)

@[expose] noncomputable def Coord.matHom : N →* M2 where
  toFun n := hc.mat (n := (n : G)) (hA n n.2) (hB n n.2)
  map_one' := by
    show LinearMap.toMatrix' _ = 1
    rw [← LinearMap.toMatrix'_id]
    exact congrArg LinearMap.toMatrix' (LinearMap.ext fun v => hc.fn_one v)
  map_mul' n n' := by
    show LinearMap.toMatrix' _ = LinearMap.toMatrix' _ * LinearMap.toMatrix' _
    rw [← LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix'
      (LinearMap.ext fun v => hc.fn_comp (hA n n.2) (hB n n.2) (hA n' n'.2) (hB n' n'.2) v)

@[expose] noncomputable def Coord.rho : N →* GL2 := (hc.matHom N hA hB).toHomUnits

theorem Coord.u_conj' (n : N) {x : G} (hx : x ∈ A) :
    u (n * x * (n : G)⁻¹) = ((hc.rho N hA hB n : GL2) : M2) *ᵥ u x :=
  hc.u_conj (hA n n.2) (hB n n.2) hx

end Hom

structure TData (A A' : Subgroup G) (u w : G → V2) (m : G → M2) : Prop where
  cu : Coord A A' u
  cw : Coord A' A w
  mmul : ∀ x ∈ A ⊓ A', ∀ y ∈ A ⊓ A', m (x * y) = m x + m y
  minj : ∀ x ∈ A ⊓ A', ∀ y ∈ A ⊓ A', m x = m y → x = y
  msurj : ∀ M : M2, ∃ x ∈ A ⊓ A', m x = M
  comm : ∀ x ∈ A, ∀ y ∈ A', x * y * x⁻¹ * y⁻¹ ∈ A ⊓ A' ∧
    m (x * y * x⁻¹ * y⁻¹) = Matrix.vecMulVec (u x) (w y)

theorem TData.m_one {A A' : Subgroup G} {u w : G → V2} {m : G → M2} (hT : TData A A' u w m) :
    m 1 = 0 := by
  have h := hT.mmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [mul_one] at h
  simpa using h.symm

theorem vecMulVec_mulVec_mulVec (P Q : M2) (a b : V2) :
    Matrix.vecMulVec (P *ᵥ a) (Q *ᵥ b) = P * Matrix.vecMulVec a b * Qᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.transpose_apply]
  ring

section TData

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} (hT : TData A A' u w m)
  (N : Subgroup G) (hN : ∀ n ∈ N, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ (∀ x ∈ A', n * x * n⁻¹ ∈ A'))

include hT hN

theorem TData.hA : ∀ n ∈ N, ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun n hn => (hN n hn).1

theorem TData.hB : ∀ n ∈ N, ∀ x ∈ A ⊓ A', n * x * n⁻¹ ∈ A' := fun n hn x hx => (hN n hn).2 x hx.2

theorem TData.hA' : ∀ n ∈ N, ∀ x ∈ A', n * x * n⁻¹ ∈ A' := fun n hn => (hN n hn).2

theorem TData.hB' : ∀ n ∈ N, ∀ x ∈ A' ⊓ A, n * x * n⁻¹ ∈ A := fun n hn x hx => (hN n hn).1 x hx.2

@[expose] noncomputable def TData.rho : N →* GL2 × GL2 :=
  (hT.cu.rho N (hT.hA N hN) (hT.hB N hN)).prod (hT.cw.rho N (hT.hA' N hN) (hT.hB' N hN))

theorem TData.u_conj (n : N) {x : G} (hx : x ∈ A) :
    u (n * x * (n : G)⁻¹) = ((hT.rho N hN n).1 : M2) *ᵥ u x :=
  hT.cu.u_conj' N (hT.hA N hN) (hT.hB N hN) n hx

theorem TData.w_conj (n : N) {x : G} (hx : x ∈ A') :
    w (n * x * (n : G)⁻¹) = ((hT.rho N hN n).2 : M2) *ᵥ w x :=
  hT.cw.u_conj' N (hT.hA' N hN) (hT.hB' N hN) n hx

theorem TData.m_conj (n : N) {x : G} (hx : x ∈ A ⊓ A') :
    m (n * x * (n : G)⁻¹) =
      ((hT.rho N hN n).1 : M2) * m x * ((hT.rho N hN n).2 : M2)ᵀ := by
  have hZ : ∀ y ∈ A ⊓ A', (n : G) * y * (n : G)⁻¹ ∈ A ⊓ A' := fun y hy =>
    ⟨hT.hA N hN n n.2 y hy.1, hT.hB N hN n n.2 y hy⟩
  have key : ∀ M : M2, ∀ y ∈ A ⊓ A', m y = M →
      m ((n : G) * y * (n : G)⁻¹) =
        ((hT.rho N hN n).1 : M2) * M * ((hT.rho N hN n).2 : M2)ᵀ := by
    intro M
    induction M using Matrix.induction_on' with
    | h_zero =>
      intro y hy hym
      have : y = 1 := hT.minj y hy 1 (Subgroup.one_mem _) (by rw [hym, hT.m_one])
      subst this
      simp [hT.m_one]
    | h_add p q hp hq =>
      intro y hy hym
      obtain ⟨xp, hxp, hxpm⟩ := hT.msurj p
      obtain ⟨xq, hxq, hxqm⟩ := hT.msurj q
      have hyy : y = xp * xq := hT.minj y hy _ ((A ⊓ A').mul_mem hxp hxq) (by
        rw [hym, hT.mmul xp hxp xq hxq, hxpm, hxqm])
      have h1 := hp xp hxp hxpm
      have h2 := hq xq hxq hxqm
      have h3 : (n : G) * y * (n : G)⁻¹ =
          ((n : G) * xp * (n : G)⁻¹) * ((n : G) * xq * (n : G)⁻¹) := by rw [hyy]; group
      rw [h3, hT.mmul _ (hZ xp hxp) _ (hZ xq hxq), h1, h2, mul_add, add_mul]
    | h_std_basis i j c =>
      intro y hy hym
      have hc : c = 0 ∨ c = 1 := by
        clear hym; revert c; decide
      rcases hc with rfl | rfl
      · have : y = 1 := hT.minj y hy 1 (Subgroup.one_mem _) (by
          rw [hym, hT.m_one]; simp)
        subst this
        simp [hT.m_one]
      · obtain ⟨xi, hxi, hxiu⟩ := hT.cu.surj (Pi.single i 1)
        obtain ⟨yj, hyj, hyjw⟩ := hT.cw.surj (Pi.single j 1)
        obtain ⟨hzmem, hzm⟩ := hT.comm xi hxi yj hyj
        have hyz : y = xi * yj * xi⁻¹ * yj⁻¹ := hT.minj y hy _ hzmem (by
          rw [hym, hzm, hxiu, hyjw, ← Matrix.single_eq_single_vecMulVec_single]) 
        have h4 : (n : G) * y * (n : G)⁻¹ =
            ((n : G) * xi * (n : G)⁻¹) * ((n : G) * yj * (n : G)⁻¹) *
              ((n : G) * xi * (n : G)⁻¹)⁻¹ * ((n : G) * yj * (n : G)⁻¹)⁻¹ := by
          rw [hyz]; group
        obtain ⟨-, hm5⟩ := hT.comm _ (hT.hA N hN n n.2 xi hxi) _ (hT.hA' N hN n n.2 yj hyj)
        rw [h4, hm5, hT.u_conj N hN n hxi, hT.w_conj N hN n hyj, hxiu, hyjw,
          vecMulVec_mulVec_mulVec, ← Matrix.single_eq_single_vecMulVec_single]
  exact key _ x hx rfl

end TData

end CFSG.Quasithin.A94.HeJ
