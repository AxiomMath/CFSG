module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Z4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def xv (T : Track Γ G) (a i : ℤ) : V := T.line.vert (a + 1 + i)

theorem xv_adj (T : Track Γ G) (a i : ℤ) : Γ.Adj (xv T a i) (xv T a (i + 1)) := by
  show Γ.Adj (T.line.vert (a + 1 + i)) (T.line.vert (a + 1 + (i + 1)))
  rw [← add_assoc]
  exact T.line.adj _

theorem xv_adj' (T : Track Γ G) (a i : ℤ) : Γ.Adj (xv T a (i + 1)) (xv T a i) :=
  (xv_adj T a i).symm

theorem xv_ne (T : Track Γ G) (a i : ℤ) : xv T a i ≠ xv T a (i + 2) := by
  show T.line.vert (a + 1 + i) ≠ T.line.vert (a + 1 + (i + 2))
  rw [← add_assoc]
  exact T.line.nb _

theorem xv_inj (F : FanTree Γ G) (T : Track Γ G) (a : ℤ) {i j : ℤ} (h : xv T a i = xv T a j) :
    i = j := by
  have := Line.vert_injective F.isTree T.line h
  omega

theorem xv_dist (F : FanTree Γ G) (T : Track Γ G) (a : ℤ) {i j : ℤ} (h : i ≤ j) :
    Γ.dist (xv T a i) (xv T a j) = (j - i).toNat := by
  have := Line.dist_eq F.isTree T.line (i := a + 1 + i) (j := a + 1 + j) (by omega)
  rw [show a + 1 + j - (a + 1 + i) = j - i by omega] at this
  exact this

theorem xv_dist_two (F : FanTree Γ G) (T : Track Γ G) (a i : ℤ) :
    Γ.dist (xv T a i) (xv T a (i + 2)) = 2 := by
  rw [xv_dist F T a (by omega)]
  simp

theorem xv_dist_two' (F : FanTree Γ G) (T : Track Γ G) (a i : ℤ) :
    Γ.dist (xv T a (i + 2)) (xv T a i) = 2 := by
  rw [dist_comm]
  exact xv_dist_two F T a i

theorem xv_br_fwd (T : Track Γ G) (a i : ℤ) :
    Br Γ (xv T a i) (xv T a (i + 1)) (xv T a (i + 2)) := by
  refine ⟨xv_adj T a i, ?_, fun h => xv_ne T a i h.symm⟩
  have := xv_adj T a (i + 1)
  rwa [show i + 1 + 1 = i + 2 by omega] at this

theorem xv_br_bwd (T : Track Γ G) (a i : ℤ) :
    Br Γ (xv T a (i + 2)) (xv T a (i + 1)) (xv T a i) :=
  (xv_br_fwd T a i).symm

theorem xv_smul (T : Track Γ G) (a k i : ℤ) : T.τ ^ k • xv T a i = xv T a (i + 2 * k) := by
  show T.τ ^ k • T.line.vert (a + 1 + i) = T.line.vert (a + 1 + (i + 2 * k))
  rw [T.zpow_smul_vert, add_assoc]

structure Ctx (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : Prop where
  val5 : valence Γ (xv T a 0) = 5
  fix : ∀ i : ℤ, L.z (xv T a 0) • xv T a i = xv T a i ↔ -6 ≤ i ∧ i ≤ 6

variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem Ctx.val_even (F : FanTree Γ G) (C : Ctx L T a) (k : ℤ) :
    valence Γ (xv T a (2 * k)) = 5 := by
  have := P514.valence_vert_add_two_mul F T.line (a + 1) k
  have h5 : valence Γ (T.line.vert (a + 1)) = 5 := by simpa [xv] using C.val5
  rw [show xv T a (2 * k) = T.line.vert (a + 1 + 2 * k) from rfl, this, h5]

theorem Ctx.val_odd (F : FanTree Γ G) (C : Ctx L T a) (k : ℤ) :
    valence Γ (xv T a (2 * k + 1)) = 3 :=
  F.val3_of_adj_val5 (xv_adj T a (2 * k)) (C.val_even F k)

@[expose] def zA (L : ZLab Γ G) (T : Track Γ G) (a k : ℤ) : G := L.z (xv T a (2 * k))

@[expose] def zY (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : G := L.z (zA L T a 5 • xv T a 0)

@[expose] def wE (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : G :=
  zA L T a 0 * zY L T a * zA L T a 0 * zY L T a

@[expose] def uE (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : G :=
  zA L T a 0 * zA L T a 4 * zA L T a 0 * zA L T a 4

theorem zA_eq (C : Ctx L T a) (k : ℤ) :
    zA L T a k = T.τ ^ k * L.z (xv T a 0) * T.τ ^ (-k) := by
  have := L.equivariant (T.τ ^ k) (xv T a 0) C.val5
  rw [xv_smul, zero_add] at this
  rw [zA, this, zpow_neg]

theorem zA_fix (C : Ctx L T a) (k i : ℤ) :
    zA L T a k • xv T a i = xv T a i ↔ 2 * k - 6 ≤ i ∧ i ≤ 2 * k + 6 := by
  rw [zA_eq C k]
  have h := P514.lab_smul_iff T (L.z (xv T a 0)) k (a + 1 + i)
  have e : a + 1 + i - 2 * k = a + 1 + (i - 2 * k) := by ring
  rw [e] at h
  have h2 := C.fix (i - 2 * k)
  show P514.lab T (L.z (xv T a 0)) k • T.line.vert (a + 1 + i) = T.line.vert (a + 1 + i) ↔ _
  rw [h]
  have : L.z (xv T a 0) • T.line.vert (a + 1 + (i - 2 * k)) = T.line.vert (a + 1 + (i - 2 * k)) ↔
      -6 ≤ i - 2 * k ∧ i - 2 * k ≤ 6 := h2
  rw [this]
  omega

theorem zA_sq (F : FanTree Γ G) (C : Ctx L T a) (k : ℤ) : zA L T a k * zA L T a k = 1 :=
  (L.isCentral _ (C.val_even F k)).2.2.1

theorem zA_comm (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a) (k : ℤ) :
    zA L T a (k + 1) * zA L T a k = zA L T a k * zA L T a (k + 1) := by
  have := z_comm_dist F H.hyp (d := xv T a (2 * (k + 1))) (l := xv T a (2 * k))
    (C.val_even F (k + 1)) (by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      exact xv_dist_two' F T a (2 * k))
  exact this.symm

structure EG (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : Prop where
  lab : Lab18 L
  ctx : Ctx L T a
  hA0 : zA L T a 0 ∈ ballStab Γ G 2 (xv T a 4)
  hA4 : zA L T a 4 ∈ ballStab Γ G 2 (xv T a 4)
  hA5 : zA L T a 5 ∈ ballStab Γ G 2 (xv T a 6)
  hb2 : zA L T a 0 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1

end P518

end CFSG.Quasithin.Fan86
