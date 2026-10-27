module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Geo

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem b3b_fix_y (F : FanTree Γ G) (C : Ctx L T a) {g : G}
    (hg : g ∈ ballStab Γ G 2 (xv T a 4)) {j : ℤ} (hj2 : 2 ≤ j) (hj4 : j ≤ 4) :
    g • zA L T a 5 • xv T a j = zA L T a 5 • xv T a j := by
  have hx4 : zA L T a 5 • xv T a 4 = xv T a 4 := (zA_fix C 5 4).2 (by omega)
  have h := dist_smul F (zA L T a 5) (xv T a 4) (xv T a j)
  rw [hx4] at h
  have hd : Γ.dist (xv T a 4) (zA L T a 5 • xv T a j) ≤ 2 := by
    rw [h, dist_comm, xv_dist F T a hj4]
    omega
  exact mem_ballStab.1 hg _ hd

theorem b3b (F : FanTree Γ G) (_h40 : Fan40 F) (E : EG L T a) :
    wE L T a * uE L T a = 1 ∨ wE L T a * uE L T a = L.z (zA L T a 5 • xv T a 2) := by
  have C := E.ctx
  have H := E.lab
  have s0 : zA L T a 0 * zA L T a 0 = 1 := zA_sq F C 0
  have s4 : zA L T a 4 * zA L T a 4 = 1 := zA_sq F C 4
  have s5 : zA L T a 5 * zA L T a 5 = 1 := zA_sq F C 5
  have i0 : (zA L T a 0)⁻¹ = zA L T a 0 := inv_eq_of_mul_eq_one_right s0
  have i4 : (zA L T a 4)⁻¹ = zA L T a 4 := inv_eq_of_mul_eq_one_right s4
  have i5 : (zA L T a 5)⁻¹ = zA L T a 5 := inv_eq_of_mul_eq_one_right s5
  have c45 : zA L T a 5 * zA L T a 4 = zA L T a 4 * zA L T a 5 := zA_comm F H C 4
  have hv0 : valence Γ (zA L T a 5 • xv T a 0) = 5 := by
    rw [F.valence_smul_eq]
    exact C.val5
  have hY : zY L T a = L.z (zA L T a 5 • xv T a 0) := rfl
  have sY : zY L T a * zY L T a = 1 := (L.isCentral _ hv0).2.2.1
  have e0 : L.z (xv T a 0) = zA L T a 0 := by simp [zA]
  have hZ : zY L T a = zA L T a 5 * zA L T a 0 * zA L T a 5 := by
    rw [hY, L.equivariant (zA L T a 5) (xv T a 0) C.val5, e0, i5]
  have hP : L.z (zA L T a 0 • zA L T a 5 • xv T a 0) =
      zA L T a 0 * zY L T a * zA L T a 0 := by
    rw [L.equivariant (zA L T a 0) _ hv0, ← hY, i0]
  have hQ : L.z (zA L T a 4 • zA L T a 5 • xv T a 0) =
      zA L T a 4 * zY L T a * zA L T a 4 := by
    rw [L.equivariant (zA L T a 4) _ hv0, ← hY, i4]
  have hx8v : valence Γ (xv T a 8) = 5 := C.val_even F 4
  have hX : L.z (zA L T a 0 • xv T a 8) = zA L T a 0 * zA L T a 4 * zA L T a 0 := by
    rw [L.equivariant (zA L T a 0) _ hx8v, i0]
    rfl
  have hx6 : zA L T a 0 • xv T a 6 = xv T a 6 := (zA_fix C 0 6).2 (by omega)
  have hd8 : Γ.dist (xv T a 6) (zA L T a 0 • xv T a 8) ≤ 2 := by
    have h := dist_smul F (zA L T a 0) (xv T a 6) (xv T a 8)
    rw [hx6] at h
    rw [h, xv_dist F T a (by omega)]
    omega
  have hf8 : zA L T a 5 • zA L T a 0 • xv T a 8 = zA L T a 0 • xv T a 8 :=
    mem_ballStab.1 E.hA5 _ hd8
  have hv8 : valence Γ (zA L T a 0 • xv T a 8) = 5 := by
    rw [F.valence_smul_eq]
    exact hx8v
  have hcz : zA L T a 5 * L.z (zA L T a 0 • xv T a 8) =
      L.z (zA L T a 0 • xv T a 8) * zA L T a 5 :=
    z_comm hv8 (MulAction.mem_stabilizer_iff.2 hf8)
  have hu5 : zA L T a 5 * uE L T a = uE L T a * zA L T a 5 := by
    have hu : uE L T a = (zA L T a 0 * zA L T a 4 * zA L T a 0) * zA L T a 4 := rfl
    rw [hu, ← hX]
    calc zA L T a 5 * (L.z (zA L T a 0 • xv T a 8) * zA L T a 4)
        = (zA L T a 5 * L.z (zA L T a 0 • xv T a 8)) * zA L T a 4 := (mul_assoc _ _ _).symm
      _ = (L.z (zA L T a 0 • xv T a 8) * zA L T a 5) * zA L T a 4 := by rw [hcz]
      _ = L.z (zA L T a 0 • xv T a 8) * (zA L T a 5 * zA L T a 4) := mul_assoc _ _ _
      _ = L.z (zA L T a 0 • xv T a 8) * (zA L T a 4 * zA L T a 5) := by rw [c45]
      _ = (L.z (zA L T a 0 • xv T a 8) * zA L T a 4) * zA L T a 5 := (mul_assoc _ _ _).symm
  have hu5' : zA L T a 5 * uE L T a * zA L T a 5 = uE L T a := by
    rw [hu5, mul_assoc, s5, mul_one]
  have hcj : ∀ g : G, zA L T a 5 * g * zA L T a 5 = MulAut.conj (zA L T a 5) g := by
    intro g
    simp [MulAut.conj_apply, i5]
  have h45 : zA L T a 5 * zA L T a 4 * zA L T a 5 = zA L T a 4 := by
    rw [c45, mul_assoc, s5, mul_one]
  have hA0c : MulAut.conj (zA L T a 5) (zA L T a 0) = zY L T a := by
    rw [← hcj, ← hZ]
  have hA4c : MulAut.conj (zA L T a 5) (zA L T a 4) = zA L T a 4 := by
    rw [← hcj]
    exact h45
  have hconj : zA L T a 5 * uE L T a * zA L T a 5 =
      zY L T a * (zA L T a 4 * zY L T a * zA L T a 4) := by
    rw [hcj]
    have hu : uE L T a = zA L T a 0 * zA L T a 4 * zA L T a 0 * zA L T a 4 := rfl
    rw [hu, map_mul, map_mul, map_mul, hA0c, hA4c]
    simp only [mul_assoc]
  have hu : uE L T a = zY L T a * (zA L T a 4 * zY L T a * zA L T a 4) :=
    hu5'.symm.trans hconj
  have hw : wE L T a = (zA L T a 0 * zY L T a * zA L T a 0) * zY L T a := rfl
  have hprod : wE L T a * uE L T a =
      (zA L T a 0 * zY L T a * zA L T a 0) * (zA L T a 4 * zY L T a * zA L T a 4) := by
    rw [hw, hu]
    calc zA L T a 0 * zY L T a * zA L T a 0 * zY L T a *
          (zY L T a * (zA L T a 4 * zY L T a * zA L T a 4))
        = (zA L T a 0 * zY L T a * zA L T a 0) *
          ((zY L T a * zY L T a) * (zA L T a 4 * zY L T a * zA L T a 4)) := by
          simp only [mul_assoc]
      _ = _ := by rw [sY, one_mul]
  have hyadj : ∀ i : ℤ, Γ.Adj (zA L T a 5 • xv T a i) (zA L T a 5 • xv T a (i + 1)) :=
    fun i => (F.adj_smul _ _ _).2 (xv_adj T a i)
  have h12 : Γ.Adj (zA L T a 5 • xv T a 1) (zA L T a 5 • xv T a 2) := hyadj 1
  have h23 : Γ.Adj (zA L T a 5 • xv T a 2) (zA L T a 5 • xv T a 3) := hyadj 2
  have h01 : Γ.Adj (zA L T a 5 • xv T a 0) (zA L T a 5 • xv T a 1) := hyadj 0
  have hA0y2 := b3b_fix_y F C E.hA0 (j := 2) le_rfl (by norm_num)
  have hA0y3 := b3b_fix_y F C E.hA0 (j := 3) (by norm_num) (by norm_num)
  have hA4y2 := b3b_fix_y F C E.hA4 (j := 2) le_rfl (by norm_num)
  have hA4y3 := b3b_fix_y F C E.hA4 (j := 3) (by norm_num) (by norm_num)
  have hm0 : zA L T a 0 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1 := E.hb2
  have hm4 : zA L T a 4 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1 := by
    intro h
    have hx1 : zA L T a 4 • xv T a 1 ≠ xv T a 1 := fun h' =>
      absurd ((zA_fix C 4 1).1 h') (by omega)
    apply hx1
    have h2 : (zA L T a 4 * zA L T a 5) • xv T a 1 = (zA L T a 5 * zA L T a 4) • xv T a 1 := by
      rw [c45]
    rw [mul_smul, mul_smul] at h2
    have h3 : zA L T a 5 • zA L T a 4 • xv T a 1 = zA L T a 5 • xv T a 1 := by
      rw [← h2, h]
    exact MulAction.injective (zA L T a 5) h3
  have hsame := same_action F h23 s0 s4 hA0y2 hA0y3 hA4y2 hA4y3 h12.symm hm0 hm4
  have hxi : zA L T a 0 • zA L T a 5 • xv T a 1 = zA L T a 4 • zA L T a 5 • xv T a 1 :=
    hsame _ h12.symm
  have hval1 : valence Γ (zA L T a 0 • zA L T a 5 • xv T a 1) = 3 := by
    rw [F.valence_smul_eq, F.valence_smul_eq]
    exact C.val_odd F 0
  have hxP : Γ.Adj (zA L T a 0 • zA L T a 5 • xv T a 1) (zA L T a 0 • zA L T a 5 • xv T a 0) :=
    (F.adj_smul _ _ _).2 h01.symm
  have hxQ : Γ.Adj (zA L T a 0 • zA L T a 5 • xv T a 1) (zA L T a 4 • zA L T a 5 • xv T a 0) := by
    rw [hxi]
    exact (F.adj_smul _ _ _).2 h01.symm
  have hxy : Γ.Adj (zA L T a 0 • zA L T a 5 • xv T a 1) (zA L T a 5 • xv T a 2) := by
    have := (F.adj_smul (zA L T a 0) _ _).2 h12
    rwa [hA0y2] at this
  have hne0 : zA L T a 5 • xv T a 2 ≠ zA L T a 0 • zA L T a 5 • xv T a 0 := by
    intro h
    have e : zA L T a 0 • zA L T a 5 • xv T a 2 =
        zA L T a 0 • (zA L T a 0 • zA L T a 5 • xv T a 0) := by rw [← h]
    rw [hA0y2, ← mul_smul, s0, one_smul] at e
    exact xv_ne T a 0 (MulAction.injective (zA L T a 5) e).symm
  have hne4 : zA L T a 5 • xv T a 2 ≠ zA L T a 4 • zA L T a 5 • xv T a 0 := by
    intro h
    have e : zA L T a 4 • zA L T a 5 • xv T a 2 =
        zA L T a 4 • (zA L T a 4 • zA L T a 5 • xv T a 0) := by rw [← h]
    rw [hA4y2, ← mul_smul, s4, one_smul] at e
    exact xv_ne T a 0 (MulAction.injective (zA L T a 5) e).symm
  rw [hprod, ← hP, ← hQ]
  exact lab_pair_of_three F H.hyp hval1 hxy hxP hxQ hne0 hne4

end P518

end CFSG.Quasithin.Fan86
