module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Far

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem tri_rel {za zb zc : G} (ha : za * za = 1) (hb : zb * zb = 1) (hc : zc * zc = 1)
    (h : za * zb * zc = 1) : za * zb = zc ∧ zb * za = zc ∧ zb * zc = za ∧ zc * zb = za ∧
      za * zc = zb ∧ zc * za = zb := by
  have ia : za⁻¹ = za := inv_eq_of_mul_eq_one_right ha
  have ib : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hb
  have ic : zc⁻¹ = zc := inv_eq_of_mul_eq_one_right hc
  have h1 : za * zb = zc := (eq_inv_of_mul_eq_one_left h).trans ic
  have h2 : zb * za = zc := by
    calc zb * za = (za * zb)⁻¹ := by rw [mul_inv_rev, ia, ib]
      _ = zc := by rw [h1, ic]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · calc zb * zc = zb * (zb * za) := by rw [h2]
      _ = za := by rw [← mul_assoc, hb, one_mul]
  · calc zc * zb = za * zb * zb := by rw [h1]
      _ = za := by rw [mul_assoc, hb, mul_one]
  · calc za * zc = za * (za * zb) := by rw [h1]
      _ = zb := by rw [← mul_assoc, ha, one_mul]
  · calc zc * za = zb * za * za := by rw [h2]
      _ = zb := by rw [mul_assoc, ha, mul_one]

theorem dist_le_four (F : FanTree Γ G) (L : ZLab Γ G)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    {x y : V} (hx : Fan86.valence Γ x = 5) (hy : Fan86.valence Γ y = 5)
    (hc : L.z x * L.z y = L.z y * L.z x) : Γ.dist x y ≤ 4 := by
  have hg2 : L.z y * L.z y = 1 := (L.isCentral y hy).2.2.1
  have hgg : ∀ v : V, L.z y • L.z y • v = v := fun v => by rw [← mul_smul, hg2, one_smul]
  have h1 : ∀ v, Γ.dist x v ≤ 4 → Γ.dist x (L.z y • v) ≤ 4 := by
    intro v hv
    have hv' : L.z x • v = v := by
      have : v ∈ fixedPts (V := V) (L.z x) := by rw [hfix x hx]; exact hv
      exact this
    have : L.z y • v ∈ fixedPts (V := V) (L.z x) := by
      show L.z x • L.z y • v = L.z y • v
      rw [← mul_smul, hc, mul_smul, hv']
    rw [hfix x hx] at this
    exact this
  have h2 : L.z y • x = x := by
    refine eq_of_ball_subset F (n := 4) fun v hv => ?_
    have e : Γ.dist (L.z y • x) v = Γ.dist x (L.z y • v) := by
      have := dist_smul F (L.z y) (L.z y • x) v
      rw [hgg] at this
      exact this.symm
    have := h1 (L.z y • v) (by rw [← e]; exact hv)
    rwa [hgg] at this
  have hxf : x ∈ fixedPts (V := V) (L.z y) := h2
  rw [hfix y hy] at hxf
  rw [SimpleGraph.dist_comm]
  exact hxf

theorem ball_inter_subset (L : ZLab Γ G)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    {x y w : V} (hx : Fan86.valence Γ x = 5) (hy : Fan86.valence Γ y = 5)
    (hw : Fan86.valence Γ w = 5) (hz : L.z x * L.z y = L.z w) {v : V} (hvx : Γ.dist x v ≤ 4)
    (hvy : Γ.dist y v ≤ 4) : Γ.dist w v ≤ 4 := by
  have h1 : L.z x • v = v := by
    have : v ∈ fixedPts (V := V) (L.z x) := by rw [hfix x hx]; exact hvx
    exact this
  have h2 : L.z y • v = v := by
    have : v ∈ fixedPts (V := V) (L.z y) := by rw [hfix y hy]; exact hvy
    exact this
  have h3 : v ∈ fixedPts (V := V) (L.z w) := by
    show L.z w • v = v
    rw [← hz, mul_smul, h2, h1]
  rw [hfix w hw] at h3
  exact h3

theorem pair_two (F : FanTree Γ G) (L : ZLab Γ G)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    {x y w : V} (hx : Fan86.valence Γ x = 5) (hy : Fan86.valence Γ y = 5)
    (hw : Fan86.valence Γ w = 5) (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (hz : L.z x * L.z y = L.z w) (hd : Γ.dist x y = 2) :
    ∃ β, ({x, y, w} : Set V) = Γ.neighborSet β := by
  obtain ⟨P, hP0, hP2⟩ := IsTree.exists_arc F.isTree 2 x y hd
  have hxm : Γ.Adj x (P.vert 1) := by
    have := P.adj 0 (by norm_num)
    rwa [hP0] at this
  have hmy : Γ.Adj (P.vert 1) y := by
    have := P.adj 1 (by norm_num)
    rwa [hP2] at this
  have hm3 : Fan86.valence Γ (P.vert 1) = 3 := valence_adj_three F hx hxm
  have dxm : Γ.dist x (P.vert 1) = 1 := dist_eq_one_iff_adj.mpr hxm
  have dym : Γ.dist y (P.vert 1) = 1 := dist_eq_one_iff_adj.mpr hmy.symm
  have hsub : ∀ v, Γ.dist (P.vert 1) v ≤ 3 → Γ.dist w v ≤ 4 := by
    intro v hv
    refine ball_inter_subset L hfix hx hy hw hz ?_ ?_
    · have := F.isTree.connected.dist_triangle (u := x) (v := P.vert 1) (w := v)
      omega
    · have := F.isTree.connected.dist_triangle (u := y) (v := P.vert 1) (w := v)
      omega
  obtain ⟨v, hv1, hv2⟩ := exists_far F (P.vert 1) w 3
  have hwm : Γ.dist w (P.vert 1) ≤ 1 := by
    have := hsub v (le_of_eq hv1)
    omega
  have hne : w ≠ P.vert 1 := fun h => by
    rw [h] at hw
    omega
  have hwm1 : Γ.Adj (P.vert 1) w := by
    have hpos := F.isTree.connected.pos_dist_of_ne hne
    exact (dist_eq_one_iff_adj.mp (by omega : Γ.dist w (P.vert 1) = 1)).symm
  obtain ⟨c, hc, hxc, hyc⟩ := exists_third_neighbor hm3 hxm.symm hmy hxy
  have hwc : w ∈ ({x, y, c} : Set V) := by
    rw [← hc]
    exact hwm1
  refine ⟨P.vert 1, ?_⟩
  rw [hc]
  rcases hwc with rfl | rfl | rfl
  · exact absurd rfl hxw
  · exact absurd rfl hyw
  · rfl

theorem pair_four (F : FanTree Γ G) (L : ZLab Γ G)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    {x y w : V} (hx : Fan86.valence Γ x = 5) (hy : Fan86.valence Γ y = 5)
    (hw : Fan86.valence Γ w = 5) (hz : L.z x * L.z y = L.z w) (hd : Γ.dist x y = 4)
    (hxw : Γ.dist x w = 4) :
    ∃ m, Fan86.valence Γ m = 5 ∧ Γ.dist m x = 2 ∧ Γ.dist m y = 2 ∧ Γ.dist m w = 2 := by
  obtain ⟨P, hP0, hP4⟩ := IsTree.exists_arc F.isTree 4 x y hd
  have hmx : Γ.dist x (P.vert 2) = 2 := by
    have := Arc.dist_eq F.isTree P 2 (by norm_num)
    rwa [hP0] at this
  have hmy : Γ.dist (P.vert 2) y = 2 := by
    have := Arc.dist_vert F.isTree P (i := 2) (j := 4) (by norm_num) le_rfl
    rw [hP4] at this
    exact this
  have hv : Fan86.valence Γ (P.vert 2) = 5 := valence_of_dist_even F hx (by rw [hmx])
  have hsub : ∀ v, Γ.dist (P.vert 2) v ≤ 2 → Γ.dist w v ≤ 4 := by
    intro v hv2
    refine ball_inter_subset L hfix hx hy hw hz ?_ ?_
    · have := F.isTree.connected.dist_triangle (u := x) (v := P.vert 2) (w := v)
      omega
    · have := F.isTree.connected.dist_triangle (u := y) (v := P.vert 2) (w := v)
      rw [SimpleGraph.dist_comm (u := y) (v := P.vert 2)] at this
      omega
  obtain ⟨v, hv1, hv2⟩ := exists_far F (P.vert 2) w 2
  have hwm : Γ.dist w (P.vert 2) ≤ 2 := by
    have := hsub v (le_of_eq hv1)
    omega
  have hwm2 : 2 ≤ Γ.dist w (P.vert 2) := by
    have := F.isTree.connected.dist_triangle (u := x) (v := P.vert 2) (w := w)
    rw [SimpleGraph.dist_comm (u := P.vert 2) (v := w)] at this
    omega
  refine ⟨P.vert 2, hv, ?_, ?_, ?_⟩
  · rw [SimpleGraph.dist_comm]
    exact hmx
  · exact hmy
  · rw [SimpleGraph.dist_comm]
    omega

end P71

end CFSG.Quasithin.Fan86
