module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Far

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem moves_dist_five (F : FanTree Γ G) (L : ZLab Γ G) (hA : ArcTrans Γ G)
    (hR : ∃ R : Arc Γ 8, Fan86.valence Γ (R.vert 0) = 5 ∧
      L.z (R.vert 0) • R.vert 5 ≠ R.vert 5)
    {l w : V} (hl : Fan86.valence Γ l = 5) (hd : Γ.dist l w = 5) : L.z l • w ≠ w := by
  obtain ⟨R, hR5, hRm⟩ := hR
  obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc F.isTree 5 l w hd
  obtain ⟨A, hA'⟩ := exists_extend F P 8 (by norm_num)
  have hA0 : A.vert 0 = l := by rw [hA' 0 (by norm_num), hP0]
  have hA5 : A.vert 5 = w := by rw [hA' 5 (by norm_num), hPn]
  obtain ⟨g, hg⟩ := hA R A hR5 (by rw [hA0]; exact hl)
  have hz : L.z l = g * L.z (R.vert 0) * g⁻¹ := by
    rw [← hA0, ← hg 0 (Nat.zero_le _)]
    exact L.equivariant g (R.vert 0) hR5
  intro h
  apply hRm
  have h' : (g * L.z (R.vert 0) * g⁻¹) • (g • R.vert 5) = g • R.vert 5 := by
    rw [hg 5 (by norm_num), hA5, ← hz]
    exact h
  rw [mul_smul, mul_smul, inv_smul_smul] at h'
  exact MulAction.injective g h'

theorem fixedPts_label (F : FanTree Γ G) (L : ZLab Γ G) (hA : ArcTrans Γ G)
    (hR : ∃ R : Arc Γ 8, Fan86.valence Γ (R.vert 0) = 5 ∧
      L.z (R.vert 0) • R.vert 5 ≠ R.vert 5)
    (hb : ∀ l, Fan86.valence Γ l = 5 → L.z l ∈ ballStab Γ G 4 l) {l : V}
    (hl : Fan86.valence Γ l = 5) : fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4} := by
  ext v
  constructor
  · intro hv
    by_contra hlt
    have h5 : 5 ≤ Γ.dist l v := by
      by_contra h5
      exact hlt (show Γ.dist l v ≤ 4 by omega)
    obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc_between F.isTree l v
    have hlfix : L.z l • l = l := MulAction.mem_stabilizer_iff.1 (L.isCentral l hl).1
    have hw := Arc.fixes_of_ends F.isTree F.adj_smul P (g := L.z l)
      (by rw [hP0]; exact hlfix) (by rw [hPn]; exact hv) 5 h5
    have hd5 : Γ.dist l (P.vert 5) = 5 := by
      have := Arc.dist_eq F.isTree P 5 h5
      rwa [hP0] at this
    exact moves_dist_five F L hA hR hl hd5 hw
  · intro hv
    exact mem_ballStab.1 (hb l hl) v hv

theorem label_ne (F : FanTree Γ G) (L : ZLab Γ G)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    {a b : V} (ha : Fan86.valence Γ a = 5) (hb : Fan86.valence Γ b = 5) (hab : a ≠ b) :
    L.z a ≠ L.z b := by
  intro h
  apply hab
  refine eq_of_ball_subset F (n := 4) fun v hv => ?_
  have h1 : v ∈ fixedPts (V := V) (L.z a) := by
    rw [hfix a ha]
    exact hv
  rw [h, hfix b hb] at h1
  exact h1

end P71

end CFSG.Quasithin.Fan86
