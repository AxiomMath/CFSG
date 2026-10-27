module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Br

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P63

theorem comm_identity {z a z' t : G} (hz' : z' = a * z * a) (ht : t = z * a * z) :
    z * (z' * z * z') = t * (a * t * a) := by
  subst hz' ht
  group

theorem dist_le_two (F : FanTree Γ G) {a b c : V} (h1 : Γ.Adj a b) (h2 : Γ.Adj b c) :
    Γ.dist a c ≤ 2 := by
  have := F.isTree.connected.dist_triangle (u := a) (v := b) (w := c)
  rw [dist_eq_one_iff_adj.2 h1, dist_eq_one_iff_adj.2 h2] at this
  omega

theorem dist_le_three (F : FanTree Γ G) {a b c d : V} (h1 : Γ.Adj a b) (h2 : Γ.Adj b c)
    (h3 : Γ.Adj c d) : Γ.dist a d ≤ 3 := by
  have := F.isTree.connected.dist_triangle (u := a) (v := c) (w := d)
  rw [dist_eq_one_iff_adj.2 h3] at this
  have := dist_le_two F h1 h2
  omega

variable {L : ZLab Γ G} {ℓ : Line Γ} {j : ℤ}

namespace LineData

variable (D : LineData L ℓ j) (F : FanTree Γ G) (h40 : Fan40 F) (H : LabHyp L)
include D F h40 H

theorem fix_four {δ μ : V} (hδ : valence Γ δ = 5) (hbr : Br Γ δ μ (ℓ.vert j))
    (hd : Γ.dist δ (ℓ.vert (j + 1)) = 3) : L.z δ • ℓ.vert (j + 2) = ℓ.vert (j + 2) := by
  by_contra hmove
  set z := L.z δ with hz
  set a := L.z (ℓ.vert (j + 4)) with ha
  have hv4 := D.val_five_j4 F
  have hz2 : z * z = 1 := z_sq hδ
  have hz3 : z ∈ ballStab Γ G 3 δ := P63.ballStab_three F H hδ
  have hdlam : Γ.dist δ (ℓ.vert j) = 2 := Br.dist_two F hbr
  have hzl : z • ℓ.vert j = ℓ.vert j := mem_ballStab.1 hz3 _ (by omega)
  have hzl1 : z • ℓ.vert (j + 1) = ℓ.vert (j + 1) := mem_ballStab.1 hz3 _ (by omega)
  have hm : Γ.Adj (ℓ.vert (j + 1)) (z • ℓ.vert (j + 2)) := by
    have := (F.adj_smul z _ _).2 (adj_j_j2 ℓ j)
    rwa [hzl1] at this
  have hm1 : z • ℓ.vert (j + 2) ≠ ℓ.vert j := by
    intro h
    rw [← hzl] at h
    exact ℓ.nb j (MulAction.injective z h).symm
  obtain ⟨g, hg, hgm⟩ := D.exists_swap_arc F h40 hm hm1 hmove
  obtain ⟨hvm, hv1, hv2, d1, d2, d3, d4⟩ := D.branches F hm hm1 hzl1 rfl hg hgm
  obtain ⟨τ, hbτ, hτl, hset⟩ := exists_sibling F hδ hbr
  have hμ1 : μ ≠ ℓ.vert (j + 1) := by
    intro h
    rw [h] at hbr
    have := dist_eq_one_iff_adj.2 hbr.1
    omega
  have hal : a • ℓ.vert j = ℓ.vert j := D.a_fix F le_rfl (by omega)
  have hvδ' : valence Γ (a • δ) = 5 := by rw [F.valence_smul_eq]; exact hδ
  have hz'3 : L.z (a • δ) ∈ ballStab Γ G 3 (a • δ) := P63.ballStab_three F H hvδ'
  have hadj1 : Γ.Adj (a • δ) (a • μ) := (F.adj_smul a _ _).2 hbr.1
  have hadj2 : Γ.Adj (a • μ) (ℓ.vert j) := by
    have := (F.adj_smul a _ _).2 hbr.2.1
    rwa [hal] at this
  have hadj3 : Γ.Adj (ℓ.vert j) μ := hbr.2.1.symm
  have hz'l : L.z (a • δ) • ℓ.vert j = ℓ.vert j :=
    mem_ballStab.1 hz'3 _ (by have := dist_le_two F hadj1 hadj2; omega)
  have hz'μ : L.z (a • δ) • μ = μ :=
    mem_ballStab.1 hz'3 _ (dist_le_three F hadj1 hadj2 hadj3)
  have hzz' : L.z (a • δ) = a * z * a := by rw [z_smul hδ a, z_inv hv4]
  have hδ''adj : Γ.Adj μ (L.z (a • δ) • δ) := by
    have := (F.adj_smul (L.z (a • δ)) _ _).2 hbr.1.symm
    rwa [hz'μ] at this
  have hδ''l : L.z (a • δ) • δ ≠ ℓ.vert j := by
    intro h
    rw [← hz'l] at h
    exact hbr.2.2 (MulAction.injective _ h).symm
  have hmemμ : L.z (a • δ) • δ ∈ Γ.neighborSet μ := hδ''adj
  rw [hset] at hmemμ
  have hid : z * L.z (L.z (a • δ) • δ) = L.z (z • ℓ.vert (j + 4)) *
      L.z (a • z • ℓ.vert (j + 4)) := by
    rw [z_smul hδ (L.z (a • δ)), z_inv hvδ', z_smul hv4 z, z_inv hδ,
      z_smul (hv1) a, z_smul hv4 z, z_inv hδ, z_inv hv4]
    exact comm_identity hzz' rfl
  have hne : z • ℓ.vert (j + 4) ≠ a • z • ℓ.vert (j + 4) := fun h => by
    rw [← h, dist_self] at d4
    omega
  rcases hmemμ with h | h | h
  ·
    rw [h, z_sq hδ] at hid
    have e : L.z (z • ℓ.vert (j + 4)) = L.z (a • z • ℓ.vert (j + 4)) := by
      have := eq_inv_of_mul_eq_one_left hid.symm
      rwa [z_inv hv2] at this
    exact H.dist _ _ hne hv1 hv2 (Or.inr d4) e
  · exact absurd h hδ''l
  ·
    have hs := sib_label F H hδ hbr hbτ hτl.symm
    have hc := z_comm_dist F H hδ hdlam
    have e1 : z * L.z τ = L.z (ℓ.vert j) := by
      rw [hs, hc, ← mul_assoc, hz2, one_mul]
    rw [h, e1] at hid
    have hv0 : valence Γ (ℓ.vert j) = 5 := D.val_five_j F
    refine H.triple _ _ _ _ hvm d2 d3 d1 ?_
    rw [← hid, z_sq hv0]
    exact one_mem _

end LineData

end P63

end CFSG.Quasithin.Fan86
