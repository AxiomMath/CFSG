module

public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem map_mul_aut' (g h : MulAut V) (J : Subgroup V) :
    J.map (g * h).toMonoidHom = (J.map h.toMonoidHom).map g.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem mem_stabSub_iff_map_eq {g : MulAut V} {J : Subgroup V} :
    g ∈ stabSub J ↔ J.map g.toMonoidHom = J :=
  CFSG.Quasithin.StabLat.mem_stabSub_iff_map

theorem rk_map_aut (J : Subgroup V) (g : MulAut V) : rk ↥(J.map g.toMonoidHom) = rk J := by
  unfold rk
  rw [Subgroup.card_map_of_injective (by exact g.injective)]

structure TwoSummands (G : Subgroup (MulAut V)) (I I' : Subgroup V) : Prop where
  disj : Disjoint I I'
  sup : I ⊔ I' = ⊤
  perm : ∀ g ∈ G, (I.map g.toMonoidHom = I ∧ I'.map g.toMonoidHom = I') ∨
    (I.map g.toMonoidHom = I' ∧ I'.map g.toMonoidHom = I)

namespace TwoSummands

variable {G H : Subgroup (MulAut V)} {I I' : Subgroup V}

theorem mono (h : TwoSummands G I I') (hHG : H ≤ G) : TwoSummands H I I' :=
  ⟨h.disj, h.sup, fun g hg => h.perm g (hHG hg)⟩

theorem symm (h : TwoSummands G I I') : TwoSummands G I' I :=
  ⟨h.disj.symm, by rw [sup_comm]; exact h.sup, fun g hg => by
    rcases h.perm g hg with h1 | h1
    · exact Or.inl ⟨h1.2, h1.1⟩
    · exact Or.inr ⟨h1.2, h1.1⟩⟩

theorem map_eq_of_swap (h : TwoSummands G I I') {g : MulAut V} (hg : g ∈ G) (hgI : g ∉ stabSub I) :
    I.map g.toMonoidHom = I' ∧ I'.map g.toMonoidHom = I := by
  rcases h.perm g hg with h1 | h1
  · exact absurd (mem_stabSub_iff_map_eq.mpr h1.1) hgI
  · exact h1

theorem map_eq_of_mem_stab (h : TwoSummands G I I') {g : MulAut V} (hg : g ∈ G)
    (hgI : g ∈ stabSub I) : I'.map g.toMonoidHom = I' := by
  have hI := mem_stabSub_iff_map_eq.mp hgI
  rcases h.perm g hg with h1 | h1
  · exact h1.2
  · have hII : I = I' := by rw [← hI, h1.1]
    have hbot : I' = ⊥ := by
      have := h.disj
      rw [← hII] at this ⊢
      exact (disjoint_self).mp this
    rw [hbot]
    exact Subgroup.map_bot _

theorem mem_stab_iff (h : TwoSummands G I I') {g : MulAut V} (hg : g ∈ G) :
    g ∈ stabSub I' ↔ g ∈ stabSub I :=
  ⟨fun hg' => by
    by_contra hgI
    have h1 := (h.map_eq_of_swap hg hgI).2
    have h2 := mem_stabSub_iff_map_eq.mp hg'
    have hII : I = I' := by rw [← h1, h2]
    have hbot : I = ⊥ := by
      have := h.disj
      rw [← hII] at this
      exact (disjoint_self).mp this
    apply hgI
    rw [mem_stabSub_iff_map_eq, hbot]
    exact Subgroup.map_bot _,
   fun hgI => mem_stabSub_iff_map_eq.mpr (h.map_eq_of_mem_stab hg hgI)⟩

theorem conj_mem_stab (h : TwoSummands G I I') {g n : MulAut V} (hg : g ∈ G) (hn : n ∈ G)
    (hnI : n ∈ stabSub I) : g * n * g⁻¹ ∈ stabSub I := by
  by_cases hgI : g ∈ stabSub I
  · exact (stabSub I).mul_mem ((stabSub I).mul_mem hgI hnI) ((stabSub I).inv_mem hgI)
  · obtain ⟨-, h2⟩ := h.map_eq_of_swap hg hgI
    have h3 := h.map_eq_of_mem_stab hn hnI
    have h4 : I.map (g⁻¹).toMonoidHom = I' := by
      have h5 : I'.map (g⁻¹ * g).toMonoidHom = I' := by
        rw [inv_mul_cancel]
        ext u
        simp
      rw [map_mul_aut', h2] at h5
      exact h5
    rw [mem_stabSub_iff_map_eq, map_mul_aut', map_mul_aut', h4, h3, h2]

theorem rk_eq_of_swap (h : TwoSummands G I I') {g : MulAut V} (hg : g ∈ G) (hgI : g ∉ stabSub I) :
    rk I' = rk I := by
  rw [← (h.map_eq_of_swap hg hgI).1, rk_map_aut]

theorem rk_add [Finite V] (h : TwoSummands G I I') : rk I + rk I' = rk V := by
  have := rk_sup_add_rk_inf I I'
  rw [h.sup, disjoint_iff.mp h.disj, rk_bot, rk_top] at this
  omega

end TwoSummands

end CFSG.Quasithin
