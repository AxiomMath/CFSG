module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2B

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α) (F : FanTree Γ G)

theorem exists_loc (h : Fan71c F L) {q : V} (hq : Γ.dist α q = 2) :
    ∃ m : Fin 5, q = D.alpha m ∨ q = D.alphaS F m := by
  obtain ⟨p, hpq, hp⟩ := IsTree.exists_adj_dist_succ F.isTree (u := α) (v := q) (n := 1) hq
  have hαp : Γ.Adj α p := dist_eq_one_iff_adj.1 hp
  obtain ⟨m, rfl⟩ := D.exists_beta_eq F h hαp
  refine ⟨m, ?_⟩
  have hqN : q ∈ Γ.neighborSet (D.beta m) := hpq
  rw [(D.alphaS_spec F m).1] at hqN
  have hqα : q ≠ α := fun h' => by rw [h', SimpleGraph.dist_self] at hq; omega
  simpa [hqα] using hqN

theorem z_alphaS (h512 : Fan512 F L) (m : Fin 5) :
    L.z (D.alphaS F m) = L.z (D.alpha m) * L.z α := by
  obtain ⟨hN, hs1, hs2⟩ := D.alphaS_spec F m
  have h1 := h512.2.2.1 (D.beta m) α (D.alpha m) (D.alphaS F m) (D.valence_beta F m) hN
    (D.alpha_ne_start m).symm hs1 hs2
  calc L.z (D.alphaS F m) = (L.z α * L.z (D.alpha m))⁻¹ := eq_inv_of_mul_eq_one_right h1
    _ = L.z (D.alpha m) * L.z α := by
      rw [mul_inv_rev, L.z_inv D.val, L.z_inv (D.valence_alpha F m)]

theorem moved_alphaS {g : G} (hg : g ∈ nbrStab Γ G α) {m : Fin 5} (hm : g • D.alpha m ≠ D.alpha m) :
    g • D.alphaS F m ≠ D.alphaS F m := by
  rcases D.perm_cases F hg m with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 hm
  · rw [h2]
    exact (D.alphaS_spec F m).2.2

include F in
theorem mem_gcirc_of_mem_nbrStab {x : G} {b : V} (hb : Γ.Adj α b)
    (hx : x ∈ nbrStab Γ G α) : x ∈ Gcirc Γ G α b :=
  ⟨⟨F.nbrStab_le_stabilizer α hx, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hx b hb)⟩,
    mul_mem hx hx⟩

end D10Set

theorem one_mem_gcirc' (a b : V) : (1 : G) ∈ Gcirc Γ G a b :=
  ⟨⟨one_mem _, one_mem _⟩, by rw [mul_one]; exact one_mem _⟩

theorem gcirc_congr {a a' b b' : V} {x : G} (ha : a = a') (hb : b = b')
    (hx : x ∈ Gcirc Γ G a b) : x ∈ Gcirc Γ G a' b' := by
  subst ha hb
  exact hx

end CFSG.Quasithin.Fan86
