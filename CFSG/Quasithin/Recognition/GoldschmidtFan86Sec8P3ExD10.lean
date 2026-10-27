module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExDih
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_d10Set {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) {α : V}
    (hα : valence Γ α = 5) : Nonempty (D10Set L α) := by
  obtain ⟨h71a, -, h71c, -⟩ := h7
  have hT := F.isTree
  obtain ⟨Q₁, Q₂, h10, h20, h1ne⟩ := exists_two_arcs F α
  obtain ⟨Q, hQ0, -, hQ8⟩ := exists_arc_eight (h10.trans h20.symm) h1ne
  have hde : Γ.dist α (Q₁.vert 4) = 4 := by
    have := Arc.dist_eq hT Q₁ 4 le_rfl
    rwa [h10] at this
  have hdd : Γ.dist α (Q₂.vert 4) = 4 := by
    have := Arc.dist_eq hT Q₂ 4 le_rfl
    rwa [h20] at this
  have he5 : valence Γ (Q₁.vert 4) = 5 := valence_of_dist_even F hα (by rw [hde])
  have hd5 : valence Γ (Q₂.vert 4) = 5 := valence_of_dist_even F hα (by rw [hdd])
  have hφ : Nonempty (↥(Subgroup.closure ({L.z (Q₁.vert 4), L.z (Q₂.vert 4)} : Set G)) ≃*
      DihedralGroup 5) := by
    have := (h71a Q (by rw [hQ0]; exact he5)).1
    rwa [hQ0, hQ8] at this
  obtain ⟨φ⟩ := hφ
  have hs : L.z (Q₂.vert 4) * L.z (Q₂.vert 4) = 1 := L.z_mul_self hd5
  have he : L.z (Q₁.vert 4) * L.z (Q₁.vert 4) = 1 := L.z_mul_self he5
  have hne : L.z (Q₂.vert 4) ≠ L.z (Q₁.vert 4) := fun h => by
    have h' := h71c.z_injective hd5 he5 h
    have := Arc.vert_injOn hT Q (i := 0) (j := 8) (by norm_num) (by norm_num)
      (by rw [hQ0, hQ8]; exact h'.symm)
    omega
  have hr := dihedral_orderOf_rot hs he (L.z_ne_one hd5) (L.z_ne_one he5) hne φ
  set r := L.z (Q₂.vert 4) * L.z (Q₁.vert 4) with hr_def
  have hrα : r ∈ MulAction.stabilizer G α := by
    refine Subgroup.mul_mem _ ((h71c.z_mem_stabilizer_iff hd5 α).2 ?_)
      ((h71c.z_mem_stabilizer_iff he5 α).2 ?_)
    · rw [SimpleGraph.dist_comm, hdd]
    · rw [SimpleGraph.dist_comm, hde]
  have hinv : ∀ i : Fin 5, (r ^ (i : ℕ))⁻¹ ∈ MulAction.stabilizer G α := fun i =>
    inv_mem (Subgroup.pow_mem _ hrα _)
  let P : Fin 5 → Arc Γ 4 := fun i => Arc.act F ((r ^ (i : ℕ))⁻¹) Q₂
  have hz : ∀ i : Fin 5, L.z ((P i).vert 4) = dihConj (L.z (Q₂.vert 4)) r i := by
    intro i
    show L.z ((r ^ (i : ℕ))⁻¹ • Q₂.vert 4) = _
    rw [L.equivariant _ _ hd5, inv_inv]
    rfl
  have hfun : (fun i : Fin 5 => L.z ((P i).vert 4)) = dihConj (L.z (Q₂.vert 4)) r := funext hz
  refine ⟨⟨P, hα, fun i => ?_, ?_, ?_, fun i => ?_⟩⟩
  · show (r ^ (i : ℕ))⁻¹ • Q₂.vert 0 = α
    rw [h20]
    exact MulAction.mem_stabilizer_iff.1 (hinv i)
  · rw [hfun]
    exact dihConj_injective hs he hr
  · rw [hfun, dihConj_closure hs he hr]
    exact ⟨φ⟩
  · rw [hz 2, hz 0, hz i, hz (i + 1)]
    exact dihConj_shift hs he hr i

end CFSG.Quasithin.Fan86
