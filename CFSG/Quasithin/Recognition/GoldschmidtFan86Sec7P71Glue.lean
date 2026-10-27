module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Dec
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PGlue

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem pow_five_moves (F : FanTree Γ G) {α : V} (h5 : Fan86.valence Γ α = 5) {x : G}
    (hx : x ∈ MulAction.stabilizer G α) (hxo : orderOf x = 5) {u : V} (hu : Γ.Adj α u) :
    x • u ≠ u := by
  intro hxu
  obtain ⟨b, hb, hbu⟩ := F.exists_adj_ne α u
  obtain ⟨j, hj⟩ := F.exists_pow_smul_eq hx (by rw [hxo, h5]) hu hb
  have hfix : x ^ j • u = u :=
    MulAction.mem_stabilizer_iff.1 (pow_mem (MulAction.mem_stabilizer_iff.2 hxu) j)
  exact hbu (hj.symm.trans hfix)

theorem exists_dihedral_arc (F : FanTree Γ G) (L : ZLab Γ G) (h40 : Fan40 F) (h62 : Fan62 F)
    (h63 : Fan63 F) (T : Track Γ G) (hT : InXi T) {c : ℤ}
    (h5 : Fan86.valence Γ (T.line.vert c) = 5) :
    ∃ A : Arc Γ 8, Fan86.valence Γ (A.vert 0) = 5 ∧
      Nonempty (↥(Subgroup.closure ({L.z (A.vert 0), L.z (A.vert 8)} : Set G)) ≃*
        DihedralGroup 5) := by
  obtain ⟨x₀, hx₀, hx₀o, hx₀stab⟩ := exists_x0 F L h40 h62 h63 T hT h5
  obtain ⟨hm4, hp4⟩ := valence_line_pm_four F T h5
  have h1 : Γ.Adj (T.line.vert c) (T.line.vert (c - 1)) := by
    have := (T.line.adj (c - 1)).symm
    rwa [sub_add_cancel] at this
  have hc : x₀ • T.line.vert c = T.line.vert c := MulAction.mem_stabilizer_iff.1 hx₀stab
  have hm : x₀ • T.line.vert (c - 1) ≠ T.line.vert (c - 1) :=
    pow_five_moves F h5 hx₀stab hx₀o h1
  have hA0 : ((T.line.glue c x₀ F hc hm).arc (c - 4) 8).vert 0 = T.line.vert (c - 4) := by
    rw [arc_vert]
    simp only [Nat.cast_zero, add_zero]
    exact Line.glue_vert_le T.line c x₀ F hc hm (by omega)
  have hA8 : ((T.line.glue c x₀ F hc hm).arc (c - 4) 8).vert 8 = x₀ • T.line.vert (c - 4) := by
    rw [arc_vert, Line.glue_vert_ge T.line c x₀ F hc hm (by push_cast; omega)]
    congr 2
    push_cast
    omega
  refine ⟨(T.line.glue c x₀ F hc hm).arc (c - 4) 8, by rw [hA0]; exact hm4, ?_⟩
  rw [hA0, hA8, L.equivariant x₀ _ hm4]
  exact dihedral_conj (L.isCentral _ hm4).2.2.1 (L.isCentral _ hm4).2.1
    (L.isCentral _ hp4).2.2.1 hx₀ hx₀o

end P71

end CFSG.Quasithin.Fan86
