module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PXiLoc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_xi_three (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h48 : Fan48Two F) : ∃ T : Track Γ G, HasLenTwoReflection Γ G T := by
  classical
  have hadj := F.adj_smul
  obtain ⟨α⟩ := F.isTree.connected.nonempty
  obtain ⟨β, hαβ⟩ := F.exists_adj α
  obtain ⟨γ, hαγ, hγβ⟩ := F.exists_adj_ne α β
  obtain ⟨x, hx, hxβ⟩ := F.loc_trans α β γ hαβ hαγ
  obtain ⟨δ, hβδ, hδα⟩ := F.exists_adj_ne β α
  obtain ⟨y, hy, hyα⟩ := F.loc_trans β α δ hαβ.symm hβδ
  have hcp : CrossPair α β x y :=
    ⟨MulAction.mem_stabilizer_iff.1 hx, by rw [hxβ]; exact hγβ, MulAction.mem_stabilizer_iff.1 hy,
      by rw [hyα]; exact hδα⟩
  set T₀ := trackOfPair hadj hαβ hcp with hT₀
  have hv1 : T₀.line.vert 1 = α := trackOfPair_vert_one hadj hαβ hcp
  have hv2 : T₀.line.vert (1 + 1) = β := trackOfPair_vert_two hadj hαβ hcp
  have hE2 : IsPGroup 2 ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :=
    F.edge_two α β hαβ
  have hEfin : Finite ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :=
    F.finite_stabilizer_inf α β
  have hEnt : Nontrivial ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
    obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (F.nbrStab_ne_bot h40 α)
    refine nontrivial_of_ne ⟨(k : G), F.nbrStab_le_edge α hαβ k.2⟩ 1 fun h => hk (Subtype.ext ?_)
    simpa using congrArg Subtype.val h
  obtain ⟨z, hzE, hz1, hzz, hzc⟩ := exists_central_involution_of_isPGroup hE2
  have hnot : ¬ ∀ i, z • T₀.line.vert i = T₀.line.vert i := by
    intro hall
    refine hz1 (fan49 F h40 h28 h33 h48 T₀ 1 z ((T₀.mem_fixer).2 hall) fun g hg => ?_)
    rw [hv1, hv2] at hg
    exact hzc g hg
  have hfix : ∀ i, i ∈ T₀.fixSet (Subgroup.zpowers z) ↔ z • T₀.line.vert i = T₀.line.vert i := by
    intro i
    constructor
    · exact fun h => h z (Subgroup.mem_zpowers z)
    · intro h g hg
      exact MulAction.mem_stabilizer_iff.1
        ((Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)) hg)
  have hbdd : ∃ b : ℤ, ∀ i : ℤ, z • T₀.line.vert i = T₀.line.vert i → i ≤ b := by
    rcases T₀.fixSet_eq_univ_or_bounded F.isTree hadj F.loc_finite (Subgroup.zpowers z) with h | h
    · exfalso
      exact hnot fun i => (hfix i).1 (by rw [h]; trivial)
    · obtain ⟨a, b, hab⟩ := h
      exact ⟨b, fun i hi => (hab i ((hfix i).2 hi)).2⟩
  obtain ⟨j, hj, hjmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨1, by
    rw [hv1]; exact MulAction.mem_stabilizer_iff.1 hzE.1⟩
  have hj1 : z • T₀.line.vert (j + 1) ≠ T₀.line.vert (j + 1) := fun h => by
    have := hjmax (j + 1) h
    omega
  obtain ⟨y', hy', hy'move, hy'2⟩ := F.exists_involutive_moving (T₀.line.adj j).symm
  have hcp' : CrossPair (T₀.line.vert j) (T₀.line.vert (j + 1)) z y' :=
    ⟨hj, hj1, MulAction.mem_stabilizer_iff.1 hy', hy'move⟩
  exact ⟨trackOfPair hadj (T₀.line.adj j) hcp', 1, z,
    trackOfPair_lenTwo hadj (T₀.line.adj j) hcp' hzz hy'2⟩

theorem exists_inXi (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h48 : Fan48Two F) : ∃ T : Track Γ G, InXi T := by
  classical
  obtain ⟨T, hT⟩ := exists_xi_three F h40 h28 h33 h48
  have hex : ∃ i, ∃ T : Track Γ G, Xi i T := ⟨3, T, hT⟩
  obtain ⟨T', hT'⟩ := Nat.find_spec hex
  exact ⟨T', Nat.find hex, hT', fun j _ hj => Nat.find_min hex hj⟩

end CFSG.Quasithin.Fan86
