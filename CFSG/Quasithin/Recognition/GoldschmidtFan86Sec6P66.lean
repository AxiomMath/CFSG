module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Rank48
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NineMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PXiLoc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P66

theorem exists_zz (F : FanTree Γ G) (h40 : Fan40 F) (T : Track Γ G) :
    ∃ z : G, z ∈ T.line.ZZ ∧ z ≠ 1 := by
  have hadj : Γ.Adj (T.line.vert 0) (T.line.vert (0 + 1)) := T.line.adj 0
  have hE2 : IsPGroup 2 ↥(MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert (0 + 1))) := F.edge_two _ _ hadj
  have hEfin : Finite ↥(MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert (0 + 1))) := F.finite_stabilizer_inf _ _
  have hEnt : Nontrivial ↥(MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert (0 + 1))) := by
    obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (F.nbrStab_ne_bot h40 (T.line.vert 0))
    refine nontrivial_of_ne ⟨(k : G), F.nbrStab_le_edge _ hadj k.2⟩ 1 fun h => hk (Subtype.ext ?_)
    simpa using congrArg Subtype.val h
  obtain ⟨z, hzE, hz1, hzz, hzc⟩ := exists_central_involution_of_isPGroup hE2
  exact ⟨z, ⟨hzz, 0, hzE, hzc⟩, hz1⟩

end P66

theorem fan66 (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h211 : Tutte.TutteTree)
    (h61 : Fan61 F) (h62 : Fan62 F) (h512cen : Fan512cen F) : Fan66 F := by
  intro T₀
  by_contra hne
  obtain ⟨T, -, hstar⟩ := fan48_1 F h40 h28 T₀ hne
  have hPi : TrackInPi T := hstar.1
  have hXi : InXi T := ⟨1, hstar, fun j hj1 hj => absurd hj (by omega)⟩
  obtain ⟨z, hzZ, hz1⟩ := P66.exists_zz F h40 T
  obtain ⟨⟨a, b, tL, tR, hcf⟩, hP⟩ := h62 h40 T hXi z hzZ hz1
  obtain ⟨hba, hRb, hLa⟩ := hP a b tL tR hcf
  have hcore : T.line.IsCore z a (a + 2) := by
    have hb : b = a + 2 := by omega
    exact hb ▸ hcf.core
  have hcin := h512cen h40 T z a hXi hzZ hz1 hcore
  have hne3 := h61 h40 _ z hcin
  have hval : valence Γ (T.line.vert (a + 1)) = 3 ∨ valence Γ (T.line.vert (a + 1)) = 5 :=
    F.valence _
  have hzfix : ∀ i, z • T.line.vert i = T.line.vert i ↔ tL ≤ i ∧ i ≤ tR := fun i => hcf.fix i
  have hzsub : z ∈ T.subFixer tL tR := (T.mem_subFixer).2 fun i h1 h2 => (hzfix i).2 ⟨h1, h2⟩
  have hzmov : z ∉ T.fixer := fun h => by
    have := (hzfix (tR + 1)).1 ((T.mem_fixer).1 h _)
    omega
  have hps : PSeg T tL tR := ⟨by omega, fun hle =>
    hzmov (hle (Subgroup.subset_closure ⟨hzsub, hzZ.1⟩))⟩
  obtain ⟨a', b', ha', hb', hp', hmax⟩ := T.exists_pseg_max F hps
  have hθ : IsTArc T a' b' := IsTArc.of_pseg_max T F h40 hp' hmax
  have hlen := (fan48_concl F h40 h28 h211 T hstar hθ).length
  have e1 : a' = tL := by omega
  have h3 := fan47 T F h40 hPi hθ (Or.inl rfl)
  rw [e1] at h3
  have hv5 : valence Γ (T.line.vert tL) = valence Γ (T.line.vert (a + 1)) := by
    have := T.valence_vert_zpow F tL 2
    rw [show tL + 2 * 2 = a + 1 by omega] at this
    exact this.symm
  omega

end CFSG.Quasithin.Fan86
