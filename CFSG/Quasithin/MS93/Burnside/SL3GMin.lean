module

public import CFSG.Quasithin.MS93.Burnside.SL3GRed
public import CFSG.Quasithin.MS93.S34FCore

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSL3G_inf_centralizer_ne_bot {Γ : Type} [Group Γ] {P W : Subgroup Γ}
    [Finite ↥P] (hP : IsPGroup 2 ↥P) (hWP : W ≤ P)
    (hnorm : P ≤ Subgroup.normalizer (W : Set Γ)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set Γ) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h0
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h0, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : Γ) ∈ Subgroup.centralizer (P : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h0
  have hmem : (y : Γ) ∈ W ⊓ Subgroup.centralizer (P : Set Γ) := ⟨hy.1, hyC⟩
  rw [h0, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem burnsideSL3G_uloc_inf_centralizer_wStar_ne_bot (h : PUHyp M T L) :
    Uloc h.le L (baseA _) ⊓ Subgroup.centralizer
      (burnsideSL3G_wStar (puAmalgam h.le) (baseB _) : Set (puAmalgam h.le).Universal) ≠ ⊥ := by
  have h20 := h.hyp20
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hP : IsPGroup 2 ↥(Qv (puAmalgam h.le) (baseB _)) :=
    isPGroup_qv _ h20 (not_isMVtx_baseB _)
  have : Finite ↥(Qv (puAmalgam h.le) (baseB _)) := finite_qv _ h20 (not_isMVtx_baseB _)
  have hUQ : Uloc h.le L (baseA _) ≤ Qv (puAmalgam h.le) (baseB _) :=
    ((S34F.uloc_le_zm' h hα).trans (zm_le_qv_self _ hα h.critDist_pos)).trans
      (qv_le_qv _ h20 hα hαβ)
  have hnorm : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (Uloc h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) _)
  have hne : Uloc h.le L (baseA _) ≠ ⊥ := by
    rw [Uloc, puTrans_baseA h.le (S4A.Uq_normal h), Ne, imM_eq_bot_iff h.le (Uq_le h.L_le)]
    exact h.Uq_ne_bot
  have h1 := burnsideSL3G_inf_centralizer_ne_bot hP hUQ hnorm hne
  intro hbot
  apply h1
  rw [eq_bot_iff, ← hbot]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (burnsideSL3G_wStar_le_qv _))

end CFSG.Quasithin.MS93.S4L
