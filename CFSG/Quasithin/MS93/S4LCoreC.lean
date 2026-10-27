module

public import CFSG.Quasithin.MS93.S34ETmpl
public import CFSG.Quasithin.MS93.S34EAB
public import CFSG.Quasithin.MS93.S4ABasic
public import CFSG.Quasithin.MS93.S34ECrit

public section

namespace CFSG.Quasithin.MS93.S4L.Core

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Template

variable (h : PUHyp M T L)
include h

theorem pre_le_of_le_qv_baseB {W : Subgroup (puAmalgam h.le).Universal}
    (hWT : W ≤ Qv (puAmalgam h.le) (baseB _)) : S33.pre h.le W ≤ T := by
  intro x hx
  obtain ⟨m, hmW, rfl⟩ := (S33.mem_pre_iff' h.le).mp hx
  have hm := hWT hmW
  rw [puAmalgam.qv_baseB] at hm
  exact (S33.ofA_mem_imM_iff h.le m).mp hm

theorem characteristic_pre {W : Subgroup (puAmalgam h.le).Universal}
    (hWn : stab (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (W : Set _)) :
    ((S33.pre h.le W).subgroupOf T).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  rintro φ _ ⟨t, ht, rfl⟩
  have ht' : (t : G) ∈ S33.pre h.le W := Subgroup.mem_subgroupOf.mp ht
  refine Subgroup.mem_subgroupOf.mpr ?_
  have h1 : puAmalgam.ofT h.le t ∈ W := by
    rw [← puAmalgam.ofA_inclusion]
    exact (S33.mem_pre_iff h.le _).mp ht'
  have hg : (puAmalgam h.le).ofB (SemidirectProduct.inr φ) ∈ stab (puAmalgam h.le) (baseB _) := by
    rw [puAmalgam.stab_baseB]
    exact ⟨_, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp (hWn hg) _).mp h1
  rw [S34E.conj_ofT h φ t, ← puAmalgam.ofA_inclusion] at h2
  exact (S33.mem_pre_iff h.le _).mpr h2

theorem qv_le_centralizer_of_le_uloc_sup_dloc (hmin : PUMin M T L) (hU : IsSL3U M T L)
    {W : Subgroup (puAmalgam h.le).Universal} (hWT : W ≤ Qv (puAmalgam h.le) (baseB _))
    (hWn : stab (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (W : Set _))
    (hW : W ≤ Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _)) :
    Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.centralizer (W : Set _) := by
  have hWM : W ≤ imM h.le M :=
    hWT.trans (by rw [puAmalgam.qv_baseB]; exact imM_mono h.le h.le)
  have himW : imM h.le (S33.pre h.le W) = W := S33.imM_pre h.le hWM
  have hW₀T := pre_le_of_le_qv_baseB h hWT
  have hW₀c := characteristic_pre h hWn
  have hUD : Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) ≤ imM h.le (Uq M T L ⊔ Dq M L) := by
    rw [Uloc, Dloc, puTrans_baseA h.le (S4A.Uq_normal h), puTrans_baseA h.le (S4A.Dq_normal h)]
    exact sup_le (imM_mono h.le le_sup_left) (imM_mono h.le le_sup_right)
  have hW₀UD : S33.pre h.le W ≤ Uq M T L ⊔ Dq M L := by
    intro x hx
    obtain ⟨m, hmW, rfl⟩ := (S33.mem_pre_iff' h.le).mp hx
    exact (S33.ofA_mem_imM_iff h.le m).mp (hUD (hW hmW))
  have hUZ : Uq M T L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [← h.Uq_inf_Zq, inf_comm]
    exact hU.2.1
  have hcen := S34E.le_center_of_le_sup h hmin hUZ hW₀T hW₀c hW₀UD
  rw [puAmalgam.qv_baseB, ← himW]
  exact S34E.imM_le_centralizer h hcen

end Template

end CFSG.Quasithin.MS93.S4L.Core
