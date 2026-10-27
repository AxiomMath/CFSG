module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj
public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_iff_conj_mem_of_eq {S : Subgroup G} {g : G} (h : conjSubgroup g S = S) (x : G) :
    x ∈ S ↔ g * x * g⁻¹ ∈ S := by
  have h1 : ∀ y : G, y ∈ conjSubgroup g S ↔ g⁻¹ * y * g ∈ S := fun y => mem_conjSubgroup
  rw [h] at h1
  have h2 := h1 (g * x * g⁻¹)
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2
  exact h2.symm

theorem Rt_conj_left {G : Type} [Group G] {M L : Subgroup G} {g : G} (hg : g ∈ M) (s : G) :
    Rt M (conjSubgroup g L) s = Rt M L s := by
  refine le_antisymm ?_ ?_
  · unfold Rt
    refine iSup₂_le fun m hm => iSup_le fun hs => ?_
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul] at hs ⊢
    exact le_iSup₂_of_le (m * g) (M.mul_mem hm hg) (le_iSup_of_le hs le_rfl)
  · unfold Rt
    refine iSup₂_le fun m hm => iSup_le fun hs => ?_
    have h1 : conjSubgroup m L = conjSubgroup (m * g⁻¹) (conjSubgroup g L) := by
      rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, show m * g⁻¹ * g = m by group]
    have hmem : s ∈ conjSubgroup (m * g⁻¹) (conjSubgroup g L) := by
      rw [← h1]
      exact hs
    rw [h1]
    exact le_iSup₂_of_le (m * g⁻¹) (M.mul_mem hm (M.inv_mem hg)) (le_iSup_of_le hmem le_rfl)

theorem Vt_conj_left {G : Type} [Group G] {M L B Z : Subgroup G} {g : G} (hg : g ∈ M)
    (s : G) : Vt M (conjSubgroup g L) (conjSubgroup g B) Z s = Vt M L B Z s := by
  unfold Vt
  congr 1
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun m hm => iSup_le fun hs => ?_
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul] at hs ⊢
    exact le_iSup₂_of_le (m * g) (M.mul_mem hm hg) (le_iSup_of_le hs le_rfl)
  · refine iSup₂_le fun m hm => iSup_le fun hs => ?_
    have h1 : conjSubgroup m B = conjSubgroup (m * g⁻¹) (conjSubgroup g B) := by
      rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, show m * g⁻¹ * g = m by group]
    have hmem : s ∈ conjSubgroup (m * g⁻¹) (conjSubgroup g L) := by
      rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, show m * g⁻¹ * g = m by group]
      exact hs
    rw [h1]
    exact le_iSup₂_of_le (m * g⁻¹) (M.mul_mem hm (M.inv_mem hg)) (le_iSup_of_le hmem le_rfl)

theorem Ctx.CN_conj_left [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {g : G} (hg : g ∈ M) (s : G) :
    (hc.conj_of_mem hg).CN s = hc.CN s := by
  ext x
  show x ∈ CNt M (LB M Q (conjSubgroup g B)) (conjSubgroup g B) Z s ↔
    x ∈ CNt M (LB M Q B) B Z s
  rw [hc.LB_conj hg]
  show (x ∈ Rt M (conjSubgroup g (LB M Q B)) s ∧
      ∀ v ∈ Vt M (conjSubgroup g (LB M Q B)) (conjSubgroup g B) Z s, ⁅x, v⁆ ∈ Z) ↔
    (x ∈ Rt M (LB M Q B) s ∧ ∀ v ∈ Vt M (LB M Q B) B Z s, ⁅x, v⁆ ∈ Z)
  rw [Rt_conj_left hg, Vt_conj_left hg]

theorem Ctx.CN_conjM [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {g : G} (hg : g ∈ M) (t : G) :
    hc.CN (g * t * g⁻¹) = conjSubgroup g (hc.CN t) := by
  have hZ : conjSubgroup g Z = Z := hc.conj_Z_eq hg
  have key : ∀ x w : G, ⁅x, g * w * g⁻¹⁆ ∈ Z ↔ ⁅g⁻¹ * x * g, w⁆ ∈ Z := by
    intro x w
    have e : ⁅x, g * w * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, w⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_iff_conj_mem_of_eq hZ _).symm
  ext x
  rw [mem_conjSubgroup]
  show (x ∈ Rt M (LB M Q B) (g * t * g⁻¹) ∧
      ∀ v ∈ Vt M (LB M Q B) B Z (g * t * g⁻¹), ⁅x, v⁆ ∈ Z) ↔
    (g⁻¹ * x * g ∈ Rt M (LB M Q B) t ∧ ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g⁻¹ * x * g, v⁆ ∈ Z)
  rw [← conjSubgroup_Rt_eq hg, ← conjSubgroup_Vt_eq hg hZ, mem_conjSubgroup]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h w hw
    have hw' : g * w * g⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * w * g⁻¹) * g = w by group]
      exact hw
    exact (key x w).mp (h _ hw')
  · intro h v hv
    rw [mem_conjSubgroup] at hv
    have h2 := (key x (g⁻¹ * v * g)).mpr (h _ hv)
    rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h2

theorem Sec8Hyp.congr_ctx [Finite G]
    {M Q Z B M' Q' Z' B' : Subgroup G}
    {hc : Ctx M Q Z B} {hc' : Ctx M' Q' Z' B'} (hM : M = M') (hQ : Q = Q') (hZ : Z = Z')
    (hB : B = B') {n : ℕ} {t : G} (h : Sec8Hyp hc n t) : Sec8Hyp hc' n t := by
  subst hM hQ hZ hB
  exact h

theorem Sec8Hyp.conjG [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec8Hyp hc n t) (g : G) :
    Sec8Hyp (hc.conjBy g) n (g * t * g⁻¹) := by
  obtain ⟨m, hm, hsp⟩ := h.sp
  exact ⟨h.toSec5.conjG g, m, hm, hsp.conjG g⟩

theorem Sec8Hyp.conjM [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec8Hyp hc n t) {g : G} (hg : g ∈ M) :
    Sec8Hyp (hc.conj_of_mem hg) n (g * t * g⁻¹) :=
  Sec8Hyp.congr_ctx (hc.conj_M_eq hg) (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) rfl (h.conjG g)

end CFSG.RankThree.GF2n.Stroth80
