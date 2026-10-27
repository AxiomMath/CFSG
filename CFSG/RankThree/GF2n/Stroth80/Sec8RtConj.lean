module

public import CFSG.RankThree.GF2n.Stroth80.Ctx

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

private theorem aux_conj_mono {g : G} {S T : Subgroup G} (h : S ≤ T) :
    conjSubgroup g S ≤ conjSubgroup g T := by
  intro x hx
  rw [mem_conjSubgroup] at hx ⊢
  exact h hx

private theorem aux_conj_fwd {L : Subgroup G} {g m s : G} (hsm : s ∈ conjSubgroup m L) :
    g * s * g⁻¹ ∈ conjSubgroup (g * m) L := by
  rw [mem_conjSubgroup] at hsm ⊢
  rw [show (g * m)⁻¹ * (g * s * g⁻¹) * (g * m) = m⁻¹ * s * m by group]
  exact hsm

private theorem aux_conj_bwd {L : Subgroup G} {g m' s : G}
    (hmem : g * s * g⁻¹ ∈ conjSubgroup m' L) : s ∈ conjSubgroup (g⁻¹ * m') L := by
  rw [mem_conjSubgroup] at hmem ⊢
  rw [show (g⁻¹ * m')⁻¹ * s * (g⁻¹ * m') = m'⁻¹ * (g * s * g⁻¹) * m' by group]
  exact hmem

private theorem aux_Rt_le {M L : Subgroup G} {t : G} {X : Subgroup G}
    (h : ∀ m ∈ M, t ∈ conjSubgroup m L → conjSubgroup m L ≤ X) : Rt M L t ≤ X := by
  unfold Rt
  refine iSup₂_le fun m hm => ?_
  exact iSup_le fun ht => h m hm ht

private theorem aux_le_Rt {M L : Subgroup G} {t m : G} (hm : m ∈ M)
    (ht : t ∈ conjSubgroup m L) : conjSubgroup m L ≤ Rt M L t := by
  unfold Rt
  refine le_iSup₂_of_le m hm ?_
  exact le_iSup_of_le ht le_rfl

private theorem aux_Vt_le {M L B Z : Subgroup G} {t : G} {X : Subgroup G} (hZX : Z ≤ X)
    (h : ∀ m ∈ M, t ∈ conjSubgroup m L → conjSubgroup m B ≤ X) : Vt M L B Z t ≤ X := by
  unfold Vt
  refine sup_le hZX ?_
  refine iSup₂_le fun m hm => ?_
  exact iSup_le fun ht => h m hm ht

private theorem aux_le_Vt {M L B Z : Subgroup G} {t m : G} (hm : m ∈ M)
    (ht : t ∈ conjSubgroup m L) : conjSubgroup m B ≤ Vt M L B Z t := by
  unfold Vt
  refine le_trans ?_ le_sup_right
  refine le_iSup₂_of_le m hm ?_
  exact le_iSup_of_le ht le_rfl

private theorem aux_Z_le_Vt {M L B Z : Subgroup G} {t : G} : Z ≤ Vt M L B Z t := by
  unfold Vt
  exact le_sup_left

theorem conjSubgroup_Rt_eq {M L : Subgroup G} {g : G} (hg : g ∈ M) (s : G) :
    conjSubgroup g (Rt M L s) = Rt M L (g * s * g⁻¹) := by
  refine le_antisymm ?_ ?_
  · have key : Rt M L s ≤ conjSubgroup g⁻¹ (Rt M L (g * s * g⁻¹)) := by
      refine aux_Rt_le fun m hm hsm => ?_
      have h1 : conjSubgroup (g * m) L ≤ Rt M L (g * s * g⁻¹) :=
        aux_le_Rt (M.mul_mem hg hm) (aux_conj_fwd (g := g) hsm)
      have h2 : conjSubgroup g⁻¹ (conjSubgroup (g * m) L) = conjSubgroup m L := by
        rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_left]
      rw [← h2]
      exact aux_conj_mono h1
    refine le_trans (aux_conj_mono (g := g) key) (le_of_eq ?_)
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel,
      CFSG.RankThree.GF2n.conjSubgroup_one]
  · refine aux_Rt_le fun m' hm' hmem => ?_
    have hm : g⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hg) hm'
    have h1 : conjSubgroup (g⁻¹ * m') L ≤ Rt M L s := aux_le_Rt hm (aux_conj_bwd hmem)
    have h2 : conjSubgroup m' L = conjSubgroup g (conjSubgroup (g⁻¹ * m') L) := by
      rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel_left]
    rw [h2]
    exact aux_conj_mono h1

theorem conjSubgroup_Vt_eq {M L B Z : Subgroup G} {g : G} (hg : g ∈ M)
    (hZ : conjSubgroup g Z = Z) (s : G) :
    conjSubgroup g (Vt M L B Z s) = Vt M L B Z (g * s * g⁻¹) := by
  have hZ' : conjSubgroup g⁻¹ Z = Z := by
    calc conjSubgroup g⁻¹ Z = conjSubgroup g⁻¹ (conjSubgroup g Z) := by rw [hZ]
      _ = conjSubgroup (g⁻¹ * g) Z := by rw [CFSG.RankThree.GF2n.conjSubgroup_mul]
      _ = Z := by rw [inv_mul_cancel, CFSG.RankThree.GF2n.conjSubgroup_one]
  refine le_antisymm ?_ ?_
  · have hZ1 : Z ≤ conjSubgroup g⁻¹ (Vt M L B Z (g * s * g⁻¹)) := by
      calc Z = conjSubgroup g⁻¹ Z := hZ'.symm
        _ ≤ conjSubgroup g⁻¹ (Vt M L B Z (g * s * g⁻¹)) := aux_conj_mono aux_Z_le_Vt
    have key : Vt M L B Z s ≤ conjSubgroup g⁻¹ (Vt M L B Z (g * s * g⁻¹)) := by
      refine aux_Vt_le hZ1 fun m hm hsm => ?_
      have h1 : conjSubgroup (g * m) B ≤ Vt M L B Z (g * s * g⁻¹) :=
        aux_le_Vt (M.mul_mem hg hm) (aux_conj_fwd (g := g) hsm)
      have h2 : conjSubgroup g⁻¹ (conjSubgroup (g * m) B) = conjSubgroup m B := by
        rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_left]
      rw [← h2]
      exact aux_conj_mono h1
    refine le_trans (aux_conj_mono (g := g) key) (le_of_eq ?_)
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel,
      CFSG.RankThree.GF2n.conjSubgroup_one]
  · have hZ0 : Z ≤ conjSubgroup g (Vt M L B Z s) := by
      calc Z = conjSubgroup g Z := hZ.symm
        _ ≤ conjSubgroup g (Vt M L B Z s) := aux_conj_mono aux_Z_le_Vt
    refine aux_Vt_le hZ0 fun m' hm' hmem => ?_
    have hm : g⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hg) hm'
    have h1 : conjSubgroup (g⁻¹ * m') B ≤ Vt M L B Z s := aux_le_Vt hm (aux_conj_bwd hmem)
    have h2 : conjSubgroup m' B = conjSubgroup g (conjSubgroup (g⁻¹ * m') B) := by
      rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel_left]
    rw [h2]
    exact aux_conj_mono h1

end CFSG.RankThree.GF2n.Stroth80
