module

public import CFSG.RankThree.Co2.XSylow
public import CFSG.RankThree.Co2.Census

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Blueprint CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

@[expose] def BadClass (i : ℕ) : Prop := i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 8

theorem BadClass.lt {i : ℕ} (hi : BadClass i) : i < 10 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem classSizes_ne_one {i : ℕ} (hi : BadClass i) : classSizes[i]! ≠ 1 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem not_isConj_rCr_rep {i : ℕ} (hi : i < 10) (h1 : classSizes[i]! ≠ 1) :
    ¬ IsConj rCr (rep i) := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  have hr : rep i = rCr := by rw [← hg, conj_rCr]
  have hcard := card_centralizer_rep hi
  have htop : Subgroup.centralizer ({rep i} : Set Cr) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [Subgroup.mem_centralizer_singleton_iff, hr]
    exact Subgroup.mem_center_iff.1 rCr_mem_center y
  rw [htop, Subgroup.card_top, natCard_Cr] at hcard
  apply h1
  omega

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem exists_partnerElts {t : h.H} (ht : IsConj h.z (t : G)) (htz : t ≠ h.zG) :
    ∃ s : h.H, IsConj h.z (s : G) ∧ s ≠ h.zG ∧ PartnerElts (h.φ t) (h.φ s) := by
  obtain ⟨s, hs, hsz, Ψ, h1, h2, -⟩ := h.exists_partner ht htz
  exact ⟨s, hs, hsz, Ψ, h1, h2⟩

theorem sq_eq_one_of_isConj_z {t : G} (ht : IsConj h.z t) : t * t = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 ht
  have hz : h.z * h.z = 1 := by
    have := pow_orderOf_eq_one h.z
    rw [h.hz, sq] at this
    exact this
  calc c * h.z * c⁻¹ * (c * h.z * c⁻¹) = c * (h.z * h.z) * c⁻¹ := by group
    _ = 1 := by rw [hz]; group

theorem ne_one_of_isConj_z {t : G} (ht : IsConj h.z t) : t ≠ 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 ht
  intro e
  have : h.z = 1 := by
    calc h.z = c⁻¹ * (c * h.z * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group
  have := h.hz
  rw [‹h.z = 1›, orderOf_one] at this
  exact absurd this (by norm_num)

theorem φ_invol {t : h.H} (ht : IsConj h.z (t : G)) :
    h.φ t * h.φ t = 1 ∧ h.φ t ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [← map_mul]
    have : t * t = 1 := Subtype.ext (h.sq_eq_one_of_isConj_z ht)
    rw [this, map_one]
  · intro e
    have : t = 1 := h.φ.injective (e.trans (map_one _).symm)
    exact h.ne_one_of_isConj_z ht (congrArg Subtype.val this)

theorem exists_partnerPair {t : h.H} (ht : IsConj h.z (t : G)) (htz : t ≠ h.zG) {i : ℕ}
    (hti : IsConj (h.φ t) (rep i)) :
    ∃ j < 10, PartnerPair i j ∧ ∃ s : h.H, IsConj h.z (s : G) ∧ s ≠ h.zG ∧
      IsConj (h.φ s) (rep j) := by
  obtain ⟨s, hs, hsz, hp⟩ := h.exists_partnerElts ht htz
  obtain ⟨hs2, hs1⟩ := h.φ_invol hs
  obtain ⟨j, hj, hsj⟩ := exists_isConj_rep (h.φ s) hs2 hs1
  exact ⟨j, hj, hp.of_conj hti hsj, s, hs, hsz, hsj⟩

theorem isConj_φ_symm {y y' : Cr} (hyy : IsConj y y') :
    IsConj ((h.φ.symm y : h.H) : G) ((h.φ.symm y' : h.H) : G) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hyy
  exact isConj_iff.2 ⟨(h.φ.symm c : G), by simp⟩

theorem not_isConj_rep_of_bad {t : h.H} (ht : IsConj h.z (t : G)) {i : ℕ} (hi : BadClass i) :
    ¬ IsConj (h.φ t) (rep i) := by
  intro hti
  by_cases htz : t = h.zG
  · rw [htz, h.φ_zG] at hti
    exact not_isConj_rCr_rep hi.lt (classSizes_ne_one hi) hti
  · obtain ⟨j, hj, hp, -⟩ := h.exists_partnerPair ht htz hti
    exact not_partnerPair hi hj hp

end Co2CentHyp

end CFSG.RankThree.Co2
