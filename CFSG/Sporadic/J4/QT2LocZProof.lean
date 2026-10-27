
module

public import CFSG.Sporadic.J4.QT2LocZCheck
public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix

@[expose] noncomputable def mixGL (m : ℕ) : GL (Fin 112) (ZMod 2) :=
  if m = 0 then gA else if m = 1 then gB else locGL (m - 2)

theorem mixGL_mem (m : ℕ) : mixGL m ∈ J := by
  unfold mixGL
  split_ifs
  · exact baseGL_mem 0
  · exact baseGL_mem 1
  · exact locGL_mem _

@[expose] noncomputable def mixElt (w : List ℤ) : J :=
  ⟨wordProd mixGL w, wordProd_mem J mixGL_mem w⟩

section Mix

variable (hM : MatFacts)
include hM

theorem mixMats_spec (m : ℕ) : rowsMatrix (mixMats[m]?.getD idRows) =
    ((mixGL m : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  have hsz : baseMats.size = 2 := rfl
  unfold mixMats
  by_cases hm : m < 2
  · rw [Array.getElem?_append_left (by omega), baseMats_spec hM m]
    unfold mixGL baseGL
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · simp
    · simp
  · rw [Array.getElem?_append_right (by omega), hsz, locMats_spec hM (m - 2)]
    unfold mixGL
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem mixInvs_spec (m : ℕ) : rowsMatrix (mixInvs[m]?.getD idRows) =
    (((mixGL m)⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  have hsz : baseInvs.size = 2 := by simp [baseInvs, baseMats]
  unfold mixInvs
  by_cases hm : m < 2
  · rw [Array.getElem?_append_left (by omega), baseInvs_spec hM m]
    unfold mixGL baseGL
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · simp
    · simp
  · rw [Array.getElem?_append_right (by omega), hsz, locInvs_spec hM (m - 2)]
    unfold mixGL
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem Mx_mixElt (w : List ℤ) : Mx (mixElt w) = rowsMatrix (mixRowsOf w) := by
  rw [Mx_apply]
  exact (rowsMatrix_wordRows (mixMats_spec hM) (mixInvs_spec hM) w).symm

theorem mixElt_comm_notin (w : List ℤ) (h : chkCommRoot (locMats ()) (locInvs ()) w = true) :
    mixElt w * eta uJ 11 1131 = eta uJ 11 1131 * mixElt w ∧ mixElt w ∉ Hj := by
  unfold chkCommRoot at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun hmem => ?_⟩
  · apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 h1)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_mixElt hM, ← Mx_eta hM 11 le_rfl] at this
    rw [map_mul, map_mul]
    exact this
  · have hfix := Hj_fix_root hM _ (Hj.inv_mem hmem)
    rw [← ofRow_inj, inv_smul_row, ← Mx_apply, Mx_mixElt hM] at hfix
    apply differs_toVec h2
    rw [frApply_toVec_eq_vecMul]
    exact hfix

theorem orderOf_mixElt (w : List ℤ) {p : ℕ} (hp : p.Prime)
    (h : chkOrder (locMats ()) (locInvs ()) w p = true) : orderOf (mixElt w) = p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold chkOrder at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hnot := (mixElt_comm_notin hM w h1).2
  have hpow : mixElt w ^ p = 1 := by
    apply Mx_injective
    rw [map_pow, map_one, Mx_mixElt hM, ← rowsMatrix_powRows, eqRows_iff.1 h2,
      rowsMatrix_idRows]
  refine orderOf_eq_prime hpow ?_
  intro h1'
  exact hnot (h1' ▸ Hj.one_mem)

end Mix

theorem exists_centralizer_not_mem_Hj (hF : J4Facts) :
    ∃ g : J, g * eta uJ 11 1131 = eta uJ 11 1131 * g ∧ g ∉ Hj :=
  ⟨mixElt gWord, mixElt_comm_notin hF.mat gWord gWord_check⟩

theorem dvd_card_centralizer_of (hF : J4Facts) (w : List ℤ) {p : ℕ} (hp : p.Prime)
    (h : chkOrder (locMats ()) (locInvs ()) w p = true) :
    p ∣ Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)) := by
  have h1 : chkCommRoot (locMats ()) (locInvs ()) w = true := by
    unfold chkOrder at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have hmem : mixElt w ∈ Subgroup.centralizer ({eta uJ 11 1131} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mixElt_comm_notin hF.mat w h1).1
  have := orderOf_dvd_natCard
    (⟨mixElt w, hmem⟩ : ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)))
  rwa [Subgroup.orderOf_mk, orderOf_mixElt hF.mat w hp h] at this

theorem seven_dvd_card_centralizer (hF : J4Facts) :
    7 ∣ Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)) :=
  dvd_card_centralizer_of hF y7Word (by norm_num) y7Word_check

theorem eleven_dvd_card_centralizer (hF : J4Facts) :
    11 ∣ Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)) :=
  dvd_card_centralizer_of hF y11Word (by norm_num) y11Word_check

end CFSG.Sporadic.J4.QT2
