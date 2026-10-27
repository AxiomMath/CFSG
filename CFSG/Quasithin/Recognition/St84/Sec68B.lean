module

public import CFSG.Quasithin.Recognition.St84.Sec68A
import CFSG.GroupTheory.SupMulCommutative
import CFSG.Quasithin.Recognition.St84.Gen.Sec6TorusCent

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

private structure Ctx (X : Setup Γ G) (s : ℕ) : Prop where
  hc : CharTwoStab (V := V) (G := G)
  hn0 : 2 ≤ X.n 0
  hs : IsSingularity Γ G s
  hodd : Odd s
  h5 : 5 ≤ s
  hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s
  hGT : Even (Nat.card X.GT)

private theorem Lst_transitive (h : Ctx X s)
    (hU : X.IsSK X.QT) {a b : V} (ha : Γ.Adj (X.vert 0) a) (hb : Γ.Adj (X.vert 0) b) :
    ∃ g ∈ X.Lst X.QT 0, g • a = b := by
  have hL : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  obtain ⟨g, hgL, hgab⟩ := hL.trans a b ha hb
  rw [X.L_eq_Lst_sup_Q hU (Or.inr h.hn0)] at hgL
  have hnorm : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (oTwoPrime_le _).trans ((X.normGi_le_Gi X.QT 0).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  rw [sup_comm] at hgL
  obtain ⟨q, hq, l, hl, hql⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hgL
  have hlG0 : l ∈ X.Gi 0 := (X.normGi_le_Gi X.QT 0) (oTwoPrime_le _ hl)
  have hla : Γ.Adj (X.vert 0) (l • a) := by
    have h0 : l • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hlG0
    rw [← h0]
    exact (X.hyp.adj_smul l (X.vert 0) a).2 ha
  refine ⟨l, hl, ?_⟩
  calc l • a = q • (l • a) := by rw [X.Q_fixes_neighbors_vert 0 (l • a) hla q hq]
    _ = (q * l) • a := (mul_smul q l a).symm
    _ = g • a := by rw [← hql]
    _ = b := hgab

private theorem m_eq_four_of_maxReg (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : m = 4 :=
  X.m_eq_four h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg

private theorem card_Z_one_eq (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) :=
  X.card_Z_one_sq h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg

private theorem card_Z_neg_one_eq (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.Z (-1)) = 2 ^ (2 * X.n 0) := by
  have hconj : X.Z (-1) = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 1) := by
    have h := X.Z_add (-1) 1
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
    exact h
  rw [hconj, card_conjSub, card_Z_one_eq X h hreg]

private theorem card_E_eq (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.E X.QT 0) = 2 ^ (3 * X.n 0) * Nat.card X.QT := by
  rw [X.card_E (m := m) h.hGT h.hs h.hodd h.h5 h.hX hreg,
    m_eq_four_of_maxReg X h hreg]
  rw [show X.n 0 * (4 - 1) = 3 * X.n 0 by omega]

private theorem card_skP_eq (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.skP X.QT) = 2 ^ X.n 0 * Nat.card (X.E X.QT 0) := by
  rw [X.card_skP (m := m) h.hGT h.hs h.hodd h.h5 h.hX hreg,
    m_eq_four_of_maxReg X h hreg, card_E_eq X h hreg]
  rw [show X.n 0 * 4 = 3 * X.n 0 + X.n 0 by ring, pow_add]
  ring

private theorem Q_conjSub {g : G} {i j : ℤ} (h : g • X.vert i = X.vert j) :
    conjSub g (X.Q i) = X.Q j := by
  unfold Setup.Q
  rw [← pCoreOf_conjSub, ← stabilizer_smul_eq_conjSub g (X.vert i), h]

private theorem conjSub_tau_K : conjSub X.τ X.K = X.K :=
  CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer X.τ_norm

private theorem conjSub_tau_Ki_zero_le_K : conjSub X.τ (X.Ki 0) ≤ X.K :=
  (conjSub_mono X.τ (inf_le_left : X.Ki 0 ≤ X.K)).trans X.conjSub_tau_K.le

private theorem Z_two_eq_conjSub : X.Z 2 = conjSub X.τ (X.Z 0) := by
  have hh := X.Z_add 1 0
  rw [show (0 : ℤ) + 2 * 1 = 2 by norm_num, zpow_one] at hh
  exact hh

private theorem E_QT_comm (h : Ctx X s) :
    ∀ x ∈ X.E X.QT 0, ∀ y ∈ X.E X.QT 0, x * y = y * x :=
  fun x hx y hy => F7.isElemAbelian_comm
    (X.isElemAbelian_E_QT h.hGT h.hs h.hodd h.h5 h.hX) hx hy

private theorem QT_le_normalizer_Z_zero : X.QT ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (X.Z 0 : Set G))
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzq : z ∈ Subgroup.centralizer (X.Q 0 : Set G) := (X.Z_le_center 0 hz).2
  exact ((Subgroup.mem_centralizer_iff.mp hzq) q (X.QT_le_Q 0 hq)).symm

private theorem Z_zero_le_Z_one (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ≤ X.Z 1 :=
  le_sup_left.trans (X.Z_zero_sup_Z_two_le h.hc (Or.inl h.hn0)
    h.hs h.hodd h.h5 h.hX h.hGT hreg)

private theorem Z_two_le_Z_one (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 2 ≤ X.Z 1 :=
  le_sup_right.trans (X.Z_zero_sup_Z_two_le h.hc (Or.inl h.hn0)
    h.hs h.hodd h.h5 h.hX h.hGT hreg)

private theorem Z_zero_le_Z_neg_one (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 0 ≤ X.Z (-1) := by
  have hZ02 := X.Z_zero_sup_Z_two_le h.hc (Or.inl h.hn0) h.hs h.hodd
    h.h5 h.hX h.hGT hreg
  have hconj : conjSub (X.τ ^ (-1 : ℤ)) (X.Z 0) ⊔ conjSub (X.τ ^ (-1 : ℤ)) (X.Z 2) ≤
      conjSub (X.τ ^ (-1 : ℤ)) (X.Z 1) := by
    simpa only [conjSub_sup] using conjSub_mono (X.τ ^ (-1 : ℤ)) hZ02
  rw [← X.Z_add (-1) 0, ← X.Z_add (-1) 2, ← X.Z_add (-1) 1] at hconj
  have h' : X.Z (-2) ⊔ X.Z 0 ≤ X.Z (-1) := by
    simpa only [show (0 : ℤ) + 2 * (-1) = -2 by norm_num,
      show (2 : ℤ) + 2 * (-1) = 0 by norm_num,
      show (1 : ℤ) + 2 * (-1) = -1 by norm_num] using hconj
  exact le_sup_right.trans h'

private theorem Z_neg_one_inf_ZM (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z (-1) ⊓ X.ZM = X.Z 0 := by
  have hZ0 : X.Z 0 ≤ X.Z (-1) := Z_zero_le_Z_neg_one X h hreg
  rw [X.ZM_eq_Z_zero_sup_QT h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX
    h.hGT hreg,
    sup_comm (X.Z 0) X.QT,
    ← Subgroup.inf_sup_assoc_of_le (H := X.QT) (K := X.Z (-1)) (N := X.Z 0)
      (QT_le_normalizer_Z_zero X) hZ0,
    inf_comm (X.Z (-1)) X.QT,
    X.QT_inf_Z_eq_bot h.hGT h.hs h.hodd h.h5 h.hX (-1), bot_sup_eq]

private theorem exists_mem_Lst_smul_vert_one_eq_vert_neg_one (h : Ctx X s) :
    ∃ y ∈ X.Lst X.QT 0, y • X.vert 1 = X.vert (-1) := by
  have hleft : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h0 : (-1 : ℤ) + 1 = 0 := by norm_num
    rw [← h0]
    exact (X.adj (-1)).symm
  exact Lst_transitive X h (X.isSK_QT h.hGT h.hs h.hodd h.h5 h.hX) (X.adj 0) hleft

private theorem isSylow_skP_Lst (h : Ctx X s) :
    IsSylowTwoOf (X.skP X.QT) (X.Lst X.QT 0) :=
  X.isSylowTwoOf_skP_Lst_QT h.hGT h.hs h.hodd h.h5 h.hX

private theorem skP_le_Lst : X.skP X.QT ≤ X.Lst X.QT 0 := by
  intro a ha
  have hP2 : IsPGroup 2 (X.skP X.QT) :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  obtain ⟨n, hn⟩ := hP2 ⟨a, ha⟩
  exact Subgroup.subset_closure
    ⟨(inf_le_right : X.skP X.QT ≤ X.normGi X.QT 0) ha, n, congrArg Subtype.val hn⟩

private theorem isSylow_conj_skP (h : Ctx X s) {y : G}
    (hy : y ∈ X.Lst X.QT 0) :
    IsSylowTwoOf (conjSub y (X.skP X.QT)) (X.Lst X.QT 0) := by
  have h0 := isSylow_skP_Lst X h
  have hL : conjSub y (X.Lst X.QT 0) = X.Lst X.QT 0 := conjSub_eq_of_mem hy
  refine ⟨?_, h0.2.1.map (MulAut.conj y).toMonoidHom, ?_⟩
  · rw [← hL]
    exact conjSub_mono y h0.1
  · rw [← hL]
    have hidx : ((conjSub y (X.skP X.QT)).subgroupOf (conjSub y (X.Lst X.QT 0))).index =
        (X.skP X.QT).relIndex (X.Lst X.QT 0) :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj y).toMonoidHom)
        (X.skP X.QT) (X.Lst X.QT 0) (MulEquiv.injective (MulAut.conj y))
    rw [hidx]
    exact h0.2.2

private theorem skP_ne_conj_skP (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {y : G} (hy : y ∈ X.Lst X.QT 0)
    (hy1 : y • X.vert 1 = X.vert (-1)) :
    X.skP X.QT ≠ conjSub y (X.skP X.QT) := by
  intro heq
  have hP'leQneg : conjSub y (X.skP X.QT) ≤ X.Q (-1) := by
    rw [← Q_conjSub X hy1]
    exact conjSub_mono y inf_le_left
  have hPleQneg : X.skP X.QT ≤ X.Q (-1) := heq ▸ hP'leQneg
  have hleft : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h0 : (-1 : ℤ) + 1 = 0 := by norm_num
    rw [← h0]
    exact (X.adj (-1)).symm
  have hne : X.vert (-1) ≠ X.vert 1 := by
    intro hh
    exact absurd (X.vert_injective hh) (by norm_num)
  have hPleQ0 : X.skP X.QT ≤ X.Q 0 := by
    have h2 : IsPGroup 2 (X.skP X.QT) :=
      (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
    have hG0 : X.skP X.QT ≤ X.Gi 0 :=
      (inf_le_right : X.skP X.QT ≤ X.normGi X.QT 0).trans (X.normGi_le_Gi X.QT 0)
    exact le_pCoreOf_of_isPGroup_fixes_two X.hyp h2 hG0 hleft (X.adj 0) hne
      (fun z hz => MulAction.mem_stabilizer_iff.mp (hPleQneg.trans (X.Q_le_Gi (-1)) hz))
      (fun z hz => MulAction.mem_stabilizer_iff.mp
        (X.Q_le_Gi 1 ((inf_le_left : X.skP X.QT ≤ X.Q 1) hz)))
  have hPnormQ : X.skP X.QT ≤ Subgroup.normalizer (X.QT : Set G) :=
    (inf_le_right : X.skP X.QT ≤ X.normGi X.QT 0).trans (X.normGi_le_normalizer X.QT 0)
  have hPleE : X.skP X.QT ≤ X.E X.QT 0 := le_inf hPleQ0 hPnormQ
  have hEGi : X.E X.QT 0 ≤ X.Gi 0 :=
    (inf_le_left : X.E X.QT 0 ≤ X.Q 0).trans (X.Q_le_Gi 0)
  haveI hGifin : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI hEfin : Finite ↥(X.E X.QT 0) :=
    Finite.of_injective (Subgroup.inclusion hEGi) (Subgroup.inclusion_injective hEGi)
  have hcardle : Nat.card ↥(X.skP X.QT) ≤ Nat.card ↥(X.E X.QT 0) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hPleE) (Subgroup.inclusion_injective hPleE)
  rw [card_skP_eq X h hreg] at hcardle
  have hQGi : X.QT ≤ X.Gi 0 := (X.QT_le_Q 0).trans (X.Q_le_Gi 0)
  haveI hQfin : Finite ↥X.QT :=
    Finite.of_injective (Subgroup.inclusion hQGi) (Subgroup.inclusion_injective hQGi)
  have hpos : 0 < Nat.card ↥(X.E X.QT 0) := by
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (X.QT_ne_bot h.hGT)
    haveI : Nonempty ↥X.QT := ⟨q⟩
    rw [card_E_eq X h hreg]
    exact Nat.mul_pos (by positivity) Nat.card_pos
  have hlt : Nat.card ↥(X.E X.QT 0) < 2 ^ X.n 0 * Nat.card ↥(X.E X.QT 0) := by
    have hpow : 2 ≤ 2 ^ X.n 0 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) h.hn0)
    have h1 : 1 < 2 ^ X.n 0 := lt_of_lt_of_le (by norm_num) hpow
    simpa [one_mul] using Nat.mul_lt_mul_of_pos_right h1 hpos
  exact (not_lt_of_ge hcardle) hlt

private theorem not_skP_le_sup (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {y : G} (hy : y ∈ X.Lst X.QT 0)
    (hy1 : y • X.vert 1 = X.vert (-1)) :
    ¬ X.skP X.QT ≤ conjSub y (X.skP X.QT) ⊔ X.E X.QT 0 := by
  have hEM0 : conjSub y (X.E X.QT 0) = X.E X.QT 0 :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
      (X.normGi_le_normalizer_E X.QT 0 ((oTwoPrime_le _) hy))
  have hE' : X.E X.QT 0 ≤ conjSub y (X.skP X.QT) := by
    rw [← hEM0]
    exact conjSub_mono y
      (X.E_le_skP (X.isSK_QT h.hGT h.hs h.hodd h.h5 h.hX))
  intro hle
  have hsup : conjSub y (X.skP X.QT) ⊔ X.E X.QT 0 = conjSub y (X.skP X.QT) :=
    sup_eq_left.mpr hE'
  rw [hsup] at hle
  have hcard : Nat.card ↥(X.skP X.QT) = Nat.card ↥(conjSub y (X.skP X.QT)) := by
    rw [card_conjSub]
  have hPGi : X.skP X.QT ≤ X.Gi 0 :=
    (inf_le_right : X.skP X.QT ≤ X.normGi X.QT 0).trans (X.normGi_le_Gi X.QT 0)
  haveI hGifin : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI hPfin : Finite ↥(X.skP X.QT) :=
    Finite.of_injective (Subgroup.inclusion hPGi) (Subgroup.inclusion_injective hPGi)
  have hP'Gi : conjSub y (X.skP X.QT) ≤ X.Gi 0 :=
    (isSylow_conj_skP X h hy).1.trans ((oTwoPrime_le (X.normGi X.QT 0)).trans
      (X.normGi_le_Gi X.QT 0))
  haveI hP'fin : Finite ↥(conjSub y (X.skP X.QT)) :=
    Finite.of_injective (Subgroup.inclusion hP'Gi) (Subgroup.inclusion_injective hP'Gi)
  have heq : X.skP X.QT = conjSub y (X.skP X.QT) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact skP_ne_conj_skP X h hreg hy hy1 heq

private theorem Z_neg_one_le_E_QT (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z (-1) ≤ X.E X.QT 0 := by
  obtain ⟨y, hy, hy1⟩ := exists_mem_Lst_smul_vert_one_eq_vert_neg_one X h
  calc X.Z (-1) = conjSub y (X.Z 1) := (X.Z_conj hy1).symm
    _ ≤ conjSub y (X.E X.QT 0) := conjSub_mono y (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX)
    _ = X.E X.QT 0 := CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
          (X.normGi_le_normalizer_E X.QT 0 ((oTwoPrime_le _) hy))

private theorem Z_neg_one_le_relCent (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {y : G} (hy : y ∈ X.Lst X.QT 0)
    (hy1 : y • X.vert 1 = X.vert (-1)) :
    X.Z (-1) ≤ relCent (X.E X.QT 0) X.ZM (conjSub y (X.skP X.QT)) := by
  have hEZ := X.E_le_normalizer_ZM
  have hZneg : X.Z (-1) = conjSub y (X.Z 1) := (X.Z_conj hy1).symm
  have hEM0 : conjSub y (X.E X.QT 0) = X.E X.QT 0 :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
      (X.normGi_le_normalizer_E X.QT 0 ((oTwoPrime_le _) hy))
  intro z' hz'
  rw [hZneg] at hz'
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz'
  rw [mem_relCent hEZ]
  refine ⟨hEM0 ▸ mul_mem_conjSub (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX hz), fun a' ha' => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  have haQ1 : a ∈ X.Q 1 := (inf_le_left : X.skP X.QT ≤ X.Q 1) ha
  have hzq : z ∈ Subgroup.centralizer (X.Q 1 : Set G) := (X.Z_le_center 1 hz).2
  have hcomm : a * z = z * a := (Subgroup.mem_centralizer_iff.mp hzq) a haQ1
  have h1 : (y * z * y⁻¹) * (y * a * y⁻¹) = (y * a * y⁻¹) * (y * z * y⁻¹) :=
    (Commute.conj (hcomm.symm) y).eq
  have h2 : ⁅(MulEquiv.toMonoidHom (MulAut.conj y)) z,
      (MulEquiv.toMonoidHom (MulAut.conj y)) a⁆ = 1 := by
    show ⁅y * z * y⁻¹, y * a * y⁻¹⁆ = 1
    rw [commutatorElement_def, h1]
    group
  rw [h2]
  exact X.ZM.one_mem

private theorem relIndex_ZM_Z_one_sup (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.ZM.relIndex (X.Z 1 ⊔ X.ZM) = 2 ^ X.n 0 := by
  have hZ1N : X.Z 1 ≤ Subgroup.normalizer (X.ZM : Set G) := by
    intro z hz
    refine Subgroup.centralizer_le_normalizer (X.ZM : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (E_QT_comm X h z (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX hz) w (X.ZM_le_E_QT
      h.hGT h.hs h.hodd h.h5 h.hX hw)).symm
  rw [← CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer hZ1N, X.Z_one_inf_ZM
          h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg]
  have hZ0Z1 : X.Z 0 ≤ X.Z 1 := Z_zero_le_Z_one X h hreg
  have hmul := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Z 1)
  rw [inf_eq_left.mpr hZ0Z1,
    X.card_Z_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg,
    card_Z_one_eq X h hreg] at hmul
  have h2 : 2 ^ (2 * X.n 0) = 2 ^ X.n 0 * 2 ^ X.n 0 := by
    rw [show 2 * X.n 0 = X.n 0 + X.n 0 by ring, pow_add]
  rw [h2] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

private theorem relIndex_ZM_Z_neg_one_sup (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.ZM.relIndex (X.Z (-1) ⊔ X.ZM) = 2 ^ X.n 0 := by
  have hZN : X.Z (-1) ≤ Subgroup.normalizer (X.ZM : Set G) := by
    intro z hz
    refine Subgroup.centralizer_le_normalizer (X.ZM : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hzE : X.Z (-1) ≤ X.E X.QT 0 := Z_neg_one_le_E_QT X h hreg
    exact (E_QT_comm X h z (hzE hz) w (X.ZM_le_E_QT
      h.hGT h.hs h.hodd h.h5 h.hX hw)).symm
  rw [← CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer hZN, Z_neg_one_inf_ZM X h hreg]
  have hZ0 : X.Z 0 ≤ X.Z (-1) := Z_zero_le_Z_neg_one X h hreg
  have hmul := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Z (-1))
  rw [inf_eq_left.mpr hZ0,
    X.card_Z_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg,
    card_Z_neg_one_eq X h hreg] at hmul
  have h2 : 2 ^ (2 * X.n 0) = 2 ^ X.n 0 * 2 ^ X.n 0 := by
    rw [show 2 * X.n 0 = X.n 0 + X.n 0 by ring, pow_add]
  rw [h2] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

private theorem eq_relCent_of_le (h : Ctx X s) {S : Subgroup G}
    (hS : IsSylowTwoOf S (X.Lst X.QT 0)) {A : Subgroup G} (hZA : X.ZM ≤ A)
    (hAle : A ≤ relCent (X.E X.QT 0) X.ZM S)
    (hrel : X.ZM.relIndex A = 2 ^ X.n 0) :
    A = relCent (X.E X.QT 0) X.ZM S := by
  have hline := (X.natQuot_M h.hGT h.hs h.hodd h.h5 h.hX).line S hS
  have hrelC : X.ZM.relIndex (relCent (X.E X.QT 0) X.ZM S) = 2 ^ X.n 0 := hline
  have hchain := Subgroup.relIndex_mul_relIndex (H := X.ZM) (K := A)
    (L := relCent (X.E X.QT 0) X.ZM S) hZA hAle
  rw [hrel, hrelC] at hchain
  have hone : A.relIndex (relCent (X.E X.QT 0) X.ZM S) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left (n := 2 ^ X.n 0) (Nat.pow_pos (by norm_num)) ?_
    rw [mul_one]
    exact hchain
  exact le_antisymm hAle (Subgroup.relIndex_eq_one.mp hone)

private theorem Z_sup_ZM_inf_and_sup (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    (X.Z 1 ⊔ X.ZM) ⊓ (X.Z (-1) ⊔ X.ZM) = X.ZM ∧
      (X.Z 1 ⊔ X.ZM) ⊔ (X.Z (-1) ⊔ X.ZM) = X.E X.QT 0 := by
  obtain ⟨y, hy, hy1⟩ := exists_mem_Lst_smul_vert_one_eq_vert_neg_one X h
  have hP := isSylow_skP_Lst X h
  have hP' := isSylow_conj_skP X h hy
  have hnot := not_skP_le_sup X h hreg hy hy1
  set R1 : Subgroup G := relCent (X.E X.QT 0) X.ZM (X.skP X.QT) with hR1
  set R2 : Subgroup G := relCent (X.E X.QT 0) X.ZM (conjSub y (X.skP X.QT)) with hR2
  have hlines := (X.natQuot_M h.hGT h.hs h.hodd h.h5 h.hX).lines_inf
    (X.skP X.QT) (conjSub y (X.skP X.QT)) hP hP' hnot
  rw [← hR1, ← hR2] at hlines
  have hZ1 : R1 = X.Z 1 ⊔ X.ZM :=
    (eq_relCent_of_le X h hP (le_sup_right) (sup_le (X.Z_one_le_relCent (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX))
      (X.ZM_le_relCent_of_le_Lst (X.ZM_le_E_QT
      h.hGT h.hs h.hodd h.h5 h.hX) (skP_le_Lst X)))
      (relIndex_ZM_Z_one_sup X h hreg)).symm
  have hZneg : R2 = X.Z (-1) ⊔ X.ZM :=
    (eq_relCent_of_le X h hP' (le_sup_right) (sup_le (Z_neg_one_le_relCent X h hreg hy hy1)
      (X.ZM_le_relCent_of_le_Lst (X.ZM_le_E_QT
      h.hGT h.hs h.hodd h.h5 h.hX) (isSylow_conj_skP X h hy).1))
      (relIndex_ZM_Z_neg_one_sup X h hreg)).symm
  rw [hZ1, hZneg] at hlines
  exact hlines

@[expose] def V0 : Subgroup G := ⨆ (g : G) (_ : g ∈ X.Lst X.QT 0), conjSub g (X.Z 1)

@[expose] def V2 : Subgroup G := conjSub X.τ X.V0

@[expose] def Vt : Subgroup G := ⁅X.E X.QT 0, X.Ki 4⁆

private theorem Ki_zero_le_centralizer_ZM (h : Ctx X s) :
    X.Ki 0 ≤ Subgroup.centralizer (X.ZM : Set G) := by
  intro k hk
  have hkL : k ∈ X.Lst X.QT 0 := X.Ki_zero_le_Lst h.hGT h.hs h.hodd h.h5 h.hX h.hn0 hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzcent : z ∈ Subgroup.centralizer (X.Lst X.QT 0 : Set G) :=
    (Subgroup.mem_inf.mp hz).2
  have hh := (Subgroup.mem_centralizer_iff.mp hzcent) k hkL
  exact hh.symm

private theorem Ki_two_le_centralizer (h : Ctx X s) :
    conjSub X.τ (X.Ki 0) ≤
      Subgroup.centralizer (X.Z 2 : Set G) ⊓ Subgroup.centralizer (X.QT : Set G) := by
  have hQτ : conjSub X.τ X.QT = X.QT := X.conjSub_tau_QT
  have hZ2 : X.Z 2 = conjSub X.τ (X.Z 0) := X.Z_two_eq_conjSub
  intro g hg
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
  have hkZM : k ∈ Subgroup.centralizer (X.ZM : Set G) := Ki_zero_le_centralizer_ZM X h hk
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZ2] at hz
    obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
    have hz0ZM : z0 ∈ X.ZM :=
      X.Z_zero_le_ZM h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hz0
    have hcomm := (Subgroup.mem_centralizer_iff.mp hkZM) z0 hz0ZM
    show X.τ * z0 * X.τ⁻¹ * (X.τ * k * X.τ⁻¹)
        = X.τ * k * X.τ⁻¹ * (X.τ * z0 * X.τ⁻¹)
    exact (Commute.conj (hcomm : Commute z0 k) X.τ).eq
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [← hQτ] at hq
    obtain ⟨q0, hq0, rfl⟩ := Subgroup.mem_map.mp hq
    have hq0ZM : q0 ∈ X.ZM :=
      X.QT_le_centerOf_Lst h.hGT h.hs h.hodd h.h5 h.hX hq0
    have hcomm := (Subgroup.mem_centralizer_iff.mp hkZM) q0 hq0ZM
    show X.τ * q0 * X.τ⁻¹ * (X.τ * k * X.τ⁻¹)
        = X.τ * k * X.τ⁻¹ * (X.τ * q0 * X.τ⁻¹)
    exact (Commute.conj (hcomm : Commute q0 k) X.τ).eq

private theorem Ki_zero_inf_two_le_centralizer (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Ki 0 ⊓ conjSub X.τ (X.Ki 0) ≤
      Subgroup.centralizer (X.Z 1 : Set G) ⊓ Subgroup.centralizer (X.QT : Set G) := by
  have hZ0Z1 : X.Z 0 ≤ X.Z 1 := Z_zero_le_Z_one X h hreg
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := Z_two_le_Z_one X h hreg
  have hZ2N : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer (X.Z 0 : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (X.Z_commute 1 b (hZ2Z1 hb) a (hZ0Z1 ha)).symm
  intro g hg
  obtain ⟨hg0, hg2⟩ := Subgroup.mem_inf.mp hg
  have hg0c := Ki_zero_le_centralizer_ZM X h hg0
  have hg2c := Ki_two_le_centralizer X h hg2
  have hg2Z : g ∈ Subgroup.centralizer (X.Z 2 : Set G) := (Subgroup.mem_inf.mp hg2c).1
  have hg2Q : g ∈ Subgroup.centralizer (X.QT : Set G) := (Subgroup.mem_inf.mp hg2c).2
  refine Subgroup.mem_inf.mpr ⟨?_, hg2Q⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz1 : z ∈ X.Z 1 := hz
  have hz' : z ∈ X.Z 0 ⊔ X.Z 2 := by
    rw [← X.Z_one_eq_Z_zero_sup_Z_two (m := m) h.hc (Or.inl h.hn0) h.hs
      h.hodd h.h5 h.hX h.hGT hreg]
    exact hz1
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hZ2N).mp hz'
  have haZM : a ∈ X.ZM :=
    X.Z_zero_le_ZM h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT ha
  have hca := (Subgroup.mem_centralizer_iff.mp hg0c) a haZM
  have hcb := (Subgroup.mem_centralizer_iff.mp hg2Z) b hb
  calc a * b * g = a * (b * g) := by group
    _ = a * (g * b) := by rw [hcb]
    _ = g * a * b := by rw [← mul_assoc, hca]
    _ = g * (a * b) := by group

private theorem E_inf_K_eq_bot :
    X.E X.QT 0 ⊓ X.K = ⊥ := by
  have hE2 : IsPGroup 2 (X.E X.QT 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  have hEG : X.E X.QT 0 ≤ X.Gi 0 ⊓ X.Gi 1 := by
    refine le_inf ((inf_le_left : X.E X.QT 0 ≤ X.Q 0).trans (X.Q_le_Gi 0)) ?_
    intro e he
    have heQ : e ∈ X.Q 0 := (inf_le_left : X.E X.QT 0 ≤ X.Q 0) he
    exact MulAction.mem_stabilizer_iff.mpr (X.Q_fixes_neighbors_vert 0 (X.vert 1) (X.adj 0) e heQ)
  haveI hG01fin : Finite ↥(X.Gi 0 ⊓ X.Gi (0 + 1)) := by
    haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
    exact Finite.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hES : X.E X.QT 0 ≤ X.S :=
    le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow 0) (X.edgeSylow_subgroupOf_normal 0)
      hEG hE2
  refine le_antisymm ?_ bot_le
  calc X.E X.QT 0 ⊓ X.K ≤ X.S ⊓ X.K := inf_le_inf_right _ hES
    _ = ⊥ := by rw [inf_comm, X.K_inf]

theorem E_eq_Z_one_sup_Z_neg_one_sup_QT (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.E X.QT 0 = X.Z 1 ⊔ X.Z (-1) ⊔ X.QT := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hsup := (Z_sup_ZM_inf_and_sup X h hreg).2
  have hZ0Z1 : X.Z 0 ≤ X.Z 1 := Z_zero_le_Z_one X h hreg
  have hZ0Zneg : X.Z 0 ≤ X.Z (-1) := Z_zero_le_Z_neg_one X h hreg
  rw [← hsup]
  rw [X.ZM_eq_Z_zero_sup_QT h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX
    h.hGT hreg]
  have h1 : X.Z 1 ⊔ (X.Z 0 ⊔ X.QT) = X.Z 1 ⊔ X.QT := by
    rw [← sup_assoc, sup_eq_left.mpr hZ0Z1]
  have h2 : X.Z (-1) ⊔ (X.Z 0 ⊔ X.QT) = X.Z (-1) ⊔ X.QT := by
    rw [← sup_assoc, sup_eq_left.mpr hZ0Zneg]
  rw [h1, h2]
  ac_rfl

theorem Ki_zero_inf_Ki_two (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Ki 0 ⊓ conjSub X.τ (X.Ki 0) = ⊥ := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hcent := Ki_zero_inf_two_le_centralizer X h hreg
  have hfpf := (X.natQuot_M h.hGT h.hs h.hodd h.h5 h.hX).fpf
  have hMleLst : X.Ki 0 ⊓ conjSub X.τ (X.Ki 0) ≤ X.Lst X.QT 0 :=
    fun g hg => X.Ki_zero_le_Lst h.hGT h.hs h.hodd h.h5 h.hX h.hn0 (Subgroup.mem_inf.mp hg).1
  have hex : ∃ e ∈ X.Z 1, e ∉ X.Z 0 := by
    by_contra hcon
    push Not at hcon
    have hle : X.Z 1 ≤ X.Z 0 := hcon
    have h1 : Nat.card ↥(X.Z 0) = 2 ^ X.n 0 :=
      X.card_Z_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg
    have h2 : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 0) := card_Z_one_eq X h hreg
    have hZ0Gi : X.Z 0 ≤ X.Gi 0 := X.Z_le_Gi 0
    haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
    haveI : Finite ↥(X.Z 0) :=
      Finite.of_injective (Subgroup.inclusion hZ0Gi) (Subgroup.inclusion_injective hZ0Gi)
    have hle2 : Nat.card ↥(X.Z 1) ≤ Nat.card ↥(X.Z 0) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [h1, h2] at hle2
    have hlt : 2 ^ X.n 0 < 2 ^ (2 * X.n 0) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hMleE : X.Ki 0 ⊓ conjSub X.τ (X.Ki 0) ≤ X.E X.QT 0 := by
    intro g hg
    by_contra hgE
    obtain ⟨e, heZ1, heZ0⟩ := hex
    have heE : e ∈ X.E X.QT 0 := X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX heZ1
    have hgc : g ∈ Subgroup.centralizer (X.Z 1 : Set G) := (Subgroup.mem_inf.mp (hcent hg)).1
    have hcomm : e * g = g * e := (Subgroup.mem_centralizer_iff.mp hgc) e heZ1
    have hcommZ : ⁅e, g⁆ ∈ X.ZM := by
      rw [commutatorElement_def, hcomm]
      have h1 : g * e * e⁻¹ * g⁻¹ = 1 := by group
      rw [h1]
      exact X.ZM.one_mem
    have hgK : g ∈ X.K := (Subgroup.mem_inf.mp hg).1.1
    have hdvd : orderOf g ∣ Nat.card ↥X.K := by
      have hh := orderOf_dvd_natCard (⟨g, hgK⟩ : ↥X.K)
      rwa [Subgroup.orderOf_mk] at hh
    have hgOdd : Odd (orderOf g) := Odd.of_dvd_nat X.odd_card_K hdvd
    have hginZM : e ∈ X.ZM := hfpf g (hMleLst hg) hgOdd hgE e heE hcommZ
    have hinf : e ∈ X.Z 1 ⊓ X.ZM := Subgroup.mem_inf.mpr ⟨heZ1, hginZM⟩
    rw [X.Z_one_inf_ZM
          h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg] at hinf
    exact heZ0 hinf
  refine le_antisymm ?_ bot_le
  calc X.Ki 0 ⊓ conjSub X.τ (X.Ki 0) ≤ X.E X.QT 0 ⊓ X.K :=
        le_inf hMleE (fun g hg => (Subgroup.mem_inf.mp hg).1.1)
    _ = ⊥ := E_inf_K_eq_bot X

private theorem card_Ki_zero_sup_conj (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.Ki 0 ⊔ conjSub X.τ (X.Ki 0)) = (2 ^ X.n 0 - 1) ^ 2 := by
  have hcard0 : Nat.card ↥(X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (X.Ki 0)
      (conjSub X.τ (X.Ki 0)) (X.conjSub_tau_Ki_zero_le_K.trans (X.K_le_normalizer_Ki 0))
      (disjoint_iff.mpr (X.Ki_zero_inf_Ki_two h.hc h.hn0 h.hs h.hodd h.h5 h.hX
        h.hGT hreg)),
    card_conjSub, hcard0, pow_two]

private theorem card_K_le_mul :
    Nat.card ↥X.K ≤ (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) := by
  have h1 :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      (X.Ki 0) (X.Ki 1) (fun b hb n hn => (Subgroup.mem_normalizer_iff.mp
        (X.K_le_normalizer_Ki 1 hb.1) n).mp hn)
  rw [X.card_Ki 0, X.card_Ki 1, ← X.K_eq_sup] at h1
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  haveI : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (inf_le_left.trans (X.K_le_Gi 0))
  haveI : Finite ↥(X.Ki 0 ⊓ X.Ki 1) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  haveI : Nonempty ↥(X.Ki 0 ⊓ X.Ki 1) := ⟨1, Subgroup.one_mem _⟩
  have hd : 1 ≤ Nat.card ↥(X.Ki 0 ⊓ X.Ki 1) := Nat.card_pos
  calc Nat.card ↥X.K = Nat.card ↥X.K * 1 := (mul_one _).symm
    _ ≤ Nat.card ↥X.K * Nat.card ↥(X.Ki 0 ⊓ X.Ki 1) := Nat.mul_le_mul_left _ hd
    _ = (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) := h1

theorem n_one_eq_n_zero (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.n 1 = X.n 0 := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hKle := card_K_le_mul X
  have hsq := card_Ki_zero_sup_conj X h hreg
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  have hcardle : Nat.card ↥(X.Ki 0 ⊔ conjSub X.τ (X.Ki 0)) ≤ Nat.card ↥X.K :=
    Subgroup.card_le_of_le (sup_le inf_le_left X.conjSub_tau_Ki_zero_le_K)
  rw [hsq] at hcardle
  have hineq : (2 ^ X.n 0 - 1) ^ 2 ≤ (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) :=
    hcardle.trans hKle
  have hpos : 0 < 2 ^ X.n 0 - 1 := by
    have h1 : 1 < 2 ^ X.n 0 := Nat.one_lt_two_pow (by omega)
    omega
  rw [pow_two] at hineq
  have hcancel : 2 ^ X.n 0 - 1 ≤ 2 ^ X.n 1 - 1 :=
    Nat.le_of_mul_le_mul_left hineq hpos
  have hpow : 2 ^ X.n 0 ≤ 2 ^ X.n 1 := by
    have h1 : 1 ≤ 2 ^ X.n 0 := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ X.n 1 := Nat.one_le_two_pow
    omega
  have hn01 : X.n 0 ≤ X.n 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hn10 : X.n 1 ≤ X.n 0 := X.n_one_le_n_zero hc (Or.inl hn0) hs hodd h5 hX hGT
  omega

theorem K_eq_Ki_zero_sup_Ki_two (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.K = X.Ki 0 ⊔ conjSub X.τ (X.Ki 0) := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hn1 : X.n 1 = X.n 0 := n_one_eq_n_zero X hc hn0 hs hodd h5 hX hGT
  have hKle : Nat.card ↥X.K ≤ (2 ^ X.n 0 - 1) ^ 2 := by
    have h := card_K_le_mul X
    rwa [hn1, ← pow_two] at h
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  refine (Subgroup.eq_of_le_of_card_ge
    (sup_le inf_le_left X.conjSub_tau_Ki_zero_le_K) ?_).symm
  rw [card_Ki_zero_sup_conj X h hreg]
  exact hKle

theorem card_K_eq_sq (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    Nat.card ↥X.K = (2 ^ X.n 0 - 1) ^ 2 := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  rw [X.K_eq_Ki_zero_sup_Ki_two hc hn0 hs hodd h5 hX hGT hreg]
  exact card_Ki_zero_sup_conj X h hreg

theorem fixes_neighbors_of_commutator_Z_four_mem (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk : k ∈ X.K)
    (hcomm : ∀ z ∈ X.Z 4, ⁅z, k⁆ ∈ X.Q 0) : ∀ w : V, Γ.Adj (X.vert 0) w → k • w = w := by
  have hQN : X.Gi 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
  have hkG : k ∈ X.Gi 0 := X.K_le_Gi 0 hk
  let C : Subgroup G :=
    { carrier := {x | x ∈ X.Gi 0 ∧ ⁅k, x⁆ ∈ X.Q 0}
      one_mem' := ⟨(X.Gi 0).one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxG, hxQ⟩ ⟨hyG, hyQ⟩
        refine ⟨(X.Gi 0).mul_mem hxG hyG, ?_⟩
        have hconj : x * ⁅k, y⁆ * x⁻¹ ∈ X.Q 0 :=
          (Subgroup.mem_normalizer_iff.mp (hQN hxG) ⁅k, y⁆).mp hyQ
        rw [commutatorElement_mul_right_eq_mul_conj]
        exact (by
          simpa only [mul_assoc] using (X.Q 0).mul_mem hxQ hconj)
      inv_mem' := by
        rintro x ⟨hxG, hxQ⟩
        refine ⟨(X.Gi 0).inv_mem hxG, ?_⟩
        have hxk : ⁅x, k⁆ ∈ X.Q 0 := by
          have h := (X.Q 0).inv_mem hxQ
          rwa [commutatorElement_inv] at h
        have hconj : x⁻¹ * ⁅x, k⁆ * x ∈ X.Q 0 := by
          simpa using
            (Subgroup.mem_normalizer_iff.mp (hQN ((X.Gi 0).inv_mem hxG)) ⁅x, k⁆).mp hxk
        rw [commutatorElement_inv_right]
        exact hconj }
  have hZ4C : X.Z 4 ≤ C := by
    intro z hz
    refine ⟨X.Z_four_le_Gi_zero hc (Or.inl hn0) hs hodd h5 hX hGT hreg hz, ?_⟩
    have h := (X.Q 0).inv_mem (hcomm z hz)
    rwa [commutatorElement_inv] at h
  have hQ0C : X.Q 0 ≤ C := by
    intro q hq
    refine ⟨X.Q_le_Gi 0 hq, ?_⟩
    have hconj : k * q * k⁻¹ ∈ X.Q 0 :=
      (Subgroup.mem_normalizer_iff.mp (hQN hkG) q).mp hq
    have h := (X.Q 0).mul_mem hconj ((X.Q 0).inv_mem hq)
    simpa [commutatorElement_def] using h
  have hSC : X.edgeSylow 0 ≤ C := by
    rw [X.edgeSylow_zero,
      ← X.Z_four_sup_Q_zero hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact sup_le hZ4C hQ0C
  have hkodd : Odd (orderOf k) := by
    have hdvd : orderOf k ∣ Nat.card ↥X.K := by
      have hh := orderOf_dvd_natCard (⟨k, hk⟩ : ↥X.K)
      rwa [Subgroup.orderOf_mk] at hh
    exact X.odd_card_K.of_dvd_nat hdvd
  intro w hw
  exact X.fixes_neighbors_of_centralizes_edgeSylow_left_gen 0
    (X.K_le_Gi 1 hk) hkG hkodd (fun x hx => (hSC hx).2) w hw

private theorem Ki_two_eq_conjSub : X.Ki 2 = conjSub X.τ (X.Ki 0) := by
  have hL : X.L 2 = conjSub X.τ (X.L 0) := by
    unfold Setup.L
    rw [show (2 : ℤ) = 0 + 2 * 1 by norm_num, X.Gi_add, ← conjSub_oTwoPrime, zpow_one]
  have hK : conjSub X.τ X.K = X.K := X.conjSub_tau_K
  unfold Setup.Ki
  rw [hL, conjSub_inf, hK]

theorem commutator_Ki_zero_Ki_two_eq_bot (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.Ki 0, conjSub X.τ (X.Ki 0)⁆ = ⊥ := by
  have hK0N : X.Ki 0 ≤ Subgroup.normalizer (conjSub X.τ (X.Ki 0) : Set G) := by
    have h1 : X.K ≤ Subgroup.normalizer (conjSub X.τ (X.Ki 0) : Set G) := by
      have h := conjSub_mono X.τ (X.K_le_normalizer_Ki 0)
      rwa [X.conjSub_tau_K, ← CFSG.Quasithin.conjSub_normalizer] at h
    exact inf_le_left.trans h1
  have hK2N : conjSub X.τ (X.Ki 0) ≤ Subgroup.normalizer (X.Ki 0 : Set G) :=
    X.conjSub_tau_Ki_zero_le_K.trans (X.K_le_normalizer_Ki 0)
  have h1 : ⁅X.Ki 0, conjSub X.τ (X.Ki 0)⁆ ≤ X.Ki 0 := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hK2N
  have h2 : ⁅X.Ki 0, conjSub X.τ (X.Ki 0)⁆ ≤ conjSub X.τ (X.Ki 0) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hK0N
  have hle : ⁅X.Ki 0, conjSub X.τ (X.Ki 0)⁆ ≤ X.Ki 0 ⊓ conjSub X.τ (X.Ki 0) := le_inf h1 h2
  rw [X.Ki_zero_inf_Ki_two hc hn0 hs hodd h5 hX hGT hreg] at hle
  exact le_bot_iff.mp hle

theorem mul_comm_of_mem_K (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {a b : G} (ha : a ∈ X.K) (hb : b ∈ X.K) : a * b = b * a := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hK : X.K = X.Ki 0 ⊔ conjSub X.τ (X.Ki 0) :=
    X.K_eq_Ki_zero_sup_Ki_two hc hn0 hs hodd h5 hX hGT hreg
  have hbot : ⁅X.Ki 0, conjSub X.τ (X.Ki 0)⁆ = ⊥ :=
    X.commutator_Ki_zero_Ki_two_eq_bot hc hn0 hs hodd h5 hX hGT hreg
  have hcomm : ∀ x ∈ X.Ki 0, ∀ y ∈ conjSub X.τ (X.Ki 0), x * y = y * x := by
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.commutator_mem_commutator hx hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hA : IsMulCommutative ↥(X.Ki 0) :=
    IsMulCommutative.of_comm fun x y =>
      Subtype.ext (X.Ki_mul_comm_gen 0 x.2 y.2)
  have hB : IsMulCommutative ↥(conjSub X.τ (X.Ki 0)) := by
    refine IsMulCommutative.of_comm fun x y => ?_
    have hx : (x : G) ∈ X.Ki 2 := by
      simpa [Ki_two_eq_conjSub X] using x.2
    have hy : (y : G) ∈ X.Ki 2 := by
      simpa [Ki_two_eq_conjSub X] using y.2
    exact Subtype.ext (X.Ki_mul_comm_gen 2 hx hy)
  haveI : IsMulCommutative ↥(X.Ki 0 ⊔ conjSub X.τ (X.Ki 0)) :=
    CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute hcomm hA hB
  rw [hK] at ha hb
  exact Subgroup.mul_comm_of_mem_isMulCommutative
    (H := X.Ki 0 ⊔ conjSub X.τ (X.Ki 0)) ha hb

private theorem QT_le_centralizer_Ki_zero (h : Ctx X s) :
    X.QT ≤ Subgroup.centralizer (X.Ki 0 : Set G) := by
  have hQTZM : X.QT ≤ X.ZM :=
    X.QT_le_centerOf_Lst h.hGT h.hs h.hodd h.h5 h.hX
  intro q hq
  have hz : q ∈ Subgroup.centralizer (X.Lst X.QT 0 : Set G) :=
    (Subgroup.mem_inf.mp (hQTZM hq)).2
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkL : k ∈ X.Lst X.QT 0 := X.Ki_zero_le_Lst h.hGT h.hs h.hodd h.h5 h.hX h.hn0 hk
  have hh := (Subgroup.mem_centralizer_iff.mp hz) k hkL
  exact hh

theorem QT_eq_inf_centralizer_K (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.QT = X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hn1 : X.n 1 = X.n 0 := n_one_eq_n_zero X hc hn0 hs hodd h5 hX hGT
  have hn12 : 2 ≤ X.n 1 := by rwa [hn1]
  have hK := K_eq_Ki_zero_sup_Ki_two X hc hn0 hs hodd h5 hX hGT hreg
  refine le_antisymm ?_ ?_
  ·
    refine le_inf (X.QT_le_Q 0) ?_
    have h0 := QT_le_centralizer_Ki_zero X h
    have hnorm : conjSub X.τ (X.Ki 0) ≤ Subgroup.normalizer (X.Ki 0 : Set G) := by
      have hKi2K : conjSub X.τ (X.Ki 0) ≤ X.K := X.conjSub_tau_Ki_zero_le_K
      exact hKi2K.trans (X.K_le_normalizer_Ki 0)
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [hK] at hk
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hk
    have hqa := (Subgroup.mem_centralizer_iff.mp (h0 hq)) a ha
    have hq2 := (Subgroup.mem_inf.mp (Ki_two_le_centralizer X h hb)).2
    have hqb := (Subgroup.mem_centralizer_iff.mp hq2) q hq
    calc a * b * q = a * (b * q) := by group
      _ = a * (q * b) := by rw [hqb]
      _ = q * a * b := by rw [← mul_assoc, hqa]
      _ = q * (a * b) := by group
  ·
    set C := X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) with hC
    have hCQ : C ≤ X.Q 0 := inf_le_left
    have hCGi : C ≤ X.Gi 0 := hCQ.trans (X.Q_le_Gi 0)
    have hGT : Subgroup.centralizer (X.K : Set G) ⊓ X.Gi 0 ≤ X.GT :=
      X.centralizer_K_le_GT hn0 hn12 0
    have hCGT : C ≤ X.GT := by
      refine (le_inf ?_ hCGi).trans hGT
      exact inf_le_right
    have h2 : IsPGroup 2 C := (pCoreOf_isPGroup' (X.Gi 0)).to_le (hCQ.trans le_rfl)
    have hGi : C ≤ X.Gi 0 ⊓ X.Gi 1 := le_inf hCGi (hCGT.trans (X.GT_le_Gi 1))
    haveI hG01fin : Finite ↥(X.Gi 0 ⊓ X.Gi (0 + 1)) := by
      haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
      exact Finite.of_injective (Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left)
    have hS : C ≤ X.S :=
      le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow 0) (X.edgeSylow_subgroupOf_normal 0)
        hGi h2
    calc C ≤ X.GT ⊓ X.S := le_inf hCGT hS
      _ = X.QT := by rw [X.GT_eq_K_sup_QT.2]

private theorem commutator_QT_Ki_four_eq_bot (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : ⁅X.QT, X.Ki 4⁆ = ⊥ := by
  have hQ : X.QT = X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) :=
    QT_eq_inf_centralizer_K X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hcent : X.QT ≤ Subgroup.centralizer (X.Ki 4 : Set G) := by
    rw [hQ]
    refine (inf_le_right : X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) ≤
      Subgroup.centralizer (X.K : Set G)).trans ?_
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hy
    exact hg y hy.1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hcent

private theorem Ki_four_eq_conjSub :
    X.Ki 4 = conjSub (X.τ ^ (2 : ℤ)) (X.Ki 0) := by
  have hL : X.L 4 = conjSub (X.τ ^ (2 : ℤ)) (X.L 0) := by
    unfold Setup.L
    rw [show (4 : ℤ) = 0 + 2 * 2 by norm_num, X.Gi_add, ← conjSub_oTwoPrime]
  have hK : conjSub (X.τ ^ (2 : ℤ)) X.K = X.K :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer (zpow_mem X.τ_norm 2)
  unfold Setup.Ki
  rw [hL, conjSub_inf, hK]

private theorem Ki_zero_le_centralizer_Z_zero (h : Ctx X s) :
    X.Ki 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzZM : z ∈ X.ZM :=
    X.Z_zero_le_ZM h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hz
  have hc := (Subgroup.mem_centralizer_iff.mp (Ki_zero_le_centralizer_ZM X h hk)) z hzZM
  exact hc

private theorem Ki_four_le_centralizer_Z_four (h : Ctx X s) :
    X.Ki 4 ≤ Subgroup.centralizer (X.Z 4 : Set G) := by
  have hZ4 : X.Z 4 = conjSub (X.τ ^ (2 : ℤ)) (X.Z 0) := X.Z_four_eq_conjSub_tau_sq
  rw [Ki_four_eq_conjSub X, hZ4]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
  have hkz := (Subgroup.mem_centralizer_iff.mp (Ki_zero_le_centralizer_Z_zero X h hk)) z0 hz0
  exact (Commute.conj (hkz : Commute z0 k) (X.τ ^ (2 : ℤ))).eq

private theorem Ki_four_eq_conjSub_tau :
    X.Ki 4 = conjSub X.τ (X.Ki 2) := by
  rw [Ki_two_eq_conjSub X, Ki_four_eq_conjSub X]
  rw [← conjSub_mul]
  congr 1
  rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]

private theorem Ki_four_inf_Ki_two (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Ki 4 ⊓ X.Ki 2 = ⊥ := by
  have hzero := Ki_zero_inf_Ki_two X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have h' := congrArg (conjSub X.τ) hzero
  rw [conjSub_inf, conjSub_bot] at h'
  have h2 : X.Ki 2 = conjSub X.τ (X.Ki 0) := Ki_two_eq_conjSub X
  have h4 : X.Ki 4 = conjSub X.τ (X.Ki 2) := Ki_four_eq_conjSub_tau X
  rw [← h2, ← h4, inf_comm] at h'
  exact h'

private theorem K_inf_Q_eq_bot (h : Ctx X s) (i : ℤ) :
    X.K ⊓ X.Q i = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  obtain ⟨hkK, hkQ⟩ := Subgroup.mem_inf.mp hk
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup' (X.Gi i)) ⟨k, hkQ⟩
  have hk2 : k ^ (2 ^ n) = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  have hodd : Odd (orderOf k) :=
    X.odd_card_K.of_dvd_nat (by
      have hh := orderOf_dvd_natCard (⟨k, hkK⟩ : ↥X.K)
      rwa [Subgroup.orderOf_mk] at hh)
  have hcop : Nat.Coprime (orderOf k) (2 ^ n) := hodd.coprime_two_right.pow_right n
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (orderOf_dvd_of_pow_eq_one hk2))

private theorem fixedPointFree_of_le_Gi_inf {i : ℤ} (hni : 2 ≤ X.n i) {Z : Subgroup G}
    (hZ2 : IsPGroup 2 Z) (hZG : Z ≤ X.Gi (i - 1) ⊓ X.Gi i) (hZQ : Z ⊓ X.Q i = ⊥)
    {k : G} (hk : k ∈ X.Ki i) (hk1 : k ≠ 1) :
    ∀ z ∈ Z, k * z * k⁻¹ = z → z = 1 := by
  intro z hz hfix
  have hzGl : z • X.vert (i - 1) = X.vert (i - 1) :=
    MulAction.mem_stabilizer_iff.mp (hZG hz).1
  have hzGi : z ∈ X.Gi i := (hZG hz).2
  have hzfix : z • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hzGi
  have hkfix : k • X.vert (i + 1) = X.vert (i + 1) := X.K_fix k hk.1 (i + 1)
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hadj : Γ.Adj (X.vert i) (z • X.vert (i + 1)) := by
    have h := (X.hyp.adj_smul z (X.vert i) (X.vert (i + 1))).2 (X.adj i)
    rwa [hzfix] at h
  have hkz : k • (z • X.vert (i + 1)) = z • X.vert (i + 1) := by
    rw [← mul_smul, show k * z = z * k by
      calc k * z = (k * z * k⁻¹) * k := by group
        _ = z * k := by rw [hfix]]
    rw [mul_smul, hkfix]
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro hh
    exact absurd (X.vert_injective hh) (by omega)
  obtain h | h := (X.torus_fixed i hni hk hk1 (z • X.vert (i + 1)) hadj).mp hkz
  · exfalso
    have h' : z • X.vert (i + 1) = z • X.vert (i - 1) := by rw [h, hzGl]
    have h2 : X.vert (i + 1) = X.vert (i - 1) := by
      have := congrArg (fun x => z⁻¹ • x) h'
      simpa using this
    exact absurd (X.vert_injective h2) (by omega)
  · have hz2 : ∃ n : ℕ, z ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hZ2 ⟨z, hz⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hzQ : z ∈ X.Q i :=
      mem_pCoreOf_of_fixes_two X.hyp hzGi hz2 hleft (X.adj i) hne hzGl h
    have hmem : z ∈ Z ⊓ X.Q i := Subgroup.mem_inf.mpr ⟨hz, hzQ⟩
    rw [hZQ] at hmem
    exact Subgroup.mem_bot.mp hmem

private theorem Ki_four_fixes_neighbors (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk : k ∈ X.Ki 4) :
    ∀ w : V, Γ.Adj (X.vert 0) w → k • w = w := by
  refine X.fixes_neighbors_of_commutator_Z_four_mem h.hc h.hn0 h.hs h.hodd h.h5 h.hX
    h.hGT hreg hk.1 ?_
  intro z hz
  have hcomm : z * k = k * z :=
    (Subgroup.mem_centralizer_iff.mp (Ki_four_le_centralizer_Z_four X h hk)) z hz
  have h1 : ⁅z, k⁆ = 1 := by
    rw [commutatorElement_def, hcomm]
    group
  rw [h1]
  exact (X.Q 0).one_mem

private theorem Z_two_ne_bot (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 2 ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card (X.Z 2) = 1 := by rw [hbot, Subgroup.card_bot]
  have hZ2card : Nat.card (X.Z 2) = 2 ^ X.n 0 := by
    rw [X.Z_two_eq_conjSub, card_conjSub,
      X.card_Z_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg]
  rw [hZ2card] at hcard
  have h4 : 4 ≤ 2 ^ X.n 0 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) h.hn0
  omega

private theorem Ki_six_fixedPointFree_Z_two (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ k ∈ X.Ki 6, k ≠ 1 → ∀ z ∈ X.Z 2, k * z * k⁻¹ = z → z = 1 := by
  have hn6 : 2 ≤ X.n 6 := by
    have hh := X.n_add 3 0
    rw [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at hh
    rw [hh]
    exact h.hn0
  have hZ2eq : X.Z 2 = conjSub X.τ (X.Z 0) := X.Z_two_eq_conjSub
  have hQ6eq : X.Q 6 = conjSub X.τ (X.Q 4) := by
    have hh := X.Q_add 1 4
    rw [show (4 : ℤ) + 2 * 1 = 6 by norm_num, zpow_one] at hh
    exact hh
  have hZ2G : X.Z 2 ≤ X.Gi 5 ⊓ X.Gi 6 := by
    have hZ0 : X.Z 0 ≤ X.Gi 3 ⊓ X.Gi 4 :=
      le_inf (X.Z_zero_fixes_three h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT)
        ((X.Z_zero_le_Gi_four h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg).trans
          inf_le_left)
    have h3 : X.Gi 5 = conjSub X.τ (X.Gi 3) := by
      have hh := X.Gi_add 1 3
      rw [show (3 : ℤ) + 2 * 1 = 5 by norm_num, zpow_one] at hh
      exact hh
    have h4 : X.Gi 6 = conjSub X.τ (X.Gi 4) := by
      have hh := X.Gi_add 1 4
      rw [show (4 : ℤ) + 2 * 1 = 6 by norm_num, zpow_one] at hh
      exact hh
    rw [hZ2eq]
    calc conjSub X.τ (X.Z 0) ≤ conjSub X.τ (X.Gi 3 ⊓ X.Gi 4) := conjSub_mono X.τ hZ0
      _ = X.Gi 5 ⊓ X.Gi 6 := by rw [conjSub_inf, h3, h4]
  have hZ2Q6 : X.Z 2 ⊓ X.Q 6 = ⊥ := by
    rw [hZ2eq, hQ6eq, ← conjSub_inf,
      X.Z_zero_inf_Q_four h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg, conjSub_bot]
  exact fun k hk hk1 =>
    fixedPointFree_of_le_Gi_inf X hn6
      ((pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)) hZ2G hZ2Q6 hk hk1

private theorem Ki_six_inf_centralizer_Z_two_eq_bot (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Ki 6 ⊓ (X.K ⊓ Subgroup.centralizer (X.Z 2 : Set G)) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro z hz
  obtain ⟨hz6, hzC⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨-, hzcent⟩ := Subgroup.mem_inf.mp hzC
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z_two_ne_bot X h hreg)
  have hw : (w : G) ∈ X.Z 2 := w.2
  have hcomm : (w : G) * z = z * (w : G) :=
    (Subgroup.mem_centralizer_iff.mp hzcent) (w : G) hw
  have hfix : z * (w : G) * z⁻¹ = (w : G) := by
    calc z * (w : G) * z⁻¹ = (w : G) * z * z⁻¹ := by rw [hcomm]
      _ = (w : G) := by group
  exact hw1 (Subtype.ext
    (Ki_six_fixedPointFree_Z_two X h hreg z hz6 hz1 (w : G) hw hfix))

private theorem K_inf_centralizer_Z_two_eq (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.K ⊓ Subgroup.centralizer (X.Z 2 : Set G) = conjSub X.τ (X.Ki 0) := by
  set C : Subgroup G := X.K ⊓ Subgroup.centralizer (X.Z 2 : Set G) with hCdef
  have hC_le_K : C ≤ X.K := inf_le_left
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  haveI : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion hC_le_K) (Subgroup.inclusion_injective hC_le_K)
  have hK2_le_C : conjSub X.τ (X.Ki 0) ≤ C :=
    le_inf X.conjSub_tau_Ki_zero_le_K ((Ki_two_le_centralizer X h).trans inf_le_left)
  have hCinf : C ⊓ X.Ki 6 = ⊥ := by
    rw [inf_comm]
    exact Ki_six_inf_centralizer_Z_two_eq_bot X h hreg
  have hcard :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf C
      (X.Ki 6) (fun b hb n hn => (Subgroup.mem_normalizer_iff.mp
        (X.K_le_normalizer_Ki 6 (Subgroup.mem_inf.mp hb).1) n).mp hn)
  rw [hCinf, Subgroup.card_bot, mul_one] at hcard
  have hle : Nat.card ↥C * Nat.card ↥(X.Ki 6) ≤ Nat.card ↥X.K := by
    rw [← hcard]
    exact Subgroup.card_le_of_le (sup_le hC_le_K inf_le_left)
  have hn6 : X.n 6 = X.n 0 := by
    have hh := X.n_add 3 0
    rw [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at hh
    exact hh
  have hK6card : Nat.card ↥(X.Ki 6) = 2 ^ X.n 0 - 1 := by
    rw [X.card_Ki 6, hn6]
  have hq : 0 < 2 ^ X.n 0 - 1 := by
    have h2 : 4 ≤ 2 ^ X.n 0 :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) h.hn0
    omega
  rw [hK6card, X.card_K_eq_sq h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT, pow_two] at hle
  have hCle : Nat.card ↥C ≤ 2 ^ X.n 0 - 1 := Nat.le_of_mul_le_mul_right hle hq
  have hK2card : Nat.card ↥(conjSub X.τ (X.Ki 0)) = 2 ^ X.n 0 - 1 := by
    rw [card_conjSub, X.card_Ki 0]
  exact (Subgroup.eq_of_le_of_card_ge hK2_le_C (by rw [hK2card]; exact hCle)).symm

theorem commutator_Ki_four_normGi_le (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.Ki 4, X.normGi X.QT 0⁆ ≤ X.E X.QT 0 := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hU : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hKM : X.K ≤ X.normGi X.QT 0 := le_inf X.K_le_normalizer_QT (X.K_le_Gi 0)
  have hKn : X.K ≤ Subgroup.normalizer (X.Lst X.QT 0 : Set G) :=
    hKM.trans (le_normalizer_oTwoPrime (X.normGi X.QT 0))
  rw [X.normGi_eq_Lst_sup_K hU (Or.inr hn0)]
  refine Subgroup.commutator_le.mpr ?_
  intro k hk x hx
  obtain ⟨l, hl, c, hcK, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKn).mp hx
  have hkK : k ∈ X.K := hk.1
  have hcomm : c * k = k * c := X.mul_comm_of_mem_K hc hn0 hs hodd h5 hX hGT hcK hkK
  have hck : c * k⁻¹ * c⁻¹ = k⁻¹ := by
    calc c * k⁻¹ * c⁻¹ = (c * k * c⁻¹)⁻¹ := by group
      _ = (k * c * c⁻¹)⁻¹ := by rw [hcomm]
      _ = k⁻¹ := by group
  have hstep : ⁅k, l * c⁆ = k * l * k⁻¹ * l⁻¹ := by
    rw [commutatorElement_def]
    rw [show k * (l * c) * k⁻¹ * (l * c)⁻¹ = k * l * (c * k⁻¹ * c⁻¹) * l⁻¹ from by
      group]
    rw [hck]
  have hmemLst : k * l * k⁻¹ * l⁻¹ ∈ X.Lst X.QT 0 := by
    have hkn : k ∈ Subgroup.normalizer (X.Lst X.QT 0 : Set G) := hKn hkK
    have hconj : k * l * k⁻¹ ∈ X.Lst X.QT 0 :=
      (Subgroup.mem_normalizer_iff.mp hkn l).mp hl
    exact (X.Lst X.QT 0).mul_mem hconj ((X.Lst X.QT 0).inv_mem hl)
  have hkG0 : k ∈ X.Gi 0 := X.K_le_Gi 0 hkK
  have hlG0 : l ∈ X.Gi 0 :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0) hl
  have hker0 : k ∈ kernelOnNeighbors Γ G (X.vert 0) :=
    mem_kernelOnNeighbors.mpr ⟨hkG0, Ki_four_fixes_neighbors X h hreg hk⟩
  have hconjker : l * k⁻¹ * l⁻¹ ∈ kernelOnNeighbors Γ G (X.vert 0) :=
    (Subgroup.mem_normalizer_iff.mp (X.kernelOnNeighbors_le_normalizer 0 hlG0) k⁻¹).mp
      (Subgroup.inv_mem _ hker0)
  have hkerG : k * l * k⁻¹ * l⁻¹ ∈ kernelOnNeighbors Γ G (X.vert 0) := by
    have hprod := (kernelOnNeighbors Γ G (X.vert 0)).mul_mem hker0 hconjker
    simpa only [mul_assoc] using hprod
  have hE : k * l * k⁻¹ * l⁻¹ ∈ X.E X.QT 0 := by
    rw [← X.Lst_inf_kernel (U := X.QT)]
    exact Subgroup.mem_inf.mpr ⟨hmemLst, hkerG⟩
  rw [hstep]
  exact hE

private theorem conjSub_Vt_le (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {g : G}
    (hg : g ∈ X.normGi X.QT 0) : conjSub g X.Vt ≤ X.Vt := by
  have hU : X.IsSK X.QT := X.isSK_QT h.hGT h.hs h.hodd h.h5 h.hX
  have hM0 : X.normGi X.QT 0 = X.Lst X.QT 0 ⊔ X.K :=
    X.normGi_eq_Lst_sup_K hU (Or.inr h.hn0)
  have hKM : X.K ≤ X.normGi X.QT 0 := le_inf X.K_le_normalizer_QT (X.K_le_Gi 0)
  have hKn : X.K ≤ Subgroup.normalizer (X.Lst X.QT 0 : Set G) :=
    hKM.trans (le_normalizer_oTwoPrime (X.normGi X.QT 0))
  have hEN := X.normGi_le_normalizer_E X.QT 0
  have hK4M : X.Ki 4 ≤ X.normGi X.QT 0 := (inf_le_left : X.Ki 4 ≤ X.K).trans hKM
  have hK4N : X.Ki 4 ≤ Subgroup.normalizer (X.E X.QT 0 : Set G) := hK4M.trans hEN
  have hVtE : X.Vt ≤ X.E X.QT 0 := by
    unfold Setup.Vt
    exact (Subgroup.commutator_mono_right hK4M).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hEN)
  have hEconj : conjSub g (X.E X.QT 0) = X.E X.QT 0 :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer (hEN hg)
  have hcomm : ⁅X.E X.QT 0, X.E X.QT 0 ⊔ X.Ki 4⁆ ≤ X.Vt := by
    refine Subgroup.commutator_le.mpr ?_
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hK4N).mp hy
    have hxa : x * a = a * x := E_QT_comm X h x hx a ha
    have hxb : ⁅x, b⁆ ∈ X.Vt := Subgroup.commutator_mem_commutator hx hb
    have hxbE : ⁅x, b⁆ ∈ X.E X.QT 0 := hVtE hxb
    have hstep : ⁅x, a * b⁆ = a * ⁅x, b⁆ * a⁻¹ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      have h1 : ⁅x, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hxa
      rw [h1]
      group
    rw [hstep]
    have hconj : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
      have hh := E_QT_comm X h a ha ⁅x, b⁆ hxbE
      rw [hh]
      group
    rw [hconj]
    exact hxb
  have hconjK4 : conjSub g (X.Ki 4) ≤ X.E X.QT 0 ⊔ X.Ki 4 := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hg' : g ∈ X.Lst X.QT 0 ⊔ X.K := by
      rwa [← hM0]
    obtain ⟨l, hl, c, hc, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKn).mp hg'
    have hck : c * k * c⁻¹ ∈ X.Ki 4 := by
      have hmem : c ∈ Subgroup.normalizer (X.Ki 4 : Set G) := X.K_le_normalizer_Ki 4 hc
      have hh := mul_mem_conjSub (g := c) hk
      rwa [CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer hmem] at hh
    have hlM : l ∈ X.normGi X.QT 0 := oTwoPrime_le (X.normGi X.QT 0) hl
    have hcommE : ⁅(c * k * c⁻¹)⁻¹, l⁆ ∈ X.E X.QT 0 :=
      Subgroup.commutator_le.mp
        (commutator_Ki_four_normGi_le X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg)
        _ (Subgroup.inv_mem _ hck) l hlM
    have hstep : l * c * k * (l * c)⁻¹ =
        (c * k * c⁻¹) * ⁅(c * k * c⁻¹)⁻¹, l⁆ := by
      rw [commutatorElement_def]
      group
    change l * c * k * (l * c)⁻¹ ∈ X.E X.QT 0 ⊔ X.Ki 4
    rw [hstep]
    have hmemsup : (c * k * c⁻¹) * ⁅(c * k * c⁻¹)⁻¹, l⁆ ∈ X.Ki 4 ⊔ X.E X.QT 0 :=
      Subgroup.mul_mem_sup hck hcommE
    rwa [sup_comm (X.Ki 4) (X.E X.QT 0)] at hmemsup
  have hconjVt : conjSub g X.Vt = ⁅conjSub g (X.E X.QT 0), conjSub g (X.Ki 4)⁆ :=
    (conjSub_commutator g (X.E X.QT 0) (X.Ki 4)).symm
  rw [hconjVt, hEconj]
  exact (Subgroup.commutator_mono_right hconjK4).trans hcomm

theorem normGi_le_normalizer_Vt (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.normGi X.QT 0 ≤ Subgroup.normalizer (X.Vt : Set G) := by
  · have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (conjSub_Vt_le X h hreg hg) ?_
    have h1 : conjSub g⁻¹ X.Vt ≤ X.Vt :=
      conjSub_Vt_le X h hreg (Subgroup.inv_mem (X.normGi X.QT 0) hg)
    have h2 : conjSub g (conjSub g⁻¹ X.Vt) ≤ conjSub g X.Vt := conjSub_mono g h1
    rwa [show conjSub g (conjSub g⁻¹ X.Vt) = X.Vt from by
      simpa using conjSub_conjSub_inv g⁻¹ X.Vt] at h2

theorem Vt_le_Z_one_sup_Z_neg_one (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Vt ≤ X.Z 1 ⊔ X.Z (-1) := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hK4Z (i : ℤ) : ⁅X.Z i, X.Ki 4⁆ ≤ X.Z i :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp fun k hk =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal i k (X.K_le_Gi i hk.1))
  have hZE : X.Z 1 ⊔ X.Z (-1) ≤ X.E X.QT 0 :=
    sup_le (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX) (Z_neg_one_le_E_QT X h hreg)
  have hQN : X.QT ≤ Subgroup.normalizer ((X.Z 1 ⊔ X.Z (-1) : Subgroup G) : Set G) :=
    fun q hq => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun y hy => E_QT_comm X h y (hZE hy) q (X.QT_le_E hq))
  unfold Setup.Vt
  rw [X.E_eq_Z_one_sup_Z_neg_one_sup_QT h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg]
  exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
    (CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
      ((hK4Z 1).trans le_sup_left) ((hK4Z (-1)).trans le_sup_right)
      (le_sup_left.trans Subgroup.le_normalizer) (le_sup_right.trans Subgroup.le_normalizer))
    ((commutator_QT_Ki_four_eq_bot X h hreg).le.trans bot_le) Subgroup.le_normalizer hQN

private theorem Ki_four_fixedPointFree_Z_zero (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk4 : k ∈ X.Ki 4) (hk1 : k ≠ 1) :
    ∀ z ∈ X.Z 0, k * z * k⁻¹ = z → z = 1 := by
  have hn4 : 2 ≤ X.n 4 := by
    have hh := X.n_add 2 0
    rw [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at hh
    rw [hh]
    exact h.hn0
  have hZ0G : X.Z 0 ≤ X.Gi 3 ⊓ X.Gi 4 :=
    le_inf (X.Z_zero_fixes_three h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT)
      ((X.Z_zero_le_Gi_four h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg).trans
        inf_le_left)
  have hZ0Q4 : X.Z 0 ⊓ X.Q 4 = ⊥ :=
    X.Z_zero_inf_Q_four h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg
  exact fixedPointFree_of_le_Gi_inf X hn4
    ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)) hZ0G hZ0Q4 hk4 hk1

private theorem Ki_four_fixedPointFree_Z_two (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk4 : k ∈ X.Ki 4) (hk1 : k ≠ 1) :
    ∀ z ∈ X.Z 2, k * z * k⁻¹ = z → z = 1 := by
  have hKcomm : ∀ a ∈ X.K, ∀ b ∈ X.K, a * b = b * a :=
    fun a ha b hb => X.mul_comm_of_mem_K h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT ha hb
  have hfp6 := Ki_six_fixedPointFree_Z_two X h hreg
  have hCeq : X.K ⊓ Subgroup.centralizer (X.Z 2 : Set G) = conjSub X.τ (X.Ki 0) :=
    K_inf_centralizer_Z_two_eq X h hreg
  have hK4infK2 : X.Ki 4 ⊓ X.Ki 2 = ⊥ := Ki_four_inf_Ki_two X h hreg
  have hK2_le_C : X.Ki 2 ≤ X.K ⊓ Subgroup.centralizer (X.Z 2 : Set G) := by
    have h := hCeq.ge
    rwa [← Ki_two_eq_conjSub X] at h
  have hK2infK6 : X.Ki 2 ⊓ X.Ki 6 = ⊥ := by
    refine le_bot_iff.mp ?_
    calc X.Ki 2 ⊓ X.Ki 6 ≤ (X.K ⊓ Subgroup.centralizer (X.Z 2 : Set G)) ⊓ X.Ki 6 :=
          inf_le_inf_right _ hK2_le_C
      _ = ⊥ := by
          rw [inf_comm]
          exact Ki_six_inf_centralizer_Z_two_eq_bot X h hreg
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  have hK2supK6 : X.Ki 2 ⊔ X.Ki 6 = X.K := by
    have hn2 : X.n 2 = X.n 0 := by
      have hh := X.n_add 1 0
      rw [show (0 : ℤ) + 2 * 1 = 2 by norm_num] at hh
      exact hh
    have hn6 : X.n 6 = X.n 0 := by
      have hh := X.n_add 3 0
      rw [show (0 : ℤ) + 2 * 3 = 6 by norm_num] at hh
      exact hh
    have hcard : Nat.card ↥(X.Ki 2 ⊔ X.Ki 6) = Nat.card ↥X.K := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (X.Ki 2)
          (X.Ki 6) (inf_le_left.trans (X.K_le_normalizer_Ki 2))
          (disjoint_iff.mpr hK2infK6),
        X.card_Ki 2, X.card_Ki 6, hn2, hn6,
        X.card_K_eq_sq h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT, pow_two]
    exact Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (le_of_eq hcard.symm)
  intro z hz hfixz
  have hkK : k ∈ X.Ki 2 ⊔ X.Ki 6 := by rw [hK2supK6]; exact hk4.1
  obtain ⟨k2, hk2, k6, hk6, hk_eq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (inf_le_left.trans (X.K_le_normalizer_Ki 2))).mp hkK
  have hk2cent : k2 ∈ Subgroup.centralizer (X.Z 2 : Set G) :=
    (Subgroup.mem_inf.mp (hK2_le_C hk2)).2
  have hk2z : k2 * z = z * k2 := ((Subgroup.mem_centralizer_iff.mp hk2cent) z hz).symm
  have hk2k6 : k2 * k6 = k6 * k2 := hKcomm k2 hk2.1 k6 hk6.1
  have hk6ne : k6 ≠ 1 := by
    intro h1
    have hkK2 : k ∈ X.Ki 2 := by rw [hk_eq, h1, mul_one]; exact hk2
    have hmem : k ∈ X.Ki 4 ⊓ X.Ki 2 := Subgroup.mem_inf.mpr ⟨hk4, hkK2⟩
    rw [hK4infK2] at hmem
    exact hk1 (Subgroup.mem_bot.mp hmem)
  have hcomm2 : Commute k2 (k6 * z * k6⁻¹) :=
    ((show Commute k2 k6 from hk2k6).mul_right (show Commute k2 z from hk2z)).mul_right
      (show Commute k2 k6 from hk2k6).inv_right
  have hkey : k * z * k⁻¹ = k6 * z * k6⁻¹ := by
    calc k * z * k⁻¹ = k2 * k6 * z * (k2 * k6)⁻¹ := by rw [hk_eq]
      _ = k2 * (k6 * z * k6⁻¹) * k2⁻¹ := by group
      _ = (k6 * z * k6⁻¹) * k2 * k2⁻¹ := by rw [hcomm2.eq]
      _ = k6 * z * k6⁻¹ := by group
  exact hfp6 k6 hk6 hk6ne z hz (by rw [← hkey]; exact hfixz)

private theorem Ki_four_fixedPointFree_Z_one (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk4 : k ∈ X.Ki 4) (hk1 : k ≠ 1) :
    ∀ z ∈ X.Z 1, k * z * k⁻¹ = z → z = 1 := by
  have hZ1eq : X.Z 1 = X.Z 0 ⊔ X.Z 2 :=
    X.Z_one_eq_Z_zero_sup_Z_two h.hc (Or.inl h.hn0) h.hs h.hodd
      h.h5 h.hX h.hGT hreg
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := Z_two_le_Z_one X h hreg
  have hZ2E : X.Z 2 ≤ X.E X.QT 0 := hZ2Z1.trans (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX)
  have hZ0Z2N : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer (X.Z 0 : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact E_QT_comm X h a (X.Z_zero_le_E ha) b (hZ2E hb)
  have hfp0 := Ki_four_fixedPointFree_Z_zero X h hreg hk4 hk1
  have hfp2 := Ki_four_fixedPointFree_Z_two X h hreg hk4 hk1
  intro r hr hfix
  have hr' : r ∈ X.Z 0 ⊔ X.Z 2 := by
    rw [← hZ1eq]
    exact hr
  obtain ⟨r0, hr0, r2, hr2, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hZ0Z2N).mp hr'
  have hk0 : k * r0 * k⁻¹ ∈ X.Z 0 := by
    have hh := mul_mem_conjSub (g := k) hr0
    rwa [X.Z_normal 0 k (X.K_le_Gi 0 hk4.1)] at hh
  have hk2 : k * r2 * k⁻¹ ∈ X.Z 2 := by
    have hh := mul_mem_conjSub (g := k) hr2
    rwa [X.Z_normal 2 k (X.K_le_Gi 2 hk4.1)] at hh
  have hprod : (k * r0 * k⁻¹) * (k * r2 * k⁻¹) = r0 * r2 := by
    calc (k * r0 * k⁻¹) * (k * r2 * k⁻¹) = k * (r0 * r2) * k⁻¹ := by group
      _ = r0 * r2 := hfix
  have hmem2 : (k * r0 * k⁻¹)⁻¹ * r0 ∈ X.Z 2 := by
    have heq : (k * r0 * k⁻¹)⁻¹ * r0 = (k * r2 * k⁻¹) * r2⁻¹ := by
      calc (k * r0 * k⁻¹)⁻¹ * r0
          = (k * r0 * k⁻¹)⁻¹ * (r0 * r2) * r2⁻¹ := by group
        _ = (k * r0 * k⁻¹)⁻¹ * ((k * r0 * k⁻¹) * (k * r2 * k⁻¹)) * r2⁻¹ := by
            rw [hprod]
        _ = (k * r2 * k⁻¹) * r2⁻¹ := by group
    rw [heq]
    exact (X.Z 2).mul_mem hk2 ((X.Z 2).inv_mem hr2)
  have hmem0 : (k * r0 * k⁻¹)⁻¹ * r0 ∈ X.Z 0 :=
    (X.Z 0).mul_mem ((X.Z 0).inv_mem hk0) hr0
  have hbot : (k * r0 * k⁻¹)⁻¹ * r0 ∈ (⊥ : Subgroup G) := by
    rw [← X.Z_zero_inf_Z_two h.hc (Or.inl h.hn0) h.hs h.hodd
      h.h5 h.hX h.hGT hreg]
    exact Subgroup.mem_inf.mpr ⟨hmem0, hmem2⟩
  have ha : k * r0 * k⁻¹ = r0 := by
    have h1 : (k * r0 * k⁻¹)⁻¹ * r0 = 1 := Subgroup.mem_bot.mp hbot
    exact inv_mul_eq_one.mp h1
  have hb : k * r2 * k⁻¹ = r2 := by
    have hp : r0 * (k * r2 * k⁻¹) = r0 * r2 := by
      rw [← hprod, ha]
    exact mul_left_cancel hp
  rw [hfp0 r0 hr0 ha, hfp2 r2 hr2 hb]
  group

theorem Z_one_le_Vt (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ≤ X.Vt := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hn4 : X.n 4 = X.n 0 := by
    have hh := X.n_add 2 0
    rw [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at hh
    exact hh
  have hK4card : Nat.card ↥(X.Ki 4) = 2 ^ X.n 0 - 1 := by
    rw [X.card_Ki 4, hn4]
  have hK4ne : X.Ki 4 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hK4card
    have h4 : 4 ≤ 2 ^ X.n 0 :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) h.hn0
    omega
  obtain ⟨k, hk41⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK4ne
  have hk4 : (k : G) ∈ X.Ki 4 := k.2
  have hk1 : (k : G) ≠ 1 := fun hh => hk41 (Subtype.ext hh)
  have hfp := Ki_four_fixedPointFree_Z_one X h hreg hk4 hk1
  haveI hZ1fin : Finite ↥(X.Z 1) := by
    have hZ1G1 : X.Z 1 ≤ X.Gi 1 := X.Z_le_Gi 1
    haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
    exact Finite.of_injective (Subgroup.inclusion hZ1G1) (Subgroup.inclusion_injective hZ1G1)
  have hZn : X.Z 1 ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hkU : (k : G) ∈ Subgroup.normalizer (X.Z 1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 (k : G) (X.K_le_Gi 1 hk4.1)
  have hkR : (k : G) ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hfree : ∀ r ∈ X.Z 1, ⁅(k : G), r⁆ ∈ (⊥ : Subgroup G) → r ∈ (⊥ : Subgroup G) := by
    intro r hr hbot
    have h1 : ⁅(k : G), r⁆ = 1 := Subgroup.mem_bot.mp hbot
    rw [commutatorElement_def] at h1
    have hfix : (k : G) * r * (k : G)⁻¹ = r := by
      calc (k : G) * r * (k : G)⁻¹ = (k : G) * r * (k : G)⁻¹ * r⁻¹ * r := by group
        _ = 1 * r := by rw [h1]
        _ = r := by group
    exact Subgroup.mem_bot.mpr (hfp r hr hfix)
  have hex := exists_commutator_mul_of_fixedPointFree (U := X.Z 1) (R := ⊥) (k := (k : G))
    bot_le hZn hkU hkR hfree
  intro z hz
  obtain ⟨v, hv, w, hw, hzw⟩ := hex z hz
  have hw1 : w = 1 := Subgroup.mem_bot.mp hw
  have hcommem : ⁅v, (k : G)⁆ ∈ X.Vt :=
    Subgroup.commutator_mem_commutator (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX hv) hk4
  rw [hzw, hw1, mul_one]
  have hinv : ⁅v, (k : G)⁆⁻¹ ∈ X.Vt := (X.Vt).inv_mem hcommem
  simpa only [commutatorElement_inv] using hinv

private theorem V0_le_Vt (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V0 ≤ X.Vt := by
  have hZ1 : X.Z 1 ≤ X.Vt :=
    Z_one_le_Vt X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hnorm : X.normGi X.QT 0 ≤ Subgroup.normalizer (X.Vt : Set G) :=
    normGi_le_normalizer_Vt X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  refine iSup_le fun g => iSup_le fun hg => ?_
  have hgM : g ∈ X.normGi X.QT 0 := oTwoPrime_le _ hg
  have hconj : conjSub g X.Vt = X.Vt :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer (hnorm hgM)
  calc conjSub g (X.Z 1) ≤ conjSub g X.Vt := conjSub_mono g hZ1
    _ = X.Vt := hconj

theorem V0_eq_Z_one_sup_Z_neg_one (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.V0 = X.Z 1 ⊔ X.Z (-1) := by
  · have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
    have hV0Vt : X.V0 ≤ X.Vt := V0_le_Vt X h hreg
    have hVtZ : X.Vt ≤ X.Z 1 ⊔ X.Z (-1) :=
      Vt_le_Z_one_sup_Z_neg_one X hc hn0 hs hodd h5 hX hGT hreg
    have hV0Z : X.V0 ≤ X.Z 1 ⊔ X.Z (-1) := hV0Vt.trans hVtZ
    have hZV0 : X.Z 1 ⊔ X.Z (-1) ≤ X.V0 := by
      refine sup_le ?_ ?_
      · refine le_iSup₂_of_le (1 : G) (by simp) ?_
        rw [conjSub_one]
      · obtain ⟨y, hy, hy1⟩ := exists_mem_Lst_smul_vert_one_eq_vert_neg_one X h
        refine le_iSup₂_of_le y hy ?_
        rw [X.Z_conj hy1]
    exact le_antisymm hV0Z hZV0

theorem V2_eq_Z_one_sup_Z_three (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.V2 = X.Z 1 ⊔ X.Z 3 := by
  have h0 := V0_eq_Z_one_sup_Z_neg_one X hc hn0 hs hodd h5 hX hGT hreg
  unfold Setup.V2
  rw [h0, conjSub_sup]
  have h3 : conjSub X.τ (X.Z 1) = X.Z 3 := by
    have hh := X.Z_add 1 1
    rw [show (1 : ℤ) + 2 * 1 = 3 by norm_num] at hh
    simpa using hh.symm
  have h1 : conjSub X.τ (X.Z (-1)) = X.Z 1 := by
    have hh := X.Z_add 1 (-1)
    rw [show (-1 : ℤ) + 2 * 1 = 1 by norm_num] at hh
    simpa using hh.symm
  rw [h3, h1, sup_comm]

private theorem V0_le_E (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V0 ≤ X.E X.QT 0 := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  have hgM : g ∈ X.normGi X.QT 0 := oTwoPrime_le (X.normGi X.QT 0) hg
  have hEg : conjSub g (X.E X.QT 0) = X.E X.QT 0 :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer (X.normGi_le_normalizer_E X.QT 0 hgM)
  calc conjSub g (X.Z 1) ≤ conjSub g (X.E X.QT 0) := conjSub_mono g (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX)
    _ = X.E X.QT 0 := hEg

private theorem V2_le_Etau (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V2 ≤ conjSub X.τ (X.E X.QT 0) := by
  unfold Setup.V2
  exact conjSub_mono X.τ (V0_le_E X h hreg)

private theorem conjSub_comm {H : Subgroup G} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (g : G) : ∀ x ∈ conjSub g H, ∀ y ∈ conjSub g H, x * y = y * x := by
  intro x hx y hy
  obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
  exact (Commute.conj (hH x0 hx0 y0 hy0 : Commute x0 y0) g).eq

private theorem V2_comm (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ x ∈ X.V2, ∀ y ∈ X.V2, x * y = y * x := by
  intro x hx y hy
  have hE := V2_le_Etau X h hreg
  exact conjSub_comm (E_QT_comm X h) X.τ x (hE hx) y (hE hy)

theorem V2_inf_Q_zero (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V2 ⊓ X.Q 0 = X.Z 1 := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  · have hZ3eq := X.Z_three_eq_Z_two_sup_Z_four
          h.hc (Or.inl h.hn0) h.hs h.hodd h.h5
      h.hX h.hGT hreg
    have hZ2Z1 : X.Z 2 ≤ X.Z 1 := Z_two_le_Z_one X h hreg
    have hV2eq : X.V2 = X.Z 1 ⊔ X.Z 4 := by
      rw [V2_eq_Z_one_sup_Z_three X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg, hZ3eq,
        ← sup_assoc, sup_eq_left.mpr hZ2Z1]
    have hZ1V2 : X.Z 1 ≤ X.V2 := le_sup_left.trans hV2eq.ge
    have hZ4V2 : X.Z 4 ≤ X.V2 := le_sup_right.trans hV2eq.ge
    have hcomm := V2_comm X h hreg
    have hnorm : X.Z 4 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
      intro a ha
      refine Subgroup.centralizer_le_normalizer (X.Z 1 : Set G) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm a (hZ4V2 ha) b (hZ1V2 hb)).symm
    have hZ1Q0 : X.Z 1 ≤ X.Q 0 := (X.Z_one_le_E
      h.hGT h.hs h.hodd h.h5 h.hX).trans inf_le_left
    have hZ4Q0 : X.Z 4 ⊓ X.Q 0 = ⊥ :=
      X.Z_four_inf_Q_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg
    rw [hV2eq, sup_comm (X.Z 1) (X.Z 4), inf_comm (X.Z 4 ⊔ X.Z 1) (X.Q 0),
      ← Subgroup.inf_sup_assoc_of_le (H := X.Z 4) (K := X.Q 0) (N := X.Z 1) hnorm hZ1Q0,
      inf_comm (X.Q 0) (X.Z 4), hZ4Q0, bot_sup_eq]

theorem V0_inf_QT (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V0 ⊓ X.QT = ⊥ := by
  have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  have hV2Q0 := V2_inf_Q_zero X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hZ1QT : X.Z 1 ⊓ X.QT = ⊥ := by
    rw [inf_comm]
    exact X.QT_inf_Z_eq_bot h.hGT h.hs h.hodd h.h5 h.hX 1
  have hτQT : conjSub X.τ X.QT = X.QT := by
    ext x
    rw [mem_conjSub]
    exact (Subgroup.mem_normalizer_iff''.mp X.tau_mem_normalizer_QT x).symm
  suffices h : conjSub X.τ (X.V0 ⊓ X.QT) = ⊥ by
    have h2 := congrArg (conjSub X.τ⁻¹) h
    rwa [conjSub_conjSub_inv, conjSub_bot] at h2
  rw [conjSub_inf, hτQT, show conjSub X.τ X.V0 = X.V2 from rfl]
  have hQTQ0 : X.QT ≤ X.Q 0 := X.QT_le_Q 0
  have h1 : (X.V2 ⊓ X.Q 0) ⊓ X.QT = X.V2 ⊓ X.QT := by
    rw [inf_assoc, inf_eq_right.mpr hQTQ0]
  rw [← h1, hV2Q0, hZ1QT]

theorem E_eq_V0_sup_QT (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.E X.QT 0 = X.V0 ⊔ X.QT := by
  rw [E_eq_Z_one_sup_Z_neg_one_sup_QT X hc hn0 hs hodd h5 hX hGT hreg,
    V0_eq_Z_one_sup_Z_neg_one X hc hn0 hs hodd h5 hX hGT hreg]

theorem V0_inf_V2_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V0 ⊓ X.V2 ≤ X.Z 1 := by
  have h16 := V2_inf_Q_zero X hc hn0 hs hodd h5 hX hGT hreg
  have hV0Q0 : X.V0 ≤ X.Q 0 := by
    rw [V0_eq_Z_one_sup_Z_neg_one X hc hn0 hs hodd h5 hX hGT hreg]
    refine sup_le ?_ ?_
    · exact (X.Z_one_le_E hGT hs hodd h5 hX).trans inf_le_left
    · exact (Z_neg_one_le_E_QT X ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩ hreg).trans inf_le_left
  calc X.V0 ⊓ X.V2 ≤ X.Q 0 ⊓ X.V2 := inf_le_inf_right _ hV0Q0
    _ = X.V2 ⊓ X.Q 0 := inf_comm (X.Q 0) X.V2
    _ = X.Z 1 := h16

theorem commutator_E_normGi_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.E X.QT 0, X.normGi X.QT 0⁆ ≤ X.V0 := by
  · have h : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
    have hV0Vt : X.V0 = X.Vt := by
      refine le_antisymm (V0_le_Vt X h hreg) ?_
      rw [V0_eq_Z_one_sup_Z_neg_one X hc hn0 hs hodd h5 hX hGT hreg]
      exact Vt_le_Z_one_sup_Z_neg_one X hc hn0 hs hodd h5 hX hGT hreg
    have hM0norm : X.normGi X.QT 0 ≤ Subgroup.normalizer (X.V0 : Set G) := by
      rw [hV0Vt]
      exact normGi_le_normalizer_Vt X hc hn0 hs hodd h5 hX hGT hreg
    have hV0M : ⁅X.V0, X.normGi X.QT 0⁆ ≤ X.V0 :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hM0norm
    have hU : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
    have hM0 : X.normGi X.QT 0 = X.Lst X.QT 0 ⊔ X.K :=
      X.normGi_eq_Lst_sup_K hU (Or.inr hn0)
    have hKM : X.K ≤ X.normGi X.QT 0 := le_inf X.K_le_normalizer_QT (X.K_le_Gi 0)
    have hKn : X.K ≤ Subgroup.normalizer (X.Lst X.QT 0 : Set G) :=
      hKM.trans (le_normalizer_oTwoPrime (X.normGi X.QT 0))
    have hQTM : ⁅X.QT, X.normGi X.QT 0⁆ = ⊥ := by
      rw [hM0, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨l, hl, c, hcK, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKn).mp hx
      have hlq : l * q = q * l := by
        have hbot : ⁅q, l⁆ = 1 := by
          have hmem := Subgroup.commutator_le.mp
            (le_of_eq (X.commutator_QT_Lst_eq_bot hGT hs hodd h5 hX))
            q hq l hl
          exact Subgroup.mem_bot.mp hmem
        exact (commutatorElement_eq_one_iff_mul_comm.mp hbot).symm
      have hcq : c * q = q * c := by
        have hqC : q ∈ X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) := by
          rw [← QT_eq_inf_centralizer_K X h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg]
          exact hq
        exact (Subgroup.mem_centralizer_iff.mp hqC.2) c hcK
      calc (l * c) * q = l * (c * q) := by group
        _ = l * (q * c) := by rw [hcq]
        _ = (l * q) * c := by group
        _ = (q * l) * c := by rw [hlq]
        _ = q * (l * c) := by group
    have hQTN : X.QT ≤ Subgroup.normalizer (X.V0 : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (X.V0 : Set G))
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact E_QT_comm X h v (V0_le_E X h hreg hv) q (X.QT_le_E hq)
    have hE : X.E X.QT 0 = X.V0 ⊔ X.QT :=
      E_eq_V0_sup_QT X hc hn0 hs hodd h5 hX hGT hreg
    rw [hE]
    refine Subgroup.commutator_le.mpr ?_
    intro e he x hx
    obtain ⟨v, hv, q, hq, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQTN).mp he
    have hq1 : ⁅q, x⁆ = 1 := by
      have hbot := Subgroup.commutator_le.mp (le_of_eq hQTM) q hq x hx
      exact Subgroup.mem_bot.mp hbot
    have hvm : ⁅v, x⁆ ∈ X.V0 := Subgroup.commutator_le.mp hV0M v hv x hx
    rw [commutatorElement_mul_left_eq_conj_mul, hq1]
    have hsimp : v * 1 * v⁻¹ * ⁅v, x⁆ = ⁅v, x⁆ := by group
    rw [hsimp]
    exact hvm

end Setup

end CFSG.Quasithin.St84
