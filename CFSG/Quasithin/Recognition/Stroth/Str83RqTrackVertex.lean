module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.BenderSylow
import CFSG.Quasithin.Background.I4Basic
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

abbrev Lv (i : ℤ) : Subgroup G := qv (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) t.x₁ t.x₂ i

theorem Lv_zero : t.Lv 0 = L1 ⊔ Q1 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Lv_one : t.Lv 1 = L2 ⊔ Q2 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Lv_le_Gv (i : ℤ) : t.Lv i ≤ t.Gv i := by
  show qv (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) t.x₁ t.x₂ i ≤
    qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ i
  refine Subgroup.map_mono ?_
  unfold trackPar
  split_ifs
  · exact sup_le le_sup_left (pCoreOf_le 2 (P1 L1 L2 S))
  · exact sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))

private theorem tv_map_conj_eq_of_mem {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have h := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at h
  exact h.symm

private theorem tv_Q1_swap : Q1 L2 L1 S = Q2 L1 L2 S := by
  simp [Q1, Q2, P1, P2, bigB_comm]

private theorem tv_Gw_even (k : ℤ) :
    t.Gw (2 * k) (2 * k + 1) = (t.Gw 0 1).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) 0 1 k
  rw [show (0 : ℤ) + 2 * k = 2 * k by simp,
    show (1 : ℤ) + 2 * k = 2 * k + 1 by rw [add_comm]] at h
  exact h.symm

private theorem tv_Gw_odd (k : ℤ) :
    t.Gw (2 * k + 1) (2 * k + 2) = (t.Gw 1 2).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) 1 2 k
  rw [show (1 : ℤ) + 2 * k = 2 * k + 1 by rw [add_comm],
    show (2 : ℤ) + 2 * k = 2 * k + 2 by rw [add_comm]] at h
  exact h.symm

private theorem tv_Gw_left_even (k : ℤ) :
    t.Gw (2 * k - 1) (2 * k) = (t.Gw (-1) 0).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) (-1) 0 k
  rw [show (-1 : ℤ) + 2 * k = 2 * k - 1 by
    rw [sub_eq_add_neg]
    exact add_comm (-1) (2 * k),
    show (0 : ℤ) + 2 * k = 2 * k by simp] at h
  exact h.symm

private theorem tv_Lv_even (k : ℤ) :
    t.Lv (2 * k) = (L1 ⊔ Q1 L1 L2 S).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := (map_qv_tau_pow (Q₁ := L1 ⊔ Q1 L1 L2 S) (Q₂ := L2 ⊔ Q2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) 0 k).symm
  simpa [t.Lv_zero, show (0 : ℤ) + 2 * k = 2 * k by simp] using h

private theorem tv_Lv_odd (k : ℤ) :
    t.Lv (2 * k + 1) = (L2 ⊔ Q2 L1 L2 S).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := (map_qv_tau_pow (Q₁ := L1 ⊔ Q1 L1 L2 S) (Q₂ := L2 ⊔ Q2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) 1 k).symm
  simpa [t.Lv_one, show (1 : ℤ) + 2 * k = 2 * k + 1 by rw [add_comm]] using h

private theorem tv_Gw_one_two :
    t.Gw 1 2 = (t.Gw 0 1).map (MulAut.conj t.x₂).toMonoidHom := by
  have h := TrackData.map_win_x₂ t.track
    (Subgroup.le_normalizer) (Subgroup.le_normalizer) (a := 0) (b := 1)
  simpa using h.symm

private theorem tv_Gw_neg_one_zero :
    t.Gw (-1) 0 = (t.Gw 0 1).map (MulAut.conj t.x₁).toMonoidHom := by
  have h := TrackData.map_win_x₁ t.track
    (Subgroup.le_normalizer) (Subgroup.le_normalizer) (a := 0) (b := 1)
  simpa using h.symm

variable [Finite G]

private theorem tv_P1_le_normalizer (hF : F112HypW L1 L2 S) :
    P1 L1 L2 S ≤ Subgroup.normalizer ((L1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
  F1.le_normalizer_sup
    (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1))
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S))

private theorem tv_P2_le_normalizer (hF : F112HypW L1 L2 S) :
    P2 L1 L2 S ≤ Subgroup.normalizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
  have hB : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have h := bigB_le_normalizer_of_hyp111 hF.1.symm
    rwa [bigB_comm] at h
  exact F1.le_normalizer_sup (sup_le Subgroup.le_normalizer hB)
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S))

private theorem tv_pCoreOf_sup_pCoreOf_right (hF : Hyp111 L1 L2 S) :
    pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) = Q2 L1 L2 S := by
  have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.symm
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

private theorem tv_Gv_even (k : ℤ) :
    t.Gv (2 * k) = (P1 L1 L2 S).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := (map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) 0 k).symm
  simpa [t.Gv_zero, show (0 : ℤ) + 2 * k = 2 * k by simp] using h

private theorem tv_Gv_odd (k : ℤ) :
    t.Gv (2 * k + 1) = (P2 L1 L2 S).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
  have h := (map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) 1 k).symm
  simpa [t.Gv_one, show (1 : ℤ) + 2 * k = 2 * k + 1 by rw [add_comm]] using h

theorem Gv_le_normalizer_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f) (i : ℤ) :
    t.Gv i ≤ normalizer (t.Lv i : Set G) := by
  show (trackPar (P1 L1 L2 S) (P2 L1 L2 S) i).map
      (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom ≤
    normalizer (((trackPar (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) i).map
      (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom : Subgroup G) : Set G)
  have hbase : trackPar (P1 L1 L2 S) (P2 L1 L2 S) i ≤
      normalizer ((trackPar (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) i : Subgroup G) : Set G) := by
    unfold trackPar
    split_ifs
    · exact tv_P1_le_normalizer hfr.hF
    · exact tv_P2_le_normalizer hfr.hF
  have hmap : (trackPar (P1 L1 L2 S) (P2 L1 L2 S) i).map
      (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom ≤
      (normalizer ((trackPar (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) i : Subgroup G) : Set G)).map
        (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom :=
    Subgroup.map_mono (f := (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom) hbase
  exact hmap.trans
    (Subgroup.le_normalizer_map (f := (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom))

theorem pCoreOf_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f) (i : ℤ) :
    pCoreOf 2 (t.Lv i) = t.Qv i := by
  have hQ : pCoreOf 2 (trackPar (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) i) =
      trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) i := by
    unfold trackPar
    split_ifs
    · exact pCoreOf_sup_pCoreOf hfr.hF.1
    · exact tv_pCoreOf_sup_pCoreOf_right hfr.hF.1
  show pCoreOf 2 ((trackPar (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) i).map
      (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom) =
    (trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) i).map
      (MulAut.conj (trackElt t.x₁ t.x₂ i)).toMonoidHom
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj (trackElt t.x₁ t.x₂ i))
    (trackPar (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) i), hQ]

private noncomputable def tv_oTwoQuotSupEquiv_right (hF : Hyp111 L1 L2 S) :
    oTwoQuot ↥(L2 ⊔ Q2 L1 L2 S) ≃* oTwoQuot ↥L2 := by
  have h := oTwoQuotSupEquiv (L1 := L2) (L2 := L1) (S := S) hF.symm
  have hsub : (L2 ⊔ Q1 L2 L1 S) = (L2 ⊔ Q2 L1 L2 S) := by rw [tv_Q1_swap]
  exact (CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv
    (MulEquiv.subgroupCongr hsub.symm)).trans h

theorem nonempty_mulEquiv_sz_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f) {i : ℤ} (hi : Even i) :
    Nonempty (oTwoQuot ↥(t.Lv i) ≃* Sz a) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · have e1 : ↥(t.Lv (2 * k)) ≃* ↥(L1 ⊔ Q1 L1 L2 S) := by
      rw [tv_Lv_even t k]
      exact (Subgroup.equivMapOfInjective (L1 ⊔ Q1 L1 L2 S)
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom (MulAut.conj _).injective).symm
    obtain ⟨e3⟩ := hfr.hSz
    exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv e1).trans
      ((oTwoQuotSupEquiv hfr.hF.1).trans e3)⟩
  · exact absurd hi (Int.not_even_two_mul_add_one k)

theorem isL2Quot_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f) {i : ℤ} (hi : Odd i) :
    IsL2Quot f (oTwoQuot ↥(t.Lv i)) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · exact absurd hi (Int.not_odd_iff_even.mpr (even_two_mul k))
  · have e1 : ↥(t.Lv (2 * k + 1)) ≃* ↥(L2 ⊔ Q2 L1 L2 S) := by
      rw [tv_Lv_odd t k]
      exact (Subgroup.equivMapOfInjective (L2 ⊔ Q2 L1 L2 S)
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom (MulAut.conj _).injective).symm
    obtain ⟨e3⟩ := hfr.hL2
    exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv e1).trans
      ((tv_oTwoQuotSupEquiv_right hfr.hF.1).trans e3)⟩

private theorem tv_isSylowTwoOf_sup_pCoreOf_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) :=
  isSylowTwoOf_sup_pCoreOf hfr.hF.1
    (eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩))

private theorem tv_isSylowTwoOf_sup_pCoreOf_right {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSylowTwoOf S (L2 ⊔ Q2 L1 L2 S) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hS2' : S = (S ⊓ L2) ⊔ Q1 L2 L1 S := by
    simpa [Q1, Q2, P1, P2, bigB_comm] using hS2
  have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hfr.hF.1.symm hS2'
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

private theorem tv_isSylowTwoOf_map_x₁ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    IsSylowTwoOf (S.map (MulAut.conj t.x₁).toMonoidHom) (L1 ⊔ Q1 L1 L2 S) := by
  have h := F7.isSylowTwoOf_conj (tv_isSylowTwoOf_sup_pCoreOf_left hfr) t.x₁
  change IsSylowTwoOf (S.map (MulAut.conj t.x₁).toMonoidHom)
    ((L1 ⊔ Q1 L1 L2 S).map (MulAut.conj t.x₁).toMonoidHom) at h
  rw [tv_map_conj_eq_of_mem
    (tv_P1_le_normalizer hfr.hF t.track.x₁_mem)] at h
  exact h

private theorem tv_isSylowTwoOf_map_x₂ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    IsSylowTwoOf (S.map (MulAut.conj t.x₂).toMonoidHom) (L2 ⊔ Q2 L1 L2 S) := by
  have h := F7.isSylowTwoOf_conj (tv_isSylowTwoOf_sup_pCoreOf_right hfr) t.x₂
  change IsSylowTwoOf (S.map (MulAut.conj t.x₂).toMonoidHom)
    ((L2 ⊔ Q2 L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom) at h
  rw [tv_map_conj_eq_of_mem
    (tv_P2_le_normalizer hfr.hF t.track.x₂_mem)] at h
  exact h

private theorem tv_pCoreOf_Gw_one_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (t.Gw 1 2) = S.map (MulAut.conj t.x₂).toMonoidHom := by
  rw [tv_Gw_one_two t, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj t.x₂) (t.Gw 0 1), t.pCoreOf_Gw_zero_one hfr]

private theorem tv_pCoreOf_Gw_neg_one_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (t.Gw (-1) 0) = S.map (MulAut.conj t.x₁).toMonoidHom := by
  rw [tv_Gw_neg_one_zero t, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj t.x₁) (t.Gw 0 1), t.pCoreOf_Gw_zero_one hfr]

private theorem tv_isSylowTwoOf_Lv_even {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (k : ℤ) :
    IsSylowTwoOf (pCoreOf 2 (t.Gw (2 * k) (2 * k + 1))) (t.Lv (2 * k)) := by
  rw [tv_Gw_even t k, tv_Lv_even t k, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj ((t.x₂ * t.x₁) ^ k)) (t.Gw 0 1), t.pCoreOf_Gw_zero_one hfr]
  have h := F7.isSylowTwoOf_conj (tv_isSylowTwoOf_sup_pCoreOf_left hfr)
    ((t.x₂ * t.x₁) ^ k)
  change IsSylowTwoOf (S.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom)
    ((L1 ⊔ Q1 L1 L2 S).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) at h
  simpa using h

private theorem tv_isSylowTwoOf_Lv_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (k : ℤ) :
    IsSylowTwoOf (pCoreOf 2 (t.Gw (2 * k + 1) (2 * k + 2))) (t.Lv (2 * k + 1)) := by
  rw [tv_Gw_odd t k, tv_Lv_odd t k, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj ((t.x₂ * t.x₁) ^ k)) (t.Gw 1 2), tv_pCoreOf_Gw_one_two t hfr]
  have h := F7.isSylowTwoOf_conj (tv_isSylowTwoOf_map_x₂ t hfr) ((t.x₂ * t.x₁) ^ k)
  change IsSylowTwoOf ((S.map (MulAut.conj t.x₂).toMonoidHom).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom)
    ((L2 ⊔ Q2 L1 L2 S).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) at h
  simpa using h

private theorem tv_isSylowTwoOf_Lv_left_even {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (k : ℤ) :
    IsSylowTwoOf (pCoreOf 2 (t.Gw (2 * k - 1) (2 * k))) (t.Lv (2 * k)) := by
  rw [tv_Gw_left_even t k, tv_Lv_even t k, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj ((t.x₂ * t.x₁) ^ k)) (t.Gw (-1) 0), tv_pCoreOf_Gw_neg_one_zero t hfr]
  have h := F7.isSylowTwoOf_conj (tv_isSylowTwoOf_map_x₁ t hfr) ((t.x₂ * t.x₁) ^ k)
  change IsSylowTwoOf ((S.map (MulAut.conj t.x₁).toMonoidHom).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom)
    ((L1 ⊔ Q1 L1 L2 S).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) at h
  simpa using h

private theorem tv_isSylowTwoOf_Lv_left_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (k : ℤ) :
    IsSylowTwoOf (pCoreOf 2 (t.Gw (2 * k) (2 * k + 1))) (t.Lv (2 * k + 1)) := by
  rw [tv_Gw_even t k, tv_Lv_odd t k, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj ((t.x₂ * t.x₁) ^ k)) (t.Gw 0 1), t.pCoreOf_Gw_zero_one hfr]
  have h := F7.isSylowTwoOf_conj (tv_isSylowTwoOf_sup_pCoreOf_right hfr)
    ((t.x₂ * t.x₁) ^ k)
  change IsSylowTwoOf (S.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom)
    ((L2 ⊔ Q2 L1 L2 S).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) at h
  simpa using h

theorem isSylowTwoOf_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (i : ℤ) : IsSylowTwoOf (pCoreOf 2 (t.Gw i (i + 1))) (t.Lv i) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · exact tv_isSylowTwoOf_Lv_even t hfr k
  · rw [show 2 * k + 1 + 1 = 2 * k + 2 by rw [add_assoc]; rfl]
    exact tv_isSylowTwoOf_Lv_odd t hfr k

theorem isSylowTwoOf_Lv_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (i : ℤ) :
    IsSylowTwoOf (pCoreOf 2 (t.Gw (i - 1) i)) (t.Lv i) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · exact tv_isSylowTwoOf_Lv_left_even t hfr k
  · rw [show 2 * k + 1 - 1 = 2 * k from add_sub_cancel_right (2 * k) 1]
    exact tv_isSylowTwoOf_Lv_left_odd t hfr k

private theorem tv_P1_eq_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    P1 L1 L2 S = (L1 ⊔ Q1 L1 L2 S) ⊔ t.K := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hLS : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    conv_lhs => rw [hS1]
    rw [← sup_assoc]
    rw [show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  calc P1 L1 L2 S = L1 ⊔ bigB L1 L2 S := rfl
    _ = L1 ⊔ (S ⊔ t.K) := by rw [t.sup_K_eq_bigB]
    _ = (L1 ⊔ S) ⊔ t.K := (sup_assoc L1 S t.K).symm
    _ = (L1 ⊔ Q1 L1 L2 S) ⊔ t.K := by rw [hLS]

private theorem tv_P2_eq_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    P2 L1 L2 S = (L2 ⊔ Q2 L1 L2 S) ⊔ t.K := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hLS : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    conv_lhs => rw [hS2]
    rw [← sup_assoc]
    rw [show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  calc P2 L1 L2 S = L2 ⊔ bigB L1 L2 S := rfl
    _ = L2 ⊔ (S ⊔ t.K) := by rw [t.sup_K_eq_bigB]
    _ = (L2 ⊔ S) ⊔ t.K := (sup_assoc L2 S t.K).symm
    _ = (L2 ⊔ Q2 L1 L2 S) ⊔ t.K := by rw [hLS]

private theorem tv_relIndex_L1Q1_odd {a f : ℕ}
    (t : Track L1 L2 S) (hfr : Frame L1 L2 S a f) :
    Odd ((L1 ⊔ Q1 L1 L2 S).relIndex (P1 L1 L2 S)) := by
  have hK : t.K ≤ Subgroup.normalizer ((L1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
    (t.hHall.1.trans (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans
      (tv_P1_le_normalizer hfr.hF)
  have h := C5.relIndex_sup_eq_of_le_normalizer (A := t.K)
    (B := L1 ⊔ Q1 L1 L2 S) hK
  rw [sup_comm t.K (L1 ⊔ Q1 L1 L2 S), ← tv_P1_eq_sup t hfr] at h
  rw [h]
  exact Odd.of_dvd_nat t.hHall.2.1 (Subgroup.relIndex_dvd_card _ _)

private theorem tv_relIndex_L2Q2_odd {a f : ℕ}
    (t : Track L1 L2 S) (hfr : Frame L1 L2 S a f) :
    Odd ((L2 ⊔ Q2 L1 L2 S).relIndex (P2 L1 L2 S)) := by
  have hK : t.K ≤ Subgroup.normalizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
    (t.hHall.1.trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans
      (tv_P2_le_normalizer hfr.hF)
  have h := C5.relIndex_sup_eq_of_le_normalizer (A := t.K)
    (B := L2 ⊔ Q2 L1 L2 S) hK
  rw [sup_comm t.K (L2 ⊔ Q2 L1 L2 S), ← tv_P2_eq_sup t hfr] at h
  rw [h]
  exact Odd.of_dvd_nat t.hHall.2.1 (Subgroup.relIndex_dvd_card _ _)

private theorem tv_le_Lv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : IsPGroup 2 X) (hX0 : X ≤ t.Gv 0) :
    X ≤ t.Lv 0 := by
  rw [t.Gv_zero] at hX0
  rw [t.Lv_zero]
  have hle : L1 ⊔ Q1 L1 L2 S ≤ P1 L1 L2 S :=
    sup_le le_sup_left (pCoreOf_le 2 (P1 L1 L2 S))
  have hnormal : ((L1 ⊔ Q1 L1 L2 S).subgroupOf (P1 L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (tv_P1_le_normalizer hfr.hF)
  have hindex : Odd ((L1 ⊔ Q1 L1 L2 S).subgroupOf (P1 L1 L2 S)).index := by
    show Odd ((L1 ⊔ Q1 L1 L2 S).relIndex (P1 L1 L2 S))
    exact tv_relIndex_L1Q1_odd t hfr
  have hsub : X.subgroupOf (P1 L1 L2 S) ≤
      (L1 ⊔ Q1 L1 L2 S).subgroupOf (P1 L1 L2 S) :=
    @CFSG.Quasithin.I4.le_of_odd_index ↥(P1 L1 L2 S) _ _ _ hnormal hindex
      (hX.comap_subtype (K := P1 L1 L2 S))
  intro x hx
  exact hsub (show (⟨x, hX0 hx⟩ : ↥(P1 L1 L2 S)) ∈
    X.subgroupOf (P1 L1 L2 S) from hx)

private theorem tv_le_Lv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≤ t.Gv 1) :
    X ≤ t.Lv 1 := by
  rw [t.Gv_one] at hX1
  rw [t.Lv_one]
  have hle : L2 ⊔ Q2 L1 L2 S ≤ P2 L1 L2 S :=
    sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))
  have hnormal : ((L2 ⊔ Q2 L1 L2 S).subgroupOf (P2 L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (tv_P2_le_normalizer hfr.hF)
  have hindex : Odd ((L2 ⊔ Q2 L1 L2 S).subgroupOf (P2 L1 L2 S)).index := by
    show Odd ((L2 ⊔ Q2 L1 L2 S).relIndex (P2 L1 L2 S))
    exact tv_relIndex_L2Q2_odd t hfr
  have hsub : X.subgroupOf (P2 L1 L2 S) ≤
      (L2 ⊔ Q2 L1 L2 S).subgroupOf (P2 L1 L2 S) :=
    @CFSG.Quasithin.I4.le_of_odd_index ↥(P2 L1 L2 S) _ _ _ hnormal hindex
      (hX.comap_subtype (K := P2 L1 L2 S))
  intro x hx
  exact hsub (show (⟨x, hX1 hx⟩ : ↥(P2 L1 L2 S)) ∈
    X.subgroupOf (P2 L1 L2 S) from hx)

theorem le_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f) {i : ℤ}
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXi : X ≤ t.Gv i) : X ≤ t.Lv i := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · have hXi' : X ≤ (P1 L1 L2 S).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      rwa [tv_Gv_even t k] at hXi
    have hP1 : ((P1 L1 L2 S).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom = P1 L1 L2 S := by
      rw [Subgroup.map_conj_map_conj, inv_mul_cancel]
      ext x
      simp
    have hYle : X.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom ≤ t.Gv 0 := by
      rw [t.Gv_zero, ← hP1]
      exact Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom) hXi'
    have hY0 : X.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom ≤ t.Lv 0 :=
      tv_le_Lv_zero t hfr (hX.map _) hYle
    rw [t.Lv_zero] at hY0
    rw [tv_Lv_even t k]
    have hXX : (X.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = X := by
      rw [Subgroup.map_conj_map_conj, mul_inv_cancel]
      ext x
      simp
    rw [← hXX]
    exact Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) hY0
  · have hXi' : X ≤ (P2 L1 L2 S).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      rwa [tv_Gv_odd t k] at hXi
    have hP2 : ((P2 L1 L2 S).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom = P2 L1 L2 S := by
      rw [Subgroup.map_conj_map_conj, inv_mul_cancel]
      ext x
      simp
    have hYle : X.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom ≤ t.Gv 1 := by
      rw [t.Gv_one, ← hP2]
      exact Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom) hXi'
    have hY1 : X.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom ≤ t.Lv 1 :=
      tv_le_Lv_one t hfr (hX.map _) hYle
    rw [t.Lv_one] at hY1
    rw [tv_Lv_odd t k]
    have hXX : (X.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)⁻¹).toMonoidHom).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = X := by
      rw [Subgroup.map_conj_map_conj, mul_inv_cancel]
      ext x
      simp
    rw [← hXX]
    exact Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) hY1

end Track

end CFSG.Quasithin.Stroth.Rq

end
