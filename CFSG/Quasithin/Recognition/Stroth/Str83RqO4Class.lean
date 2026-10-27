module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
import CFSG.Quasithin.Recognition.St84.SetupOf
import CFSG.Quasithin.Background.F7E1
import CFSG.GroupTheory.WielandtProductBasic

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {X : Subgroup G}

private theorem CosetTrans.of_le_inf {H H' A B : Subgroup G} (h : CosetTrans H A B)
    (hH : H ⊓ A ≤ H') : CosetTrans H' A B := by
  intro g hg
  obtain ⟨n, hn, hnb⟩ := h g hg
  exact ⟨n, ⟨hH hn, hn.2⟩, hnb⟩

private theorem CosetTrans.inf_right {H A B : Subgroup G} (h : CosetTrans H A B) :
    CosetTrans H A (A ⊓ B) := by
  intro g hg
  obtain ⟨n, hn, hnb⟩ := h g hg
  exact ⟨n, hn, ⟨A.mul_mem (A.inv_mem hn.2) hg, hnb⟩⟩

private theorem relIndex_eq_of_cosetTrans {M A B : Subgroup G} (hM : M ≤ A)
    (h : CosetTrans M A B) : (M ⊓ B).relIndex M = B.relIndex A := by
  classical
  let f : ↥M ⧸ (M ⊓ B).subgroupOf M → ↥A ⧸ B.subgroupOf A :=
    Quotient.map' (fun m : M => (⟨(m : G), hM m.2⟩ : A)) (by
      intro m1 m2 hm
      rw [QuotientGroup.leftRel_apply] at hm ⊢
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hm)).2)
  have hinj : Function.Injective f := by
    intro q1 q2 hq
    induction q1 using Quotient.ind with
    | _ m1 =>
      induction q2 using Quotient.ind with
      | _ m2 =>
        apply Quotient.sound
        change QuotientGroup.leftRel ((M ⊓ B).subgroupOf M) m1 m2
        rw [QuotientGroup.leftRel_apply]
        have hq' := Quotient.exact hq
        change QuotientGroup.leftRel (B.subgroupOf A)
          (⟨(m1 : G), hM m1.2⟩ : A) ⟨(m2 : G), hM m2.2⟩ at hq'
        rw [QuotientGroup.leftRel_apply] at hq'
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · exact M.mul_mem (M.inv_mem m1.2) m2.2
        · simpa using Subgroup.mem_subgroupOf.mp hq'
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quotient.ind with
    | _ a =>
      obtain ⟨m, hm, hmb⟩ := h (a : G) a.2
      obtain ⟨hmM, _⟩ := Subgroup.mem_inf.mp hm
      refine ⟨Quotient.mk'' ⟨m, hmM⟩, ?_⟩
      have hf : f (Quotient.mk'' ⟨m, hmM⟩) = Quotient.mk'' (⟨m, hM hmM⟩ : A) := rfl
      rw [hf]
      apply Quotient.sound
      change QuotientGroup.leftRel (B.subgroupOf A) ⟨m, hM hmM⟩ a
      rw [QuotientGroup.leftRel_apply]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hmb)
  have hmain := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa [Subgroup.relIndex, Subgroup.index] using hmain

private theorem eq_pCoreOf_sup_of_le {E W K : Subgroup G} (hE : E = pCoreOf 2 E ⊔ K)
    (hKW : K ≤ W) (hWE : W ≤ E) : W = pCoreOf 2 W ⊔ K := by
  refine le_antisymm (fun w hw => ?_) (sup_le (pCoreOf_le 2 W) hKW)
  have hKN : K ≤ normalizer (pCoreOf 2 E : Set G) :=
    (hKW.trans hWE).trans (le_normalizer_pCoreOf 2 E)
  have hwE : w ∈ pCoreOf 2 E ⊔ K := by rw [← hE]; exact hWE hw
  obtain ⟨s, hs, k, hk, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hKN).mp hwE
  have hsW : s ∈ W := by
    have := mul_mem hw (inv_mem (hKW hk))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (F7.pCoreOf_inf_le hWE ⟨hs, hsW⟩)) (mem_sup_right hk)

private theorem pow_not_mem_of_sq_mem {H : Subgroup G} {y : G} (hy : y ∉ H)
    (hy2 : y ^ 2 ∈ H) : ∀ m : ℕ, Odd m → y ^ m ∉ H := by
  intro m hm
  obtain ⟨k, rfl⟩ := hm
  have hpow : y ^ (2 * k + 1) = (y ^ 2) ^ k * y := by
    rw [pow_succ, pow_mul]
  rw [hpow]
  intro hmem
  apply hy
  have hk : (y ^ 2) ^ k ∈ H := H.pow_mem hy2 k
  convert H.mul_mem (H.inv_mem hk) hmem using 1
  group

theorem ArcL.normIn_Gw_zero_one (hX : t.ArcL X) :
    normIn X (t.Gw 0 1) = normIn X (t.Gw (-1) 1) := by
  have h1 : t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 := by simpa using t.Gw_add_one 0
  have h2 : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
    simpa using t.Gw_sub_one_add_one 0
  rw [h1, h2]
  refine le_antisymm ?_ ?_
  · intro n hn
    obtain ⟨hnN, hnG01⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨hnG0, hnG1⟩ := Subgroup.mem_inf.mp hnG01
    rcases hX.pair n (Subgroup.mem_inf.mpr ⟨hnN, hnG0⟩) with hfix | hswap
    · refine Subgroup.mem_inf.mpr ⟨hnN, ?_⟩
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hfix.2, hnG0⟩, hnG1⟩
    · exfalso
      have hx1 : t.x₁⁻¹ ∈ t.Gv 1 := by
        simpa using (t.Gv 1).mul_mem hswap.1 ((t.Gv 1).inv_mem hnG1)
      have : t.x₁ ∈ t.Gv 1 := by simpa using (t.Gv 1).inv_mem hx1
      rw [t.Gv_one] at this
      exact t.track.x₁_not_mem this
  · intro n hn
    obtain ⟨hnN, hnG⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨hnGm0, hnG1⟩ := Subgroup.mem_inf.mp hnG
    obtain ⟨-, hnG0⟩ := Subgroup.mem_inf.mp hnGm0
    exact Subgroup.mem_inf.mpr ⟨hnN, Subgroup.mem_inf.mpr ⟨hnG0, hnG1⟩⟩

theorem pX_eq_pCoreOf {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.PX X = pCoreOf 2 (normIn X (t.Gw (-1) 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGm : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
    simpa using t.Gw_sub_one_add_one 0
  have hWm : t.Gw (-1) 1 ≤ t.Gv (-1) := win_le_qv le_rfl (by norm_num)
  have hW0 : t.Gw (-1) 1 ≤ t.Gv 0 := win_le_qv (by norm_num) (by norm_num)
  have hW1 : t.Gw (-1) 1 ≤ t.Gv 1 := win_le_qv (by norm_num) le_rfl
  have hQm : t.Qv 0 ≤ t.Gv (-1) := (t.Qv_le_Gv hfr 0).1
  have hQ0 : t.Qv 0 ≤ t.Gv 0 := t.Qv_le_Gv_self 0
  have hP2 : IsPGroup 2 (t.PX X) := (t.isPGroup_Qv 0).to_le inf_le_left
  have hPleA : t.PX X ≤ normIn X (t.Gw (-1) 1) := by
    refine le_inf ?_ ?_
    · exact inf_le_right.trans inf_le_left
    · rw [hGm]
      have hPGm : t.PX X ≤ t.Gv (-1) := by
        change t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv 1) ≤ t.Gv (-1)
        exact inf_le_left.trans hQm
      have hPG0 : t.PX X ≤ t.Gv 0 := by
        change t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv 1) ≤ t.Gv 0
        exact inf_le_left.trans hQ0
      have hPG1 : t.PX X ≤ t.Gv 1 := by
        change t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv 1) ≤ t.Gv 1
        exact inf_le_right.trans inf_le_right
      exact le_inf (le_inf hPGm hPG0) hPG1
  have hANP : normIn X (t.Gw (-1) 1) ≤ normalizer (t.PX X : Set G) := by
    have hA0 : normIn X (t.Gw (-1) 1) ≤ t.Gv 0 := inf_le_right.trans hW0
    have hA1 : normIn X (t.Gw (-1) 1) ≤ t.Gv 1 := inf_le_right.trans hW1
    have hAN : normIn X (t.Gw (-1) 1) ≤ normalizer (X : Set G) := inf_le_left
    have hAB : normIn X (t.Gw (-1) 1) ≤ normalizer (t.MX X 1 : Set G) := by
      have hNN : normIn X (t.Gw (-1) 1) ≤ normalizer (normalizer (X : Set G) : Set G) :=
        hAN.trans (Subgroup.le_normalizer (H := normalizer (X : Set G)))
      have hNG1 : normIn X (t.Gw (-1) 1) ≤ normalizer (t.Gv 1 : Set G) :=
        hA1.trans Subgroup.le_normalizer
      have h := (le_inf hNN hNG1).trans
        (Subgroup.inf_normalizer_le_normalizer_inf
          (H := normalizer (X : Set G)) (K := t.Gv 1))
      simpa [Track.MX, normIn] using h
    have hAQ0 : normIn X (t.Gw (-1) 1) ≤ normalizer (t.Qv 0 : Set G) :=
      hA0.trans (t.Gv_le_normalizer_Qv 0)
    exact (le_inf hAQ0 (by simpa [Track.PX, Track.MX, normIn] using hAB)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.Qv 0) (K := t.MX X 1))
  have hle : t.PX X ≤ pCoreOf 2 (normIn X (t.Gw (-1) 1)) :=
    le_pCoreOf_of_le_normalizer hPleA hANP hP2
  refine le_antisymm hle ?_
  have hO2 : pCoreOf 2 (normIn X (t.Gw (-1) 1)) ≤ normIn X (t.Gw (-1) 1) :=
    pCoreOf_le 2 _
  have hpA : IsPGroup 2 (pCoreOf 2 (normIn X (t.Gw (-1) 1))) := pCoreOf_isPGroup 2 _
  have hQ : pCoreOf 2 (normIn X (t.Gw (-1) 1)) ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num) hpA
      (hO2.trans inf_le_right)
  exact le_inf hQ (hO2.trans (le_inf inf_le_left (inf_le_right.trans hW1)))

private theorem ArcL.isSylowTwoOf_pX_gw_zero_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    IsSylowTwoOf (t.PX X) (normIn X (t.Gw 0 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := normIn X (t.Gw 0 1)
  have hG01 : t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 := by simpa using t.Gw_add_one 0
  have hAdef : A = t.MX X 1 ⊓ t.Gv 0 := by
    simp only [A, Track.MX, normIn, hG01]
    ac_rfl
  have hP_eq : t.PX X = pCoreOf 2 A := by
    rw [pX_eq_pCoreOf (t := t) hfr, ← hX.normIn_Gw_zero_one]
  have hP2 : IsPGroup 2 (t.PX X) := (t.isPGroup_Qv 0).to_le inf_le_left
  have hKA : t.K ≤ A := by
    rw [hAdef]
    exact le_inf (le_inf hX.K_le (t.K_le_Gv 1)) (t.K_le_Gv 0)
  have hAGw : A ≤ t.Gw 0 1 := by
    simp only [A, normIn]
    exact inf_le_right
  have hA_eq : A = t.PX X ⊔ t.K := by
    have h := eq_pCoreOf_sup_of_le (E := t.Gw 0 1) (W := A) (K := t.K)
      (t.Gw_eq_sup hfr (u := 0) (w := 1) (by norm_num)) hKA hAGw
    rwa [← hP_eq] at h
  have hPleA : t.PX X ≤ A := by rw [hP_eq]; exact pCoreOf_le 2 A
  have hKB : t.K ≤ normalizer (t.MX X 1) := by
    have hNN : t.K ≤ normalizer (normalizer (X : Set G) : Set G) :=
      hX.K_le.trans (Subgroup.le_normalizer (H := normalizer (X : Set G)))
    have hNG1 : t.K ≤ normalizer (t.Gv 1) := (t.K_le_Gv 1).trans Subgroup.le_normalizer
    have h := (le_inf hNN hNG1).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := normalizer (X : Set G)) (K := t.Gv 1))
    simpa [Track.MX, normIn] using h
  have hKN : t.K ≤ normalizer (t.PX X) := by
    have hQ := (t.K_le_Gv 0).trans (t.Gv_le_normalizer_Qv 0)
    have h := (le_inf hQ hKB).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.Qv 0) (K := t.MX X 1))
    simpa [Track.PX, Track.MX, normIn] using h
  have hrelA : (t.PX X).relIndex A = ((t.PX X) ⊓ t.K).relIndex t.K := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hKN).2
    rw [sup_comm] at h
    rw [← hA_eq] at h
    exact h.trans (by rw [inf_comm])
  have hdiv : (t.PX X).relIndex A ∣ Nat.card t.K := by
    rw [hrelA]
    exact Subgroup.relIndex_dvd_card ((t.PX X) ⊓ t.K) t.K
  have hoddA : Odd ((t.PX X).relIndex A) := t.hHall.2.1.of_dvd_nat hdiv
  refine F7.isSylowTwoOf_of_relIndex hPleA hP2 ?_
  intro h2
  exact Nat.not_even_iff_odd.mpr hoddA (even_iff_two_dvd.mpr h2)

private theorem ArcL.odd_relIndex_gw_zero_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    Odd ((normIn X (t.Gw 0 1)).relIndex (t.MX X 1)) := by
  let A : Subgroup G := normIn X (t.Gw 0 1)
  have hG01 : t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 := by simpa using t.Gw_add_one 0
  have hAdef' : A = t.MX X 1 ⊓ (t.Gv 1 ⊓ t.Gv 0) := by
    have hAdef : A = t.MX X 1 ⊓ t.Gv 0 := by
      simp only [A, Track.MX, normIn, hG01]
      ac_rfl
    rw [hAdef, ← inf_assoc,
      inf_eq_left.mpr (show t.MX X 1 ≤ t.Gv 1 from inf_le_right)]
  have hMleA : t.MX X 1 ≤ t.Gv 1 := inf_le_right
  have htrans : CosetTrans (t.MX X 1) (t.Gv 1) (t.Gv 0) := by
    have h := CosetTrans.of_le_inf (H := normalizer (X : Set G)) (H' := t.MX X 1)
      (A := t.Gv 1) (B := t.Gv 0) hX.trans₀ (by simp [Track.MX, normIn])
    simpa [Track.MX, normIn] using h
  have htrans' : CosetTrans (t.MX X 1) (t.Gv 1) (t.Gv 1 ⊓ t.Gv 0) :=
    CosetTrans.inf_right htrans
  have hrelAM : A.relIndex (t.MX X 1) = (t.Gv 1 ⊓ t.Gv 0).relIndex (t.Gv 1) := by
    have h := relIndex_eq_of_cosetTrans hMleA htrans'
    rwa [← hAdef'] at h
  have hf0 : f ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by norm_num : 0 < 2) hfr.hf)
  have hoddval : Odd ((t.Gv 1 ⊓ t.Gv 0).relIndex (t.Gv 1)) := by
    have hval : (t.Gw 0 1).relIndex (t.Gv 1) = 2 ^ f + 1 := by
      rw [t.Gw_zero_one hfr.hF, t.Gv_one]
      exact f112_relIndex_right_l2 hfr.hF hf0 hfr.hL2
    have hval' : (t.Gv 1 ⊓ t.Gv 0).relIndex (t.Gv 1) = 2 ^ f + 1 := by
      rw [inf_comm, ← hG01]
      exact hval
    rw [hval']
    exact (even_two.pow_of_ne_zero hf0).add_one
  rw [show A.relIndex (t.MX X 1) = (t.Gv 1 ⊓ t.Gv 0).relIndex (t.Gv 1) from hrelAM]
  exact hoddval

theorem ArcL.isSylowTwoOf_pX_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) : IsSylowTwoOf (t.PX X) (t.MX X 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := normIn X (t.Gw 0 1)
  have hSylA : IsSylowTwoOf (t.PX X) A :=
    ArcL.isSylowTwoOf_pX_gw_zero_one (t := t) hfr hX
  have hoddAM : Odd (A.relIndex (t.MX X 1)) :=
    ArcL.odd_relIndex_gw_zero_one (t := t) hfr hX
  have hP2 : IsPGroup 2 (t.PX X) := (t.isPGroup_Qv 0).to_le inf_le_left
  have hAM : A ≤ t.MX X 1 := by
    change normIn X (t.Gw 0 1) ≤ t.MX X 1
    rw [show t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 from by simpa using t.Gw_add_one 0]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hoddA : Odd ((t.PX X).relIndex A) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact F7.isSylowTwoOf_odd_relIndex hSylA
  have hrelM : (t.PX X).relIndex (t.MX X 1) =
      (t.PX X).relIndex A * A.relIndex (t.MX X 1) :=
    (Subgroup.relIndex_mul_relIndex (H := t.PX X) (K := A) (L := t.MX X 1)
      hSylA.1 hAM).symm
  refine F7.isSylowTwoOf_of_relIndex
    (show t.PX X ≤ t.MX X 1 from inf_le_right) hP2 ?_
  rw [hrelM]
  exact fun h2 => Nat.not_even_iff_odd.mpr (hoddA.mul hoddAM) (even_iff_two_dvd.mpr h2)

theorem ArcL.normIn_Gw_eq_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    normIn X (t.Gw (-1) 1) = t.PX X ⊔ t.K := by
  have hG01 : t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 := by simpa using t.Gw_add_one 0
  have hKA : t.K ≤ normIn X (t.Gw 0 1) := by
    rw [hG01]
    exact le_inf hX.K_le (le_inf (t.K_le_Gv 0) (t.K_le_Gv 1))
  have hAW : normIn X (t.Gw 0 1) ≤ t.Gw 0 1 := inf_le_right
  have hEq := eq_pCoreOf_sup_of_le (E := t.Gw 0 1) (W := normIn X (t.Gw 0 1))
    (K := t.K) (t.Gw_eq_sup hfr (u := 0) (w := 1) (by norm_num)) hKA hAW
  have hP' : t.PX X = pCoreOf 2 (normIn X (t.Gw 0 1)) := by
    rw [pX_eq_pCoreOf (t := t) hfr, ← hX.normIn_Gw_zero_one]
  rw [← hP'] at hEq
  exact hX.normIn_Gw_zero_one.symm.trans hEq

private theorem ArcL.exists_swap_conj {g : G} (hgM0 : g ∈ t.MX X 0)
    (hgu : t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub g (normIn X (t.Gw (-1) 1)) = normIn X (t.Gw (-1) 1) := by
  let A : Subgroup G := normIn X (t.Gw (-1) 1)
  set u : G := t.x₁⁻¹ * g with hu_def
  have hu : u ∈ t.Gv 1 ⊓ t.Gv (-1) := by simpa [hu_def] using hgu
  have hg_eq : g = t.x₁ * u := by rw [hu_def]; group
  have hgN : g ∈ normalizer (X : Set G) := hgM0.1
  have hgG0 : g ∈ t.Gv 0 := hgM0.2
  have hA_def : A = normalizer (X : Set G) ⊓ (t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1) := by
    simp only [A, normIn]
    rw [show t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 by
      simpa using t.Gw_sub_one_add_one 0]
  have hNconj : conjSub g (normalizer (X : Set G)) = normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := normalizer (X : Set G)) hgN)
  have hG0conj : conjSub g (t.Gv 0) = t.Gv 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgG0)
  have huN : (t.Gv 1).map (MulAut.conj u).toMonoidHom = t.Gv 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((t.Gv 1).le_normalizer hu.1)
  have huM : (t.Gv (-1)).map (MulAut.conj u).toMonoidHom = t.Gv (-1) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((t.Gv (-1)).le_normalizer hu.2)
  have hcomp : (MulAut.conj g).toMonoidHom =
      (MulAut.conj t.x₁).toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hg_eq]
    group
  have hG1conj : conjSub g (t.Gv 1) = t.Gv (-1) := by
    show (t.Gv 1).map (MulAut.conj g).toMonoidHom = t.Gv (-1)
    rw [hcomp, ← Subgroup.map_map, huN, t.map_Gv_x₁]
  have hGmconj : conjSub g (t.Gv (-1)) = t.Gv 1 := by
    show (t.Gv (-1)).map (MulAut.conj g).toMonoidHom = t.Gv 1
    rw [hcomp, ← Subgroup.map_map, huM, t.map_Gv_x₁]
    norm_num
  have hAconj : conjSub g A = A := by
    rw [hA_def, conjSub_inf, hNconj, conjSub_inf, conjSub_inf, hGmconj, hG0conj, hG1conj]
    ac_rfl
  simpa [A] using hAconj

private theorem ArcL.exists_swap_mem_data (hX : t.ArcL X) {g : G} (hgM0 : g ∈ t.MX X 0)
    (hgu : t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    g ∉ normIn X (t.Gw (-1) 1) ∧ g * g ∈ normIn X (t.Gw (-1) 1) := by
  let A : Subgroup G := normIn X (t.Gw (-1) 1)
  have hA_M : A = t.MX X 0 ⊓ t.Gv 1 := by
    have hM : t.MX X 0 ⊓ t.Gv 1 = normIn X (t.Gw 0 1) := by
      simp only [Track.MX, normIn]
      rw [show t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 from by simpa using t.Gw_add_one 0]
      ac_rfl
    rw [hM, hX.normIn_Gw_zero_one]
  set u : G := t.x₁⁻¹ * g with hu_def
  have hu : u ∈ t.Gv 1 ⊓ t.Gv (-1) := by simpa [hu_def] using hgu
  have hg_eq : g = t.x₁ * u := by rw [hu_def]; group
  have hgA : g ∉ A := by
    intro h
    rw [hA_M] at h
    have hgG1 : g ∈ t.Gv 1 := h.2
    have hx1 : t.x₁⁻¹ ∈ t.Gv 1 := by
      have h' : u * g⁻¹ ∈ t.Gv 1 :=
        (t.Gv 1).mul_mem hu.1 ((t.Gv 1).inv_mem hgG1)
      convert h' using 1
      rw [hu_def]; group
    have hx : t.x₁ ∈ t.Gv 1 := by simpa using (t.Gv 1).inv_mem hx1
    rw [t.Gv_one] at hx
    exact t.track.x₁_not_mem hx
  have hx1map : (t.Gv (-1)).map (MulAut.conj t.x₁).toMonoidHom = t.Gv 1 := by
    simpa using t.map_Gv_x₁ (-1)
  have hx1u : t.x₁ * u * t.x₁⁻¹ ∈ t.Gv 1 := by
    have h' := mul_mem_conjSub (g := t.x₁) (H := t.Gv (-1)) hu.2
    rwa [show conjSub t.x₁ (t.Gv (-1)) =
      (t.Gv (-1)).map (MulAut.conj t.x₁).toMonoidHom from rfl, hx1map] at h'
  have hx1sq : t.x₁ * t.x₁ ∈ t.Gv 1 := by
    simpa [t.Gv_one] using t.track.x₁_mul_self_mem
  have hg2A : g * g ∈ A := by
    have hx1ux1 : t.x₁ * u * t.x₁ ∈ t.Gv 1 := by
      have h' := (t.Gv 1).mul_mem hx1u hx1sq
      convert h' using 1
      group
    have hg2G1 : g * g ∈ t.Gv 1 := by
      have h' := (t.Gv 1).mul_mem hx1ux1 hu.1
      convert h' using 1
      rw [hg_eq]; group
    rw [hA_M]
    exact ⟨(t.MX X 0).mul_mem hgM0 hgM0, hg2G1⟩
  exact ⟨by simpa [A] using hgA, by simpa [A] using hg2A⟩

private theorem ArcL.exists_swap_A_sylow {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    IsSylowTwoOf (t.PX X) (normIn X (t.Gw (-1) 1)) ∧
      ((t.PX X).subgroupOf (normIn X (t.Gw (-1) 1))).Normal ∧
      normIn X (t.Gw (-1) 1) = t.PX X ⊔ t.K ∧ t.PX X ⊓ t.K = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := normIn X (t.Gw (-1) 1)
  let P : Subgroup G := t.PX X
  have hA_PK : A = P ⊔ t.K := by
    simpa [A, P] using ArcL.normIn_Gw_eq_sup (t := t) hfr hX
  have hP_eq : P = pCoreOf 2 A := by
    simp only [A, P]
    rw [pX_eq_pCoreOf (t := t) hfr, ← hX.normIn_Gw_zero_one]
  have hKA : t.K ≤ A := by rw [hA_PK]; exact le_sup_right
  have hPleA : P ≤ A := by rw [hA_PK]; exact le_sup_left
  have hKN : t.K ≤ normalizer (P : Set G) := by
    have hQ := (t.K_le_Gv 0).trans (t.Gv_le_normalizer_Qv 0)
    have hB : t.K ≤ normalizer (t.MX X 1) := by
      have hNN : t.K ≤ normalizer (normalizer (X : Set G) : Set G) :=
        hX.K_le.trans (Subgroup.le_normalizer (H := normalizer (X : Set G)))
      have hNG1 : t.K ≤ normalizer (t.Gv 1) := (t.K_le_Gv 1).trans Subgroup.le_normalizer
      have h := (le_inf hNN hNG1).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := normalizer (X : Set G))
          (K := t.Gv 1))
      simpa [Track.MX, normIn] using h
    have h := (le_inf hQ hB).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.Qv 0) (K := t.MX X 1))
    have hPdef : P = t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv 1) := rfl
    rw [hPdef]
    exact h
  have hrelA : P.relIndex A = (P ⊓ t.K).relIndex t.K := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hKN).2
    rw [sup_comm] at h
    rw [← hA_PK] at h
    exact h.trans (by rw [inf_comm])
  have hdiv : P.relIndex A ∣ Nat.card t.K := by
    rw [hrelA]; exact Subgroup.relIndex_dvd_card (P ⊓ t.K) t.K
  have hSylP_A : IsSylowTwoOf P A := by
    refine F7.isSylowTwoOf_of_relIndex hPleA ((t.isPGroup_Qv 0).to_le inf_le_left) ?_
    intro h2
    exact Nat.not_even_iff_odd.mpr (t.hHall.2.1.of_dvd_nat hdiv)
      (even_iff_two_dvd.mpr h2)
  have hPnorm : (P.subgroupOf A).Normal := by
    rw [hP_eq]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 A)
  have hPK_bot : P ⊓ t.K = ⊥ := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 A).exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hP_eq, hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr t.hHall.2.1)
  exact ⟨by simpa [A, P] using hSylP_A, by simpa [A, P] using hPnorm,
    by simpa [A, P] using hA_PK, by simpa [A, P] using hPK_bot⟩

private theorem ArcL.exists_swap_conj_K {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) {g : G}
    (hAconj : conjSub g (normIn X (t.Gw (-1) 1)) = normIn X (t.Gw (-1) 1)) :
    conjSub g (t.PX X) = t.PX X ∧ conjSub g t.K ≤ normIn X (t.Gw (-1) 1) ∧
      t.PX X ⊔ conjSub g t.K = normIn X (t.Gw (-1) 1) ∧
        t.PX X ⊓ conjSub g t.K = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := normIn X (t.Gw (-1) 1)
  let P : Subgroup G := t.PX X
  have hA_PK : A = P ⊔ t.K := by
    simpa [A, P] using ArcL.normIn_Gw_eq_sup (t := t) hfr hX
  have hKA : t.K ≤ A := by rw [hA_PK]; exact le_sup_right
  have hP_eq : P = pCoreOf 2 A := by
    simp only [A, P]
    rw [pX_eq_pCoreOf (t := t) hfr, ← hX.normIn_Gw_zero_one]
  have hKg : conjSub g t.K ≤ A := by
    have h := conjSub_mono g hKA
    rwa [show conjSub g A = A from hAconj] at h
  have hPconj : conjSub g P = P := by
    rw [hP_eq, ← pCoreOf_conjSub, show conjSub g A = A from hAconj]
  have hA_gK : P ⊔ conjSub g t.K = A := by
    have h := congrArg (conjSub g) (hA_PK.symm)
    rw [conjSub_sup, hPconj, show conjSub g A = A from hAconj] at h
    exact h
  have hPKg_bot : P ⊓ conjSub g t.K = ⊥ := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 A).exists_card_eq
    have hcard : Nat.card (conjSub g t.K) = Nat.card t.K :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hP_eq, hn, hcard]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr t.hHall.2.1)
  exact ⟨by simpa [P] using hPconj, by simpa [A] using hKg, by simpa [A, P] using hA_gK,
    by simpa [A, P] using hPKg_bot⟩

private theorem ArcL.exists_swap_y {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    ∃ y, y ∈ t.MX X 0 ∧ y ∉ normIn X (t.Gw (-1) 1) ∧
      y ∈ normalizer (t.K : Set G) ∧ y * y ∈ normIn X (t.Gw (-1) 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgM0, hgu⟩ := hX.swap
  have hAconj := ArcL.exists_swap_conj (t := t) hgM0 hgu
  obtain ⟨hgA, hg2A⟩ := ArcL.exists_swap_mem_data (t := t) hX hgM0 hgu
  obtain ⟨hSylP_A, hPnorm, hA_PK, hPK_bot⟩ :=
    ArcL.exists_swap_A_sylow (t := t) hfr hX
  obtain ⟨hPconj, hKg, hA_gK, hPKg_bot⟩ :=
    ArcL.exists_swap_conj_K (t := t) hfr hX hAconj
  let A : Subgroup G := normIn X (t.Gw (-1) 1)
  let P : Subgroup G := t.PX X
  have hPleA : P ≤ A := by
    change t.PX X ≤ normIn X (t.Gw (-1) 1)
    rw [hA_PK]; exact le_sup_left
  have hKA : t.K ≤ A := by
    change t.K ≤ normIn X (t.Gw (-1) 1)
    rw [hA_PK]; exact le_sup_right
  obtain ⟨n, hnP, hnK⟩ := CFSG.Quasithin.St84.exists_conj_eq_of_complement
    (F := A) hPleA (by simpa [A, P] using hPnorm) (by simpa [A, P] using hSylP_A)
      hKA (by simpa [A] using hKg) hA_PK.symm (by simpa [A, P] using hA_gK)
      (by simpa [A, P] using hPK_bot) (by simpa [A, P] using hPKg_bot)
  have hnA : n ∈ A := hPleA hnP
  have hnA' : n ∈ normIn X (t.Gw (-1) 1) := by simpa [A] using hnA
  have hnN : n ∈ normalizer (X : Set G) := (Subgroup.mem_inf.mp hnA').1
  have hnG0 : n ∈ t.Gv 0 :=
    win_le_qv (by norm_num) (by norm_num) (Subgroup.mem_inf.mp hnA').2
  have hyM0 : n * g ∈ t.MX X 0 :=
    (t.MX X 0).mul_mem (Subgroup.mem_inf.mpr ⟨hnN, hnG0⟩) hgM0
  have hyA : n * g ∉ A := by
    intro h
    exact hgA (by
      have h' := A.mul_mem (A.inv_mem hnA) h
      simpa [A] using h')
  have hyK : n * g ∈ normalizer (t.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub (n * g) t.K = t.K
    rw [conjSub_mul, hnK, conjSub_inv_conjSub]
  have hgng : g * n * g⁻¹ ∈ A := by
    have h' := mul_mem_conjSub (g := g) (H := A) hnA
    rwa [show conjSub g A = A from hAconj] at h'
  have hy2A : (n * g) ^ 2 ∈ A := by
    have h' := A.mul_mem (A.mul_mem hnA hgng) (by simpa [A] using hg2A)
    rw [pow_two]
    convert h' using 1
    group
  have hy2A' : n * g * (n * g) ∈ normIn X (t.Gw (-1) 1) := by
    simpa [A, pow_two] using hy2A
  exact ⟨n * g, hyM0, by simpa [A] using hyA, hyK, hy2A'⟩

private theorem ArcL.exists_swap_pow2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) {y : G}
    (hyM0 : y ∈ t.MX X 0) (hyA : y ∉ normIn X (t.Gw (-1) 1))
    (hyK : y ∈ normalizer (t.K : Set G)) (hy2A : y * y ∈ normIn X (t.Gw (-1) 1)) :
    ∃ s, s ∈ t.MX X 0 ∧ s ∈ normalizer (t.K : Set G) ∧
      s ∉ normIn X (t.Gw (-1) 1) ∧ (∃ n : ℕ, s ^ 2 ^ n = 1) ∧ s * s ∈ t.PX X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := normIn X (t.Gw (-1) 1)
  let P : Subgroup G := t.PX X
  have hy2A' : y ^ 2 ∈ A := by simpa [A, pow_two] using hy2A
  have hyfin : IsOfFinOrder y := by
    haveI : Finite ↥(t.MX X 0) :=
      Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
    obtain ⟨k, hkpos, hk⟩ := (isOfFinOrder_of_finite
      (⟨y, hyM0⟩ : ↥(t.MX X 0))).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hkpos, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨a, m, hm_odd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (ne_of_gt hyfin.orderOf_pos)
  let s : G := y ^ m
  have hsM0 : s ∈ t.MX X 0 := (t.MX X 0).pow_mem hyM0 m
  have hsK : s ∈ normalizer (t.K : Set G) :=
    (Subgroup.normalizer (t.K : Set G)).pow_mem hyK m
  have hsA : s ∉ A := pow_not_mem_of_sq_mem (by simpa [A] using hyA) hy2A' m hm_odd
  have hspow : s ^ 2 ^ a = 1 := by
    rw [show s = y ^ m from rfl, ← pow_mul, Nat.mul_comm, ← hord, pow_orderOf_eq_one]
  have hssA : s * s ∈ A := by
    have hss : s * s = (y ^ 2) ^ m := by
      rw [show s = y ^ m from rfl, ← pow_add, show m + m = 2 * m by ring, pow_mul]
    rw [hss]; exact A.pow_mem hy2A' m
  have hssP : s * s ∈ P := by
    obtain ⟨hSylP_A, hPnorm, -, -⟩ := ArcL.exists_swap_A_sylow (t := t) hfr hX
    have h2 : (s * s) ^ 2 ^ a = 1 := by
      calc (s * s) ^ 2 ^ a = (s ^ 2) ^ 2 ^ a := by rw [pow_two]
        _ = s ^ (2 * 2 ^ a) := by rw [pow_mul]
        _ = s ^ (2 ^ a * 2) := by rw [Nat.mul_comm]
        _ = (s ^ 2 ^ a) ^ 2 := by rw [pow_mul]
        _ = 1 := by rw [hspow, one_pow]
    have hZ2 : IsPGroup 2 (Subgroup.zpowers (s * s)) :=
      CFSG.GroupTheory.WielandtProduct.isPGroup_zpowers_of_pow_eq_one h2
    have hZle : Subgroup.zpowers (s * s) ≤ A := Subgroup.zpowers_le.mpr hssA
    have hle : Subgroup.zpowers (s * s) ≤ P :=
      F7.le_of_normal_sylow (by simpa [A, P] using hSylP_A)
        (by simpa [A, P] using hPnorm) hZle hZ2
    exact hle (Subgroup.mem_zpowers (s * s))
  exact ⟨s, hsM0, hsK, by simpa [A] using hsA, ⟨a, hspow⟩, by simpa [P] using hssP⟩

theorem ArcL.exists_swap {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hX : t.ArcL X) :
    ∃ s ∈ t.MX X 0, s ∈ normalizer (t.K : Set G) ∧ t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1) ∧
      (∃ n : ℕ, s ^ 2 ^ n = 1) ∧ s * s ∈ t.PX X := by
  obtain ⟨y, hyM0, hyA, hyK, hy2A⟩ := ArcL.exists_swap_y (t := t) hfr hX
  obtain ⟨s, hsM0, hsK, hsA, hspow, hssP⟩ :=
    ArcL.exists_swap_pow2 (t := t) hfr hX hyM0 hyA hyK hy2A
  have hA_M : normIn X (t.Gw (-1) 1) = t.MX X 0 ⊓ t.Gv 1 := by
    have hM : t.MX X 0 ⊓ t.Gv 1 = normIn X (t.Gw 0 1) := by
      simp only [Track.MX, normIn]
      rw [show t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 from by simpa using t.Gw_add_one 0]
      ac_rfl
    rw [hM, hX.normIn_Gw_zero_one]
  have hswap : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1) := by
    rcases hX.pair s (Subgroup.mem_inf.mpr ⟨hsM0.1, hsM0.2⟩) with hfix | hswap
    · exfalso
      apply hsA
      rw [hA_M]
      exact ⟨hsM0, hfix.1⟩
    · exact hswap
  exact ⟨s, hsM0, hsK, hswap, hspow, hssP⟩

theorem map_MX_of_swap {s : G} (hsX : s ∈ normalizer (X : Set G))
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1) :
    (t.MX X 1).map (MulAut.conj s).toMonoidHom = t.MX X (-1) := by
  have hN : (normalizer (X : Set G)).map (MulAut.conj s).toMonoidHom =
      normalizer (X : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.le_normalizer (H := normalizer (X : Set G))) hsX)
  have huN : t.x₁⁻¹ * s ∈ normalizer (t.Gv 1 : Set G) := (t.Gv 1).le_normalizer hs
  have hu : (t.Gv 1).map (MulAut.conj (t.x₁⁻¹ * s)).toMonoidHom = t.Gv 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
  have hcomp : (MulAut.conj s).toMonoidHom =
      (MulAut.conj t.x₁).toMonoidHom.comp (MulAut.conj (t.x₁⁻¹ * s)).toMonoidHom := by
    ext g
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [show s = t.x₁ * (t.x₁⁻¹ * s) from by group]
    group
  have hG : (t.Gv 1).map (MulAut.conj s).toMonoidHom = t.Gv (-1) := by
    rw [hcomp, ← Subgroup.map_map, hu, t.map_Gv_x₁]
  calc (t.MX X 1).map (MulAut.conj s).toMonoidHom
      = ((normalizer (X : Set G)) ⊓ t.Gv 1).map (MulAut.conj s).toMonoidHom := rfl
    _ = (normalizer (X : Set G)).map (MulAut.conj s).toMonoidHom ⊓
          (t.Gv 1).map (MulAut.conj s).toMonoidHom :=
        Subgroup.map_inf _ _ _ (MulAut.conj s).injective
    _ = normalizer (X : Set G) ⊓ t.Gv (-1) := by rw [hN, hG]

theorem ArcL.MX_zero_le_normalizer_pX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    t.MX X 0 ≤ normalizer (t.PX X : Set G) := by
  intro m hm
  obtain ⟨hmN, hmG0⟩ := Subgroup.mem_inf.mp hm
  have hP'leP : t.Qv 0 ⊓ t.MX X (-1) ≤ t.PX X := by
    refine le_inf inf_le_left ?_
    exact le_inf (inf_le_right.trans inf_le_left)
      (inf_le_left.trans (t.Qv_le_Gv hfr 0).2)
  have hPleP' : t.PX X ≤ t.Qv 0 ⊓ t.MX X (-1) := by
    refine le_inf inf_le_left ?_
    exact le_inf (inf_le_right.trans inf_le_left)
      (inf_le_left.trans (t.Qv_le_Gv hfr 0).1)
  have hP_eq : t.Qv 0 ⊓ t.MX X (-1) = t.PX X := le_antisymm hP'leP hPleP'
  have hQ : (t.Qv 0).map (MulAut.conj m).toMonoidHom = t.Qv 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.Gv_le_normalizer_Qv 0 hmG0)
  have hmapP : (t.PX X).map (MulAut.conj m).toMonoidHom = t.PX X := by
    rw [Track.PX, Subgroup.map_inf _ _ _ (MulAut.conj m).injective, hQ]
    rcases hX.pair m (Subgroup.mem_inf.mpr ⟨hmN, hmG0⟩) with hfix | hswap
    · have hmMX : m ∈ t.MX X 1 := Subgroup.mem_inf.mpr ⟨hmN, hfix.1⟩
      have hmapMX : (t.MX X 1).map (MulAut.conj m).toMonoidHom = t.MX X 1 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hmMX)
      rw [hmapMX]
    · have hmapMX : (t.MX X 1).map (MulAut.conj m).toMonoidHom = t.MX X (-1) :=
        map_MX_of_swap (t := t) hmN hswap.1
      rw [hmapMX, hP_eq]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapP

theorem ArcL.arcL_of_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) {R : Subgroup G} (hR : R ≠ ⊥)
    (hRw : R ≤ t.Gw (-1) 1) (hM : t.MX X 1 ≤ normalizer (R : Set G))
    (hK : t.K ≤ normalizer (R : Set G)) {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hsR : s ∈ normalizer (R : Set G))
    (hpair : (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0) :
    t.ArcL R := by
  have hGm : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
    simpa using t.Gw_sub_one_add_one 0
  have hRle : R ≤ t.Gv 0 ⊓ t.Gv 1 := by
    rw [hGm] at hRw
    exact hRw.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hRle' : R ≤ t.Gv 1 ⊓ t.Gv 0 ⊓ t.Gv (-1) := by
    rw [hGm] at hRw
    exact hRw.trans (le_of_eq (by ac_rfl))
  have htrans0 : CosetTrans (normalizer (R : Set G)) (t.Gv 1) (t.Gv 0) :=
    CosetTrans.of_le_inf hX.trans₀ hM
  have hmapM : (t.MX X 1).map (MulAut.conj s).toMonoidHom = t.MX X (-1) :=
    map_MX_of_swap (t := t) hs0.1 hs.1
  have hmapNR : (normalizer (R : Set G)).map (MulAut.conj s).toMonoidHom =
      normalizer (R : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsR)
  have hMXm : t.MX X (-1) ≤ normalizer (R : Set G) := by
    rw [← hmapM]
    exact (Subgroup.map_mono hM).trans (le_of_eq hmapNR)
  have htrans2 : CosetTrans (normalizer (R : Set G)) (t.Gv (-1)) (t.Gv 0) :=
    CosetTrans.of_le_inf hX.trans₂ hMXm
  have hpairR : ∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
      t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1) := by
    rcases hpair with hpair | hcover
    · exact hpair
    · exfalso
      have h0 : CosetTrans (normalizer (R : Set G)) (t.Gv 0) (t.Gv 1) := by
        have h := cosetTrans_zero_of_le_sup (t := t) hfr
          (H := normIn R (t.Gv 0)) inf_le_right hcover
        exact CosetTrans.of_le_inf h (inf_le_left.trans inf_le_left)
      exact hR (eq_bot_of_cosetTrans (t := t) hfr hRle h0 htrans0)
  refine ⟨hR, hRle', hK, htrans0, htrans2, hpairR, ?_⟩
  exact ⟨s, Subgroup.mem_inf.mpr ⟨hsR, hs0.2⟩, hs⟩

private theorem ArcL.mem_normalizer_pX_of_swap {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {s : G}
    (hsM0 : s ∈ t.MX X 0) (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    s ∈ normalizer (t.PX X : Set G) := by
  classical
  have hsN : s ∈ normalizer (X : Set G) := hsM0.1
  have hsG0 : s ∈ t.Gv 0 := hsM0.2
  set u : G := t.x₁⁻¹ * s with hu_def
  have hu : u ∈ t.Gv 1 ⊓ t.Gv (-1) := by simpa [hu_def] using hs
  have hs_eq : s = t.x₁ * u := by rw [hu_def]; group
  have hNconj : conjSub s (normalizer (X : Set G)) = normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := normalizer (X : Set G)) hsN)
  have hQ0 : conjSub s (t.Qv 0) = t.Qv 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.Gv_le_normalizer_Qv 0 hsG0)
  have huN : (t.Gv 1).map (MulAut.conj u).toMonoidHom = t.Gv 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((t.Gv 1).le_normalizer hu.1)
  have hcomp : (MulAut.conj s).toMonoidHom =
      (MulAut.conj t.x₁).toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hs_eq]
    group
  have hG1conj : conjSub s (t.Gv 1) = t.Gv (-1) := by
    show (t.Gv 1).map (MulAut.conj s).toMonoidHom = t.Gv (-1)
    rw [hcomp, ← Subgroup.map_map, huN, t.map_Gv_x₁]
  have hPeq : t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv (-1)) = t.PX X := by
    refine le_antisymm ?_ ?_
    · refine le_inf inf_le_left ?_
      exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans (t.Qv_le_Gv hfr 0).2)
    · exact le_inf inf_le_left
        (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans (t.Qv_le_Gv hfr 0).1))
  have hPs : conjSub s (t.PX X) = t.PX X := by
    rw [show t.PX X = t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv 1) from rfl,
      conjSub_inf, hQ0, conjSub_inf, hNconj, hG1conj, hPeq]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPs

private theorem isSylowTwoOf_of_normalizer_le {U C X : Subgroup G} (hUC : U ≤ C)
    (hU : IsPGroup 2 U) (hNX : C ⊓ normalizer (U : Set G) ≤ X)
    (hsyl : IsSylowTwoOf U X) : IsSylowTwoOf U C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hUS⟩ := A4.exists_isSylowTwoOf_ge hUC hU
  have hSU : S ≤ U := by
    by_contra hSU
    have hlt : U.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hSU
      intro x hx
      have hx' : (⟨x, hx⟩ : S) ∈ U.subgroupOf S := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp hx'
    haveI : Group.IsNilpotent ↥S := hS.2.1.isNilpotent
    have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
    obtain ⟨x, hxN, hxU⟩ := SetLike.exists_of_lt (hnc (U.subgroupOf S) hlt)
    have hxS : (x : G) ∈ S := x.2
    have hxNorm : (x : G) ∈ normalizer (U : Set G) := by
      have hxsub : x ∈ (normalizer (U : Set G)).subgroupOf S := by
        rw [Subgroup.subgroupOf_normalizer_eq hUS]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp hxsub
    have hxX : (x : G) ∈ X := hNX (Subgroup.mem_inf.mpr ⟨hS.1 hxS, hxNorm⟩)
    have hz2 : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      hS.2.1.to_le (Subgroup.zpowers_le.mpr hxS)
    have hVp : IsPGroup 2 (Subgroup.zpowers (x : G) ⊔ U : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (p := 2) hz2 hU
        (Subgroup.zpowers_le.mpr hxNorm)
    have hVX : (Subgroup.zpowers (x : G) ⊔ U : Subgroup G) ≤ X :=
      sup_le (Subgroup.zpowers_le.mpr hxX) hsyl.1
    have hle := (A4.isSylowTwoOf_iff_maximal.mp hsyl).2.2
      (Subgroup.zpowers (x : G) ⊔ U : Subgroup G) hVX hVp le_sup_right
    exact hxU (Subgroup.mem_subgroupOf.mpr
      (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers (x : G)))))
  have hSUeq : S = U := le_antisymm hSU hUS
  rwa [hSUeq] at hS

private theorem ArcLMax.arcL_of_char
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hpair : ∀ R : Subgroup G, t.K ≤ normalizer (R : Set G) → (∃ s ∈ normIn R (t.Gv 0),
        t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) → (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0)
    {C : Subgroup G} (hCP : C ≤ t.PX X) (hCne : C ≠ ⊥)
    (hCchar : (C.subgroupOf (t.PX X)).Characteristic)
    (hM1norm : t.MX X 1 ≤ normalizer (C : Set G)) :
    t.ArcL C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := t.PX X
  have hGm : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
    simpa using t.Gw_sub_one_add_one 0
  have hCw : C ≤ t.Gw (-1) 1 := by
    rw [hGm]
    exact le_inf (le_inf (hCP.trans (inf_le_left.trans (t.Qv_le_Gv hfr 0).1))
      (hCP.trans (inf_le_left.trans (t.Qv_le_Gv_self 0))))
      (hCP.trans (inf_le_left.trans (t.Qv_le_Gv hfr 0).2))
  have hKN : t.K ≤ normalizer (P : Set G) := by
    have hQ := (t.K_le_Gv 0).trans (t.Gv_le_normalizer_Qv 0)
    have hB : t.K ≤ normalizer (t.MX X 1) := by
      have hNN : t.K ≤ normalizer (normalizer (X : Set G) : Set G) :=
        hX.1.K_le.trans (Subgroup.le_normalizer (H := normalizer (X : Set G)))
      have hNG1 : t.K ≤ normalizer (t.Gv 1) := (t.K_le_Gv 1).trans Subgroup.le_normalizer
      have h := (le_inf hNN hNG1).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := normalizer (X : Set G))
          (K := t.Gv 1))
      simpa [Track.MX, normIn] using h
    have h := (le_inf hQ hB).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.Qv 0) (K := t.MX X 1))
    have hPdef : P = t.Qv 0 ⊓ (normalizer (X : Set G) ⊓ t.Gv 1) := rfl
    rw [hPdef]
    exact h
  have hCnormP : normalizer (P : Set G) ≤ normalizer (C : Set G) := by
    haveI : (C.subgroupOf P).Characteristic := hCchar
    have hmap : (C.subgroupOf P).map P.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := P) (K := C.subgroupOf P)
    rwa [hmap] at h
  have hKC : t.K ≤ normalizer (C : Set G) := hKN.trans hCnormP
  obtain ⟨s, hsM0, -, hsx, -, -⟩ :=
    ArcL.exists_swap (t := t) (a := a) (f := f) hfr hX.1
  have hsP : s ∈ normalizer (P : Set G) :=
    ArcL.mem_normalizer_pX_of_swap (t := t) hfr hsM0 hsx
  have hsC : s ∈ normalizer (C : Set G) := hCnormP hsP
  have hs_normC : s ∈ normIn C (t.Gv 0) := Subgroup.mem_inf.mpr ⟨hsC, hsM0.2⟩
  have hpairC := hpair C hKC ⟨s, hs_normC, hsx⟩
  exact ArcL.arcL_of_le (t := t) hfr hX.1 hCne hCw hM1norm hKC hsM0 hsx hsC hpairC

private theorem ArcLMax.MX_eq_of_char
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hpair : ∀ R : Subgroup G, t.K ≤ normalizer (R : Set G) → (∃ s ∈ normIn R (t.Gv 0),
        t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) → (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0)
    {C : Subgroup G} (hCP : C ≤ t.PX X) (hCne : C ≠ ⊥)
    (hCchar : (C.subgroupOf (t.PX X)).Characteristic)
    (hM1norm : t.MX X 1 ≤ normalizer (C : Set G)) :
    t.MX C 1 = t.MX X 1 := by
  have hC2 : IsPGroup 2 C := (t.isPGroup_Qv 0).to_le (hCP.trans inf_le_left)
  have hCArc : t.ArcL C :=
    ArcLMax.arcL_of_char (t := t) hfr hX hpair hCP hCne hCchar hM1norm
  have hMXle : t.MX X 1 ≤ t.MX C 1 :=
    le_inf hM1norm (inf_le_right : t.MX X 1 ≤ t.Gv 1)
  exact le_antisymm (hX.2.2 C hCArc hC2 hMXle) hMXle

private theorem ArcLMax.normalizer_pX_le_MX_one
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hpair : ∀ R : Subgroup G, t.K ≤ normalizer (R : Set G) → (∃ s ∈ normIn R (t.Gv 0),
        t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) → (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0)
    {C : Subgroup G} (hCP : C ≤ t.PX X) (hCne : C ≠ ⊥)
    (hCchar : (C.subgroupOf (t.PX X)).Characteristic)
    (hM1norm : t.MX X 1 ≤ normalizer (C : Set G)) :
    t.Gv 1 ⊓ normalizer (t.PX X : Set G) ≤ t.MX X 1 := by
  let P : Subgroup G := t.PX X
  have hCnormP : normalizer (P : Set G) ≤ normalizer (C : Set G) := by
    haveI : (C.subgroupOf P).Characteristic := hCchar
    have hmap : (C.subgroupOf P).map P.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := P) (K := C.subgroupOf P)
    rwa [hmap] at h
  have hMXeq : t.MX C 1 = t.MX X 1 :=
    ArcLMax.MX_eq_of_char (t := t) hfr hX hpair hCP hCne hCchar hM1norm
  intro x hx
  obtain ⟨hxG1, hxNP⟩ := Subgroup.mem_inf.mp hx
  have hxMC : x ∈ t.MX C 1 := Subgroup.mem_inf.mpr ⟨hCnormP hxNP, hxG1⟩
  rwa [hMXeq] at hxMC

private theorem ArcLMax.isSylowTwoOf_pX_Gv_one
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hpair : ∀ R : Subgroup G, t.K ≤ normalizer (R : Set G) → (∃ s ∈ normIn R (t.Gv 0),
        t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) → (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0)
    {C : Subgroup G} (hCP : C ≤ t.PX X) (hCne : C ≠ ⊥)
    (hCchar : (C.subgroupOf (t.PX X)).Characteristic)
    (hM1norm : t.MX X 1 ≤ normalizer (C : Set G)) :
    IsSylowTwoOf (t.PX X) (t.Gv 1) := by
  let P : Subgroup G := t.PX X
  have hP2 : IsPGroup 2 P := (t.isPGroup_Qv 0).to_le inf_le_left
  have hPleG1 : P ≤ t.Gv 1 := inf_le_right.trans inf_le_right
  exact isSylowTwoOf_of_normalizer_le (U := P) (C := t.Gv 1) (X := t.MX X 1)
    hPleG1 hP2
    (ArcLMax.normalizer_pX_le_MX_one (t := t) hfr hX hpair hCP hCne hCchar hM1norm)
    (ArcL.isSylowTwoOf_pX_one (t := t) hfr hX.1)

theorem ArcLMax.noCharNormal
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hpair : ∀ R : Subgroup G, t.K ≤ normalizer (R : Set G) → (∃ s ∈ normIn R (t.Gv 0),
        t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) → (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0) :
    NoCharNormal (t.PX X) (t.MX X 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro C hCP hCne hCchar hM1norm
  let P : Subgroup G := t.PX X
  have hSylP_G1 : IsSylowTwoOf P (t.Gv 1) :=
    ArcLMax.isSylowTwoOf_pX_Gv_one (t := t) hfr hX hpair hCP hCne hCchar hM1norm
  have hQ0Gw : t.Qv 0 ≤ t.Gw 0 1 := by
    rw [show t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 from by simpa using t.Gw_add_one 0]
    exact le_inf (t.Qv_le_Gv_self 0) (t.Qv_le_Gv hfr 0).2
  have hQ0S : t.Qv 0 ≤ pCoreOf 2 (t.Gw 0 1) :=
    t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Qv 0) hQ0Gw
  have hPleS : P ≤ pCoreOf 2 (t.Gw 0 1) := inf_le_left.trans hQ0S
  have hSG1 : pCoreOf 2 (t.Gw 0 1) ≤ t.Gv 1 :=
    (pCoreOf_le 2 _).trans (win_le_qv (by norm_num) le_rfl)
  have hS2 : IsPGroup 2 (pCoreOf 2 (t.Gw 0 1)) := pCoreOf_isPGroup 2 _
  have hSleP : pCoreOf 2 (t.Gw 0 1) ≤ P :=
    (A4.isSylowTwoOf_iff_maximal.mp hSylP_G1).2.2 _ hSG1 hS2 hPleS
  have hSleQ0 : pCoreOf 2 (t.Gw 0 1) ≤ t.Qv 0 := hSleP.trans inf_le_left
  have hrel : (t.Qv 0).relIndex (pCoreOf 2 (t.Gw 0 1)) = (2 ^ (2 * a + 1)) ^ 2 := by
    simpa using (t.relIndex_Qv_pCoreOf hfr 0).2
  have hrel1 : (t.Qv 0).relIndex (pCoreOf 2 (t.Gw 0 1)) = 1 :=
    Subgroup.relIndex_eq_one.mpr hSleQ0
  rw [hrel1] at hrel
  have hq : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  have hsq : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    have h := Nat.pow_le_pow_left hq 2
    norm_num at h ⊢
    exact h
  omega

theorem exists_arcLMax (hX : t.ArcL X) (hX2 : IsPGroup 2 X) :
    ∃ Y, t.ArcLMax Y ∧ t.MX X 1 ≤ t.MX Y 1 := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) (by
      intro H K h
      exact Subgroup.ext (fun x => by simpa using Set.ext_iff.mp h x))
  let S : Set (Subgroup G) :=
    {Y | t.ArcL Y ∧ IsPGroup 2 Y ∧ t.MX X 1 ≤ t.MX Y 1}
  have hSne : S.Nonempty := ⟨X, hX, hX2, le_rfl⟩
  obtain ⟨Y, hYS, hYmax⟩ := (Set.toFinite S).exists_maximalFor
    (f := fun Y : Subgroup G => Nat.card (t.MX Y 1)) S hSne
  obtain ⟨hYclass, hY2, hXY⟩ := hYS
  refine ⟨Y, ?_, hXY⟩
  simp only [IsArcClassMax]
  refine ⟨hYclass, hY2, ?_⟩
  intro Z hZclass hZ2 hYZ
  have hZS : Z ∈ S := ⟨hZclass, hZ2, hXY.trans hYZ⟩
  have hcardY : Nat.card (t.MX Y 1) ≤ Nat.card (t.MX Z 1) :=
    Subgroup.card_le_of_le hYZ
  have hcardZ : Nat.card (t.MX Z 1) ≤ Nat.card (t.MX Y 1) := hYmax hZS hcardY
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hYZ hcardZ).symm

theorem exists_arcSzMax {X : Subgroup G} (hX : t.ArcSz X) (hX2 : IsPGroup 2 X) :
    ∃ Y, t.ArcSzMax Y ∧ t.MX X 0 ≤ t.MX Y 0 := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) (by
      intro H K h
      exact Subgroup.ext (fun x => by simpa using Set.ext_iff.mp h x))
  let S : Set (Subgroup G) :=
    {Y | t.ArcSz Y ∧ IsPGroup 2 Y ∧ t.MX X 0 ≤ t.MX Y 0}
  have hSne : S.Nonempty := ⟨X, hX, hX2, le_rfl⟩
  obtain ⟨Y, hYS, hYmax⟩ := (Set.toFinite S).exists_maximalFor
    (f := fun Y : Subgroup G => Nat.card (t.MX Y 0)) S hSne
  obtain ⟨hYclass, hY2, hXY⟩ := hYS
  refine ⟨Y, ?_, hXY⟩
  simp only [IsArcClassMax]
  refine ⟨hYclass, hY2, ?_⟩
  intro Z hZclass hZ2 hYZ
  have hZS : Z ∈ S := ⟨hZclass, hZ2, hXY.trans hYZ⟩
  have hcardY : Nat.card (t.MX Y 0) ≤ Nat.card (t.MX Z 0) :=
    Subgroup.card_le_of_le hYZ
  have hcardZ : Nat.card (t.MX Z 0) ≤ Nat.card (t.MX Y 0) := hYmax hZS hcardY
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hYZ hcardZ).symm

end Track

end CFSG.Quasithin.Stroth.Rq

end
