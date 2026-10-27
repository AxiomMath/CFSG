module

public import CFSG.Quasithin.Recognition.St84.Sec46Cases
public import CFSG.Quasithin.Recognition.St84.Sec4Local
public import CFSG.Quasithin.Recognition.St84.Sec4Data
public import CFSG.GroupTheory.Commutator.JoinNormalizer

import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qOfCaseB
import CFSG.Quasithin.Recognition.St84.Gen.NatSecIndex
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.St84.Sec4TreeData
public import CFSG.Quasithin.Recognition.St84.Sec6QQuot

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

private theorem caseB_r_eq_four_or_eight (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) (hodd : Odd d₁) :
    2 * d₁ + 2 = r ∧ d₀ ≤ 2 ∧ (r = 4 ∨ r = 8) := by
  have hd₁' : X.HasB (d₁ + 1) d₀ := by
    refine (X.hasB_iff_of_even (i := (d₁ : ℤ) + 1) (j := 0) ?_ d₀).mpr hd₀
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have h1 : 2 * d₁ + d₀ ≤ r := X.s46_step1 H hd₁ hd₁' hR hR1
  have h2 := X.hasB_one_bounds H hd₁
  have h3 := X.hasB_zero_bounds H hd₀
  have h0 : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  have hr4 : 4 ≤ r := by
    have h5 := H.five_le
    have hl := H.le_r
    omega
  have hrev : 2 * d₁ + 2 = r := by
    obtain ⟨m, hm⟩ := H.even_r
    have := h2.1
    omega
  have hd2 : d₀ ≤ 2 := by omega
  have h4dvd : 4 ∣ r := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  refine ⟨hrev, hd2, ?_⟩
  have h8 : r ≤ 8 := by omega
  obtain ⟨m, hm⟩ := h4dvd
  omega

private theorem caseB_eight_sup_eq_edgeSylow (X : Setup Γ G) (H : X.Sec4Hyp s 8)
    (hd₁ : X.HasB 1 3) (hZ2 : X.HasB 2 2) (hZ4 : X.HasB 4 2) (hZ1Gi3 : X.Z 1 ≤ X.Gi 3)
    (hZ1Gi4 : X.Z 1 ≤ X.Gi 4) (hZ2Gi3 : X.Z 2 ≤ X.Gi 3) (hZ2Gi4 : X.Z 2 ≤ X.Gi 4)
    (hZ4Gi2 : X.Z 4 ≤ X.Gi 2) (hZ4Gi3 : X.Z 4 ≤ X.Gi 3) :
    X.Z 1 ⊔ X.Q 4 = X.edgeSylow 3 ∧ X.Z 2 ⊔ X.Q 4 = X.edgeSylow 3 ∧
      X.Z 4 ⊔ X.Q 2 = X.edgeSylow 2 := by
  have hZ1notQ4 : ¬ X.Z 1 ≤ X.Q 4 := (X.not_Z_le_Q_edge hd₁).1
  have hZ2notQ4 : ¬ X.Z 2 ≤ X.Q 4 := (X.not_Z_le_Q_edge hZ2).1
  have hZ4notQ2 : ¬ X.Z 4 ≤ X.Q 2 := (X.not_Z_le_Q_edge hZ4).2
  have hZ1edge3 : X.Z 1 ≤ X.edgeSylow 3 := X.le_edgeSylow_of_le_inf 3
    ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)) (le_inf hZ1Gi3 hZ1Gi4)
  have hZ2edge3 : X.Z 2 ≤ X.edgeSylow 3 := X.le_edgeSylow_of_le_inf 3
    ((pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)) (le_inf hZ2Gi3 hZ2Gi4)
  have hZ4edge2 : X.Z 4 ≤ X.edgeSylow 2 := X.le_edgeSylow_of_le_inf 2
    ((pCoreOf_isPGroup' (X.Gi 4)).to_le (X.Z_le_Q 4)) (le_inf hZ4Gi2 hZ4Gi3)
  have hKZ1 : X.K ≤ Subgroup.normalizer (X.Z 1 : Set G) :=
    fun k hk => mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 k (X.K_le_Gi 1 hk))
  have hKZ2 : X.K ≤ Subgroup.normalizer (X.Z 2 : Set G) :=
    fun k hk => mem_normalizer_iff_conjSub.mpr (X.Z_normal 2 k (X.K_le_Gi 2 hk))
  have hKZ4 : X.K ≤ Subgroup.normalizer (X.Z 4 : Set G) :=
    fun k hk => mem_normalizer_iff_conjSub.mpr (X.Z_normal 4 k (X.K_le_Gi 4 hk))
  have hsupZ1 : X.Z 1 ⊔ X.Q 4 = X.edgeSylow 3 :=
    X.sup_Q_eq_edgeSylow_of_gen (A := X.Z 1) 3 (inf_le_left.trans hKZ1) hZ1edge3 hZ1notQ4
  have hsupZ2 : X.Z 2 ⊔ X.Q 4 = X.edgeSylow 3 :=
    X.sup_Q_eq_edgeSylow_of_gen (A := X.Z 2) 3 (inf_le_left.trans hKZ2) hZ2edge3 hZ2notQ4
  have hsupZ4Q2 : X.Z 4 ⊔ X.Q 2 = X.edgeSylow 2 :=
    X.sup_Q_eq_edgeSylow_of_left_gen (A := X.Z 4) 2 (inf_le_left.trans hKZ4) hZ4edge2
      hZ4notQ2
  exact ⟨hsupZ1, hsupZ2, hsupZ4Q2⟩

private theorem caseB_eight_R_eq_pCoreOf (X : Setup Γ G) (H : X.Sec4Hyp s 8)
    (hd₁ : X.HasB 1 3) (hZ4 : X.HasB 4 2) (hR4 : ⁅X.Z 1, X.Z 4⁆ ≤ X.Z 1 ⊓ X.Z 4)
    (hR4ne : ⁅X.Z 1, X.Z 4⁆ ≠ ⊥) : ⁅X.Z 1, X.Z 4⁆ = pCoreOf 2 (X.arcStab (-2) 6) := by
  have hRarc : ⁅X.Z 1, X.Z 4⁆ ≤ X.arcStab (-2) 6 := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro q hq
    have hZ1 := X.fixSet_Z 1 hd₁
    have hZ4' := X.fixSet_Z 4 hZ4
    by_cases hj4 : j ≤ 4
    · have hmem : j ∈ X.fixSet (X.Z 1) := by
        rw [hZ1, Set.mem_Icc]
        omega
      exact hmem q (hR4.trans inf_le_left hq)
    · have hmem : j ∈ X.fixSet (X.Z 4) := by
        rw [hZ4', Set.mem_Icc]
        omega
      exact hmem q (hR4.trans inf_le_right hq)
  have hR2g : IsPGroup 2 (⁅X.Z 1, X.Z 4⁆ : Subgroup G) :=
    ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)).to_le (hR4.trans inf_le_left)
  have hRK : X.K ≤ Subgroup.normalizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (⁅X.Z 1, X.Z 4⁆ : Subgroup G).map (MulAut.conj k).toMonoidHom = ⁅X.Z 1, X.Z 4⁆
    have h1 : (X.Z 1).map (MulAut.conj k).toMonoidHom = X.Z 1 :=
      X.Z_normal 1 k (X.K_le_Gi 1 hk)
    have h4 : (X.Z 4).map (MulAut.conj k).toMonoidHom = X.Z 4 :=
      X.Z_normal 4 k (X.K_le_Gi 4 hk)
    rw [Subgroup.map_commutator, h1, h4]
  have hRleP : ⁅X.Z 1, X.Z 4⁆ ≤ pCoreOf 2 (X.arcStab (-2) 6) := by
    have h := X.le_pCoreOf_arcStab_r H (a := -2) hR2g (by simpa using hRarc)
    simpa using h
  have h := X.eq_of_le_pCoreOf_arcStab_r H (a := -2) hRK hR4ne (by simpa using hRleP)
  simpa using h

private theorem caseB_eight_reflection (X : Setup Γ G) (H : X.Sec4Hyp s 8)
    (hReqP : ⁅X.Z 1, X.Z 4⁆ = pCoreOf 2 (X.arcStab (-2) 6)) :
    ∃ t : G, (∀ k : ℤ, conjSub t (X.Z k) = X.Z (4 - k)) ∧
      conjSub t (X.edgeSylow 2) = X.edgeSylow 1 ∧
      conjSub t ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 1, X.Z 4⁆ := by
  obtain ⟨t, -, htref⟩ := X.exists_reflection H 2
  have hconjZ (k : ℤ) : conjSub t (X.Z k) = X.Z (4 - k) := by
    have h := X.Z_smul X (show t • X.vert k = X.vert (4 - k) from by
      have hh := htref (k - 2)
      simpa [show 2 + (k - 2) = k by ring, show 2 - (k - 2) = 4 - k by ring] using hh)
    exact h.symm
  have hconjGi : ∀ k : ℤ, conjSub t (X.Gi k) = X.Gi (4 - k) := by
    intro k
    rw [← stabilizer_smul_eq_conjSub,
      show t • X.vert k = X.vert (4 - k) from by
        have hh := htref (k - 2)
        simpa [show 2 + (k - 2) = k by ring, show 2 - (k - 2) = 4 - k by ring] using hh]
  have hconjE2 : conjSub t (X.edgeSylow 2) = X.edgeSylow 1 := by
    unfold Setup.edgeSylow
    rw [← pCoreOf_conjSub, conjSub_inf]
    have h2 : conjSub t (X.Gi 2) = X.Gi (4 - 2) := hconjGi 2
    have h3 : conjSub t (X.Gi (2 + 1)) = X.Gi (4 - 3) := by simpa using hconjGi 3
    rw [h2, h3]
    norm_num
    rw [inf_comm]
  have harcP : conjSub t (X.arcStab (-2) 6) = X.arcStab (-2) 6 := by
    have h := X.conjSub_arcStab_of_reflection (i := 2) (a := -2) (c := 6) (t := t) htref
    simpa using h
  have hPt : conjSub t (pCoreOf 2 (X.arcStab (-2) 6)) =
      pCoreOf 2 (X.arcStab (-2) 6) := by
    rw [← pCoreOf_conjSub, harcP]
  have hRt : conjSub t ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 1, X.Z 4⁆ := by
    rw [hReqP]
    exact hPt
  exact ⟨t, hconjZ, hconjE2, hRt⟩

private theorem caseB_eight_R_eq_commutator_Z_two (X : Setup Γ G)
    (hZ1Gi4 : X.Z 1 ≤ X.Gi 4) (hZ2Gi4 : X.Z 2 ≤ X.Gi 4)
    (hsupZ1 : X.Z 1 ⊔ X.Q 4 = X.edgeSylow 3) (hsupZ2 : X.Z 2 ⊔ X.Q 4 = X.edgeSylow 3) :
    ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 2, X.Z 4⁆ := by
  have hQ4normZ2 : X.Z 2 ≤ Subgroup.normalizer (X.Q 4 : Set G) :=
    hZ2Gi4.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4))
  have hQ4normZ1 : X.Z 1 ≤ Subgroup.normalizer (X.Q 4 : Set G) :=
    hZ1Gi4.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4))
  have hZ4cenQ4 : ∀ q ∈ X.Q 4, ∀ z ∈ X.Z 4, q * z = z * q := by
    intro q hq z hz
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 4 hz)).2 q hq
  have hRle : ⁅X.Z 1, X.Z 4⁆ ≤ ⁅X.Z 2, X.Z 4⁆ := by
    refine Subgroup.commutator_le.mpr ?_
    intro x hx z hz
    have hx' : x ∈ X.Z 2 ⊔ X.Q 4 := by
      rw [hsupZ2, ← hsupZ1]
      exact Subgroup.mem_sup_left hx
    obtain ⟨y, hy, q, hq, hxq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ4normZ2).mp hx'
    have hqz : ⁅q, z⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hZ4cenQ4 q hq z hz
    have e : ⁅x, z⁆ = ⁅y, z⁆ := by
      rw [hxq, commutatorElement_mul_left_eq_conj_mul, hqz]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator hy hz
  have hRge : ⁅X.Z 2, X.Z 4⁆ ≤ ⁅X.Z 1, X.Z 4⁆ := by
    refine Subgroup.commutator_le.mpr ?_
    intro y hy z hz
    have hy' : y ∈ X.Z 1 ⊔ X.Q 4 := by
      rw [hsupZ1, ← hsupZ2]
      exact Subgroup.mem_sup_left hy
    obtain ⟨x, hx, q, hq, hyq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ4normZ1).mp hy'
    have hqz : ⁅q, z⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hZ4cenQ4 q hq z hz
    have e : ⁅y, z⁆ = ⁅x, z⁆ := by
      rw [hyq, commutatorElement_mul_left_eq_conj_mul, hqz]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator hx hz
  exact le_antisymm hRle hRge

private theorem caseB_eight_centralizer_R (X : Setup Γ G)
    (hR4 : ⁅X.Z 1, X.Z 4⁆ ≤ X.Z 1 ⊓ X.Z 4) (hReq : ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 2, X.Z 4⁆)
    (hcommZ2Z4 : ⁅X.Z 2, X.Z 4⁆ ≤ X.Z 2) (hsupQ : X.Q 2 ⊔ X.Q 3 = X.edgeSylow 2)
    (hQ3leZ4Q2 : X.Q 3 ≤ X.Z 4 ⊔ X.Q 2) {t : G}
    (hconjE2 : conjSub t (X.edgeSylow 2) = X.edgeSylow 1)
    (hRt : conjSub t ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 1, X.Z 4⁆) :
    X.Q 2 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) ∧
      X.Q 3 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) ∧
      X.edgeSylow 1 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) ∧
      X.edgeSylow 2 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) := by
  have hRcenZ4 : ⁅X.Z 1, X.Z 4⁆ ≤ Subgroup.centralizer (X.Z 4 : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (X.Z_commute 4 r (hR4.trans inf_le_right hr) z hz).symm
  have hRcenQ2 : ⁅X.Z 1, X.Z 4⁆ ≤ Subgroup.centralizer (X.Q 2 : Set G) := by
    rw [hReq]
    refine hcommZ2Z4.trans ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2 q hq
  have hQ2cenR : X.Q 2 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) :=
    Subgroup.le_centralizer_iff.mpr hRcenQ2
  have hQ3cenR : X.Q 3 ≤
      Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) := by
    refine hQ3leZ4Q2.trans ?_
    exact sup_le (Subgroup.le_centralizer_iff.mpr hRcenZ4) hQ2cenR
  have hE2cenR : X.edgeSylow 2 ≤
      Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) := by
    rw [← hsupQ]
    exact sup_le hQ2cenR hQ3cenR
  have hE1cenR : X.edgeSylow 1 ≤
      Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) := by
    have h := conjSub_mono t hE2cenR
    rw [hconjE2, ← conjSub_centralizer, hRt] at h
    exact h
  exact ⟨hQ2cenR, hQ3cenR, hE1cenR, hE2cenR⟩

private theorem caseB_eight_commutator_Z_two_L_two_le (X : Setup Γ G)
    (hReq : ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 2, X.Z 4⁆) (hsupQ : X.Q 2 ⊔ X.Q 3 = X.edgeSylow 2)
    (hQ3leZ4Q2 : X.Q 3 ≤ X.Z 4 ⊔ X.Q 2) (hZ4Gi2 : X.Z 4 ≤ X.Gi 2) {t : G}
    (hconjZ : ∀ k : ℤ, conjSub t (X.Z k) = X.Z (4 - k))
    (hconjE2 : conjSub t (X.edgeSylow 2) = X.edgeSylow 1)
    (hRt : conjSub t ⁅X.Z 1, X.Z 4⁆ = ⁅X.Z 1, X.Z 4⁆)
    (hQ2cenR : X.Q 2 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)))
    (hQ3cenR : X.Q 3 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)))
    (hE1cenR :
      X.edgeSylow 1 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)))
    (hE2cenR :
      X.edgeSylow 2 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G))) :
    ⁅X.Z 2, X.L 2⁆ ≤ ⁅X.Z 1, X.Z 4⁆ := by
  have hQ2N : X.Q 2 ≤ Subgroup.normalizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) :=
    hQ2cenR.trans (Subgroup.centralizer_le_normalizer _)
  have hQ3N : X.Q 3 ≤ Subgroup.normalizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) :=
    hQ3cenR.trans (Subgroup.centralizer_le_normalizer _)
  have hZ2cenQ2 : X.Z 2 ≤ Subgroup.centralizer (X.Q 2 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2 q hq
  have hZjQ2 : ⁅X.Z 2, X.Q 2⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZ2cenQ2
  have hZ4normQ2 : X.Z 4 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    hZ4Gi2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hZjQ3 : ⁅X.Z 2, X.Q 3⁆ ≤ ⁅X.Z 1, X.Z 4⁆ := by
    refine Subgroup.commutator_le.mpr ?_
    intro y hy q hq
    obtain ⟨z, hz, u, hu, hzu⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZ4normQ2).mp
        (hQ3leZ4Q2 hq)
    have huy : ⁅y, u⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 2 hy)).2 u hu).symm
    have e : ⁅y, q⁆ = ⁅y, z⁆ := by
      rw [hzu, commutatorElement_mul_right_eq_mul_conj, huy]
      group
    rw [e, hReq]
    exact Subgroup.commutator_mem_commutator hy hz
  have hZjQ2le : ⁅X.Z 2, X.Q 2⁆ ≤ ⁅X.Z 1, X.Z 4⁆ := by
    rw [hZjQ2]
    exact bot_le
  have hE2comm : ⁅X.Z 2, X.edgeSylow 2⁆ ≤ ⁅X.Z 1, X.Z 4⁆ := by
    rw [← hsupQ]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hQ2N hQ3N hZjQ2le hZjQ3
  have hE1comm : ⁅X.Z 2, X.edgeSylow 1⁆ ≤ ⁅X.Z 1, X.Z 4⁆ := by
    have hmap : conjSub t ⁅X.Z 2, X.edgeSylow 2⁆ = ⁅X.Z 2, X.edgeSylow 1⁆ := by
      change (⁅X.Z 2, X.edgeSylow 2⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = _
      rw [Subgroup.map_commutator]
      have h1 : (X.Z 2).map (MulAut.conj t).toMonoidHom = X.Z 2 := hconjZ 2
      have h2 : (X.edgeSylow 2).map (MulAut.conj t).toMonoidHom = X.edgeSylow 1 := hconjE2
      rw [h1, h2]
    rw [← hmap]
    exact (conjSub_mono t hE2comm).trans (le_of_eq hRt)
  have hE1N : X.edgeSylow 1 ≤ Subgroup.normalizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) :=
    hE1cenR.trans (Subgroup.centralizer_le_normalizer _)
  have hE2N : X.edgeSylow 2 ≤ Subgroup.normalizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) :=
    hE2cenR.trans (Subgroup.centralizer_le_normalizer _)
  rw [← X.edgeSylow_sup_edgeSylow 2]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hE1N hE2N hE1comm hE2comm

private theorem caseB_r_ne_eight (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) (hodd : Odd d₁) : r ≠ 8 := by
  intro hr8
  classical
  obtain ⟨h2d, hd0le, -⟩ := X.caseB_r_eq_four_or_eight H hd₀ hd₁ hR hR1 hodd
  have hd1 : d₁ = 3 := by omega
  have hd0 : d₀ = 2 := by
    have hb := X.hasB_zero_bounds H hd₀
    omega
  subst hd1
  subst hd0
  subst hr8
  have hR4 : ⁅X.Z 1, X.Z 4⁆ ≤ X.Z 1 ⊓ X.Z 4 := by simpa using hR
  have hR4ne : ⁅X.Z 1, X.Z 4⁆ ≠ ⊥ := by simpa using hR1
  have hZ2 : X.HasB 2 2 := by
    have h := (X.hasB_iff_of_even (i := (2 : ℤ)) (j := 0)
      (by exact ⟨1, by norm_num⟩) 2).mpr hd₀
    simpa using h
  have hZ4 : X.HasB 4 2 := by
    have h := (X.hasB_iff_of_even (i := (4 : ℤ)) (j := 0)
      (by exact ⟨2, by norm_num⟩) 2).mpr hd₀
    simpa using h
  have hZ1Gi3 : X.Z 1 ≤ X.Gi 3 := hd₁.Z_le_Gi (by norm_num)
  have hZ1Gi4 : X.Z 1 ≤ X.Gi 4 := hd₁.Z_le_Gi (by norm_num)
  have hZ2Gi3 : X.Z 2 ≤ X.Gi 3 := hZ2.Z_le_Gi (by norm_num)
  have hZ2Gi4 : X.Z 2 ≤ X.Gi 4 := hZ2.Z_le_Gi (by norm_num)
  have hZ4Gi2 : X.Z 4 ≤ X.Gi 2 := hZ4.Z_le_Gi (by norm_num)
  have hZ4Gi3 : X.Z 4 ≤ X.Gi 3 := hZ4.Z_le_Gi (by norm_num)
  obtain ⟨hsupZ1, hsupZ2, hsupZ4Q2⟩ := X.caseB_eight_sup_eq_edgeSylow H hd₁ hZ2 hZ4 hZ1Gi3
    hZ1Gi4 hZ2Gi3 hZ2Gi4 hZ4Gi2 hZ4Gi3
  have hsupQ : X.Q 2 ⊔ X.Q 3 = X.edgeSylow 2 := by
    have h := X.sup_Q_eq_edgeSylow H.char 2
    rwa [show (2 : ℤ) + 1 = 3 by norm_num] at h
  have hReqP := X.caseB_eight_R_eq_pCoreOf H hd₁ hZ4 hR4 hR4ne
  obtain ⟨t, hconjZ, hconjE2, hRt⟩ := X.caseB_eight_reflection H hReqP
  have hReq := X.caseB_eight_R_eq_commutator_Z_two hZ1Gi4 hZ2Gi4 hsupZ1 hsupZ2
  have hcommZ2Z4 : ⁅X.Z 2, X.Z 4⁆ ≤ X.Z 2 := by
    have hZ4normZ2 : X.Z 4 ≤ Subgroup.normalizer (X.Z 2 : Set G) := fun g hg =>
      mem_normalizer_iff_conjSub.mpr (X.Z_normal 2 g (hZ4Gi2 hg))
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hZ4normZ2
  have hQ3leZ4Q2 : X.Q 3 ≤ X.Z 4 ⊔ X.Q 2 := by
    rw [hsupZ4Q2, ← hsupQ]
    exact le_sup_right
  obtain ⟨hQ2cenR, hQ3cenR, hE1cenR, hE2cenR⟩ :=
    X.caseB_eight_centralizer_R hR4 hReq hcommZ2Z4 hsupQ hQ3leZ4Q2 hconjE2 hRt
  have hL2cenR : X.L 2 ≤ Subgroup.centralizer (((⁅X.Z 1, X.Z 4⁆ : Subgroup G) : Set G)) := by
    rw [← X.edgeSylow_sup_edgeSylow 2]
    exact sup_le hE1cenR hE2cenR
  have hRZL2 : ⁅X.Z 1, X.Z 4⁆ ≤ centerOf (X.L 2) := by
    refine le_inf ?_ (Subgroup.le_centralizer_iff.mpr hL2cenR)
    rw [hReq]
    exact hcommZ2Z4.trans (le_oTwoPrime_of_isPGroup
      ((pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)) (X.Z_le_Gi 2))
  have hZjL2 := X.caseB_eight_commutator_Z_two_L_two_le hReq hsupQ hQ3leZ4Q2 hZ4Gi2 hconjZ
    hconjE2 hRt hQ2cenR hQ3cenR hE1cenR hE2cenR
  have hL2comm : X.L 2 = ⁅X.L 2, X.L 2⁆ ⊔ X.Q 2 :=
    X.L_eq_commutator_sup_Q 2 (H.two_le_n 2)
      (X.hyp.isLocL2_oTwoPrime (X.vert 2)).quot
  have hZjL2R : ⁅X.Z 2, X.L 2⁆ ≤ centerOf (X.L 2) := hZjL2.trans hRZL2
  have hZ2Z : X.Z 2 ≤ centerOf (X.L 2) := fun v hv =>
    X.mem_centerOf_L_of_commutator_mem hL2comm (X.Z_le_center 2 hv)
      (fun l hl => hZjL2R (Subgroup.commutator_mem_commutator hv hl))
  have hZ4L2 : X.Z 4 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 4)).to_le (X.Z_le_Q 4)) hZ4Gi2
  have hRbot : ⁅X.Z 1, X.Z 4⁆ = ⊥ := by
    rw [hReq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hZ2Z.trans inf_le_right).trans
      (Subgroup.centralizer_le (by intro z hz; exact hZ4L2 hz))
  exact hR4ne hRbot

private theorem not_r4_b2 (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) (hodd : Odd d₁) (hr : r = 4) :
    d₀ ≠ 2 := by
  intro hd0
  classical
  subst hr
  have h6 := X.caseB_r_eq_four_or_eight H hd₀ hd₁ hR hR1 hodd
  obtain ⟨h2d, -, -⟩ := h6
  have hd1 : d₁ = 1 := by omega
  have hd2 : X.HasB 2 d₀ := by
    refine (X.hasB_iff_of_even (i := (2 : ℤ)) (j := 0) ?_ d₀).mpr hd₀
    norm_num
  haveI : Finite ↥(X.Z 2) := finite_of_le_stabilizer X.hyp (H := X.Z 2) (X.Z_le_Gi 2)
  haveI : Finite ↥(X.L 2) := finite_of_le_stabilizer X.hyp (H := X.L 2) (X.L_le_Gi 2)
  have hZ2arc : X.Z 2 ≤ X.arcStab 0 ((4 : ℕ) : ℤ) := by
    refine X.le_arcStab_of_fixSet ?_
    intro k hk
    rw [X.fixSet_Z 2 hd2, hd0]
    rw [Set.mem_Icc] at hk ⊢
    constructor <;> omega
  have hZ2p : X.Z 2 ≤ pCoreOf 2 (X.arcStab 0 (4 : ℕ)) := by
    refine X.le_pCoreOf_arcStab_r H ((pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)) ?_
    simpa using hZ2arc
  have hZ2card : Nat.card (X.Z 2) ≤ 2 ^ X.n 0 := by
    by_cases hbot : pCoreOf 2 (X.arcStab 0 (4 : ℕ)) = ⊥
    · rw [hbot] at hZ2p
      rw [le_bot_iff] at hZ2p
      rw [hZ2p, Subgroup.card_bot]
      exact Nat.one_le_two_pow
    · have h4 : Nat.card (pCoreOf 2 (X.arcStab 0 (4 : ℕ))) = 2 ^ X.n 0 := by
        have h := (X.pCoreOf_arcStab_r H 0 hbot).1
        simpa using h
      haveI : Finite ↥(pCoreOf 2 (X.arcStab 0 (4 : ℕ))) :=
        finite_of_le_stabilizer X.hyp (H := pCoreOf 2 (X.arcStab 0 (4 : ℕ)))
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab 0 (4 : ℕ))).trans
            (X.arcStab_le_Gi_left (show (0 : ℤ) < 4 by norm_num)))
      calc Nat.card (X.Z 2) ≤ Nat.card (pCoreOf 2 (X.arcStab 0 (4 : ℕ))) :=
            Subgroup.card_le_of_le hZ2p
        _ = 2 ^ X.n 0 := h4
  have hq : IsL2Quot (X.n 2) (oTwoQuot ↥(X.L 2)) := (X.hyp.isLocL2_oTwoPrime (X.vert 2)).quot
  have hn20 : X.n 2 = X.n 0 := by simpa using X.n_add 1 0
  have hn0 : 2 ≤ X.n 0 := H.two_le_n 0
  have hQeq : pCoreOf 2 (X.L 2) = X.Q 2 := (X.hyp.isLocL2_oTwoPrime (X.vert 2)).pCoreOf_eq
  have hLNe : X.L 2 ≤ Subgroup.normalizer (X.Z 2 : Set G) :=
    fun l hl => mem_normalizer_iff_conjSub.mpr (X.Z_normal 2 l (X.L_le_Gi 2 hl))
  have hcore : ⁅X.Z 2, pCoreOf 2 (X.L 2)⁆ ≤ ⊥ := by
    rw [hQeq, Subgroup.commutator_le]
    intro z hz q hq
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2 q hq).symm
  have hbot0 : (⊥ : Subgroup G).relIndex (X.Z 2) ≠ 0 := by
    rw [Subgroup.relIndex_bot_left]
    exact Nat.card_pos.ne'
  have hlt : (⊥ : Subgroup G).relIndex (X.Z 2) < 2 ^ (2 * X.n 2) := by
    rw [Subgroup.relIndex_bot_left, hn20]
    calc Nat.card (X.Z 2) ≤ 2 ^ X.n 0 := hZ2card
      _ < 2 ^ (2 * X.n 0) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcomm : ⁅X.Z 2, X.L 2⁆ ≤ ⊥ :=
    comm_le_of_relIndex_lt_two_pow (L := X.L 2) (E := X.Z 2) (N := ⊥) (by omega) hq bot_le
      (fun x _ => Subgroup.mem_normalizer_iff.mpr (by intro y; simp))
      hLNe (fun x _ => Subgroup.mem_normalizer_iff.mpr (by intro y; simp))
      ((pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)) hcore hbot0 hlt
  have hZ2L2 : X.Z 2 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)) (X.Z_le_Gi 2)
  have hcent : X.Z 2 ≤ centerOf (X.L 2) := by
    refine le_inf hZ2L2 ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hmem := hcomm (Subgroup.commutator_mem_commutator (H₁ := X.Z 2) (H₂ := X.L 2) hz hl)
    rw [Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  have hZ1Gi : X.Z 1 ≤ X.Gi 2 := by
    have h := hd₁.1 ((2 : ℤ) - 1) (by omega)
    simpa using h
  have hZ1L2 : X.Z 1 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)) hZ1Gi
  have hRbot : ⁅X.Z 1, X.Z (d₁ + 1)⁆ = ⊥ := by
    rw [hd1, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hbC : b ∈ Subgroup.centralizer (X.L 2 : Set G) := (Subgroup.mem_inf.mp (hcent hb)).2
    exact Subgroup.mem_centralizer_iff.mp hbC a (hZ1L2 ha)
  exact hR1 hRbot

theorem caseB_of (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) (hodd : Odd d₁) :
    s = 5 ∧ r = 4 ∧ d₀ = 1 ∧ d₁ = 1 ∧ X.CaseB := by
  have h6 := X.caseB_r_eq_four_or_eight H hd₀ hd₁ hR hR1 hodd
  obtain ⟨h2d, hd0le, hr⟩ := h6
  have hrne := X.caseB_r_ne_eight H hd₀ hd₁ hR hR1 hodd
  have hr4 : r = 4 := by
    rcases hr with h | h
    · exact h
    · exact absurd h hrne
  have hd1 : d₁ = 1 := by omega
  have hd0ne := X.not_r4_b2 H hd₀ hd₁ hR hR1 hodd hr4
  have hd0ge : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  have hd0 : d₀ = 1 := by omega
  subst hr4
  have hs5 : s = 5 := by
    have h1 := H.five_le
    have h2 := H.le_r
    omega
  subst hs5
  subst hd0
  subst hd1
  have hR2 : ⁅X.Z 1, X.Z 2⁆ ≤ X.Z 1 ⊓ X.Z 2 := by simpa using hR
  have hZ1' : conjSub (X.τ ^ (-1 : ℤ)) (X.Z 1) = X.Z (-1) := by
    have h := X.Z_add (-1) 1
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
    exact h.symm
  have hZ2' : conjSub (X.τ ^ (-1 : ℤ)) (X.Z 2) = X.Z 0 := by
    have h := X.Z_add (-1) 2
    rw [show (2 : ℤ) + 2 * (-1) = 0 by norm_num] at h
    exact h.symm
  have hRτ : ⁅X.Z (-1), X.Z 0⁆ ≤ X.Z (-1) ⊓ X.Z 0 := by
    have h := conjSub_mono (X.τ ^ (-1 : ℤ)) hR2
    have hZ1m : Subgroup.map (MulAut.conj (X.τ ^ (-1 : ℤ))).toMonoidHom (X.Z 1) =
        X.Z (-1) := hZ1'
    have hZ2m : Subgroup.map (MulAut.conj (X.τ ^ (-1 : ℤ))).toMonoidHom (X.Z 2) =
        X.Z 0 := hZ2'
    have hc : conjSub (X.τ ^ (-1 : ℤ)) ⁅X.Z 1, X.Z 2⁆ = ⁅X.Z (-1), X.Z 0⁆ := by
      change Subgroup.map (MulAut.conj (X.τ ^ (-1 : ℤ))).toMonoidHom ⁅X.Z 1, X.Z 2⁆ = _
      rw [Subgroup.map_commutator, hZ1m, hZ2m]
    rw [hc, conjSub_inf, hZ1', hZ2'] at h
    exact h
  obtain ⟨t, -, htref⟩ := X.exists_reflection H 0
  have hZmt : conjSub t (X.Z (-1)) = X.Z 1 := by
    have hsmul : t • X.vert (-1) = X.vert 1 := by
      have h := htref (-1)
      simpa using h
    have h := X.Z_smul X hsmul
    exact h.symm
  have hZ0t : conjSub t (X.Z 0) = X.Z 0 := by
    have hsmul : t • X.vert 0 = X.vert 0 := by
      have h := htref 0
      simpa using h
    have h := X.Z_smul X hsmul
    exact h.symm
  have hRt : ⁅X.Z 1, X.Z 0⁆ ≤ X.Z 1 ⊓ X.Z 0 := by
    have h := conjSub_mono t hRτ
    have hmt : Subgroup.map (MulAut.conj t).toMonoidHom (X.Z (-1)) = X.Z 1 := hZmt
    have h0t : Subgroup.map (MulAut.conj t).toMonoidHom (X.Z 0) = X.Z 0 := hZ0t
    have hc : conjSub t ⁅X.Z (-1), X.Z 0⁆ = ⁅X.Z 1, X.Z 0⁆ := by
      change Subgroup.map (MulAut.conj t).toMonoidHom ⁅X.Z (-1), X.Z 0⁆ = _
      rw [Subgroup.map_commutator, hmt, h0t]
    rw [hc, conjSub_inf, hZmt, hZ0t] at h
    exact h
  have hRle : ⁅X.Z 0, X.Z 1⁆ ≤ X.Z 0 ⊓ X.Z 1 := by
    rw [Subgroup.commutator_comm, inf_comm]
    exact hRt
  have hRne : ⁅X.Z 0, X.Z 1⁆ ≠ ⊥ := by
    intro hbot
    apply hR1
    have hconj : conjSub (X.τ * t⁻¹) ⁅X.Z 0, X.Z 1⁆ = ⁅X.Z 1, X.Z 2⁆ := by
      rw [conjSub_mul]
      have htinv1 : conjSub t⁻¹ (X.Z 1) = X.Z (-1) := by
        calc conjSub t⁻¹ (X.Z 1) = conjSub t⁻¹ (conjSub t (X.Z (-1))) := by rw [hZmt]
          _ = X.Z (-1) := conjSub_conjSub_inv t (X.Z (-1))
      have htinv0 : conjSub t⁻¹ (X.Z 0) = X.Z 0 := by
        calc conjSub t⁻¹ (X.Z 0) = conjSub t⁻¹ (conjSub t (X.Z 0)) := by rw [hZ0t]
          _ = X.Z 0 := conjSub_conjSub_inv t (X.Z 0)
      have hi0 : Subgroup.map (MulAut.conj t⁻¹).toMonoidHom (X.Z 0) = X.Z 0 := htinv0
      have hi1 : Subgroup.map (MulAut.conj t⁻¹).toMonoidHom (X.Z 1) = X.Z (-1) := htinv1
      have hstep : conjSub t⁻¹ ⁅X.Z 0, X.Z 1⁆ = ⁅X.Z (-1), X.Z 0⁆ := by
        change Subgroup.map (MulAut.conj t⁻¹).toMonoidHom ⁅X.Z 0, X.Z 1⁆ = _
        rw [Subgroup.map_commutator, hi0, hi1, Subgroup.commutator_comm]
      rw [hstep]
      have hZ1τ : conjSub X.τ (X.Z (-1)) = X.Z 1 := by
        have h := X.Z_add (1 : ℤ) (-1)
        rw [show (-1 : ℤ) + 2 * 1 = 1 by norm_num] at h
        simpa using h.symm
      have hZ0τ : conjSub X.τ (X.Z 0) = X.Z 2 := by
        have h := X.Z_add (1 : ℤ) 0
        rw [show (0 : ℤ) + 2 * 1 = 2 by norm_num] at h
        simpa using h.symm
      have h1τ : Subgroup.map (MulAut.conj X.τ).toMonoidHom (X.Z (-1)) = X.Z 1 := hZ1τ
      have h0τ : Subgroup.map (MulAut.conj X.τ).toMonoidHom (X.Z 0) = X.Z 2 := hZ0τ
      change Subgroup.map (MulAut.conj X.τ).toMonoidHom ⁅X.Z (-1), X.Z 0⁆ = _
      rw [Subgroup.map_commutator, h1τ, h0τ]
    rw [hbot, conjSub_bot] at hconj
    exact hconj.symm
  exact ⟨rfl, rfl, rfl, rfl, ⟨H, hd₀, hd₁, hRle, hRne⟩⟩

theorem caseB_data (X : Setup Γ G) (B : X.CaseB) (hn : ∀ i : ℤ, X.n i = 2) :
    X.TreeSp44Data := by
  have H : X.Sec4Hyp 5 4 := B.hyp
  have BG := B.toGen
  have h8 := BG.step8
  have hQeq : ∀ i : ℤ, pCoreOf 2 (X.L i) = X.Q i := fun i =>
    (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq
  have hQ : ∀ i : ℤ, i = 0 ∨ i = 1 → Nat.card (X.Q i) = 2 ^ 6 := fun i hi => by
    norm_num [BG.card_Q hi, hn]
  have hS : Nat.card X.S = 2 ^ 8 := by norm_num [BG.card_S, hn]
  have hnatQ : ∀ i : ℤ, i = 0 ∨ i = 1 → NatQuot (X.L i) (X.Q i) (centerOf (X.L i)) 2 := by
    intro i hi
    have h := h8.nat i hi
    rw [← (BG.Q_eq_Z h8 hi).1, hn] at h
    exact h
  have hcen : ∀ i : ℤ, i = 0 ∨ i = 1 → Nat.card ↥(centerOf (X.L i)) = 2 ^ 2 := fun i hi => by
    rw [(BG.Q_eq_Z h8 hi).2.2, hn]
  have hinf : Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) = 2 ^ 4 := by
    rw [hQeq, hQeq, BG.card_Q_inf (by rw [hn, hn])]
    norm_num [hn]
  refine
    { card_S := hS
      card_edge := by
        rw [X.card_edge_of_Ki_inf (BG.Ki_inf_eq_bot h8), hS, hn 0, hn 1]; norm_num
      elem_left := ?_
      card_left := ?_
      center_left := hcen 0 (Or.inl rfl)
      nat_left := ?_
      indec_left := ?_
      elem_right := ?_
      card_right := ?_
      center_right := hcen 1 (Or.inr rfl)
      nat_right := ?_
      indec_right := ?_
      card_inf := hinf }
  · rw [hQeq]; exact BG.elem_Q h8 (Or.inl rfl)
  · rw [hQeq, hQ 0 (Or.inl rfl)]
  · rw [hQeq]; exact (hnatQ 0 (Or.inl rfl)).natSec (pCoreOf_isPGroup' (X.Gi 0))
  · rw [hQeq]; exact BG.indec h8 (Or.inl rfl)
  · rw [hQeq]; exact BG.elem_Q h8 (Or.inr rfl)
  · rw [hQeq, hQ 1 (Or.inr rfl)]
  · rw [hQeq]; exact (hnatQ 1 (Or.inr rfl)).natSec (pCoreOf_isPGroup' (X.Gi 1))
  · rw [hQeq]; exact BG.indec h8 (Or.inr rfl)

end Setup

end CFSG.Quasithin.St84
