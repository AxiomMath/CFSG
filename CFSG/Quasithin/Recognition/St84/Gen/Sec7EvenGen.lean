module

public import CFSG.Quasithin.Recognition.St84.Sec7Even
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen
import CFSG.Quasithin.Recognition.St84.Gen.L2CoreElem
import CFSG.Quasithin.Recognition.St84.Gen.L2CoreNatural
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique

section Even

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem Setup.singularity_le_four_gen (X : Setup Γ G) (hs : IsSingularity Γ G s)
    (hev : Even s) : s ≤ 4 :=
  singularity_le_four_of_even_gen X.hyp hs hev X.toKTrack
    (by
      intro i a b ha hb ha1 ha2 hb1 hb2
      obtain ⟨k, hk, hkb⟩ := X.Ki_transitive_gen i ha hb ha1 ha2 hb1 hb2
      exact ⟨k, hk.1, hkb⟩)
    X.hyp.le_G1_of_isPGroup_fixes_two

theorem Setup.singularity_eq_four_gen (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hev : Even s) : s = 4 := by
  have hle := X.singularity_le_four_gen hs hev
  have h3 := three_le_of_isSingularity X.hyp hc hs
  obtain ⟨t, ht⟩ := hev
  omega

namespace Setup

variable (X : Setup Γ G)

theorem card_S_gen (hs : IsSingularity Γ G 4) : Nat.card X.S = 2 ^ (3 * X.n 0) := by
  classical
  have hev4 : Even 4 := ⟨2, rfl⟩
  have hK : Nat.card ↥X.K * Nat.card ↥X.S = Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) :=
    card_mul_pCoreOf_edgeStab X.hyp (X.adj 0) X.K_le_inf X.K_inf X.K_sup
  have hreg1 : X.RightTransAt 0 1 := by
    have h := (X.trans_of_lt hs 0 (k := 1) (by norm_num) (by norm_num)).2
    simpa using h
  have hreg2 : X.RightTransAt 0 2 := by
    have h := (X.trans_of_lt hs 0 (k := 2) (by norm_num) (by norm_num)).2
    simpa using h
  have hreg3 : X.RightTransAt 0 3 := by
    have h := (X.trans_of_lt hs 0 (k := 3) (by norm_num) (by norm_num)).2
    simpa using h
  have h43 : (X.arcStab 0 4).relIndex (X.arcStab 0 3) = 2 ^ X.n 3 :=
    X.relIndex_arcStab_succ 0 3 (by norm_num) hreg3
  have h32 : (X.arcStab 0 3).relIndex (X.arcStab 0 2) = 2 ^ X.n 2 :=
    X.relIndex_arcStab_succ 0 2 (by norm_num) hreg2
  have h21 : (X.arcStab 0 2).relIndex (X.arcStab 0 1) = 2 ^ X.n 1 :=
    X.relIndex_arcStab_succ 0 1 (by norm_num) hreg1
  have hle43 : X.arcStab 0 4 ≤ X.arcStab 0 3 :=
    X.arcStab_anti (by norm_num) (by norm_num)
  have hle32 : X.arcStab 0 3 ≤ X.arcStab 0 2 :=
    X.arcStab_anti (by norm_num) (by norm_num)
  have hle21 : X.arcStab 0 2 ≤ X.arcStab 0 1 :=
    X.arcStab_anti (by norm_num) (by norm_num)
  have hle41 : X.arcStab 0 4 ≤ X.arcStab 0 1 := hle43.trans (hle32.trans hle21)
  have hA42 : (X.arcStab 0 4).relIndex (X.arcStab 0 2) =
      2 ^ X.n 3 * 2 ^ X.n 2 := by
    rw [← Subgroup.relIndex_mul_relIndex (H := X.arcStab 0 4) (K := X.arcStab 0 3)
      (L := X.arcStab 0 2) hle43 hle32, h43, h32]
  have hA41 : (X.arcStab 0 4).relIndex (X.arcStab 0 1) =
      2 ^ X.n 3 * 2 ^ X.n 2 * 2 ^ X.n 1 := by
    rw [← Subgroup.relIndex_mul_relIndex (H := X.arcStab 0 4) (K := X.arcStab 0 2)
      (L := X.arcStab 0 1) (hle43.trans hle32) hle21, hA42, h21]
  have hA4K : X.arcStab 0 4 = X.K := by
    have h := X.arcStab_eq_K hs hev4 0
    simpa using h
  have hA1Gi : X.arcStab 0 1 = X.Gi 0 ⊓ X.Gi 1 := X.arcStab_eq_inf (by norm_num)
  have hcardA1 : Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) =
      2 ^ X.n 3 * 2 ^ X.n 2 * 2 ^ X.n 1 * Nat.card ↥X.K := by
    rw [← hA1Gi, ← hA4K]
    have h := Subgroup.relIndex_mul_card (H := X.arcStab 0 4) (K := X.arcStab 0 1)
    rw [inf_eq_left.mpr hle41, hA41] at h
    exact h.symm
  have hn1 : X.n 1 = X.n 0 := (X.n_zero_eq_n_one_of_even hs hev4).symm
  have hn2 : X.n 2 = X.n 0 := X.n_two
  have hn3 : X.n 3 = X.n 1 := X.n_three
  have hcastn : 2 ^ X.n 3 * 2 ^ X.n 2 * 2 ^ X.n 1 = 2 ^ (3 * X.n 0) := by
    rw [hn3, hn1, hn2, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hcastn] at hcardA1
  rw [hcardA1] at hK
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  haveI : Nonempty ↥X.K := ⟨⟨1, X.K.one_mem⟩⟩
  have hKpos : 0 < Nat.card ↥X.K := Nat.card_pos
  rw [mul_comm (2 ^ (3 * X.n 0)) (Nat.card ↥X.K)] at hK
  exact Nat.eq_of_mul_eq_mul_left hKpos hK

theorem card_Q_gen (hs : IsSingularity Γ G 4) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    Nat.card (X.Q i) = 2 ^ (2 * X.n 0) := by
  classical
  have hS : Nat.card X.S = 2 ^ (3 * X.n 0) := X.card_S_gen hs
  rcases hi with rfl | rfl
  · have hle : X.Q 0 ≤ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0
    have hrel : (X.Q 0).relIndex (X.edgeSylow 0) = 2 ^ X.n 0 := X.relIndex_Q_edgeSylow 0
    have h := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.edgeSylow 0)
    rw [inf_eq_left.mpr hle, hrel, X.edgeSylow_zero, hS] at h
    have hpos : 0 < 2 ^ X.n 0 := pow_pos (by norm_num) _
    have h' : 2 ^ X.n 0 * Nat.card (X.Q 0) =
        2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
      rw [h, ← pow_add]
      congr 1
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  · have hle : X.Q 1 ≤ X.edgeSylow 0 := by simpa using X.Q_le_edgeSylow 0
    have hn1 : X.n 1 = X.n 0 := (X.n_zero_eq_n_one_of_even hs ⟨2, rfl⟩).symm
    have hrel : (X.Q 1).relIndex (X.edgeSylow 0) = 2 ^ X.n 0 := by
      simpa [hn1] using X.relIndex_Q_succ_edgeSylow 0
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.edgeSylow 0)
    rw [inf_eq_left.mpr hle, hrel, X.edgeSylow_zero, hS] at h
    have hpos : 0 < 2 ^ X.n 0 := pow_pos (by norm_num) _
    have h' : 2 ^ X.n 0 * Nat.card (X.Q 1) =
        2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
      rw [h, ← pow_add]
      congr 1
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h'

theorem card_Q_inf_gen (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G 4) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 0 := by
  classical
  have hcard0 : Nat.card (X.Q 0) = 2 ^ (2 * X.n 0) := X.card_Q_gen hs (Or.inl rfl)
  have hcard1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 0) := X.card_Q_gen hs (Or.inr rfl)
  have hS : Nat.card X.S = 2 ^ (3 * X.n 0) := X.card_S_gen hs
  have hQS1 : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := by
    simpa [X.edgeSylow_zero] using X.sup_Q_eq_edgeSylow hc 0
  have hnorm : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.Q_le_Gi_adj 0 |>.trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hleft : (X.Q 1).relIndex X.S = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.S)
    rw [inf_eq_left.mpr hQS1, hcard1, hS] at h
    have h' : (X.Q 1).relIndex X.S * 2 ^ (2 * X.n 0) =
        2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
      rw [← pow_add, show X.n 0 + 2 * X.n 0 = 3 * X.n 0 by ring]
      exact h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h'
  have hsecond := CFSG.Quasithin.SzR1.MNU.Norm.relIndex_sup_eq_of_le_normalizer
    (D := X.Q 1) (T := X.Q 0) hnorm
  rw [hsup] at hsecond
  have hrel1 : (X.Q 1).relIndex (X.Q 0) = 2 ^ X.n 0 := by
    rw [← hsecond, hleft]
  have hinfrel : (X.Q 1 ⊓ X.Q 0).relIndex (X.Q 0) = 2 ^ X.n 0 := by
    rw [Subgroup.inf_relIndex_right, hrel1]
  have hmul := Subgroup.relIndex_mul_card (H := X.Q 1 ⊓ X.Q 0) (K := X.Q 0)
  rw [inf_eq_left.mpr (inf_le_right : X.Q 1 ⊓ X.Q 0 ≤ X.Q 0), hinfrel, hcard0] at hmul
  have hmain : Nat.card ↥(X.Q 1 ⊓ X.Q 0) = 2 ^ X.n 0 := by
    have h' : 2 ^ X.n 0 * Nat.card ↥(X.Q 1 ⊓ X.Q 0) =
        2 ^ X.n 0 * 2 ^ X.n 0 := by
      rw [hmul, ← pow_add]
      congr 1
      ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h'
  rw [inf_comm]
  exact hmain

theorem le_card_Q_inf_centralizer_gen (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G 4) (he0 : IsElemAbelian 2 (X.Q 0)) (he1 : IsElemAbelian 2 (X.Q 1))
    {i : ℤ} (hi : i = 0 ∨ i = 1) :
    2 ^ X.n 0 ≤ Nat.card ↥(X.Q i ⊓ Subgroup.centralizer (X.S : Set G)) := by
  classical
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := by
    simpa [X.edgeSylow_zero] using X.sup_Q_eq_edgeSylow hc 0
  have hcent0 : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.Q 0 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact IsElemAbelian.comm he0 hx hy.1
  have hcent1 : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.Q 1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact IsElemAbelian.comm he1 hx hy.2
  have hsupcent : X.Q 0 ⊔ X.Q 1 ≤ Subgroup.centralizer (X.Q 0 ⊓ X.Q 1 : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mpr hcent0) (Subgroup.le_centralizer_iff.mpr hcent1)
  have hcent : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.S : Set G) := by
    rw [← hsup]
    exact Subgroup.le_centralizer_iff.mpr hsupcent
  have hcard : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 0 := X.card_Q_inf_gen hc hs
  rcases hi with rfl | rfl
  · haveI : Finite ↥(X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G)) :=
      finite_of_le_stabilizer X.hyp (H := X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G))
        (inf_le_left.trans (X.Q_le_Gi 0))
    have hle : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G) :=
      le_inf inf_le_left hcent
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rw [hcard] at h
    exact h
  · haveI : Finite ↥(X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G)) :=
      finite_of_le_stabilizer X.hyp (H := X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G))
        (inf_le_left.trans (X.Q_le_Gi 1))
    have hle : X.Q 1 ⊓ X.Q 0 ≤ X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G) :=
      le_inf inf_le_left (by simpa [inf_comm] using hcent)
    have hcard' : Nat.card ↥(X.Q 1 ⊓ X.Q 0) = 2 ^ X.n 0 := by
      rw [inf_comm, hcard]
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rw [hcard'] at h
    exact h

theorem charTwo_L (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) : CharTwo (X.L i) := by
  have hL : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  intro g hg
  rw [hL.pCoreOf_eq] at hg ⊢
  exact hc (X.vert i) ⟨X.L_le_Gi i hg.1, hg.2⟩

end Setup

end Even

section TypeZero

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem Setup.even_singularity_gen (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hev : Even s) (hn : 2 ≤ X.n 0) :
    s = 4 ∧ X.n 1 = X.n 0 ∧
      CFSG.Quasithin.F112R.St84.L3qLocalData (X.L 0) (X.L 1) X.S (X.n 0) := by
  classical
  have h4 : s = 4 := X.singularity_eq_four_gen hc hs hev
  subst h4
  have hn1 : X.n 1 = X.n 0 := (X.n_zero_eq_n_one_of_even hs ⟨2, rfl⟩).symm
  have hn1ge : 2 ≤ X.n 1 := by omega
  have hcardS : Nat.card X.S = 2 ^ (3 * X.n 0) := X.card_S_gen hs
  have hcard0 : Nat.card (X.Q 0) = 2 ^ (2 * X.n 0) := X.card_Q_gen hs (Or.inl rfl)
  have hcard1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 0) := X.card_Q_gen hs (Or.inr rfl)
  have hL0 : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hL1 : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  haveI : Finite ↥(X.L 0) :=
    Finite.of_injective (Subgroup.inclusion (X.L_le_Gi 0))
      (Subgroup.inclusion_injective (X.L_le_Gi 0))
  haveI : Finite ↥(X.L 1) :=
    Finite.of_injective (Subgroup.inclusion (X.L_le_Gi 1))
      (Subgroup.inclusion_injective (X.L_le_Gi 1))
  have hquot0 : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) := by
    simpa [IsL2Quot, oTwoQuot] using hL0.quot
  have hquot1 : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) := by
    simpa [IsL2Quot, oTwoQuot] using hL1.quot
  have hcardL0 : Nat.card (pCoreOf 2 (X.L 0)) = 2 ^ (2 * X.n 0) := by
    rw [hL0.pCoreOf_eq]
    exact hcard0
  have hcardL1 : Nat.card (pCoreOf 2 (X.L 1)) = 2 ^ (2 * X.n 0) := by
    rw [hL1.pCoreOf_eq]
    exact hcard1
  have hcardL1n : Nat.card (pCoreOf 2 (X.L 1)) = 2 ^ (2 * X.n 1) := by
    rw [hn1]
    exact hcardL1
  have heL0 : IsElemAbelian 2 (pCoreOf 2 (X.L 0)) :=
    isElemAbelian_pCoreOf_of_card hn (X.charTwo_L hc 0) hquot0 hcardL0
  have heL1 : IsElemAbelian 2 (pCoreOf 2 (X.L 1)) :=
    isElemAbelian_pCoreOf_of_card hn1ge (X.charTwo_L hc 1) hquot1 hcardL1n
  have heQ0 : IsElemAbelian 2 (X.Q 0) := by
    show IsElemAbelian 2 (pCoreOf 2 (MulAction.stabilizer G (X.vert 0)))
    rw [← hL0.pCoreOf_eq]
    exact heL0
  have heQ1 : IsElemAbelian 2 (X.Q 1) := by
    show IsElemAbelian 2 (pCoreOf 2 (MulAction.stabilizer G (X.vert 1)))
    rw [← hL1.pCoreOf_eq]
    exact heL1
  have hT0 : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have hT1 : IsSylowTwoOf X.S (X.L 1) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L_succ 0
  have hC0 : 2 ^ X.n 0 ≤
      Nat.card ↥(X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G)) :=
    X.le_card_Q_inf_centralizer_gen hc hs heQ0 heQ1 (Or.inl rfl)
  have hC1 : 2 ^ X.n 0 ≤
      Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G)) :=
    X.le_card_Q_inf_centralizer_gen hc hs heQ0 heQ1 (Or.inr rfl)
  have hC0' : 2 ^ X.n 0 ≤
      Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ Subgroup.centralizer (X.S : Set G)) := by
    rwa [hL0.pCoreOf_eq]
  have hC1' : 2 ^ X.n 1 ≤
      Nat.card ↥(pCoreOf 2 (X.L 1) ⊓ Subgroup.centralizer (X.S : Set G)) := by
    rw [hn1, hL1.pCoreOf_eq]
    exact hC1
  have hlin0 : IsLin2Type (X.L 0) (X.n 0) :=
    isLin2Type_of_card_centralizer hn (X.charTwo_L hc 0) hquot0 heL0
      (fun W hW hLW => eq_bot_or_eq_pCoreOf_of_card hn (X.charTwo_L hc 0) hquot0
        hcardL0 hW hLW)
      hcardL0 hT0 hC0'
  have hlin1 : IsLin2Type (X.L 1) (X.n 1) :=
    isLin2Type_of_card_centralizer hn1ge (X.charTwo_L hc 1) hquot1 heL1
      (fun W hW hLW => eq_bot_or_eq_pCoreOf_of_card hn1ge (X.charTwo_L hc 1) hquot1
        hcardL1n hW hLW)
      hcardL1n hT1 hC1'
  have hcardInf : Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) = 2 ^ X.n 0 := by
    rw [hL0.pCoreOf_eq, hL1.pCoreOf_eq]
    exact X.card_Q_inf_gen hc hs
  exact ⟨rfl, hn1, hcardS, hcardL0, hlin0, hcardL1, hn1 ▸ hlin1, hcardInf⟩

end TypeZero

end CFSG.Quasithin.St84
