module

public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.Quasithin.Background.F1Borel

import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.EmptyFaithful.T1521SBlkBasic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverA
import CFSG.Quasithin.EmptyFaithful.S1422Quot
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Gaschutz
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.C5
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem _root_.CFSG.Quasithin.Hyp111.pCoreOf_le_left (hH : Hyp111 L1 L2 S) :
    pCoreOf 2 L1 ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (IsSylowTwoOf.le_of_normalizes (S := S ⊓ L1) (K := L1) (N := pCoreOf 2 L1)
    hH.h1.sylow (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1)
    (pCoreOf_isPGroup 2 L1)).trans inf_le_left

theorem _root_.CFSG.Quasithin.Hyp111.pCoreOf_le_right (hH : Hyp111 L1 L2 S) :
    pCoreOf 2 L2 ≤ S :=
  hH.symm.pCoreOf_le_left

theorem _root_.CFSG.Quasithin.Hyp111.charTwo_left (hH : Hyp111 L1 L2 S) : CharTwo L1 := by
  have hle : L1 ≤ L1 ⊔ S ⊔ borelOf L2 S := le_sup_left.trans le_sup_left
  refine CharTwo.of_normal hH.h1.charTwo hle ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  exact sup_le (sup_le Subgroup.le_normalizer hH.h1.normalizes) hH.h1.borel_le

theorem _root_.CFSG.Quasithin.Hyp111.charTwo_right (hH : Hyp111 L1 L2 S) : CharTwo L2 :=
  hH.symm.charTwo_left

theorem twoPart_of_isLin2Type {L : Subgroup G} {f k : ℕ} (hlin : IsLin2Type L f)
    (hQ : Nat.card (pCoreOf 2 L) = 2 ^ k) : twoPart L = 2 ^ (k + f) := by
  have hlin0 := hlin
  obtain ⟨F, hField, hFintype, hFcard, -⟩ := hlin
  letI := hField
  letI := hFintype
  have hf : 1 ≤ f := by
    have htwo : 2 ≤ Fintype.card F := Fintype.one_lt_card
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hFcard
    omega
  have hquot : Nat.card (oTwoQuot ↥L) = 2 ^ f * (4 ^ f - 1) :=
    CFSG.Quasithin.isLin2Type_card_quot (n := f) hlin0
  have hpc : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) := by
    rw [CFSG.Open.pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
  have hcard : Nat.card ↥L = 2 ^ (k + f) * (4 ^ f - 1) := by
    calc
      Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (CFSG.pCore 2 ↥L) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
      _ = Nat.card (oTwoQuot ↥L) * Nat.card (pCoreOf 2 L) := by rw [hpc]
      _ = (2 ^ f * (4 ^ f - 1)) * 2 ^ k := by rw [hquot, hQ]
      _ = (2 ^ f * 2 ^ k) * (4 ^ f - 1) := by
        rw [mul_assoc, mul_comm (4 ^ f - 1) (2 ^ k), ← mul_assoc]
      _ = 2 ^ (k + f) * (4 ^ f - 1) := by
        rw [mul_comm (2 ^ f) (2 ^ k), ← pow_add]
  have hodd : Odd (4 ^ f - 1) := by
    have h4 : Even (4 ^ f) := (show Even 4 by norm_num).pow_of_ne_zero (by omega)
    exact Nat.Even.sub_odd (m := 4 ^ f) (n := 1)
      (Nat.one_le_pow f 4 (by norm_num)) h4 (by norm_num)
  have hnot : ¬ 2 ∣ 4 ^ f - 1 := by
    intro hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  unfold twoPart
  rw [hcard, Nat.factorization_mul (by positivity) hodd.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot, add_zero, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
  simp

theorem _root_.CFSG.Quasithin.Hyp111.le_left_of_twoPart (hH : Hyp111 L1 L2 S)
    (h : twoPart L1 = Nat.card S) : S ≤ L1 := by
  have hcard : Nat.card ↥(S ⊓ L1) = Nat.card ↥S := by
    rw [IsSylowTwoOf.card_eq hH.h1.sylow, h]
  have hEq : S ⊓ L1 = S := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hcard]
  exact inf_eq_left.mp hEq

theorem _root_.CFSG.Quasithin.Hyp111.le_right_of_twoPart (hH : Hyp111 L1 L2 S)
    (h : twoPart L2 = Nat.card S) : S ≤ L2 :=
  hH.symm.le_left_of_twoPart h

theorem hyp111R_of_isLin2Type {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hH : Hyp111 L1 L2 S)
    (h1 : IsLin2Type L1 m) (h2 : IsLin2Type L2 n) : Hyp111R L1 L2 S :=
  hyp111R_of_isL2Quot (by omega) (by omega) hH
    (CFSG.Quasithin.F146Field.isL2Quot_of_isPSL
      (CFSG.Quasithin.isPSL_of_isLin2Type1521 hm h1))
    (CFSG.Quasithin.F146Field.isL2Quot_of_isPSL
      (CFSG.Quasithin.isPSL_of_isLin2Type1521 hn h2))

theorem sup_bigB_left_of_le (hS1 : S ≤ L1) : L1 ⊔ bigB L1 L2 S = L1 ⊔ borelOf L2 S := by
  have hB1 : borelOf L1 S ≤ L1 := borelOf_le L1 S
  have hB2big : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S :=
    le_sup_right.trans le_sup_left
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [bigB]
    exact sup_le (sup_le (hB1.trans le_sup_left) le_sup_right) (hS1.trans le_sup_left)
  · rw [bigB]
    exact sup_le le_sup_left (hB2big.trans le_sup_right)

theorem sup_bigB_right_of_le (hS2 : S ≤ L2) : L2 ⊔ bigB L1 L2 S = L2 ⊔ borelOf L1 S := by
  rw [← CFSG.Quasithin.bigB_comm L1 L2 S]
  exact sup_bigB_left_of_le hS2

theorem isSylowTwoOf_sup_bigB_left_of_le (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2) :
    IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := by
  have hB2 : S ≤ borelOf L2 S := le_inf hS2 (le_normalizer_inf_of_le hH.h2.normalizes)
  have hSInf : S ≤ L1 ⊓ borelOf L2 S := le_inf hS1 hB2
  have hsyl1 : IsSylowTwoOf S L1 := by
    have h := hH.h1.sylow
    rw [inf_eq_left.mpr hS1] at h
    exact h
  have hsyl2 : IsSylowTwoOf S L2 := by
    have h := hH.h2.sylow
    rw [inf_eq_left.mpr hS2] at h
    exact h
  have htwoB2 : twoPart (borelOf L2 S) = Nat.card S := by
    apply le_antisymm
    · calc
        twoPart (borelOf L2 S) ≤ twoPart L2 := twoPart_mono (borelOf_le L2 S)
        _ = Nat.card S := (IsSylowTwoOf.card_eq hsyl2).symm
    · exact card_le_twoPart hB2 hH.h1.pgroup
  have htwoInf : twoPart (L1 ⊓ borelOf L2 S) = Nat.card S := by
    apply le_antisymm
    · calc
        twoPart (L1 ⊓ borelOf L2 S) ≤ twoPart L1 := twoPart_mono inf_le_left
        _ = Nat.card S := (IsSylowTwoOf.card_eq hsyl1).symm
    · exact card_le_twoPart hSInf hH.h1.pgroup
  rw [sup_bigB_left_of_le hS1]
  refine isSylowTwoOf_of_card_eq (hS1.trans le_sup_left) hH.h1.pgroup ?_
  have hcard : Nat.card ↥(L1 ⊔ borelOf L2 S) * Nat.card ↥(L1 ⊓ borelOf L2 S) =
      Nat.card ↥L1 * Nat.card ↥(borelOf L2 S) := by
    have h := card_sup_mul_card_inf_of_le_normalizer
      (A := borelOf L2 S) (B := L1) hH.h1.borel_le
    rw [sup_comm (borelOf L2 S) L1, inf_comm (borelOf L2 S) L1,
      mul_comm (Nat.card ↥(borelOf L2 S)) (Nat.card ↥L1)] at h
    exact h
  have hfac : (Nat.card ↥(L1 ⊔ borelOf L2 S)).factorization 2 +
      (Nat.card ↥(L1 ⊓ borelOf L2 S)).factorization 2 =
      (Nat.card ↥L1).factorization 2 +
      (Nat.card ↥(borelOf L2 S)).factorization 2 := by
    have h := congrArg (fun n : ℕ => n.factorization 2) hcard
    rwa [Nat.factorization_mul (Nat.card_pos (α := ↥(L1 ⊔ borelOf L2 S))).ne'
          (Nat.card_pos (α := ↥(L1 ⊓ borelOf L2 S))).ne',
      Nat.factorization_mul (Nat.card_pos (α := ↥L1)).ne'
          (Nat.card_pos (α := ↥(borelOf L2 S))).ne'] at h
  have htwo : twoPart (L1 ⊔ borelOf L2 S) * twoPart (L1 ⊓ borelOf L2 S) =
      twoPart L1 * twoPart (borelOf L2 S) := by
    unfold twoPart
    rw [← pow_add, ← pow_add, hfac]
  have h := htwo
  rw [htwoInf, htwoB2, ← IsSylowTwoOf.card_eq hsyl1] at h
  exact (Nat.mul_right_cancel (Nat.card_pos (α := ↥S)) h).symm

theorem isSylowTwoOf_sup_bigB_right_of_le (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2) :
    IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) := by
  rw [← CFSG.Quasithin.bigB_comm L1 L2 S]
  exact isSylowTwoOf_sup_bigB_left_of_le hH.symm hS2 hS1

theorem pCoreOf_sup_bigB_left_of_le (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2) :
    pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
  have hPnorm : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact sup_le (sup_le ((borelOf_le L1 S).trans Subgroup.le_normalizer) hH.h1.borel_le)
      hH.h1.normalizes
  have hle1 : pCoreOf 2 L1 ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left hPnorm
  have hle2 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsSylowTwoOf.le_of_normalizes (S := S) (K := L1 ⊔ bigB L1 L2 S)
      (N := pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
      (isSylowTwoOf_sup_bigB_left_of_le hH hS1 hS2)
      (pCoreOf_le 2 (L1 ⊔ bigB L1 L2 S))
      (le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
      (pCoreOf_isPGroup 2 (L1 ⊔ bigB L1 L2 S))
  have hle3 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ L1 :=
    hle2.trans hS1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_antisymm
    (le_pCoreOf_of_le_normalizer 2 hle3
      ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 (L1 ⊔ bigB L1 L2 S))) hle1

theorem pCoreOf_sup_bigB_right_of_le (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2) :
    pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 := by
  rw [← CFSG.Quasithin.bigB_comm L1 L2 S]
  exact pCoreOf_sup_bigB_left_of_le hH.symm hS2 hS1

theorem isLinSemidirect_left_of_le (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2)
    (hQ1 : IsElemAbelian 2 (pCoreOf 2 L1)) (hQ2 : IsElemAbelian 2 (pCoreOf 2 L2))
    (hcard : Nat.card S * Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card (pCoreOf 2 L1) * Nat.card (pCoreOf 2 L2))
    {F : Type*} [Field F] {n : ℕ} {Γ : Subgroup (GL (Fin n) F)}
    (hact : LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) Γ) :
    IsLinSemidirect (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) Γ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPchar : L1 ⊔ S ⊔ borelOf L2 S = L1 ⊔ bigB L1 L2 S := by
    rw [sup_eq_left.mpr hS1, sup_bigB_left_of_le hS1]
  have hcent : (L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer (pCoreOf 2 L1 : Set G) ≤ pCoreOf 2 L1 := by
    have h := hH.h1.charTwo
    unfold CharTwo at h
    rw [hPchar, pCoreOf_sup_bigB_left_of_le hH hS1 hS2] at h
    exact h
  have hPnorm : L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 L1 : Set G) := by
    rw [sup_bigB_left_of_le hS1]
    exact sup_le (le_normalizer_pCoreOf 2 L1)
      (hH.h1.borel_le.trans (normalizer_le_normalizer_pCoreOf 2 L1))
  have hQab : ∀ a ∈ pCoreOf 2 L1, ∀ b ∈ pCoreOf 2 L1, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hQ1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hQ1p : IsPGroup 2 (pCoreOf 2 L1) :=
    hH.h1.pgroup.to_le hH.pCoreOf_le_left
  obtain ⟨R, hRQ2, hRinf, hRsup⟩ :=
    C5.exists_complement_elemAb2 (C5.isElemAbelian_two_iff.mp hQ2)
      (inf_le_right : pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ≤ pCoreOf 2 L2)
  have hRdisj : R ⊓ pCoreOf 2 L1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxInt : x ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := ⟨hx.2, hRQ2 hx.1⟩
    have hmem : x ∈ R ⊓ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := ⟨hx.1, hxInt⟩
    rwa [hRinf] at hmem
  have hRS : R ≤ S := hRQ2.trans hH.pCoreOf_le_right
  have hRQ1norm : R ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    hRS.trans (hS1.trans (le_normalizer_pCoreOf 2 L1))
  have hcommQ2 : ∀ a ∈ pCoreOf 2 L2, ∀ b ∈ pCoreOf 2 L2, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hQ2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcommR : ∀ a ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    exact hcommQ2 a ha.2 b (hRQ2 hb)
  have hcardQ2 : Nat.card (pCoreOf 2 L2) =
      Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) * Nat.card R := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) R hcommR).1
    rw [sup_comm (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) R, hRsup,
      inf_comm (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) R, hRinf,
      Subgroup.card_bot, mul_one] at h
    exact h
  have hcardS : Nat.card S = Nat.card (pCoreOf 2 L1) * Nat.card R := by
    have h := hcard
    rw [hcardQ2] at h
    have h' : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) * Nat.card S =
        Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) *
          (Nat.card (pCoreOf 2 L1) * Nat.card R) := by
      rw [mul_comm (Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)) (Nat.card S), h,
        Nat.mul_left_comm]
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2))) h'
  have hcardQ1R : Nat.card ↥(pCoreOf 2 L1 ⊔ R) = Nat.card S := by
    have h := card_sup_mul_card_inf_of_le_normalizer
      (A := R) (B := pCoreOf 2 L1) hRQ1norm
    rw [hRdisj, Subgroup.card_bot, mul_one] at h
    calc Nat.card ↥(pCoreOf 2 L1 ⊔ R) = Nat.card ↥(R ⊔ pCoreOf 2 L1) := by rw [sup_comm]
      _ = Nat.card R * Nat.card (pCoreOf 2 L1) := h
      _ = Nat.card (pCoreOf 2 L1) * Nat.card R := by rw [mul_comm]
      _ = Nat.card S := hcardS.symm
  have hS_eq : pCoreOf 2 L1 ⊔ R = S := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hH.pCoreOf_le_left hRS) ?_
    rw [hcardQ1R]
  obtain ⟨X₀, hX₀P, hX₀inf, hX₀sup⟩ :=
    C5.exists_complement_of_sylow_split (Q := pCoreOf 2 L1)
      (X := L1 ⊔ bigB L1 L2 S) (P := S) (C := R)
      ((pCoreOf_le 2 L1).trans le_sup_left) hPnorm hQab hQ1p
      (isSylowTwoOf_sup_bigB_left_of_le hH hS1 hS2) hRS hRdisj
      (by rw [sup_comm]; exact hS_eq)
  exact ⟨(pCoreOf_le 2 L1).trans le_sup_left, hPnorm, hcent,
    ⟨X₀, hX₀P, by simpa [inf_comm] using hX₀inf, hX₀sup⟩, hact⟩

theorem isLinSemidirect_right_of_le (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2)
    (hQ1 : IsElemAbelian 2 (pCoreOf 2 L1)) (hQ2 : IsElemAbelian 2 (pCoreOf 2 L2))
    (hcard : Nat.card S * Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card (pCoreOf 2 L1) * Nat.card (pCoreOf 2 L2))
    {F : Type*} [Field F] {n : ℕ} {Γ : Subgroup (GL (Fin n) F)}
    (hact : LinAction (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) Γ) :
    IsLinSemidirect (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) Γ := by
  have hcard' : Nat.card S * Nat.card ↥(pCoreOf 2 L2 ⊓ pCoreOf 2 L1) =
      Nat.card (pCoreOf 2 L2) * Nat.card (pCoreOf 2 L1) := by
    rw [inf_comm (pCoreOf 2 L2) (pCoreOf 2 L1),
      mul_comm (Nat.card (pCoreOf 2 L2)) (Nat.card (pCoreOf 2 L1))]
    exact hcard
  have hact' : LinAction (L2 ⊔ bigB L2 L1 S) (pCoreOf 2 L2) Γ := by
    rw [CFSG.Quasithin.bigB_comm L1 L2 S]
    exact hact
  have h := isLinSemidirect_left_of_le hH.symm hS2 hS1 hQ2 hQ1 hcard' hact'
  rw [CFSG.Quasithin.bigB_comm L1 L2 S] at h
  exact h

theorem _root_.CFSG.Quasithin.Hyp111R.blockZ_inf_blockZ (hR : Hyp111R L1 L2 S) :
    blockZ L1 ⊓ blockZ L2 = ⊥ := by
  have hH := hR.hyp
  have hZ1S : blockZ L1 ≤ S :=
    (inf_le_left.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (le_normalizer_pCoreOf 2 L1))).trans hH.pCoreOf_le_left
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x ∈ blockZ L1 := hx.1
  have hx2 : x ∈ blockZ L2 := hx.2
  have hxS : x ∈ S := hZ1S hx1
  have hxM : x ∈ Subgroup.centralizer ((L1 ⊔ L2 : Subgroup G) : Set G) := by
    have hsup : L1 ⊔ L2 ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hx1.2) l hl)
      · intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hx2.2) l hl)
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hm)
  have hSnorm : S ≤ Subgroup.normalizer ((L1 ⊔ L2 : Subgroup G) : Set G) :=
    le_normalizer_sup hH.h1.normalizes hH.h2.normalizes
  have hxcore : x ∈ coreIn (bigB L1 L2 S) (L1 ⊔ L2 ⊔ S) := by
    refine mem_coreIn.mpr ⟨(le_sup_right : S ≤ L1 ⊔ L2 ⊔ S) hxS, ?_⟩
    intro h hh
    obtain ⟨m, hm, s, hs, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hSnorm).mp hh
    have hmx : m⁻¹ * x * m = x := by
      have hcomm : m * x = x * m :=
        (Subgroup.mem_centralizer_iff.mp hxM) m hm
      calc m⁻¹ * x * m = m⁻¹ * (x * m) := by group
        _ = m⁻¹ * (m * x) := by rw [← hcomm]
        _ = x := by group
    have hmul : (m * s)⁻¹ * x * (m * s) = s⁻¹ * x * s := by
      rw [mul_inv_rev]
      calc s⁻¹ * m⁻¹ * x * (m * s) = s⁻¹ * (m⁻¹ * x * m) * s := by group
        _ = s⁻¹ * x * s := by rw [hmx]
    rw [hmul]
    exact Subgroup.mem_sup_right (S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs)
  have hbot := (prop_F19 hR).2.2.1
  rw [hbot] at hxcore
  simpa using hxcore

theorem pCoreOf_inf_centralizer_le_right (hH : Hyp111 L1 L2 S) (hS2 : S ≤ L2) :
    pCoreOf 2 L1 ⊓ Subgroup.centralizer (S : Set G) ≤ pCoreOf 2 L2 := by
  intro x hx
  have hxS : x ∈ S := hH.pCoreOf_le_left hx.1
  have hxL2 : x ∈ L2 := hS2 hxS
  have hxCQ2 : x ∈ Subgroup.centralizer (pCoreOf 2 L2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2) y (hH.pCoreOf_le_right hy)
  exact hH.charTwo_right ⟨hxL2, hxCQ2⟩

theorem pCoreOf_inf_centralizer_le_left (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) :
    pCoreOf 2 L2 ⊓ Subgroup.centralizer (S : Set G) ≤ pCoreOf 2 L1 :=
  pCoreOf_inf_centralizer_le_right hH.symm hS1

theorem inf_le_centralizer_of_sup_eq (hS : pCoreOf 2 L1 ⊔ pCoreOf 2 L2 = S)
    (hQ1 : IsElemAbelian 2 (pCoreOf 2 L1)) (hQ2 : IsElemAbelian 2 (pCoreOf 2 L2)) :
    pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ≤ Subgroup.centralizer (S : Set G) := by
  intro x hx
  have hSle : S ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hS]
    refine sup_le ?_ ?_
    · intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hQ1.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx.1⟩))
    · intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hQ2.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx.2⟩))
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact Subgroup.mem_centralizer_singleton_iff.mp (hSle hs)

end CFSG.Quasithin.F112R.St84

end
