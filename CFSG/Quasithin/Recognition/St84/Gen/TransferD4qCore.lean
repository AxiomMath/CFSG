module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftData
public import CFSG.Quasithin.Recognition.St84.Gen.TransferD4qData

import CFSG.Quasithin.Recognition.St84.Gen.TransferEdgeHyp
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalCompl
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalIndec
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoLocal
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeLift
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalIndecRight
public import CFSG.Quasithin.Background.SpecialPowCenter

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem d4q_commutator_eq_centerOf {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : D4qLocalData L1 L2 S f) :
    ⁅pCoreOf 2 L1, pCoreOf 2 L1⁆ = centerOf (pCoreOf 2 L1) ∧
      Nat.card (centerOf (pCoreOf 2 L1)) = 2 ^ f := by
  have h2 : 2 ≤ 2 ^ f :=
    Nat.succ_le_iff.mpr (Nat.one_lt_two_pow (by have := hd.one_le; omega))
  exact CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow (p := 2) (q := 2 ^ f)
    (w := 4) (by norm_num) h2 hd.special_left

private theorem d4q_card_centerOf_right {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : D4qLocalData L1 L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L2)) = 2 ^ (2 * f) := by
  obtain ⟨F, hFld, hFintype, hFcard, α, hα, hker, hnat⟩ := hd.nat_right
  letI := hFld
  letI := hFintype
  have h := card_centerOf_of_isNatSecOf_bot hnat
  rw [h, Nat.card_eq_fintype_card, hFcard, ← pow_mul]
  congr 1
  ring

private theorem d4q_commutator_pCoreOf_le_self (E : Subgroup H) :
    ⁅pCoreOf 2 E, oTwoPrime E⁆ ≤ pCoreOf 2 E :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((oTwoPrime_le E).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E))

private theorem d4q_commute_of_commutator_eq_center {E : Subgroup H}
    (hN : ⁅pCoreOf 2 E, oTwoPrime E⁆ = centerOf (pCoreOf 2 E))
    (hZc : centerOf (pCoreOf 2 E) ≤ Subgroup.centralizer (oTwoPrime E : Set H))
    (hE_NZ : E ≤ Subgroup.normalizer (centerOf (pCoreOf 2 E) : Set H))
    {k : H} (hk : k ∈ oTwoPrime E) (hkodd : Odd (orderOf k)) :
    ∀ x ∈ pCoreOf 2 E, x * k = k * x := by
  intro x hx
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 E) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E
  have hZ2 : IsPGroup 2 ↥(centerOf (pCoreOf 2 E)) := hQ2.to_le inf_le_left
  have hkNZ : k ∈ Subgroup.normalizer (centerOf (pCoreOf 2 E) : Set H) :=
    hE_NZ (oTwoPrime_le E hk)
  have hJodd : Odd (Nat.card ↥(Subgroup.zpowers k)) := by
    rw [Nat.card_zpowers]
    exact hkodd
  have hxNZ : x ∈ Subgroup.normalizer (centerOf (pCoreOf 2 E) : Set H) :=
    hE_NZ ((CFSG.LieType.BorelTits.pCoreOf_le 2 E) hx)
  have hcommZ : ∀ j ∈ Subgroup.zpowers k,
      j * x * j⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 E) := by
    intro j hj
    have hjL : j ∈ oTwoPrime E := Subgroup.zpowers_le.mpr hk hj
    have hc : ⁅x, j⁆ ∈ centerOf (pCoreOf 2 E) := by
      have h := Subgroup.commutator_mem_commutator hx hjL
      rwa [hN] at h
    rw [show j * x * j⁻¹ * x⁻¹ = ⁅x, j⁆⁻¹ from by rw [commutatorElement_def]; group]
    exact Subgroup.inv_mem _ hc
  obtain ⟨z, hzZ, hzx⟩ := exists_mul_mem_centralizer_of_odd
    (Q := centerOf (pCoreOf 2 E)) (J := Subgroup.zpowers k) hZ2 hJodd
    (Subgroup.zpowers_le.mpr hkNZ) hxNZ hcommZ
  have hzk : z * k = k * z :=
    (Subgroup.mem_centralizer_iff.mp (hZc hzZ) k hk).symm
  have hzxk : k * (z * x) = (z * x) * k :=
    Subgroup.mem_centralizer_iff.mp hzx k (Subgroup.mem_zpowers k)
  have h4 : z * (k * x) = z * (x * k) := by
    calc z * (k * x) = (z * k) * x := by group
      _ = (k * z) * x := by rw [hzk]
      _ = k * (z * x) := by group
      _ = (z * x) * k := hzxk
      _ = z * (x * k) := by group
  exact (mul_left_cancel h4).symm

private theorem d4q_centralizer_pCoreOf_of_commutator_eq_center {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f)
    (hN : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S)))
    {k : H} (hk : k ∈ oTwoPrime (f112saP1' L1 L2 S)) (hkodd : Odd (orderOf k)) :
    k ∈ Subgroup.centralizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) := by
  have hZc : centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H) := by
    have h := hd.center_left
    rw [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
    rw [h]
    exact inf_le_right
  have hE_NZ : f112saP1' L1 L2 S ≤ Subgroup.normalizer
      (centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) : Set H) := by
    intro g hg
    have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP1' L1 L2 S) hg
    have hgC : g ∈ Subgroup.normalizer
        (Subgroup.centralizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) : Set H) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (pCoreOf 2 (f112saP1' L1 L2 S)) hgQ
    change g ∈ Subgroup.normalizer
      ((pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        Subgroup.centralizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :
        Subgroup H) : Set H)
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hgQ, hgC⟩)
  exact Subgroup.mem_centralizer_iff.mpr
    (d4q_commute_of_commutator_eq_center hN hZc hE_NZ hk hkodd)

theorem f112ll_d4q_eq_of_localData {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    m = 3 * f ∧ f = n := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hcardα : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (9 * f + m) := by
    rw [(f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR).card_eq,
      twoPart_of_isL2Quot (a := 9 * f) (by omega)
        (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2) hd.card_left]
  have hcardβ : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (11 * f + n) := by
    rw [(f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR).card_eq,
      twoPart_of_isL2Quot (a := 11 * f) (by omega)
        (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2) hd.card_right]
  have hmul : 12 * f = 9 * f + m :=
    Nat.pow_right_injective (a := 2) (by norm_num) (hd.card_S.symm.trans hcardα)
  have hnul : 12 * f = 11 * f + n :=
    Nat.pow_right_injective (a := 2) (by norm_num) (hd.card_S.symm.trans hcardβ)
  omega

private theorem d4q_commutator_ne_center {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f)
    (hN : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) :
    False := by
  classical
  let L : Subgroup H := oTwoPrime (f112saP1' L1 L2 S)
  let Q : Subgroup H := pCoreOf 2 (f112saP1' L1 L2 S)
  let T : Subgroup H := S ⊓ f112saK L1 L2 S
  have hH : Hyp111 L (oTwoPrime (f112saP2' L1 L2 S)) T :=
    f112ll_hyp111_edge hF hm hn h1 h2
  have hm3 : m = 3 * f := (f112ll_d4q_eq_of_localData hF hm hn h1 h2 hd).1
  have h1' : IsL2Quot (3 * f) (oTwoQuot ↥L) := by
    rw [← hm3]
    exact f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  obtain ⟨Hh, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hd.exists_hall_bigB hH h1'
  obtain ⟨hcardHL, -, -, -, -⟩ := hd.torus_left_of_hall hH h1' hHB hSH hSinfH hHcard hHcomm
  have h7 : 7 ≤ Nat.card ↥(Hh ⊓ L) := by
    rw [hcardHL]
    have h8 : 8 ≤ 2 ^ (3 * f) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hne : Hh ⊓ L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h7
    omega
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hkH : (k : H) ∈ Hh ⊓ L := k.2
  have hk1' : (k : H) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkL : (k : H) ∈ L := (Subgroup.mem_inf.mp hkH).2
  have hkodd : Odd (orderOf (k : H)) := by
    have hodd : Odd (Nat.card ↥(Hh ⊓ L)) := by
      rw [hcardHL]
      exact odd_two_pow_sub_one (by omega)
    have hdvd : orderOf (k : H) ∣ Nat.card ↥(Hh ⊓ L) :=
      Subgroup.orderOf_dvd_natCard (Hh ⊓ L) k.2
    exact Odd.of_dvd_nat hodd hdvd
  have hkC : (k : H) ∈ Subgroup.centralizer (Q : Set H) :=
    d4q_centralizer_pCoreOf_of_commutator_eq_center hd hN hkL hkodd
  have hkQ : (k : H) ∈ Q := by
    have hchar := hH.charTwo_left
    have hkC' : (k : H) ∈ Subgroup.centralizer (pCoreOf 2 L : Set H) := by
      rwa [pCoreOf_oTwoPrime]
    have h := hchar (Subgroup.mem_inf.mpr ⟨hkL, hkC'⟩)
    rwa [pCoreOf_oTwoPrime] at h
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP1' L1 L2 S)) ⟨k, hkQ⟩
  have hoddj : Odd (2 ^ j) := by
    rw [← hj, Subgroup.orderOf_mk]
    exact hkodd
  have hj0 : j = 0 := by
    by_contra hj0
    exact (Nat.not_even_iff_odd.mpr hoddj) (Even.pow_of_ne_zero (a := 2) even_two hj0)
  have hkord : orderOf (⟨k, hkQ⟩ : ↥Q) = 1 := by
    rw [hj, hj0, pow_zero]
  have hkone : (k : H) = 1 := by
    have h := orderOf_eq_one_iff.mp hkord
    simpa using congrArg (fun y : ↥Q => (y : H)) h
  exact hk1' hkone

theorem f112ll_d4q_indec_left {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP1' L1 L2 S) := by
  classical
  let E : Subgroup H := f112saP1' L1 L2 S
  let L : Subgroup H := oTwoPrime E
  let Q : Subgroup H := pCoreOf 2 E
  let Z : Subgroup H := centerOf Q
  let N : Subgroup H := ⁅Q, L⁆
  have hQeq : pCoreOf 2 L = Q := pCoreOf_oTwoPrime E
  have hQ_le_L : Q ≤ L := by
    have h := CFSG.LieType.BorelTits.pCoreOf_le 2 L
    rwa [hQeq] at h
  have hZeq : ⁅Q, Q⁆ = Z := by
    have h := (d4q_commutator_eq_centerOf hd).1
    rwa [hQeq] at h
  have hN_le_Q : N ≤ Q := d4q_commutator_pCoreOf_le_self E
  have hZ_le_N : centerOf (pCoreOf 2 L) ≤ N := by
    rw [hQeq]
    show Z ≤ N
    exact hZeq ▸ Subgroup.commutator_mono le_rfl hQ_le_L
  have hN_le_Q' : N ≤ pCoreOf 2 L := by
    rwa [hQeq]
  have hL_N : L ≤ Subgroup.normalizer (N : Set H) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := Q) (H₂ := L)
  rcases hd.irred_left N hZ_le_N hN_le_Q' hL_N with h | h
  · exfalso
    refine d4q_commutator_ne_center hF hm hn h1 h2 hd ?_
    have h' : N = Z := by rw [h, hQeq]
    exact h'
  · exact h.trans hQeq

private theorem d4q_nat_right_transfer {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    ∃ (F : Type) (_ : Field F) (_ : CharP F 2)
      (α : ↥(oTwoPrime (f112saP2' L1 L2 S)) →* SL(2, F)), Function.Surjective α ∧
        α.ker = CFSG.pCore 2 ↥(oTwoPrime (f112saP2' L1 L2 S)) ∧
        IsNatSecOf (oTwoPrime (f112saP2' L1 L2 S))
          (centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))) ⊥ α := by
  obtain ⟨F, hFld, hFintype, hFcard, α, hα, hker, hnat⟩ := hd.nat_right
  letI := hFld
  letI := hFintype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨F, hFld, charP_of_card_eq_prime_pow (p := 2) (f := f) hFcard, α, hα, hker, hnat⟩

private theorem d4q_gen_left_transfer {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    ∀ N : Subgroup H,
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤ N →
      centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ N →
      N ≤ pCoreOf 2 (f112saP1' L1 L2 S) →
      oTwoPrime (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (N : Set H) →
      N = pCoreOf 2 (f112saP1' L1 L2 S) := by
  intro N hZα hZβ hNQ hLN
  have hf1 : 1 ≤ f := hd.one_le
  have hZα' : centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ≤ N := by
    rwa [pCoreOf_oTwoPrime]
  have hNQ' : N ≤ pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := by
    rwa [pCoreOf_oTwoPrime]
  rcases hd.irred_left N hZα' hNQ' hLN with h | h
  · exfalso
    have hZβ_le : centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤
        centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
      have h1 := hZβ.trans (le_of_eq h)
      rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h1
    have hcardZα : Nat.card (centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) = 2 ^ f := by
      have h1 := (d4q_commutator_eq_centerOf hd).2
      rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h1
    have hcardZβ : Nat.card (centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) = 2 ^ (2 * f) := by
      have h1 := d4q_card_centerOf_right hd
      rwa [pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at h1
    have hle : 2 ^ (2 * f) ≤ 2 ^ f := by
      rw [← hcardZβ, ← hcardZα]
      exact Subgroup.card_le_of_le hZβ_le
    have hlt : 2 ^ f < 2 ^ (2 * f) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd hle (not_le.mpr hlt)
  · exact h.trans (pCoreOf_oTwoPrime (f112saP1' L1 L2 S))

private theorem d4q_torus_left_transfer {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) (hf2 : 2 ≤ f) :
    ∃ J : Subgroup H,
      J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
        (S ⊓ f112saK L1 L2 S) ∧
      Odd (Nat.card J) ∧
      (∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
        ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) ∧
      pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥ := by
  have hm3 : m = 3 * f := (f112ll_d4q_eq_of_localData hF hm hn h1 h2 hd).1
  have hH : Hyp111 (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) := f112ll_hyp111_edge hF hm hn h1 h2
  have h1' : IsL2Quot (3 * f) (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
    rw [← hm3]
    exact f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  obtain ⟨Hh, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hd.exists_hall_bigB hH h1'
  obtain ⟨hcardHL, hcardHtriv, -, -, -⟩ :=
    hd.torus_left_of_hall hH h1' hHB hSH hSinfH hHcard hHcomm
  refine ⟨Hh ⊓ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)), ?_, ?_, ?_, ?_⟩
  · exact inf_le_left.trans hHB
  · rw [hcardHtriv]
    exact odd_two_pow_sub_one (by omega)
  · intro j hj l hl
    have h := (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hj).2).2 l hl
    rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
  · refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    have hxQ' : x ∈ pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := by
      rwa [pCoreOf_oTwoPrime]
    exact hd.eq_one_of_mem_pCoreOf_left_of_commute hf2 hH h1' hHB hSH hSinfH hHcard hHcomm
      hxQ' (fun h hh => by
        have h1' := Subgroup.mem_centralizer_iff.mp hxC h hh
        rw [h1']
        group)

theorem D4qEdgeData.transferLeftData {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : D4qEdgeData L1 L2 S f) :
    TransferLeftData L1 L2 S := by
  have hloc : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := hd
  have heq := f112ll_d4q_eq_of_localData hF hm hn h1 h2 hloc
  have hf2 : 2 ≤ f := by have := heq.2; omega
  have h1' : IsL2Quot (3 * f) (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
    rw [← heq.1]
    exact f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  refine
    { nat_right := d4q_nat_right_transfer hloc
      centerRight_le := ?_
      commutator_le := ?_
      centerLeft_le := ?_
      gen_left := d4q_gen_left_transfer hloc
      torus_left := d4q_torus_left_transfer hF hm hn h1 h2 hloc hf2
      indec_left := f112ll_d4q_indec_left hF hm hn h1 h2 hloc
      eq_one_of_mem_trivOTwoQuot := fun k hk hkodd hktriv =>
        D4qLocalData.eq_one_of_mem_trivOTwoQuot hf2
          (f112ll_hyp111_edge hF hm hn h1 h2) hloc h1' hk hkodd hktriv }
  · have h := hloc.centerOf_pCoreOf_right_le_left (f112ll_hyp111_edge hF hm hn h1 h2) h1'
    rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S), pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at h
  · have h := (d4q_commutator_eq_centerOf hloc).1
    rw [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
    exact le_of_eq h
  · have h := hloc.center_left
    rw [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
    rw [h]
    exact inf_le_right

end CFSG.Quasithin.F112R.St84

end
