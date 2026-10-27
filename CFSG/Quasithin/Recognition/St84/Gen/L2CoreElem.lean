module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRFrat
import CFSG.Quasithin.Background.E5Two
import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic
import CFSG.Quasithin.Recognition.St84.AppTreeL2
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type} [Group G]

private theorem exists_orderOf_eq_three {L : Subgroup G} [Finite ↥L] {n : ℕ} (hn : 2 ≤ n)
    (hquot : IsL2Quot n (oTwoQuot ↥L)) : ∃ x : G, x ∈ L ∧ orderOf x = 3 := by
  have hqcard : Nat.card (oTwoQuot ↥L) = 2 ^ n * (4 ^ n - 1) := hquot.card (by omega)
  have hLcard : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) * Nat.card (pCoreOf 2 L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), hqcard]
    congr 1
    rw [← CFSG.openPCoreOf_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CFSG.openPCoreOf_le 2 L)).toEquiv
  have h3dvd : 3 ∣ Nat.card ↥L := by
    rw [hLcard]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (by simpa using Nat.sub_one_dvd_pow_sub_one 4 n) (2 ^ n))
      (Nat.card (pCoreOf 2 L))
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x₀, hx₀3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact ⟨(x₀ : G), x₀.2, by rw [Subgroup.orderOf_coe, hx₀3]⟩

private theorem eq_one_of_odd_of_mem_centralizer [Finite G] {L : Subgroup G} {x : G}
    (hc : CharTwo L) (hxL : x ∈ L) (hxodd : Odd (orderOf x))
    (hxcent : x ∈ Subgroup.centralizer (pCoreOf 2 L : Set G)) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Quasithin.F53Push.eq_one_of_odd_of_mem
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) (hc ⟨hxL, hxcent⟩) hxodd

private theorem isElemAbelian_pCoreOf_of_card_finite [Finite G] {L : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hc : CharTwo L) (hquot : IsL2Quot n (oTwoQuot ↥L))
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (2 * n)) : IsElemAbelian 2 (pCoreOf 2 L) := by
  classical
  haveI h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥L := Subtype.finite
  obtain ⟨x, hxL, hx3⟩ := exists_orderOf_eq_three (L := L) hn hquot
  have hxodd : Odd (orderOf x) := by rw [hx3]; exact ⟨1, rfl⟩
  have hxne : x ≠ 1 := by
    intro h
    rw [h] at hx3
    norm_num at hx3
  set Q := pCoreOf 2 L
  have hLnorm : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hsec : GH74.QTGen4.DSGen4.IsElemSec (CFSG.Quasithin.F53Push.phi Q) Q :=
    ⟨CFSG.Quasithin.F53Push.phi_le_self Q, CFSG.Quasithin.F53Push.commutator_le_phi Q,
      fun e he => by simpa [pow_two] using CFSG.Quasithin.F53Push.sq_mem_phi he⟩
  have hLnormPhi : L ≤ Subgroup.normalizer (CFSG.Quasithin.F53Push.phi Q : Set G) :=
    CFSG.Quasithin.F53Push.le_normalizer_phi hLnorm
  have hQtriv : ∀ p ∈ Q, ∀ v ∈ Q, ⁅p, v⁆ ∈ CFSG.Quasithin.F53Push.phi Q :=
    fun p hp v hv => CFSG.Quasithin.F53Push.comm_mem_phi hp hv
  by_cases hnt : ∃ l ∈ L, ∃ v ∈ Q, ⁅l, v⁆ ∉ CFSG.Quasithin.F53Push.phi Q
  ·
    have hrel : 2 ^ (2 * n) ≤ (CFSG.Quasithin.F53Push.phi Q).relIndex Q :=
      two_pow_le_relIndex_of_nontrivial (m := n) (by omega) hquot hsec
        (le_inf hLnorm hLnormPhi) hQtriv hnt
    have hrelcard : (CFSG.Quasithin.F53Push.phi Q).relIndex Q *
        Nat.card (CFSG.Quasithin.F53Push.phi Q) = Nat.card Q := by
      have h := Subgroup.relIndex_mul_card (H := CFSG.Quasithin.F53Push.phi Q) (K := Q)
      rwa [inf_eq_left.mpr (CFSG.Quasithin.F53Push.phi_le_self Q)] at h
    have hPhi1 : Nat.card (CFSG.Quasithin.F53Push.phi Q) = 1 := by
      have hpos : 0 < (CFSG.Quasithin.F53Push.phi Q).relIndex Q := by
        rw [Subgroup.relIndex, Subgroup.index]
        exact Nat.card_pos
      have hle1 : Nat.card (CFSG.Quasithin.F53Push.phi Q) ≤ 1 := by
        refine Nat.le_of_mul_le_mul_left ?_ hpos
        calc (CFSG.Quasithin.F53Push.phi Q).relIndex Q *
            Nat.card (CFSG.Quasithin.F53Push.phi Q) = Nat.card Q := hrelcard
          _ = 2 ^ (2 * n) := hcard
          _ ≤ (CFSG.Quasithin.F53Push.phi Q).relIndex Q := hrel
          _ = (CFSG.Quasithin.F53Push.phi Q).relIndex Q * 1 := (mul_one _).symm
      have hpos' : 0 < Nat.card (CFSG.Quasithin.F53Push.phi Q) := Nat.card_pos
      omega
    have hbot : CFSG.Quasithin.F53Push.phi Q = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ hPhi1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun e he => ?_⟩
    · have h := CFSG.Quasithin.F53Push.comm_mem_phi (R := Q) a.2 b.2
      rw [hbot, Subgroup.mem_bot] at h
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h)
    · have h := CFSG.Quasithin.F53Push.sq_mem_phi (R := Q) he
      rw [hbot, Subgroup.mem_bot] at h
      simpa [pow_two] using h
  ·
    push Not at hnt
    have htriv : ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ CFSG.Quasithin.F53Push.phi Q := by
      intro q hq
      simpa [commutatorElement_def] using hnt x hxL q hq
    have hcent := CFSG.Quasithin.F53Push.centralizes_of_trivial_mod_phi hQ2 (hLnorm hxL)
      hxodd htriv
    have hxcent : x ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq => (mul_inv_eq_iff_eq_mul.mp (hcent q hq)).symm
    have hxQ : x ∈ Q := hc ⟨hxL, hxcent⟩
    exact absurd (CFSG.Quasithin.F53Push.eq_one_of_odd_of_mem hQ2 hxQ hxodd) hxne

private theorem eq_bot_or_eq_pCoreOf_of_card_finite [Finite G] {L W : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hc : CharTwo L) (hquot : IsL2Quot n (oTwoQuot ↥L))
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (2 * n)) (hW : W ≤ pCoreOf 2 L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = pCoreOf 2 L := by
  classical
  haveI h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥L := Subtype.finite
  have hQelem : IsElemAbelian 2 (pCoreOf 2 L) :=
    isElemAbelian_pCoreOf_of_card_finite hn hc hquot hcard
  haveI : IsMulCommutative ↥(pCoreOf 2 L) := hQelem.1
  have hQcomm : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, ⁅a, b⁆ = 1 := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩))
  have hQsq : ∀ e ∈ pCoreOf 2 L, e ^ 2 = 1 := hQelem.2
  have hLnormQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  by_cases hw : W = ⊥
  · exact Or.inl hw
  by_cases hwq : W = pCoreOf 2 L
  · exact Or.inr hwq
  exfalso
  obtain ⟨x, hxL, hx3⟩ := exists_orderOf_eq_three (L := L) hn hquot
  have hxodd : Odd (orderOf x) := by rw [hx3]; exact ⟨1, rfl⟩
  have hxne : x ≠ 1 := by
    intro h
    rw [h] at hx3
    norm_num at hx3
  by_cases hntW : ∃ l ∈ L, ∃ w ∈ W, ⁅l, w⁆ ∉ (⊥ : Subgroup G)
  ·
    have hsec : GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup G) W := by
      refine ⟨bot_le, ?_, ?_⟩
      · rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [hQcomm a (hW ha) b (hW hb)]
        exact (⊥ : Subgroup G).one_mem
      · intro e he
        rw [Subgroup.mem_bot]
        exact hQsq e (hW he)
    have hrel : 2 ^ (2 * n) ≤ (⊥ : Subgroup G).relIndex W :=
      two_pow_le_relIndex_of_nontrivial (m := n) (by omega) hquot hsec
        (le_inf hLW (by
          intro x _
          rw [Subgroup.mem_normalizer_iff]
          intro y
          rw [Subgroup.mem_bot, Subgroup.mem_bot]
          simp))
        (fun p hp v hv => by rw [hQcomm p hp v (hW hv)]; exact (⊥ : Subgroup G).one_mem)
        hntW
    rw [Subgroup.relIndex_bot_left] at hrel
    have hlt : Nat.card W < 2 ^ (2 * n) := by
      have hle : Nat.card W ≤ Nat.card (pCoreOf 2 L) := Subgroup.card_le_of_le hW
      have hne : Nat.card W ≠ Nat.card (pCoreOf 2 L) := by
        intro heq
        exact hwq (Subgroup.eq_of_le_of_card_ge hW (le_of_eq heq.symm))
      have hlt' : Nat.card W < Nat.card (pCoreOf 2 L) := lt_of_le_of_ne hle hne
      rwa [hcard] at hlt'
    omega
  · push Not at hntW
    by_cases hntV : ∃ l ∈ L, ∃ v ∈ pCoreOf 2 L, ⁅l, v⁆ ∉ W
    ·
      have hsec : GH74.QTGen4.DSGen4.IsElemSec W (pCoreOf 2 L) := by
        refine ⟨hW, ?_, ?_⟩
        · rw [Subgroup.commutator_le]
          intro a ha b hb
          rw [hQcomm a ha b hb]
          exact W.one_mem
        · intro e he
          rw [hQsq e he]
          exact W.one_mem
      have hrel : 2 ^ (2 * n) ≤ W.relIndex (pCoreOf 2 L) :=
        two_pow_le_relIndex_of_nontrivial (m := n) (by omega) hquot hsec
          (le_inf hLnormQ hLW)
          (fun p hp v hv => by rw [hQcomm p hp v hv]; exact W.one_mem)
          hntV
      have hrelcard : W.relIndex (pCoreOf 2 L) * Nat.card W = 2 ^ (2 * n) := by
        have h := Subgroup.relIndex_mul_card (H := W) (K := pCoreOf 2 L)
        rw [inf_eq_left.mpr hW, hcard] at h
        exact h
      have hpos : 0 < W.relIndex (pCoreOf 2 L) := by
        rw [Subgroup.relIndex, Subgroup.index]
        exact Nat.card_pos
      have hW2 : 2 ≤ Nat.card W := by
        have h1 : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot W).mpr hw
        omega
      have hle1 : Nat.card W ≤ 1 := by
        refine Nat.le_of_mul_le_mul_left ?_ hpos
        calc W.relIndex (pCoreOf 2 L) * Nat.card W = 2 ^ (2 * n) := hrelcard
          _ ≤ W.relIndex (pCoreOf 2 L) := hrel
          _ = W.relIndex (pCoreOf 2 L) * 1 := (mul_one _).symm
      omega
    ·
      push Not at hntV
      have hxW : x ∈ Subgroup.centralizer (W : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun w hw =>
          (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hntW x hxL w hw))).symm
      have hxS : x ∈ CFSG.Quasithin.E5.quotStab (pCoreOf 2 L) W := by
        rw [CFSG.Quasithin.E5.mem_quotStab_iff]
        exact ⟨hLW hxL, fun q hq => hntV x hxL q hq⟩
      have hxcentQ : x ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
        CFSG.Quasithin.E5.mem_centralizer_of_odd hW hQ2 hxW hxS hxodd
      exact hxne (eq_one_of_odd_of_mem_centralizer hc hxL hxodd hxcentQ)

private theorem pCoreOf_top_map (L : Subgroup G) :
    (pCoreOf 2 (⊤ : Subgroup ↥L)).map L.subtype = pCoreOf 2 L := by
  rw [← Subgroup.subgroupOf_self (H := L)]
  exact pCoreOf_subgroupOf_map le_rfl

private theorem card_pCoreOf_top (L : Subgroup G) :
    Nat.card (pCoreOf 2 (⊤ : Subgroup ↥L)) = Nat.card (pCoreOf 2 L) := by
  rw [← pCoreOf_top_map L]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).toEquiv

private theorem charTwo_top (L : Subgroup G) (hc : CharTwo L) :
    CharTwo (⊤ : Subgroup ↥L) := by
  simpa [Subgroup.subgroupOf_self] using
    (CFSG.Quasithin.F6.GoldPair.charTwo_subgroupOf_iff (I := L) (K := L) le_rfl).mpr hc

private theorem isL2Quot_top (L : Subgroup G) {n : ℕ} (hquot : IsL2Quot n (oTwoQuot ↥L)) :
    IsL2Quot n (oTwoQuot ↥(⊤ : Subgroup ↥L)) := by
  obtain ⟨e⟩ := hquot
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥(⊤ : Subgroup ↥L)) (CFSG.pCore 2 ↥L)
    Subgroup.topEquiv (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 Subgroup.topEquiv)).trans e⟩

theorem isElemAbelian_pCoreOf_of_card {L : Subgroup G} [Finite ↥L] {n : ℕ} (hn : 2 ≤ n)
    (hc : CharTwo L) (hquot : IsL2Quot n (oTwoQuot ↥L))
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (2 * n)) : IsElemAbelian 2 (pCoreOf 2 L) := by
  have htop := pCoreOf_top_map L
  have hcard' := (card_pCoreOf_top L).trans hcard
  have hfin : IsElemAbelian 2 (pCoreOf 2 (⊤ : Subgroup ↥L)) :=
    isElemAbelian_pCoreOf_of_card_finite hn (charTwo_top L hc) (isL2Quot_top L hquot) hcard'
  have hmap := hfin.map L.subtype
  rwa [htop] at hmap

theorem eq_bot_or_eq_pCoreOf_of_card {L W : Subgroup G} [Finite ↥L] {n : ℕ} (hn : 2 ≤ n)
    (hc : CharTwo L) (hquot : IsL2Quot n (oTwoQuot ↥L))
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (2 * n)) (hW : W ≤ pCoreOf 2 L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = pCoreOf 2 L := by
  have htop := pCoreOf_top_map L
  have hcard' := (card_pCoreOf_top L).trans hcard
  have hWL : W ≤ L := hW.trans (CFSG.openPCoreOf_le 2 L)
  have hsub : (pCoreOf 2 L).subgroupOf L = pCoreOf 2 (⊤ : Subgroup ↥L) :=
    Subgroup.map_injective L.subtype_injective (by
      rw [Subgroup.map_subgroupOf_eq_of_le (CFSG.openPCoreOf_le 2 L)]
      exact htop.symm)
  have hW' : W.subgroupOf L ≤ pCoreOf 2 (⊤ : Subgroup ↥L) := by
    rw [← hsub]
    exact Subgroup.subgroupOf_mono L hW
  have hLW' : (⊤ : Subgroup ↥L) ≤
      Subgroup.normalizer (W.subgroupOf L : Set ↥L) := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hcoe : ((y * w * y⁻¹ : ↥L) : G) = (y : G) * (w : G) * (y : G)⁻¹ := by simp
    rw [hcoe]
    exact Subgroup.mem_normalizer_iff.mp (hLW y.2) (w : G)
  rcases eq_bot_or_eq_pCoreOf_of_card_finite (L := ⊤) (W := W.subgroupOf L)
    hn (charTwo_top L hc) (isL2Quot_top L hquot) hcard' hW' hLW' with h | h
  · left
    calc W = (W.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hWL).symm
      _ = (⊥ : Subgroup ↥L).map L.subtype := by rw [h]
      _ = ⊥ := Subgroup.map_bot L.subtype
  · right
    calc W = (W.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hWL).symm
      _ = (pCoreOf 2 (⊤ : Subgroup ↥L)).map L.subtype := by rw [h]
      _ = pCoreOf 2 L := htop

end CFSG.Quasithin.St84
