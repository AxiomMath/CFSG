module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenDefs
public import CFSG.Quasithin.Vol2.Ch11SecE3L0
import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompL2
import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple
import CFSG.LocalAnalysis.WeakClosure81.GenEiConj
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn
import CFSG.RankThree.GF2n.Tim79a34ResidualSylow
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.Quasithin.Recognition.GoldschmidtF112RY9Group
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

namespace FourTenSetting

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p e : ℕ}

theorem five_le (h : FourTenSetting Q L p e) : 5 ≤ p ^ e := by
  have hodd : Odd (p ^ e) := (h.prime.odd_of_ne_two h.ne_two).pow
  obtain ⟨k, hk⟩ := hodd
  have h3 := h.three_lt
  omega

theorem isSimpleGroup (h : FourTenSetting Q L p e) : IsSimpleGroup ↥L :=
  (EmptyFaithfulMultiple.F618Comp.isL2_facts h.isL2 h.ne_two h.five_le).1

theorem nonabelian (h : FourTenSetting Q L p e) : ∃ a b : ↥L, a * b ≠ b * a :=
  (EmptyFaithfulMultiple.F618Comp.isL2_facts h.isL2 h.ne_two h.five_le).2.1

theorem centralizer_eq_bot (h : FourTenSetting Q L p e) :
    centralizer (L : Set Q) = ⊥ := by
  have hgf : CFSG.generalizedFitting Q = L := by
    rw [← fstar_top_eq_generalizedFitting Q, h.fstar_eq]
  have hle : centralizer (L : Set Q) ≤ L := by
    have := CFSG.centralizer_generalizedFitting_le Q
    rwa [hgf] at this
  have : IsSimpleGroup ↥L := h.isSimpleGroup
  have hZ : Subgroup.center ↥L = ⊥ :=
    EmptyFaithfulMultiple.F618Comp.center_eq_bot_of_isSimpleGroup h.nonabelian
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ L := hle hx
  have hxc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
  rw [hZ, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

theorem sup_eq_top_of_isSylowIn (h : FourTenSetting Q L p e) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) : L ⊔ T = ⊤ := by
  obtain ⟨T₀, hT₀, hLT₀⟩ := h.sup_eq_top
  have : L.Normal := h.normal
  have hquotTop : IsPGroup 2 (↥(⊤ : Subgroup Q) ⧸ L.subgroupOf ⊤) :=
    CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (K := ⊤) hT₀.isPGroup le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      (by simpa using hLT₀)
  have hquot : IsPGroup 2 (Q ⧸ L) := hquotTop.of_equiv
    (QuotientGroup.congr _ _ (Subgroup.topEquiv (G := Q)) (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmain := CFSG.RankThree.GF2n.Tim79a.sup_eq_top_of_sylow hquot
    (hT.isPGroup.toSylow (by
      simpa [Subgroup.relIndex_top_right] using hT.not_dvd_relIndex))
  simpa using hmain

theorem almostSimple (h : FourTenSetting Q L p e) : Vol2.Ch11.SecE3.AlmostSimple L := by
  obtain ⟨T, hT, hLT⟩ := h.sup_eq_top
  exact almostSimple_of_normal_simple_sup_sylow h.normal h.isSimpleGroup h.nonabelian
    h.centralizer_eq_bot hT hLT

theorem pCoreOf_two_top (h : FourTenSetting Q L p e) : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ :=
  pCoreOf_top_eq_bot_of_almostSimple h.normal h.isSimpleGroup h.nonabelian h.centralizer_eq_bot

theorem tA_eq (h : FourTenSetting Q L p e) (T A : Subgroup Q) :
    tA T A = T ⊓ centralizer (A : Set Q) := by
  have hO : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := h.pCoreOf_two_top
  ext t
  rw [tA, E1.mem_tauOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff_commutator_eq_one']
  constructor
  · rintro ⟨ht, -, hcomm⟩
    exact ⟨ht, by simpa [hO] using hcomm⟩
  · rintro ⟨ht, hcomm⟩
    refine ⟨ht, ?_, fun a ha => ?_⟩
    · rw [hO, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top t
    · rw [hO, Subgroup.mem_bot]
      exact hcomm a ha

end FourTenSetting

theorem w4Lem4_10F_of (hL : FourTenLarge) (hP : FourTenPrime)
    (h9 : FourTenNine) : W4Lem4_10F := by
  intro Q _ _ L p e hset T hTsyl Ω hΩ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hTsyl
  rw [inFOmega_iff_sup_eq_top 1 hΩ]
  have hodd : Odd p := hset.prime.odd_of_ne_two hset.ne_two
  have hcases : (3 ≤ e ∨ (e = 2 ∧ 5 ≤ p)) ∨ (e = 1 ∧ 7 ≤ p) ∨ (p = 3 ∧ e = 2) := by
    rcases e with _ | e
    · have h3 := hset.three_lt
      simp only [pow_zero] at h3
      omega
    rcases e with _ | e
    · right; left
      have hp3 : 3 < p := by simpa using hset.three_lt
      have hp5 : 5 ≤ p := by
        obtain ⟨k, hk⟩ := hodd
        rcases lt_or_ge p 5 with hp | hp
        · omega
        · exact hp
      refine ⟨rfl, ?_⟩
      rcases lt_or_ge p 7 with hp | hp
      · have hpne5 : p ≠ 5 := by
          rintro rfl
          exact hset.not_isAlt_five
            (CFSG.QuasithinUnique.Setup.Family.alternating_five_of_model_five hset.isL2)
        obtain ⟨k, hk⟩ := hodd
        omega
      · exact hp
    rcases e with _ | e
    · rcases lt_or_ge p 5 with hp | hp
      · right; right
        have hp3 : p = 3 := by
          obtain ⟨k, hk⟩ := hodd
          have h2p : 2 ≤ p := hset.prime.two_le
          have h2 : 2 < p := by omega
          omega
        exact ⟨hp3, rfl⟩
      · left; right; exact ⟨rfl, hp⟩
    · left; left; omega
  by_cases hall : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A
  · rcases hcases with hlarge | hprime | hnine
    · exact hL Q L p e hset hlarge T hTs Ω hΩ hall
    · exact hP Q L p e hset hprime T hTs Ω hΩ hall
    · exact h9 Q L p e hset hnine T hTs Ω hΩ hall
  · push Not at hall
    obtain ⟨B, hBΩ, hBT, hBlt⟩ := hall
    have hBel : IsElemAbelian 2 B := hΩ.elemAbelian B hBΩ
    have hBne : B ≠ ⊥ := hΩ.ne_bot B hBΩ
    have hBpg : IsPGroup 2 B := hBel.isPGroup
    have hB2 : Nat.card B ≤ 2 := by
      by_contra h
      have h2ne : Nat.card B ≠ 2 := by omega
      have h4 := CFSG.QuasithinUnique.four_le_card_of_ne_two hBpg hBne h2ne
      omega
    have hmq : E3.mQuot B (pCoreOf 2 (⊤ : Subgroup Q)) ≤ 1 :=
      mQuot_pCoreOf_top_le_of_card_le hset.almostSimple hBpg (by simpa using hB2)
    have hIn : InCalEi 1 T B ⊤ :=
      inCalEi_top_of_almostSimple hset.almostSimple hTs hBne hmq
    exact eq_top_iff.mpr ((le_genEi_of_inCalEi hBΩ hBT hIn).trans le_sup_left)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
