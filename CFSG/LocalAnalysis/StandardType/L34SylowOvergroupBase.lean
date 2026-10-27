
module

public import CFSG.LocalAnalysis.StandardType.PermStabilizerAlternatingSix
public import CFSG.LocalAnalysis.StandardType.SylowOvergroupReduction
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.StandardType.L34SylowTabs
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

@[expose] public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem closureTabs_gensS : closureTabs gensS = S := by
  unfold closureTabs S
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, hr⟩
    obtain ⟨a, ha, har⟩ := gensS_tabs j hj
    rw [hr.perm_eq har]
    exact ha
  · exact fun hg => gensS_cover g hg

structure OvergroupFacts : Prop where
  card_S : Nat.card ↥(closureTabs gensS) = 20160
  card_P : Nat.card ↥(closureTabs pGens) = 9
  P_le_S : closureTabs pGens ≤ closureTabs gensS
  aSix : ∀ j < 6, commutator ↥(closureTabs (pGensWith mRs[j]!)) = ⊤ ∧
    Nonempty (↥(closureTabs (pGensWith mRs[j]!)) ≃* alternatingGroup (Fin 6))
  trichotomy : ∀ Z : Subgroup (Equiv.Perm (Fin 42)), closureTabs pGens ≤ Z →
    Z ≤ closureTabs gensS → Z = closureTabs gensS ∨
      (∃ j < 6, Z = closureTabs (pGensWith mRs[j]!)) ∨ Group.IsSolvable ↥Z

theorem isSolvable_of_no_order {Z : Subgroup (Equiv.Perm (Fin 42))}
    (hcard : Nat.card ↥(closureTabs gensS) = 20160) (hZS : Z ≤ closureTabs gensS)
    (h5 : ¬ ∃ x ∈ Z, x ≠ 1 ∧ x ^ 5 = 1) (h7 : ¬ ∃ x ∈ Z, x ≠ 1 ∧ x ^ 7 = 1) :
    Group.IsSolvable ↥Z := by
  have hdvd : Nat.card ↥Z ∣ 20160 := hcard ▸ Subgroup.card_dvd_of_le hZS
  have hnd : ∀ q : ℕ, q.Prime → (¬ ∃ x ∈ Z, x ≠ 1 ∧ x ^ q = 1) → ¬ q ∣ Nat.card ↥Z := by
    intro q hq hno hdq
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdq
    refine hno ⟨(x : Equiv.Perm (Fin 42)), x.2, ?_, ?_⟩
    · intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      exact hq.one_lt.ne hx
    · have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
  have hc5 : Nat.Coprime (Nat.card ↥Z) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 (hnd 5 Nat.prime_five h5)).symm
  have hc7 : Nat.Coprime (Nat.card ↥Z) 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hnd 7 (by norm_num) h7)).symm
  exact SylowOvergroup.isSolvable_of_coprime (a := 6) (b := 2) (m := 35)
    (by norm_num; exact hdvd) (by simpa [show (35 : ℕ) = 5 * 7 from rfl] using hc5.mul_right hc7)

end CFSG.StandardType.L34Sylow
