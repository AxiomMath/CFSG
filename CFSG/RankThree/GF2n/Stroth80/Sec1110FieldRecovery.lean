module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Arith

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem card_eq_two_pow_of_naturalRep (hc : Ctx M Q Z B)
    {m x : ℕ} (hm : 3 ≤ m)
    {K : Type} [Field K] [Finite K] {X₁ X₂ : Subgroup G}
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁ (Q))
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) :
    Nat.card K = 2 ^ x := by
  obtain ⟨hQn, hNE⟩ := quotMulEquivBar (M := M) (Q := Q)
    (S := XbarPre M Q Z B) (Q_le_XbarPre hc) (XbarPre_le_M hc)
  letI := hQn
  obtain ⟨eBar⟩ := hNE
  let ePre : ↥(XbarPre M Q Z B) ⧸ Q.subgroupOf (XbarPre M Q Z B) ≃* Xbar M Q Z B :=
    eBar.trans (MulEquiv.subgroupCongr (bar_XbarPre hc))
  obtain ⟨φ, hrange, hker, hSA⟩ := nat2
  obtain ⟨hS, hN, ψ, hact⟩ := hSA
  have hker' : φ.rangeRestrict.ker = Q.subgroupOf (XbarPre M Q Z B) := by
    rw [MonoidHom.ker_rangeRestrict, hker]
  let eSL : ↥(XbarPre M Q Z B) ⧸ Q.subgroupOf (XbarPre M Q Z B) ≃* StatedSL m K :=
    ((QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ.rangeRestrict
        φ.rangeRestrict_surjective)).trans (MulEquiv.subgroupCongr hrange)
  let e : Xbar M Q Z B ≃* StatedSL m K := ePre.symm.trans eSL
  obtain ⟨eModK⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj
      (E := K) (d := m) e
  have hCM : CFSG.Open.StatedClassicalModel (XbarMod M Q Z B) .PSL m 2 x :=
    hLm.statedClassicalModel_of_ne_zero (by omega)
  obtain ⟨hadm, F, hF, hFfin, hFcard, ⟨eModF⟩⟩ := hCM
  have hx1 : 1 ≤ x := hadm.2.1
  have hKpow : ∃ f, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
    haveI hN' : (X₁.subgroupOf X₂).Normal := hN
    have hcardV : Nat.card (↥X₂ ⧸ X₁.subgroupOf X₂) = Nat.card K ^ m := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_fin]
    have hQ2 : IsPGroup 2 Q := by
      rw [hc.hyp.hQ]
      exact (pCore_isPGroup (p := 2) (G := M)).map M.subtype
    have hX₂2 : IsPGroup 2 X₂ := hQ2.to_le hX₂Q
    have hquot2 : IsPGroup 2 (↥X₂ ⧸ X₁.subgroupOf X₂) :=
      hX₂2.to_quotient (X₁.subgroupOf X₂)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥X₂ ⧸ X₁.subgroupOf X₂)).mp hquot2
    have hpow : Nat.card K ^ m = 2 ^ a := by
      rw [← hcardV, ha]
    letI : Fintype K := Fintype.ofFinite K
    haveI := ringChar.charP K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have hcardK : Nat.card K = (ringChar K) ^ (n : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hn
    have hdvd : ringChar K ∣ 2 ^ a := by
      rw [← hpow, hcardK, ← pow_mul]
      exact dvd_pow_self _ (mul_ne_zero n.ne_zero (by omega : m ≠ 0))
    have hp2 : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
    refine ⟨(n : ℕ), ?_, ?_⟩
    · exact n.pos
    · rw [hcardK, hp2]
  obtain ⟨f, hf1, hf⟩ := hKpow
  have hvK :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.padicValNat_card_statedProj_statedSL
      (K := K) (p := 2) (m := f) (a := m) Nat.prime_two hf1 hf (by omega)
  have hvF :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.padicValNat_card_statedProj_statedSL
      (K := F) (p := 2) (m := x) (a := m) Nat.prime_two hx1 hFcard (by omega)
  have hcardEq : Nat.card (StatedProj (StatedSL m K)) =
      Nat.card (StatedProj (StatedSL m F)) :=
    Nat.card_congr (eModK.symm.trans eModF).toEquiv
  have hvEq : f * (m * (m - 1) / 2) = x * (m * (m - 1) / 2) := by
    rw [← hvK, ← hvF, hcardEq]
  have hNpos : 0 < m * (m - 1) / 2 := by
    apply Nat.div_pos
    · calc 2 ≤ 3 * 2 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    · norm_num
  have hfx : f = x := Nat.eq_of_mul_eq_mul_right hNpos hvEq
  rw [hf, hfx]

theorem two_pow_eq_card_Z_of_naturalRep (hc : Ctx M Q Z B)
    {m x : ℕ} (hm : 3 ≤ m)
    {K : Type} [Field K] [Finite K] {X₁ X₂ : Subgroup G}
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁ (Q))
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x)
    (hK : Nat.card K = Nat.card Z) :
    2 ^ x = Nat.card Z :=
  (card_eq_two_pow_of_naturalRep hc hm hX₁ hX₂Q nat2 hLm).symm.trans hK

end CFSG.RankThree.GF2n.Stroth80
