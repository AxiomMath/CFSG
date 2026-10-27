module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsAutL3
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowAut
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def U3OddInnerEps : Prop :=
  ∀ n : ℕ, Odd n → ∀ (h : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) [Finite (unitaryPSU h 3)]
    (A : Subgroup (MulAut (unitaryPSU h 3))) (α : MulAut (unitaryPSU h 3))
    (K : Subgroup (unitaryPSU h 3)), α ∈ (psuConj h).range → CfgSEps (unitaryPSU h 3) A α K → False

theorem CfgSEps.exists_order_three {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    {σ : MulAut S} {K : Subgroup S} (hc : CfgSEps S A σ K) : ∃ k ∈ K, k ≠ 1 ∧ k ^ 3 = 1 := by
  have h3 : 3 ∣ Nat.card K :=
    (three_dvd_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)).trans
      (Subgroup.card_quotient_dvd_card _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3
  refine ⟨k, k.2, fun h1 => ?_, ?_⟩
  · have : k = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hk
    omega
  · have := pow_orderOf_eq_one k
    rw [hk] at this
    exact congrArg Subtype.val this

theorem two_pow_mod_three' (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem rowSEpsOf_seven_SU3_of (hU3 : U3OddInnerEps) :
    ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSU 3 2 n) := by
  intro n hn S _ _ hs hna ⟨eS⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 (2 * n) with hF
  have hFcard : Nat.card F = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  have h : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn, hFcard⟩
  obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  set τ : S ≃* unitaryPSU h 3 := eS.trans φ₀.symm with hτ
  haveI : Finite (unitaryPSU h 3) := Finite.of_equiv _ τ.toEquiv
  rcases two_pow_mod_three' n with hmod | hmod
  ·
    have hq2 : 2 < 2 ^ n := by
      have : n ≠ 1 := fun h1 => by rw [h1] at hmod; norm_num at hmod
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact noCfgSEps_of_autNoE27
      ((autNoE27_unitaryPSU_three_of_mod_one h hmod hq2).of_mulEquiv τ)
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | h
    · exfalso
      rw [← two_mul, pow_mul] at hmod
      norm_num [Nat.pow_mod] at hmod
    · exact h
  have hq2 : 2 < 2 ^ n ∨ n = 1 := by
    rcases Nat.eq_or_lt_of_le hn with rfl | h1
    · exact Or.inr rfl
    · left
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
      omega
  rcases hq2 with hq2 | rfl
  swap
  ·
    exfalso
    have hsolv : Group.IsSolvable (projSU 3 2 1) := CFSG.RankThree.PartTwo.Sec13.isSolvable_projSU_two
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := eS.symm.toMonoidHom) eS.symm.surjective
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr ‹_› a b)
  refine NoCfgSEps.of_mulEquiv τ ?_
  intro A α K hc
  haveI := hc.isPerfect
  have hα3 : α ^ 3 = 1 := hc.pow_three
  by_cases hD : α ∈ (psuConj h).range
  · exact hU3 n hodd h A α K hD hc
  ·
    have hnt : K ≠ ⊥ := by
      haveI := hc.nontrivial
      exact fun hb => by
        obtain ⟨x, hx1⟩ := exists_ne (1 : K)
        exact hx1 (Subtype.ext (by simpa [hb] using x.2))
    have h3 := hc.exists_order_three
    obtain ⟨φ, hφ, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
    have hστ' : MulAut.congr ((MulEquiv.refl _).trans (psuConj h H)⁻¹) α = psuField h φ := by
      rw [congr_trans_mulAut, hαH]
      ext x
      simp
    obtain ⟨m, hnm, hm, hK₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hφ
    have h₀ : UnitaryFieldData 2 m (fixedField φ) := ⟨Nat.prime_two, hm, hK₀⟩
    have hbar := bar_coe_fixedField h hnm h₀
    have hmod' : 2 ^ m % 3 = 2 := by
      rw [← pow_three_mod_three, ← pow_mul, mul_comm, ← hnm, hmod]
    by_cases hm1 : 2 ^ m = 2
    · exact false_of_uniFix_two h₀ hbar ((MulEquiv.refl _).trans (psuConj h H)⁻¹) hστ' hm1
        (fun x => Sec4.mem_autFix) hc.le_autFix hnt
    have hq₀ : 2 < 2 ^ m := by
      have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
      omega
    obtain ⟨⟨eK⟩, hO2⟩ := fieldCase_unitary h₀ hbar ((MulEquiv.refl _).trans (psuConj h H)⁻¹)
      hστ' hq₀ (fun x => Sec4.mem_autFix) hc.le_autFix hnt hc.isSubnormal h3
    have hG₀ : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) :=
      GaloisField.card 2 (2 * m) (by omega)
    have h₁ : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) := ⟨Nat.prime_two, hm, hG₀⟩
    have := Fintype.ofFinite (fixedField φ)
    have ψ : fixedField φ ≃+* GaloisField 2 (2 * m) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 (2 * m) (by omega) hK₀
    obtain ⟨φ₁⟩ := nonempty_unitaryPSU_mulEquiv_projSU h₁
    have eK' : K ≃* projSU 3 2 m := (eK.trans
      (CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.psuEquiv ψ h₁ h₀ hq₀)).trans φ₁
    have hKs : IsSimpleGroup K := by
      haveI : IsSimpleGroup (projSU 3 2 m) :=
        CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
          ⟨Nat.prime_two, hm, le_rfl, fun h' => by simp only [Prod.mk.injEq] at h'; omega⟩
      exact eK'.isSimpleGroup
    have hO2K : CFSG.pCore 2 K = ⊥ := by
      haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 K) with h' | h'
      · exact h'
      · exfalso
        obtain ⟨k, hkK, hk1, hk3⟩ := h3
        have hkN : (⟨k, hkK⟩ : K) ∈ CFSG.pCore 2 K := h' ▸ Subgroup.mem_top _
        exact hk1 (congrArg Subtype.val (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup
          hkN (Subtype.ext (by simpa using hk3))))
    have e1 : K ⧸ CFSG.pCore 2 K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hO2K).trans QuotientGroup.quotientBot
    exact false_of_isTypeEps_of_isoLThreePi hc.isType hm (p := 2)
      (Or.inr ⟨hmod', ⟨e1.trans eK'⟩⟩)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
