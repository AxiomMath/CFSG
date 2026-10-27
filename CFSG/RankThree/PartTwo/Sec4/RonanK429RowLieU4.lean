module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieRows
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieArithU4
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4FieldOuter
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOdd
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj StatedScalars)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3

@[expose] def U4OddInner429 : Prop :=
  ∀ n : ℕ, Odd n → ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* projSU 4 2 n) →
    ∀ σ : MulAut S, IsInnerAut σ → σ ^ 3 = 1 → σ ≠ 1 →
      ∀ K : Subgroup S, K ≤ Sec4.autFix σ → Group.IsPerfect K →
        (K.subgroupOf (Sec4.autFix σ)).IsSubnormal → IsType429 (K ⧸ CFSG.pCore 2 K) → False

section U4


theorem isSimpleGroup_unitarySU_four {k : ℕ} {F : Type} [Field F] (h₀ : UnitaryFieldData 2 k F) :
    IsSimpleGroup (unitarySU 2 k F 4) := by
  have := h₀.finite
  have hbot : unitaryScalars h₀ 4 = ⊥ := by
    rw [unitaryScalars_eq h₀ (by norm_num)]
    have hodd : Odd (2 ^ k + 1) :=
      (Nat.even_pow.mpr ⟨even_two, by have := h₀.one_le; omega⟩).add_one
    have hcop : Nat.Coprime 4 (2 ^ k + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    exact CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot
      (by rw [h₀.card, ← pow_mul, mul_comm]) (by norm_num) hcop
  haveI := CFSG.SeitzReduction.UnitaryPilot.isSimpleGroup_unitaryPSU_of_three_le h₀
    (n := 4) (by norm_num) (by simp)
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem u4Excl429 {k : ℕ} {F : Type} [Field F] (h₀ : UnitaryFieldData 2 k F) (G : Type) [Group G]
    [Finite G] (C J : Subgroup G) (hC : Nonempty (C ≃* unitarySU 2 k F 4)) (hJC : J ≤ C)
    (hJperf : Group.IsPerfect J) (hsub : (J.subgroupOf C).IsSubnormal)
    (htype : IsType429 (J ⧸ CFSG.pCore 2 J)) : False := by
  obtain ⟨eC⟩ := hC
  haveI := hJperf
  obtain ⟨E, hEJ, -, hE3, hE9, -⟩ := exists_e9_of_type429 htype
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have hk₀J : k₀ ∈ J := hEJ hk₀E
  have hJnt : J ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hk₀J))
  have hk₀1' : (⟨k₀, hk₀J⟩ : J) ≠ 1 := fun h => hk₀1 (congrArg Subtype.val h)
  have hk₀3' : (⟨k₀, hk₀J⟩ : J) ^ 3 = 1 := Subtype.ext (by simpa using hk₀3)
  haveI := isSimpleGroup_unitarySU_four h₀
  have hCs' : IsSimpleGroup C := eC.isSimpleGroup
  have hJC' : J = C := eq_of_subnormal_of_le_simple hJC le_rfl hsub hCs' hJnt
  haveI hJs : IsSimpleGroup J := by
    rw [hJC']
    exact hCs'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : CFSG.pCore 2 J = ⊥ := by
    haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 J) with h | h
    · exact h
    · exfalso
      have hkN : (⟨k₀, hk₀J⟩ : J) ∈ CFSG.pCore 2 J := h ▸ Subgroup.mem_top _
      exact hk₀1' (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup hkN hk₀3')
  have hcardQ : Nat.card (J ⧸ CFSG.pCore 2 J) =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
    have e1 : (J ⧸ CFSG.pCore 2 J) ≃* J :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
    rw [Nat.card_congr e1.toEquiv, ← card_unitarySU_four h₀, ← Nat.card_congr eC.toEquiv]
    exact congrArg (fun H : Subgroup G => Nat.card H) hJC'
  have hk1 := h₀.one_le
  have hbig : 604800 < (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1))
      ∨ (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) = 25920 := by
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk2
    · right
      norm_num
    · left
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have h6 : 4 ^ 6 ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left h4 6
      have hA : 15 ≤ (2 ^ k) ^ 2 - 1 := by
        have := Nat.pow_le_pow_left h4 2
        omega
      have hB : 65 ≤ (2 ^ k) ^ 3 + 1 := by
        have := Nat.pow_le_pow_left h4 3
        omega
      have hC4 : 255 ≤ (2 ^ k) ^ 4 - 1 := by
        have := Nat.pow_le_pow_left h4 4
        omega
      calc 604800 < 4 ^ 6 * (15 * 65 * 255) := by norm_num
        _ ≤ (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) :=
          Nat.mul_le_mul h6 (Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC4)
  rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, -⟩⟩ |
    hc | hc | hc | hc
  · exact u4_mul_three_ne_L3 hk1 hp hp3 he (hcardQ ▸ hc)
  · exact u4_mul_three_ne_U3 hk1 hp hp3 he (hcardQ ▸ hc)
  all_goals omega

end U4

section Chain


theorem exists_autFix_mulEquiv_unitarySU_four {n : ℕ} (hn1 : 1 ≤ n)
    {α : MulAut (projSU 4 2 n)} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ k : ℕ, n = 3 * k ∧ 1 ≤ k ∧ ∃ (F : Type) (_ : Field F) (h₀ : UnitaryFieldData 2 k F),
      Nonempty (Sec4.autFix α ≃* unitarySU 2 k F 4) := by
  have hU := unitaryFieldData_galoisField 2 n hn1
  have hC : IsPrimeFormGram (1 : GL (Fin 4) (GaloisField 2 (2 * n))) := isPrimeFormGram_one_GL
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (by norm_num)
    (fun h' => absurd h'.1 (by norm_num))
  set P := primeFormP hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) with hPdef
  let e : projSU 4 2 n ≃* P :=
    (projSUEquivStatedProj 4 2 n).trans ((unitaryPSUEquiv hU (by norm_num)).symm.trans e₃.symm)
  set β := MulAut.congr e α with hβdef
  have hβ : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut β := fun h' => hout ((isInnerAut_congr e α).mp h')
  obtain ⟨φ, H, hφ3, hβeq⟩ := WitnessU4.exists_eq_conj_primeFormFieldHom hU hC β hβ hβout
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hβout
    rw [hβeq, map_one, mul_one, mul_inv_cancel]
    exact ⟨1, map_one _⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨f₀, hf, hf₀, hcard⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three hU hσ
  have h₀ : UnitaryFieldData 2 f₀ (fixedField φ) := ⟨Nat.prime_two, hf₀, hcard⟩
  have hbar := KFacts.bar_coe_fixedField hU hf h₀
  have := h₀.finite
  set Y := unitarySU 2 f₀ (fixedField φ) 4 with hYdef
  set fφ := primeFormFieldHom hU hC φ
  set σS := primeFormFieldSU hU hC φ
  set cH := primeFormConjHom hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) H
  have h1 : (Item426.fixSub α).map e.toMonoidHom = Item426.fixSub β := Item426.map_fixSub_eq e α
  have h2 : Item426.fixSub β = (Item426.fixSub fφ).map cH.toMonoidHom := by
    rw [hβeq, fixSub_conj]
  have h3 : Item426.fixSub fφ = (Item426.fixSub σS).map (primeFormPEquiv hU _).toMonoidHom :=
    fixSub_primeFormFieldHom_eq hU hC φ
  have hSeq : unitarySU 2 n (GaloisField 2 (2 * n)) 4 = gramSU hU
      ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU hU 4
  set ι : Y →* gramSU hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) :=
    (MulEquiv.subgroupCongr hSeq).toMonoidHom.comp (suInclFix hU h₀ hbar) with hιdef
  have hιinj : Function.Injective ι :=
    (MulEquiv.subgroupCongr hSeq).injective.comp (suInclFix_injective hU h₀ hbar)
  have hrange : ι.range = Item426.fixSub σS := by
    ext y
    rw [Item426.mem_fixSub]
    constructor
    · rintro ⟨g₀, rfl⟩
      apply Subtype.ext
      change glAut φ ((suInclFix hU h₀ hbar g₀ : unitarySU 2 n _ 4) : GL (Fin 4) _) = _
      exact (mem_range_suInclFix_iff hU h₀ hbar _).mp ⟨g₀, rfl⟩
    · intro hy
      have hy' : glAut φ (y : GL (Fin 4) (GaloisField 2 (2 * n))) = y := congrArg Subtype.val hy
      have hy2 : (y : GL (Fin 4) (GaloisField 2 (2 * n))) ∈
          unitarySU 2 n (GaloisField 2 (2 * n)) 4 := by
        rw [hSeq]
        exact y.2
      obtain ⟨g₀, hg₀⟩ := (mem_range_suInclFix_iff hU h₀ hbar
        (⟨(y : GL (Fin 4) (GaloisField 2 (2 * n))), hy2⟩ :
          unitarySU 2 n (GaloisField 2 (2 * n)) 4)).mpr hy'
      refine ⟨g₀, Subtype.ext ?_⟩
      change ((suInclFix hU h₀ hbar g₀ : unitarySU 2 n (GaloisField 2 (2 * n)) 4) :
        GL (Fin 4) (GaloisField 2 (2 * n))) = (y : GL (Fin 4) (GaloisField 2 (2 * n)))
      rw [hg₀]
  have Φ : Item426.fixSub α ≃* Y :=
    (((Item426.fixSub α).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (h1.trans h2)).trans
        ((Item426.fixSub fφ).equivMapOfInjective cH.toMonoidHom cH.injective).symm)).trans
      (((MulEquiv.subgroupCongr h3).trans
        ((Item426.fixSub σS).equivMapOfInjective _ (primeFormPEquiv hU _).injective).symm).trans
        ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hιinj).symm))
  have hfix : Sec4.autFix α = Item426.fixSub α := by
    ext x
    rw [Sec4.mem_autFix, Item426.mem_fixSub]
  exact ⟨f₀, hf, hf₀, fixedField φ, inferInstance, h₀, ⟨(MulEquiv.subgroupCongr hfix).trans Φ⟩⟩

end Chain

section Row


theorem seven_SU4_of (hU4 : U4OddInner429) :
    ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSU 4 2 n) := by
  intro n hn
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨eS⟩ => ?_
  intro A σ K hc
  haveI := hc.isPerfect
  have hσ3 := cfgS429_pow_three hc
  set α := MulAut.congr eS σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hin : IsInnerAut σ
  · rcases Nat.even_or_odd n with hev | hodd
    ·
      obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 hc.isType
      have hfix : ∀ k ∈ K, σ k = k := fun k hk => Sec4.mem_autFix.mp (hc.le_autFix hk)
      have hZ := center_trivial_of_isSimpleGroup hs hna
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hmod : 2 ^ n % 3 = 1 := by
        obtain ⟨j, rfl⟩ := hev
        rw [← two_mul, pow_mul]
        norm_num [Nat.pow_mod]
      have hrank := Sec4.HeringUnitary.pRank_projSU_four_le_two (p := 2) (by norm_num) hn hmod
      have hcen := Sec4.RonanK432.center_projSU_four_two_eq_bot hn
      refine false_of_fix_e9 (MulAut.conj : S →* MulAut S).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
        hσ3 hc.ne_one hEK hEc hE3 hE9 hfix hEZ
      intro B hB h3B hcB
      refine card_le_nine_inn (fun E' hE' h27 => ?_) hZ hB h3B hcB
      set ψ : S →* projSU 4 2 n ⧸ Subgroup.center (projSU 4 2 n) :=
        (QuotientGroup.mk' (Subgroup.center (projSU 4 2 n))).comp eS.toMonoidHom with hψ
      have hψinj : Function.Injective ψ := by
        intro x y hxy
        have h1 := QuotientGroup.eq.mp hxy
        rw [hcen, Subgroup.mem_bot] at h1
        exact eS.injective (inv_mul_eq_one.mp h1)
      refine Sec4.Item434Spor.noE27_of_pRank_le_two hrank (E'.map ψ) ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩ ?_
      · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
        apply Subtype.ext
        simp only [Subgroup.coe_mul, ← map_mul]
        exact congrArg ψ (congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hE'.2 x hx, map_one]
      · rw [Subgroup.card_map_of_injective hψinj, h27]
    ·
      exact hU4 n hodd S ⟨eS⟩ σ hin hσ3 hc.ne_one K hc.le_autFix hc.isPerfect hc.isSubnormal
        hc.isType
  ·
    have hαout : ¬ IsInnerAut α := fun h => hin ((isInnerAut_congr eS σ).mp h)
    obtain ⟨k, -, -, F, _, h₀, ⟨eα⟩⟩ := exists_autFix_mulEquiv_unitarySU_four hn hα3 hαout
    exact u4Excl429 h₀ S (Sec4.autFix σ) K ⟨(Sec4.autFixCongrEquiv eS σ).symm.trans eα⟩
      hc.le_autFix hc.isPerfect hc.isSubnormal hc.isType

end Row

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
