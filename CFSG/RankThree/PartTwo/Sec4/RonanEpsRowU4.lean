module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4
public import CFSG.RankThree.PartTwo.KFacts.KS222U4Even
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def U4OddInnerEps : Prop :=
  ∀ n : ℕ, Odd n → ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* projSU 4 2 n) →
    ∀ σ : MulAut S, IsInnerAut σ → σ ^ 3 = 1 → σ ≠ 1 →
      ∀ K : Subgroup S, K ≤ Sec4.autFix σ → Group.IsPerfect K →
        (K.subgroupOf (Sec4.autFix σ)).IsSubnormal → IsTypeEps (K ⧸ CFSG.pCore 2 K) →
          IsTypeEpsCube (K ⧸ CFSG.pCore 2 K) → False

theorem isSimpleGroup_unitarySU_four' {k : ℕ} {F : Type} [Field F] (h₀ : UnitaryFieldData 2 k F) :
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

theorem CfgSEps.false_of_autFix_su4 {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    {σ : MulAut S} {K : Subgroup S} (hc : CfgSEps S A σ K) {k : ℕ} {F : Type} [Field F]
    (h₀ : UnitaryFieldData 2 k F) (eC : autFix σ ≃* unitarySU 2 k F 4) : False := by
  have hcardC : Nat.card (autFix σ) =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
    rw [Nat.card_congr eC.toEquiv, Item419Res3.card_unitarySU_four h₀]
  have hk1 := h₀.one_le
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk2
  · have h1 := le_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
    have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card (autFix σ) :=
      (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hc.le_autFix)
    rw [hcardC] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    norm_num at this
    omega
  · haveI hs := isSimpleGroup_unitarySU_four' h₀
    have hna : ∃ a b : unitarySU 2 k F 4, a * b ≠ b * a := by
      by_contra h
      push Not at h
      haveI := hc.nontrivial
      haveI := hc.isPerfect
      have hKab : ∀ a b : K, a * b = b * a := fun a b => Subtype.ext
        (show (a : S) * b = b * a from by
          have := congrArg (fun x => ((eC.symm x : autFix σ) : S))
            (h (eC ⟨a, hc.le_autFix a.2⟩) (eC ⟨b, hc.le_autFix b.2⟩))
          simpa only [← map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] using this)
      exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hKab)
    obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
    have hcube := hc.isTypeEpsCube_of_le hc.le_autFix le_rfl
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hq) (center_eq_bot_of_mulEquiv eC hZ)
    exact not_isTypeEpsCube_of_card_u4_even hk1 hcardC hcube

section Row


theorem rowSEpsOf_seven_SU4_of (hU4 : U4OddInnerEps) :
    ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSU 4 2 n) := by
  intro n hn S _ _ hs hna ⟨eS⟩ A σ K hc
  haveI := hc.isPerfect
  by_cases hin : IsInnerAut σ
  · rcases Nat.even_or_odd n with hev | hodd
    ·
      obtain ⟨s, rfl⟩ := hin
      have hZ := center_eq_bot_of_isSimpleGroup hs hna
      have hinj := conj_injective_of_center_eq_bot hZ
      have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hc.pow_three, map_one])
      have hs1 : s ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
      have hℓ : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hso]
      have hcz : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup S) : Set S) =
          Subgroup.centralizer ({s} : Set S) := by
        ext x
        simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
          SetLike.mem_coe]
        constructor
        · intro h
          exact h s (Subgroup.mem_zpowers s)
        · intro h y hy
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact (Commute.zpow_left (show Commute s x from h) k).eq
      have hfix : autFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) :=
        RowV.autFix_conj_eq_centralizer s
      have htop : (⊤ : Subgroup S) ⊓ Subgroup.centralizer ((Subgroup.zpowers s : Subgroup S) :
          Set S) = autFix (MulAut.conj s) := by
        rw [top_inf_eq, hcz, hfix]
      have hn0 : 0 < n := by omega
      have hres := Sec21.ks222U4Even S ⊤ (Subgroup.zpowers s) n hn0 hev
        ⟨Subgroup.topEquiv.trans eS⟩ le_top hℓ
      rw [htop] at hres
      set N := inSubgroup perfectResidual (autFix (MulAut.conj s)) with hN
      have hKN : K ≤ N := hc.le_perfectResidual
      have hNC : N ≤ autFix (MulAut.conj s) := Subgroup.map_subtype_le _
      have key : ∀ m : ℕ, 2 ≤ m → Nonempty (N ≃* projSL 2 (GaloisField 2 m)) → False := by
        intro m hm ⟨ι⟩
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hFm : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
        obtain ⟨ι₂⟩ := nonempty_sl2_mulEquiv_projSL hFm
        set ι' := ι.trans ι₂.symm
        have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
          rw [hFm]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        haveI : CharP (GaloisField 2 m) 2 := inferInstance
        have hNq : IsQuasisimple N := CFSG.LocalCores.isQuasisimple_of_mulEquiv ι'.symm
          (RonanKChevTwo.SpFour.isQuasisimple_sl2 h4)
        have hNZ : Subgroup.center N = ⊥ :=
          center_eq_bot_of_mulEquiv ι' Sec19.Item19Res2Proof.center_sl2_eq_bot
        have hcube := hc.isTypeEpsCube_of_le hKN hNC hNq hNZ
        refine not_isTypeEpsCube_of_card_sl2_even (n := m) (by omega) ?_ hcube
        rw [Nat.card_congr ι'.toEquiv, card_SL_two, hFm]
      have hn2 : 2 ≤ n := by obtain ⟨j, rfl⟩ := hev; omega
      rcases hres with h | h
      · exact key n hn2 h
      · exact key (2 * n) (by omega) h
    ·
      exact hU4 n hodd S ⟨eS⟩ σ hin hc.pow_three hc.ne_one K hc.le_autFix hc.isPerfect
        hc.isSubnormal hc.isType (isTypeEpsCube_of_cfgSEps hc)
  ·
    set α := MulAut.congr eS σ with hα
    have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hc.pow_three, map_one]
    have hαout : ¬ IsInnerAut α := fun h => hin ((isInnerAut_congr eS σ).mp h)
    obtain ⟨k, -, -, F, _, h₀, ⟨eα⟩⟩ := exists_autFix_mulEquiv_unitarySU_four hn hα3 hαout
    exact hc.false_of_autFix_su4 h₀ ((Sec4.autFixCongrEquiv eS σ).symm.trans eα)

end Row

end CFSG.RankThree.PartTwo.Sec4.RonanEps
