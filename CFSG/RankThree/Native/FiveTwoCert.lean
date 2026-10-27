module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoCert

public section

namespace CFSG.RankThree.Native

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census

structure FiveTwoData where
  base : Data
  w : ℕ

namespace FiveTwoData

variable {M V : Type} (O : Ops M V)

@[expose] def check [Inhabited M] (D : FiveTwoData) : Bool :=
  let R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  D.base.prog.all (Op.lt D.base.nregs) && decide (D.w < D.base.nregs) &&
    O.eq (O.pow R[D.w]! 10) O.one &&
    NC2Data.movesOK O D.base.tests (O.pow R[D.w]! 5) &&
    NC2Data.movesOK O D.base.tests (O.pow R[D.w]! 2)

end FiveTwoData

theorem exists_commuting_two_five_of_pow {G : Type*} [Group G] {w : G} (h10 : w ^ 10 = 1)
    (h5 : w ^ 5 ≠ 1) (h2 : w ^ 2 ≠ 1) :
    ∃ z y : G, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨w ^ 5, w ^ 2, orderOf_eq_prime ?_ h5, orderOf_eq_prime ?_ h2,
    (Commute.pow_pow_self w 5 2).eq⟩
  · rw [← pow_mul]
    exact h10
  · rw [← pow_mul]
    exact h10

theorem exists_commuting_two_five_of_mulEquiv {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    (h : ∃ z y : G, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z) :
    ∃ z y : S, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z := by
  obtain ⟨z, y, hz, hy, hzy⟩ := h
  refine ⟨e.symm z, e.symm y, by rw [MulEquiv.orderOf_eq, hz], by rw [MulEquiv.orderOf_eq, hy], ?_⟩
  rw [← map_mul, ← map_mul, hzy]

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem exists_of_fiveTwoCheck [Inhabited M] (D : FiveTwoData)
    (h : FiveTwoData.check O D = true) :
    ∃ z y : (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ,
      orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z := by
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold FiveTwoData.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hprog, hw⟩, h10⟩, h5⟩, h2⟩ := h
  have hA : Sp.WF (O.decode D.base.seedA) ∧ Sp.toMat (O.decode D.base.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.base.seedB) ∧ Sp.toMat (O.decode D.base.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ := PartTwo.Census.OpsSpec.initRegs_regs Sp S hA hB D.base.nregs
  obtain ⟨hs, hok⟩ :=
    PartTwo.Census.OpsSpec.run_regs Sp S D.base.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  obtain ⟨hWf, hWS⟩ := hok D.w (by rw [hs, hs0]; exact hw)
  have hpow : ∀ e : ℕ, Sp.toMat (O.pow R[D.w]! e) = Sp.toMat R[D.w]! ^ e :=
    fun e => (Sp.pow_spec hWf e).2
  have hW10 : Sp.toMat R[D.w]! ^ 10 = 1 := by
    rw [← hpow, ← Sp.toMat_one]
    exact Sp.toMat_eq (Sp.pow_spec hWf 10).1 Sp.one_wf h10
  have hW5 : Sp.toMat R[D.w]! ^ 5 ≠ 1 := by
    rw [← hpow]
    exact PartTwo.Census.OpsSpec.toMat_ne_one_of_movesOK Sp (Sp.pow_spec hWf 5).1 h5
  have hW2 : Sp.toMat R[D.w]! ^ 2 ≠ 1 := by
    rw [← hpow]
    exact PartTwo.Census.OpsSpec.toMat_ne_one_of_movesOK Sp (Sp.pow_spec hWf 2).1 h2
  have hS10 : (⟨Sp.toMat R[D.w]!, hWS⟩ : S) ^ 10 = 1 :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hW10)
  let u : Sˣ := Units.ofPowEqOne _ 10 hS10 (by norm_num)
  have hu : ∀ e : ℕ,
      (((u ^ e : Sˣ) : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat R[D.w]! ^ e := fun e => by
    rw [Units.val_pow_eq_pow_val, Units.val_ofPowEqOne, SubmonoidClass.coe_pow]
  refine exists_commuting_two_five_of_pow (w := u) (Units.pow_ofPowEqOne _ _) (fun h => hW5 ?_)
    (fun h => hW2 ?_)
  · rw [← hu 5, h, Units.val_one, OneMemClass.coe_one]
  · rw [← hu 2, h, Units.val_one, OneMemClass.coe_one]

end OpsSpec

end CFSG.RankThree.Native
