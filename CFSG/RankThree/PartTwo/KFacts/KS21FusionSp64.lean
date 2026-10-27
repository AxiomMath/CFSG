module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionCore
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionDFT
public import CFSG.RankThree.PartTwo.KFacts.KS21Sp64

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.Sp64

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21.DFT CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem leviSp_injective : Function.Injective (leviSp (r := 3) (k := F4)) := by
  intro A B h
  apply Units.ext
  ext i j
  have := congrArg (fun g : Sp => mat g (Sum.inl i) (Sum.inl j)) h
  simpa [mat, coe_leviSp] using this

theorem card_Sp_eq : Nat.card Sp = 3 ^ (3 + 1) * 50692096000 := by
  rw [card_statedSp, card_F4]
  decide

theorem exists_omega : ∃ ω : F4ˣ, orderOf ω = 3 := by
  have h := IsCyclic.exists_ofOrder_eq_natCard (α := F4ˣ)
  rwa [card_F4_units] at h

theorem card_V3 : Nat.card (Fin 3 → ZMod 3) = 3 ^ 3 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem three_smul_V3 (x : Fin 3 → ZMod 3) : 3 • x = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]

theorem hasFusionTarget_Sp : HasFusionTarget Sp := by
  obtain ⟨ω, hω⟩ := exists_omega
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    norm_num at hω
  have hω' := sq_add_add_one_eq_zero hω3 hω1
  exact hasFusionTarget_of_torus_hom leviSp leviSp_injective (tau3_injective hω3 hω)
    permGL3_pow_three (permGL3_mul_tau3 hω3) rot3_ne card_V3 card_Sp_eq (by norm_num)
    rot3_norm' (g₀ := dftGL two_eq_zero hω')
    (fun c hc _ => dftGL_mul_tau3_of_fixed hω3 two_eq_zero hω' hc) (three_smul_V3 _)
    (dftGL_mul_permGL3_tau3 hω3 two_eq_zero hω')

theorem hasFusionTarget_projSp : HasFusionTarget (projSp 3 F4) :=
  hasFusionTarget_Sp.of_mulEquiv equivSp.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
