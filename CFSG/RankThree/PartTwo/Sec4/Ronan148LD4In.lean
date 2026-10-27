module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LD4Pgu
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Aut
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsS
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix (ProjGenLinGroup)

section U3

variable {m : ℕ}

theorem modThree_two_pow (hm : Odd m) : ModThree false (2 ^ m) := by
  obtain ⟨r, rfl⟩ := hm
  change 2 ^ (2 * r + 1) % 3 = 2
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem piField_galoisField (hm1 : 1 ≤ m) : PiField false 2 m (GaloisField 2 (2 * m)) :=
  ⟨Nat.prime_two, hm1, by
    rw [GaloisField.card 2 (2 * m) (by omega), piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩

theorem exists_e9_projSU (hm : Odd m) :
    ∃ E : Subgroup (projSU 3 2 m), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hm1 : 1 ≤ m := hm.pos
  have hK := piField_galoisField hm1
  have hq := modThree_two_pow hm
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hK hq
  have hdS : diagTau hτ3 ∈ slPi false 3 (2 ^ m) (GaloisField 2 (2 * m)) :=
    diagTau_mem_slPi (fun _ => hK.unitary) (fun _ => hq) hτ3
  have hcS : (cycThree : GL (Fin 3) (GaloisField 2 (2 * m))) ∈
      slPi false 3 (2 ^ m) (GaloisField 2 (2 * m)) := cycThree_mem_slPi (fun _ => hK.unitary)
  have h9 := Sec14.Ronan148W.card_hessian hK hτ3 hτ1 hdS hcS
  set x₁ := projOf (slPi false 3 (2 ^ m) (GaloisField 2 (2 * m))) ⟨diagTau hτ3, hdS⟩ with hx₁
  set x₂ := projOf (slPi false 3 (2 ^ m) (GaloisField 2 (2 * m))) ⟨cycThree, hcS⟩ with hx₂
  have cx₁ : (x₁ : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * m))) =
      ProjGenLinGroup.mk (diagTau hτ3) := rfl
  have cx₂ : (x₂ : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * m))) =
      ProjGenLinGroup.mk cycThree := rfl
  have hx12 : x₁ * x₂ = x₂ * x₁ := Subtype.ext (by
    simp only [Subgroup.coe_mul, cx₁, cx₂]
    exact mk_diagTau_cycThree hτ3)
  have hx13 : x₁ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, cx₁, ← map_pow, diagTau_pow_three hτ3, map_one, Subgroup.coe_one])
  have hx23 : x₂ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, cx₂, ← map_pow, cycThree_pow_three, map_one, Subgroup.coe_one])
  set E₀ : Subgroup (projImage (slPi false 3 (2 ^ m) (GaloisField 2 (2 * m)))) :=
    Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hE₀
  have hE₀ab : CFSG.Assembly.IsElemAbelian 3 E₀ := by
    have h1 : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers (1 : _)) := by
      refine isElemAbelian_sup_zpowers ?_ (one_pow 3) (fun a _ => by rw [mul_one, one_mul])
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, hx13, one_zpow]
    rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq] at h1
    exact isElemAbelian_sup_zpowers h1 hx23 (fun a ha => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left hx12 i).eq)
  have heq : projImage (slPi false 3 (2 ^ m) (GaloisField 2 (2 * m))) = projSU 3 2 m :=
    CFSG.PGLModel.projImage_statedSU 3 2 m
  refine ⟨E₀.map (MulEquiv.subgroupCongr heq).toMonoidHom, ?_, ?_⟩
  · exact Ronan148S.isElemAbelian_map _ hE₀ab
  · rw [Subgroup.card_map_of_injective (MulEquiv.subgroupCongr heq).injective]
    exact h9

theorem exists_not_commute_projSU (hm : Odd m) :
    ∃ a b : projSU 3 2 m, a * b ≠ b * a := by
  have hm1 : 1 ≤ m := hm.pos
  have hK := piField_galoisField hm1
  have hq := modThree_two_pow hm
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hK hq
  have hdS : diagTau hτ3 ∈ slPi false 3 (2 ^ m) (GaloisField 2 (2 * m)) :=
    diagTau_mem_slPi (fun _ => hK.unitary) (fun _ => hq) hτ3
  have htS := nswap12_mem_slPi (p := 2) (f := m) hK.unitary
  have heq : projImage (slPi false 3 (2 ^ m) (GaloisField 2 (2 * m))) = projSU 3 2 m :=
    CFSG.PGLModel.projImage_statedSU 3 2 m
  refine ⟨⟨ProjGenLinGroup.mk (diagTau hτ3), heq ▸ ⟨_, hdS, rfl⟩⟩,
    ⟨ProjGenLinGroup.mk nswap12, heq ▸ ⟨_, htS, rfl⟩⟩, fun h => ?_⟩
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h'
  exact false_of_mk_diagTau_nswap12 hτ3 hτ1 (by rw [map_mul, map_mul]; exact h')

theorem center_projSU_eq_bot (hm : Odd m) (hm1 : 1 < m) :
    Subgroup.center (projSU 3 2 m) = ⊥ := by
  have hs := Item462AltProof.isSimpleGroup_projSU_three 2 m (by omega) (by
    intro h
    have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  exact RonanK429.center_eq_bot_of_isSimpleGroup hs (exists_not_commute_projSU hm)

end U3

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
