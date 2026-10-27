module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318H
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open scoped commutatorElement IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem W₃_le_commutator_self (hD : Data G T M L D n k α Φ) :
    W₃ Φ ≤ ⁅W₃ Φ, liftCore α (flagStabilizer n (ZMod 2) {3})⁆ := by
  classical
  have hn := hD.n4
  set Y := liftCore α (flagStabilizer n (ZMod 2) {3}) with hY
  set S := (⁅W₃ Φ, Y⁆).comap ((vPlus L T).subtype.comp (Φ.comp (ext3 n k))) with hS
  suffices hS' : S = ⊤ by
    rintro _ ⟨x, rfl⟩
    have : x ∈ S := hS' ▸ Subgroup.mem_top x
    exact this
  refine eq_top_of_single_mem S fun i a => ?_
  show ((Φ (ext3 n k (Multiplicative.ofAdd (Pi.single i (Pi.single a 1))))) : G) ∈ ⁅W₃ Φ, Y⁆
  rw [ext3_single (by omega)]
  obtain ⟨b, hba⟩ : ∃ b : Fin 3, b ≠ a := ⟨a + 1, by
    intro h
    have := congrArg (fun x : Fin 3 => (x : ℕ)) h
    fin_cases a <;> simp_all⟩
  set a' : Fin n := ⟨a, by omega⟩ with ha'
  set b' : Fin n := ⟨b, by omega⟩ with hb'
  have hab' : a' ≠ b' := fun e => hba (Fin.ext (by
    have := congrArg Fin.val e
    simpa [ha', hb'] using this.symm))
  have h3 : 0 + 3 ≤ n := by omega
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hmem : SpecialLinearGroup.transvection hab' (1 : ZMod 2) ∈
      perfectCore (flagStabilizer n (ZMod 2) {3}) := by
    rw [transvection_eq_liftT h3 a.isLt b.isLt hab']
    exact Ln2.liftT_mem_perfectCore h3 le_rfl hno _
  obtain ⟨y, hyY, hye⟩ := exists_mem_liftCore hD.surj hmem
  set c : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle i (Multiplicative.ofAdd (Pi.single b' 1)) with hc
  set ca : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle i (Multiplicative.ofAdd (Pi.single a' 1)) with hca
  have hcW : (Φ c : G) ∈ W₃ Φ := by
    refine ⟨Multiplicative.ofAdd (Pi.single i (Pi.single b 1)), ?_⟩
    show ((Φ (ext3 n k (Multiplicative.ofAdd (Pi.single i (Pi.single b 1))))) : G) = (Φ c : G)
    rw [ext3_single (by omega)]
  have hconj : (y : G) * (Φ c : G) * y⁻¹ = (Φ c : G) * (Φ ca : G) := by
    have h1 := hD.equiv ⟨y, liftCore_le α _ hyY⟩ c
    rw [hye] at h1
    rw [h1, ← Subgroup.coe_mul, ← map_mul]
    congr 2
    rw [hc, vecAct_mulSingle, hca, ← Pi.mulSingle_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
    have := SpecialLinearGroup.transvection_smul_single_snd hab' (1 : ZMod 2)
    rw [Matrix.SpecialLinearGroup.smul_def, one_smul] at this
    exact this
  have hcomm : ⁅y, (Φ c : G)⁆ = (Φ ca : G) := by
    rw [commutatorElement_def, hconj]
    have hab := (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.1
    have := congrArg Subtype.val (hab.1.is_comm.comm (Φ c) (Φ ca))
    simp only [Subgroup.coe_mul] at this
    rw [this]
    group
  rw [← hcomm, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hyY hcW

end Data

end CFSG.Quasithin.H13.L3318
