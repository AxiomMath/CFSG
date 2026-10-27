module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Excl
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Index
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3ExclGen
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def ExclL3Model1412 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ β : MulAut (LinearFlag.projectiveSL 3 (GaloisField p 1)), orderOf β = 2 → Excl1412 β

@[expose] def ExclU3Model1412 (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] (h : UnitaryFieldData p 1 K) (α : MulAut (unitaryPSU h 3)),
    orderOf α = 2 → Excl1412 α

private theorem excl1412_of_mulEquiv_projSL {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (e : G ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p 1)) (hE : ExclL3Model1412 p)
    (α : MulAut G) (hα : orderOf α = 2) : Excl1412 α := by
  set ε : G ≃* LinearFlag.projectiveSL 3 (GaloisField p 1) :=
    e.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 _) with hε
  exact Excl1412.of_congr ε (hE _ (by rw [MulEquiv.orderOf_eq]; exact hα))

private theorem excl1412_of_mulEquiv_projSU {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (e : G ≃* CFSG.Assembly.RankThreeEven.projSU 3 p 1) (hE : ExclU3Model1412 p)
    (α : MulAut G) (hα : orderOf α = 2) : Excl1412 α := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p 1 :=
    ⟨Fact.out, le_rfl, le_rfl, fun h => by
      have h2 := (Prod.mk.inj h).2
      rw [pow_one] at h2
      omega⟩
  obtain ⟨-, K, _, _, hK, ⟨eD⟩⟩ := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  have hu : UnitaryFieldData p 1 K := ⟨Fact.out, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  set ε := eD.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm with hε
  exact Excl1412.of_congr ε (hE K hu _ (by rw [MulEquiv.orderOf_eq]; exact hα))

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem noSmall1412_of_isL3eps1412 (h : Hyp1411 X L S)
    (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {p : ℕ} [Fact p.Prime]
    (hL : IsL3eps1412 ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) p)
    (h5 : haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩; ExclL3Model1412 5)
    (h17 : haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩; ExclL3Model1412 17)
    (h7 : ExclU3Model1412 7) (h31 : ExclU3Model1412 31) (h127 : ExclU3Model1412 127) :
    NoSmall1412 X L S := by
  refine noSmall1412_of_forall_excl h hK (isSimpleGroup_of_isL3eps1412 hL)
    (center_eq_bot_of_isL3eps1412 hL) fun α hα => ?_
  have hp3 := hL.1
  by_cases hp5 : p = 5
  · subst hp5
    obtain ⟨-, ⟨-, ⟨e⟩⟩ | ⟨hmod, -⟩⟩ := hL
    · exact excl1412_of_mulEquiv_projSL e h5 α hα
    · omega
  by_cases hp17 : p = 17
  · subst hp17
    obtain ⟨-, ⟨-, ⟨e⟩⟩ | ⟨hmod, -⟩⟩ := hL
    · exact excl1412_of_mulEquiv_projSL e h17 α hα
    · omega
  by_cases hp7 : p = 7
  · subst hp7
    obtain ⟨-, ⟨hmod, -⟩ | ⟨-, ⟨e⟩⟩⟩ := hL
    · omega
    · exact excl1412_of_mulEquiv_projSU hp3 e h7 α hα
  by_cases hp31 : p = 31
  · subst hp31
    obtain ⟨-, ⟨hmod, -⟩ | ⟨-, ⟨e⟩⟩⟩ := hL
    · omega
    · exact excl1412_of_mulEquiv_projSU hp3 e h31 α hα
  by_cases hp127 : p = 127
  · subst hp127
    obtain ⟨-, ⟨hmod, -⟩ | ⟨-, ⟨e⟩⟩⟩ := hL
    · omega
    · exact excl1412_of_mulEquiv_projSU hp3 e h127 α hα
  exact excl1412_of_isL3eps1412 hL hp5 hp7 hp17 hp31 hp127 α hα

end CFSG.RankThree.PartTwo.Sec20
