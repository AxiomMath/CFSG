module

public import CFSG.Quasithin.Background.RonanG72Classical
public import CFSG.Quasithin.Background.Harris.G2.U33Rank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.CaseM22Dispatch
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem false_of_psl3 {L Γ A : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact false_of_oddL3 hp2 h hm

theorem clause1_psu3 {L Γ A : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hq : CFSG.IsQuasisimple ↥L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p 1) :
    IsPSU 3 3 1 ↥L ∧ Module.finrank (ZMod 2) V = 6 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p = 3 := oddU3_reduce hp2 h hm
  subst hp3
  have hodd := odd_card_center_of_irr' h.H_irr
  have hm' := hm
  obtain ⟨hadm, K, hK1, hK2, hK, ⟨e0⟩⟩ := hm
  have hK9 : Nat.card K = 9 := hK.trans (by norm_num)
  have hZ : (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 3 K) = ⊥ :=
    CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hK9
  let eS : StatedProj (StatedSU 3 3 K) ≃* ↥(StatedSU 3 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e1 : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(StatedSU 3 3 K) := e0.trans eS
  let π : ↥L →* ↥(StatedSU 3 3 K) :=
    e1.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e1.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  haveI : Group.IsPerfect ↥L := ⟨h.L_comp.2.2.1⟩
  have hker1 : π.ker = ⊥ :=
    CFSG.SectionRank.OddCover.prime_classical_three_perfect_odd_extension_trivial
      (ε := -1) Nat.prime_three (by norm_num) (Or.inr ⟨rfl, hK9.trans (by norm_num), rfl⟩) π hπ
      hker.le (by rw [hker]; exact hodd)
  have hZbot : Subgroup.center ↥L = ⊥ := hker ▸ hker1
  let eL : ↥L ≃* (↥L ⧸ Subgroup.center ↥L) := mulEquiv_of_center_eq_bot hZbot (MulEquiv.refl _)
  have hmL : StatedClassicalModel ↥L .PSU 3 3 1 :=
    CFSG.Quasithin.RonanG72.statedClassicalModel_of_mulEquiv eL hm'
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have hsimp : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hs := CFSG.Quasithin.G11.Harris.OneCompSetting.of_g93Hyp h
  have hP : B42TypeU33 ↥L := CFSG.Quasithin.G11.Harris.G2.b42TypeU33_of_simple hsimp hmL
  obtain ⟨θ⟩ := CFSG.Quasithin.B42U33.nonempty_equiv_g2Derived hP
  have hm3 : m ≤ 3 := CFSG.Quasithin.G11.Harris.G2.m_le_three_u33 hs θ
  have hb := h.bound
  exact CFSG.Quasithin.RonanG72.u33_six h.H_irr (by omega) hmL

end CFSG.Quasithin.RonanG73
