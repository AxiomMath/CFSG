module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.Model
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4

set_option linter.unusedSectionVars false


variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

abbrev Gm : Type := ↥(F4.reeGamma K a)

@[expose] def Ug : Subgroup (Gm K a) :=
  (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)

@[expose] def Pg (j : Fin F4.fixedOrbitCount) : Subgroup (Gm K a) :=
  (F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a)

variable {K a}

theorem invE_mem_gamma (hK : Nat.card K = 2 ^ (2 * a + 1)) : invE K a ∈ F4.reeGamma K a :=
  reeFixedPosUnipotent_le_reeGamma (invE_invF_mem hK).2.2.1

theorem invF_mem_gamma (hK : Nat.card K = 2 ^ (2 * a + 1)) : invF K a ∈ F4.reeGamma K a :=
  reeFixedPosUnipotent_le_reeGamma (invE_invF_mem hK).2.2.2.1

@[expose] def zg (hK : Nat.card K = 2 ^ (2 * a + 1)) : Gm K a := ⟨invE K a, invE_mem_gamma hK⟩

@[expose] def tg (hK : Nat.card K = 2 ^ (2 * a + 1)) : Gm K a := ⟨invF K a, invF_mem_gamma hK⟩

theorem zg_mem_Ug (hK : Nat.card K = 2 ^ (2 * a + 1)) : zg hK ∈ Ug K a :=
  Subgroup.mem_subgroupOf.2 (invE_invF_mem hK).2.2.1

theorem tg_mem_Ug (hK : Nat.card K = 2 ^ (2 * a + 1)) : tg hK ∈ Ug K a :=
  Subgroup.mem_subgroupOf.2 (invE_invF_mem hK).2.2.2.1

theorem orderOf_zg (hK : Nat.card K = 2 ^ (2 * a + 1)) : orderOf (zg hK) = 2 := by
  rw [← orderOf_injective (F4.reeGamma K a).subtype (Subgroup.subtype_injective _)]
  exact (invE_invF_mem hK).2.2.2.2.1

theorem orderOf_tg (hK : Nat.card K = 2 ^ (2 * a + 1)) : orderOf (tg hK) = 2 := by
  rw [← orderOf_injective (F4.reeGamma K a).subtype (Subgroup.subtype_injective _)]
  exact (invE_invF_mem hK).2.2.2.2.2

end CFSG.Quasithin.H13.F431.TwoF4
