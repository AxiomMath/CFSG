module

public import CFSG.Quasithin.EmptyFaithful.S153XBridge
public import CFSG.Quasithin.EmptyFaithful.S153XBlk
public import CFSG.Quasithin.EmptyFaithful.S153XPair
public import CFSG.Quasithin.EmptyFaithful.S153XIrr
public import CFSG.Quasithin.EmptyFaithful.S153XAsm
public import CFSG.Quasithin.EmptyFaithful.S153XExE
public import CFSG.Quasithin.EmptyFaithful.S153XPgrp

public section

namespace CFSG.Quasithin

namespace X1469

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ModF CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem localFacts_of_cfg {I S Iz K₁ K₂ T : Subgroup G} {r z : G}
    (C : LocalCfg I S Iz K₁ K₂ T r z) : LocalFacts I S Iz r z := by
  obtain ⟨t, PG⟩ := exists_pairGen C
  obtain ⟨c₁, BF₁⟩ := exists_blockFacts C.cfg C.hnot C.hD
  obtain ⟨c₂, BF₂⟩ := exists_blockFacts C.cfg.symm PG.hnot₂ (by rw [sup_comm]; exact C.hD)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    exists_sub_facts PG BF₁ BF₂ C.hz1 (fun s hs => C.hzc s (C.hST hs))
  have hES : E0 K₁ K₂ Iz ≤ S := h5.trans (h4.trans PG.R_le_S)
  have hSN : S ≤ Subgroup.normalizer ((E0 K₁ K₂ Iz : Subgroup G) : Set G) :=
    PG.S_le_Iz.trans PG.Iz_normalizes_E
  have hZN : S ≤ Subgroup.normalizer ((z0 Iz : Subgroup G) : Set G) :=
    PG.S_le_Iz.trans ((le_normalizer_pCoreOf 2 Iz).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 Iz)))
  refine ⟨h1, h2, irred_Rz_of PG BF₁ BF₂, Kp c₁ c₂, Pp K₁ K₂ Iz c₁ c₂, E0 K₁ K₂ Iz, h3, h4, h5,
    PG.Iz_normalizes_E, h6, le_rfl, h7, h8, h9, h10, irred_E0_of PG BF₁ BF₂,
    exists_fixed_mod C.cfg.sylow.isPGroup hES hSN hZN h11,
    exists_e_of C PG (by rw [BF₁.card_E]; norm_num)⟩

end X1469

theorem input1469A5Fin_proved : Input1469A5Fin :=
  input1469A5Fin_of_loc fun _ _ _ _ _ _ _ _ _ _ _ C => X1469.localFacts_of_cfg C

end CFSG.Quasithin
