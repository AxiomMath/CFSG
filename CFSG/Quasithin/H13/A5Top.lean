module

public import CFSG.Quasithin.H13.A5S1517
public import CFSG.Quasithin.H13.A5S135

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

@[expose] def Input13515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V)
    (H : Subgroup G), H ∈ S.Hz → H ≤ Subgroup.normalizer (S.L1 : Set G) →
    ¬ IsElemAbelian 2 (conjClosure S.V3 H) → ∃ I : Subgroup G, Data13515 S H I

@[expose] def Input13518 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) →
    ∃ H ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H) ∧
      H ≤ Subgroup.normalizer (S.L1 : Set G)

@[expose] def Input136 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ IsElemAbelian 2 (conjClosure V S.G1)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thm_13_6_1 (h1323 : Input1323Two) (h1336 : Input1336) (h13515 : Input13515)
    (h13518 : Input13518) (h136 : Input136) (hF112 : F112LegacyPrintedError) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hG1 := S.G1_mem_Hz h1336
  by_cases hab : IsElemAbelian 2 (conjClosure S.V3 S.G1)
  ·
    exact absurd (((S.tfae_13_5_10 h1323 hG1).out 2 3).1 hab) (h136 G T L V S)
  ·
    obtain ⟨H, hH, hna, hn⟩ := h13518 G T L V S hab
    obtain ⟨I, D⟩ := h13515 G T L V S H hH hn hna
    exact S.prop_13_5_17 hH D hF112 hF431

theorem thm_13_6_1_corrected (h1323 : Input1323Two) (h1336 : Input1336) (h13515 : Input13515)
    (h13518 : Input13518) (h136 : Input136) (hF112 : F112Statement) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hG1 := S.G1_mem_Hz h1336
  by_cases hab : IsElemAbelian 2 (conjClosure S.V3 S.G1)
  ·
    exact absurd (((S.tfae_13_5_10 h1323 hG1).out 2 3).1 hab) (h136 G T L V S)
  ·
    obtain ⟨H, hH, hna, hn⟩ := h13518 G T L V S hab
    obtain ⟨I, D⟩ := h13515 G T L V S H hH hn hna
    exact S.prop_13_5_17_corrected hH D hF112 hF431

end Setting

end CFSG.Quasithin.H13.A5
