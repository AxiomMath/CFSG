module

public import CFSG.Quasithin.H13.A5R1Frame

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

@[expose] noncomputable def R1 : Subgroup G := S.frame.R1

theorem R1_le_T : S.R1 ≤ T := S.frame.R1_le_T

theorem mem_R1 {t : G} (ht : t ∈ T) :
    t ∈ S.R1 ↔ InK4 (S.frame.ρ ⟨t, S.frame.T_le ht⟩) :=
  S.frame.mem_R1 ht

theorem lemma_13_2_4_one :
    thompsonJ S.R1 ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧
      thompsonJ S.R1 = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ∧
      baum S.R1 = baum (T ⊓ Subgroup.centralizer (V : Set G)) :=
  S.frame.lemma_13_2_4_one S.elemAbelian_V S.V_le_T

end Setting

end CFSG.Quasithin.H13.A5
