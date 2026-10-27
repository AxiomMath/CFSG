module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Facts
public import CFSG.Quasithin.Vol2.Ch12Sec4G2Off

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

instance finite_zornQ_mod {F : Type} [Field F] [Finite F]
    (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) :
    Finite (FFModel.zornQ Γ).Mod := by
  have : Finite (Multiplicative (quasithinZorn F)) := inferInstanceAs (Finite (quasithinZorn F))
  have : Finite ↥(zornO0 F) := inferInstance
  exact inferInstanceAs (Finite (↥(zornO0 F) ⧸ (zornR F).subgroupOf (zornO0 F)))

instance finite_zornO0_mod {F : Type} [Field F] [Finite F]
    (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) :
    Finite (zornO0Model Γ).Mod := by
  have : Finite (Multiplicative (quasithinZorn F)) := inferInstanceAs (Finite (quasithinZorn F))
  have : Finite ↥(zornO0 F) := inferInstance
  exact inferInstanceAs (Finite (↥(zornO0 F) ⧸ (⊥ : Subgroup _).subgroupOf (zornO0 F)))

@[expose] def U33G2Facts : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    G2Facts (g2QAct K).range ((g2Derived K).map (g2QAct K)) ∧
    G2Facts (g2OAct K).range ((g2Derived K).map (g2OAct K))

end CFSG.Quasithin.H13.U3.GC137
