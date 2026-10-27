module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4315

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat

@[expose] def Step43U35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G)
    (m : ℕ) (F : Type) [Field F] [Fintype F] (α : ↥K →* ↥(StatedSL 3 F))
    (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)) (W' : Submodule F (Fin 3 → F))
    (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G) (KZ : Subgroup G),
    Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ → m = 2 →
    IsPSU 3 5 1 (ModO2 KZ ⧸ Subgroup.center (ModO2 KZ)) → False

variable {G : Type} [Group G] [Finite G]

end CFSG.Quasithin.H13.Ch4
