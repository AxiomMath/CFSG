module

public import CFSG.Quasithin.EmptyFaithful.S153E58Q

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E61

section Data

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

@[expose] def Data61 (cx : Ctx15350 T Mc M V₁ V₂ t) : Prop :=
  letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  ∃ (K : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))))
    (W₁ W₂ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (π : ↥(StatedSL 3 (ZMod 2)) →* ↥K),
    S153E58.Setup58 (HStar153 T M V₁ Mc) K W₁ W₂ (S153E58.bilU cx) ∧ ⁅K, K⁆ = K ∧
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π

theorem data61_of_core58 (h09 : Input15309Two) (iTwo : Input15358Two) (iG93 : Input15358G93)
    (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}
    (c : Chain15357 cx N₁ N₂ g s y t₁) : Data61 cx := by
  obtain ⟨-, hcore⟩ := S153E58.core58 h09 iTwo iG93 cx c
  obtain ⟨K, W₁, W₂, π, hS, hperf, hπ, -⟩ := hcore
  exact ⟨K, W₁, W₂, π, hS, hperf, hπ⟩

end Data

end S153E61

end CFSG.Quasithin
