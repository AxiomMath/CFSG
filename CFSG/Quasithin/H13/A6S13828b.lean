module

public import CFSG.Quasithin.H13.A6S13828a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Hat

variable {K : Subgroup G} {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

theorem card_UH_hat (hd : S.HatData K ρ β) : Nat.card ↥(conjClosure S.V3 S.G1) = 32 := by
  obtain ⟨-, -, -, -, -, -, -, hβs, hβk, -⟩ := hd
  have hk : β.ker = (fsuV1 T V).subgroupOf (conjClosure S.V3 S.G1) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  have h2 : Nat.card (↥(conjClosure S.V3 S.G1) ⧸ β.ker) = 16 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2))]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have h3 : Nat.card ↥β.ker = 2 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((S.V1_le_V2.trans S.V2_le_V3).trans (le_conjClosure S.V3 S.G1))).toEquiv, S.card_V1]
  rw [h1, h2, h3]

end Hat

end Setting4

end CFSG.Quasithin.H13.A6

