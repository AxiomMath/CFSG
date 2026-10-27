module

public import CFSG.Quasithin.Background.SmithB51SL3B
public import CFSG.Quasithin.Background.SmithB51SL3A

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section Coords

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

structure SL3Coords (G L : Subgroup (MulAut V)) : Type 1 where
  d : SL3Data G L
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  n : ℕ
  hK : Nat.card K = 2 ^ n
  c₁ : NatSec L d.I (d.I ⊓ fixV L) K
  c₂ : NatSec L d.W₂ d.Y₂ K
  hax₁ : Module.finrank K (fixK (c₁.pre d.A)) = 2 ∧ c₁.pre d.A = axisSub (fixK (c₁.pre d.A))
  hax₂ : Module.finrank K (fixK (c₂.pre d.A)) = 2 ∧ c₂.pre d.A = axisSub (fixK (c₂.pre d.A))
  hcardA : Nat.card d.A = Nat.card K ^ 2

attribute [instance] SL3Coords.instField SL3Coords.instFinite

theorem exists_sl3Coords (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∉ IrrPlus L ⊤) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) : Nonempty (SL3Coords G L) := by
  classical
  obtain ⟨d⟩ := sl3_sections hA21 hB42 hA36 hIH hV h hU hK eL
  have hAel : IsElemAbelian2 d.A := d.hmin.1.2.2.1
  have hAne : d.A ≠ ⊥ := d.hmin.1.2.1
  obtain ⟨n₁, K₁, _, _, hK₁, ⟨c₁⟩⟩ := exists_natSec inf_le_left d.hLI d.hLY d.hf₁ d.hnat₁
  obtain ⟨n₂, K₂, _, _, hK₂, ⟨c₂⟩⟩ := exists_natSec d.hY₂W₂ d.hLW₂ d.hLY₂ d.hf₂ d.hnat₂
  obtain ⟨h1a, h1b, h1c⟩ := c₁.axis hK₁ inf_le_left d.hLI d.hLY d.hAL hAel hAne d.hr₁
  obtain ⟨-, -, h2c⟩ := c₂.axis hK₂ d.hY₂W₂ d.hLW₂ d.hLY₂ d.hAL hAel hAne d.hr₂
  have hcard : Nat.card K₂ = Nat.card K₁ := by
    have := h2c.symm.trans h1c
    exact Nat.pow_left_injective (by norm_num) this
  have := Fintype.ofFinite K₁
  have := Fintype.ofFinite K₂
  have hcard' : Fintype.card K₂ = Fintype.card K₁ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
  let e : K₂ ≃+* K₁ := FiniteField.ringEquivOfCardEq hcard'
  set c₂' := c₂.transport e with hc₂'
  obtain ⟨h3a, h3b, -⟩ := c₂'.axis hK₁ d.hY₂W₂ d.hLW₂ d.hLY₂ d.hAL hAel hAne d.hr₂
  exact ⟨⟨d, K₁, n₁, hK₁, c₁, c₂', ⟨h1a, h1b⟩, ⟨h3a, h3b⟩, h1c⟩⟩

end Coords

end B5

end CFSG.Quasithin
