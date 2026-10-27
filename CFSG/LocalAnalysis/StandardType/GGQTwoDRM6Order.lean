module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMOrder

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Dispatch

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
  {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
  {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}

theorem qTwoD6_family_linWeyl
    (hfin : Module.finrank (ZMod 3) U = 6)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hrefl : ∃ t ∈ Abar, ZS.IsRefl 3 t)
    (hcard : Nat.card Abar ≤ 3 ^ 6 * (2 ^ (6 - 1) * (6 - 1).factorial))
    (hFam : ZS.Family 3 Abar) : ZS.LinWeyl 3 Abar := by
  let : Finite V := qTwoGlobLin_finite (ι := ι)
  let : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  have hd4 : 4 ≤ Module.finrank (ZMod 3) U := by omega
  have hcard' : Nat.card Abar ≤ 2799360 :=
    le_trans hcard (by norm_num [Nat.factorial])
  have hbound : Nat.card Abar ≤ 3 ^ 6 * (2 * Nat.factorial 7) :=
    le_trans hcard' (by norm_num [Nat.factorial])
  cases hFam with
  | weyl hW => exact hW
  | slpm hSL =>
    exfalso
    have hlower := ZS.pow_le_card_of_sl_le hfin Abar (fun g hg => (hSL g).mpr (Or.inl hg))
    have hlower' : 14348907 ≤ Nat.card Abar := by simpa using hlower
    omega
  | orth Q hQ hO =>
    exfalso
    have hcomm := qTwoGlobLin_orth_commutators (ι := ι) Q hQ (Or.inl hO) (by omega)
    exact qTwoGlobIdx_degSix_false hQ hfin Abar hcomm hrefl hbound
  | orthClass Q c hQ hc hO =>
    exfalso
    have hcomm := qTwoGlobLin_orth_commutators (ι := ι) Q hQ (Or.inr ⟨c, hc, hO⟩) (by omega)
    exact qTwoGlobIdx_degSix_false hQ hfin Abar hcomm hrefl hbound
  | gmmn f i₀ i₁ ζ t hi ht hζ hO =>
    exact False.elim (qTwo_family_imprimitive_excl f i₀ i₁ ζ t hi (Or.inl ⟨ht, hζ, hO⟩))
  | g2mmn f i₀ i₁ ζ t hi ht hζ hO =>
    exact False.elim (qTwo_family_imprimitive_excl f i₀ i₁ ζ t hi (Or.inr ⟨ht, hζ, hO⟩))
  | exc k hadm hdeg hord hcen hmax hclass hmodel =>
    have hk := qTwo_family_exc_excl k hadm hD.2.2.1 hdeg hd4 hcen
    subst hk
    exact False.elim (qTwo_family_H4_excl hdeg hord)
  | h4 hadm hdeg _ hneg hmax hclass => omega

theorem qTwoD_family_linWeyl_of_card {m : ℕ} (hm : 6 ≤ m)
    (hfin : Module.finrank (ZMod 3) U = m)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hrefl : ∃ t ∈ Abar, ZS.IsRefl 3 t)
    (hcard : Nat.card Abar ≤ 3 ^ m * (2 ^ (m - 1) * (m - 1).factorial))
    (hFam : ZS.Family 3 Abar) : ZS.LinWeyl 3 Abar := by
  rcases Nat.eq_or_lt_of_le hm with h6 | h7
  · subst h6
    exact qTwoD6_family_linWeyl hfin hD hrefl hcard hFam
  · exact qTwoD_family_linWeyl (by omega) hfin hD
      (lt_of_le_of_lt (Nat.mul_le_mul_left 8 hcard) (qTwoDRM_growth (by omega))) hFam

end Dispatch

end CFSG.StandardType.QTwo

end
