module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Commute
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Descent
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Fixed
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.StandardType.E6FieldFix

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

variable {K : Type} [Field K] [Finite K]

theorem exists_inndiagConj_restrict
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) {σ : K ≃+* K} (hσ : orderOf σ = p) (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 3) (w : inndiagGroup Tag.E6 K)
    (hc : inndiagConj Tag.E6 K w * entrywiseAdjointAut Tag.E6 σ =
      entrywiseAdjointAut Tag.E6 σ * inndiagConj Tag.E6 K w) :
    ∃ w₀ : inndiagGroup Tag.E6 (fixSubfield σ), ∀ y : adjointGroup Tag.E6 (fixSubfield σ),
      inndiagConj Tag.E6 K w
          ((fixE6Equiv σ hσp hcop y : ↥(ggFixSub (entrywiseAdjointAut Tag.E6 σ))) :
            adjointGroup Tag.E6 K) =
        ((fixE6Equiv σ hσp hcop (inndiagConj Tag.E6 (fixSubfield σ) w₀ y) :
          ↥(ggFixSub (entrywiseAdjointAut Tag.E6 σ))) : adjointGroup Tag.E6 K) := by
  have hσ1 : σ ≠ 1 := by
    intro h
    have h1 : orderOf σ = 1 := by rw [h, orderOf_one]
    rw [hσ] at h1
    exact hp.ne_one h1
  have hK4 : 4 ≤ Nat.card K :=
    four_le_card_of_ne_one (ℓ := 2) (f := n) (by norm_num) hn hK hσ1
  have hfix : Units.map (entrywiseHom σ.toRingHom) (w : ModGL Tag.E6 K) =
      (w : ModGL Tag.E6 K) :=
    entrywise_inndiag_eq_of_commute (τ := Tag.E6) hK4 σ w hc
  have hk : Nat.card (fixSubfield σ) = 2 ^ (n / orderOf σ) :=
    (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      (by norm_num) hn hK σ).2
  obtain ⟨w₀m, hw₀m, hbase⟩ :=
    exists_inndiagGroup_of_fixed (τ := Tag.E6) (n := n) (e := n / orderOf σ) hK σ hk
      (w := (w : ModGL Tag.E6 K)) w.2 hfix
  refine ⟨⟨w₀m, hw₀m⟩, fun y => ?_⟩
  apply Subtype.ext
  simp only [coe_inndiagConj, coe_fixE6Equiv, map_mul, map_inv, hbase]

end CFSG.StandardType.E6FieldFix

end
