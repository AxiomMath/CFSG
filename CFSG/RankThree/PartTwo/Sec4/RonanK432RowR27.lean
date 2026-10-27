module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowR27Gen
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.AGLEmbedding.ReeModel CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.HardMathSupport.Lang.Coordinator (small_Ree_outer_fixed_order card_reeGamma_G2_eq)


abbrev Ree27Field : Type := GaloisField 3 (2 * 1 + 1)

theorem card_ree27Field : Nat.card Ree27Field = 3 ^ (2 * 1 + 1) :=
  GaloisField.card 3 (2 * 1 + 1) (by omega)

section


abbrev Ree27 : Type := ↥(ReeTag.G2.reeGamma Ree27Field 1)

instance finite_ree27 : Finite Ree27 := Subtype.finite

theorem not_dvd_card_ree27 : ¬ 3 ^ (9 + 1) ∣ Nat.card Ree27 := by
  have h := (std_facts (a := 1) (K := Ree27Field) card_ree27Field).2.2.2
  rw [h]
  norm_num

theorem pow_dvd_card_ree27 : 3 ^ 9 ∣ Nat.card Ree27 := by
  have h := (std_facts (a := 1) (K := Ree27Field) card_ree27Field).2.2.2
  rw [h]
  norm_num

theorem card_stdU_ree27 : Nat.card (stdU 1 Ree27Field) = 3 ^ 9 := by
  obtain ⟨⟨P, hP⟩, -⟩ := std_facts (a := 1) (K := Ree27Field) card_ree27Field
  rw [← hP]
  exact card_sylow_three_eq P pow_dvd_card_ree27 not_dvd_card_ree27

theorem listRow_ree27 : ListRow Ree27 := by
  have hK := card_ree27Field
  refine listRow_of_sylow_center_field (K := Ree27Field) (by rw [hK]; norm_num) (zHom hK)
    (zHom_injective hK) 9 (stdU 1 Ree27Field) card_stdU_ree27 not_dvd_card_ree27 ?_ ?_
  · intro u hu hc
    rw [zHom_range hK]
    exact ⟨hu, Subgroup.mem_centralizer_iff.mpr fun q hq => hc q hq⟩
  · intro μ
    obtain ⟨g, -, hg⟩ := exists_normalizer_mul hK μ
    exact ⟨g, fun c => hg (Multiplicative.ofAdd c)⟩

theorem outerRow_ree27 : OuterRow Ree27 := by
  have hK := card_ree27Field
  refine outerRow_of_fixed_card_dvd (ReeTag.center_reeGamma_G2_eq_bot hK) ?_
  intro σ hσ hout
  obtain ⟨d, hd, hdvd⟩ := small_Ree_outer_fixed_order 1 le_rfl Ree27Field hK Nat.prime_three
    (by norm_num) σ hσ hout
  have hd1 : d = 1 := by omega
  subst hd1
  refine ⟨fixedSubgroup σ, (3 ^ 1) ^ 3 * ((3 ^ 1) ^ 3 + 1) * (3 ^ 1 - 1), fun x => Iff.rfl, hdvd,
    ?_⟩
  rw [card_reeGamma_G2_eq hK]
  norm_num

end

theorem rowOf_r27 :
    ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      RowOf (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  intro hr S _ _ _ _ ⟨e⟩
  obtain ⟨f⟩ := nonempty_reeGamma_equiv 1 le_rfl hr
  let e' : S ≃* Ree27 := e.trans f.symm
  exact GoodRow.of_mulEquiv e'.symm ⟨listRow_ree27, outerRow_ree27⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
