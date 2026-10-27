module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F918Z4eDickson
public import CFSG.Quasithin.Background.F918Z4eOrders
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.Sporadic.J1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.BenderSuzuki.MatrixGroups

namespace Z4e

theorem two_mul_card_of_isPSL_two_odd {D : Type} [Group D] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 D) : 2 * Nat.card D = p * (p ^ 2 - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = p := by simpa using hK
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hfm := CFSG.GorensteinWalter.psl2_card_formula K ⟨p, 1, hp, hodd, le_rfl, by simpa using hK⟩
  rw [Nat.card_congr (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
    hfm, hK']
  refine Nat.mul_div_cancel' ?_
  exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _

theorem isPSL_two_two_two_of_isPSL_two_five {D : Type} [Group D]
    (h : IsPSL 2 5 1 D) : IsPSL 2 2 2 D := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK5 : Nat.card K = 5 := by simpa using hK
  obtain ⟨e5⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K (Or.inr hK5)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hc4)
  exact ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, by rw [hc4]; norm_num, ⟨e.trans (e5.trans e4.symm)⟩⟩

theorem eq_five_or_seven_le {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : p = 5 ∨ 7 ≤ p := by
  by_contra h
  have h4 : p = 4 ∨ p = 6 := by omega
  rcases h4 with rfl | rfl <;> exact absurd hp (by norm_num)

end Z4e

open Z4e

theorem exists_psl2_of_faithful_two
    {D : Type} [Group D] [Finite D] (hA : A38Types D) [IsSimpleGroup D]
    (hnonab : ∃ a b : D, a * b ≠ b * a) {F : Type} [Field F] [Finite F] [CharP F 2]
    (ρ : D →* Matrix.GeneralLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    ∃ n, IsPSL 2 2 n D := by
  have hord : IsEvenPSL2Order (Nat.card D) :=
    card_eq_sixty_or_two_pow_of_faithful_two hnonab ρ hρ
  rcases hA with hA | ⟨n, hn⟩ | ⟨⟨e⟩⟩ | ⟨p, hp, hp3, hpsl⟩
  · exact hA
  ·
    exfalso
    obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hn
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.card_suzukiMatrixGroup a ha] at hord
    exact not_isEvenPSL2Order_suzuki a hord
  ·
    exfalso
    have hc : Nat.card D = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    rw [hc] at hord
    exact not_isEvenPSL2Order_j1 hord
  ·
    rcases eq_five_or_seven_le hp hp3 with rfl | hp7
    · exact ⟨2, isPSL_two_two_two_of_isPSL_two_five hpsl⟩
    · exfalso
      exact not_isEvenPSL2Order_of_two_mul_eq hp hp7
        (two_mul_card_of_isPSL_two_odd hp (by omega) hpsl) hord

end CFSG.Quasithin
