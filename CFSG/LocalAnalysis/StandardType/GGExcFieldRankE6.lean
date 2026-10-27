module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
public import CFSG.LieType.SeitzGeneration.ExcTorusE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Nine
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.TwistMapFixed
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Sylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.Open (IsElemAbelian)

private theorem not_dvd_small_E6 {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk0 : 0 < k)
    (hk : k ≤ 6) (hk5 : k ≠ 5) : ¬ p ∣ k := by
  intro h
  have hle : p ≤ k := Nat.le_of_dvd hk0 h
  have hp6 : p ≤ 6 := hle.trans hk
  have hp5' : p = 5 := by
    interval_cases p <;> first | rfl | exact absurd hp (by decide)
  subst hp5'
  interval_cases k
  · exact hk5 rfl
  · norm_num at h

section F4Fixed


private noncomputable def e6F4Fixed (K : Type) [Field K] [CharP K 2] :
    Subgroup (adjointGroup .E6 K) :=
  (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subgroupOf
    (adjointGroup TwistTag.E6.tag K)

private noncomputable def e6F4FixedEquiv (K : Type) [Field K] [CharP K 2] :
    e6F4Fixed K ≃* adjointGroup .F4 K :=
  (Subgroup.subgroupOfEquivOfLe
      (twistedFixedGroup_le_adjointGroup TwistTag.E6 K (RingHom.id K))).trans
    (e6FixedF4Equiv K (CharP.cast_eq_zero K 2))

private noncomputable def e6F4EmbedFixed (K : Type) [Field K] [CharP K 2] :
    adjointGroup .F4 K →* adjointGroup .E6 K :=
  (e6F4Fixed K).subtype.comp (e6F4FixedEquiv K).symm.toMonoidHom

private theorem e6F4EmbedFixed_injective (K : Type) [Field K] [CharP K 2] :
    Function.Injective (e6F4EmbedFixed K) :=
  Subtype.val_injective.comp (e6F4FixedEquiv K).symm.injective

private theorem range_e6F4EmbedFixed (K : Type) [Field K] [CharP K 2] :
    (e6F4EmbedFixed K).range = e6F4Fixed K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((e6F4FixedEquiv K).symm y).2
  · intro hx
    refine ⟨(e6F4FixedEquiv K) ⟨x, hx⟩, ?_⟩
    simp [e6F4EmbedFixed]

private theorem card_e6F4Fixed (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card (e6F4Fixed K) = CFSG.Open.ordF4 (Nat.card K) := by
  rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)]
  exact Nat.card_congr (e6F4FixedEquiv K).toEquiv

private theorem index_e6F4Fixed (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K % 3 = 2) :
    (e6F4Fixed K).index =
      Nat.card K ^ 12 * (Nat.card K ^ 9 - 1) * (Nat.card K ^ 5 - 1) := by
  have hcard := Subgroup.card_mul_index (e6F4Fixed K)
  rw [card_e6F4Fixed, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
    CFSG.LieType.SeitzGeneration.ExcHighThree.ordE6_eq_ordF4_mul_of_mod_two hK] at hcard
  exact Nat.eq_of_mul_eq_mul_left (by
    rw [← card_e6F4Fixed K]
    exact Nat.card_pos) hcard

end F4Fixed

section OneThree


private theorem rankLE_E6_one_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) {E : Subgroup (adjointGroup .E6 K)} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 6 := by
  have hconj_inj : Function.Injective
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) := by
    intro x y hxy
    have h1 : MulAut.conj (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hc : x * y⁻¹ ∈ Subgroup.center (adjointGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun f : MulAut (adjointGroup .E6 K) => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      have hg' : (x * y⁻¹) * g = g * (x * y⁻¹) := by
        have h := congrArg (fun t : adjointGroup .E6 K => t * (x * y⁻¹)) hg
        simpa [mul_assoc] using h
      exact hg'.symm
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    exact mul_inv_eq_one.mp hc
  have hX : IsElemAbelian 3
      (E.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K))) := hE.map _
  have hXI : E.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) ≤
      (TableBExc.E6Three.hatAut .E6 K).range := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, TableBExc.E6Three.adjointGroup_le_hatGroup x.2⟩, ?_⟩
    ext y : 1
    apply Subtype.ext
    rw [TableBExc.E6Three.coe_hatAut_apply, MulAut.conj_apply]
    rfl
  have h6 := (TableBExc.E6Three.card_le_and_normalizes_of_le_hatAut h3 hX hXI).1
  rwa [Subgroup.card_map_of_injective hconj_inj] at h6

end OneThree

section TwoThree


private theorem rankLE_E6_two_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (adjointGroup .E6 K)} (hE : IsElemAbelian 3 E)
    (he : orderOf ((Nat.card K : ℕ) : ZMod 3) = 2) :
    Nat.card E ≤ 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq0 : ((Nat.card K : ℕ) : ZMod 3) ≠ 0 := by
    intro h
    exact (not_dvd_of_orderOf_pos Nat.prime_three he (by norm_num))
      ((ZMod.natCast_eq_zero_iff (Nat.card K) 3).1 h)
  have hq1 : ((Nat.card K : ℕ) : ZMod 3) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    exact absurd he (by norm_num)
  have hval : ((Nat.card K : ℕ) : ZMod 3).val = 2 := by
    have hlt := ZMod.val_lt ((Nat.card K : ℕ) : ZMod 3)
    have hne0 : ((Nat.card K : ℕ) : ZMod 3).val ≠ 0 := fun hv =>
      hq0 ((ZMod.val_eq_zero _).1 hv)
    have hne1 : ((Nat.card K : ℕ) : ZMod 3).val ≠ 1 := fun hv =>
      hq1 ((ZMod.val_eq_one (by norm_num : 1 < 3) _).1 hv)
    omega
  have hmod : Nat.card K % 3 = 2 := by
    rw [← ZMod.val_natCast 3 (Nat.card K)]
    exact hval
  have hd3 : 3 ∣ Nat.card K ^ 2 - 1 :=
    (dvd_pow_sub_one_iff_orderOf hq he).2 (by norm_num : 2 ∣ 2)
  have hnot : ¬ 3 ∣ (e6F4Fixed K).index := by
    rw [index_e6F4Fixed K hmod]
    exact ExcHighThree.not_dvd_three_mod_two hmod
  obtain ⟨g, hg⟩ := ExcHighThree.exists_conj_le_of_not_dvd_index
    (e6F4Fixed K) hnot hE.isPGroup
  set h : adjointGroup .E6 K := g⁻¹ with hh
  have hconj : ∀ x ∈ E, MulAut.conj h x ∈ e6F4Fixed K := by
    intro x hx
    rw [MulAut.conj_apply, hh, inv_inv]
    exact hg x hx
  set E₁ : Subgroup (adjointGroup .E6 K) :=
    E.map (MulAut.conj h).toMonoidHom with hE₁def
  have hE₁ : IsElemAbelian 3 E₁ := hE.map _
  have hE₁le : E₁ ≤ e6F4Fixed K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconj x hx
  have hcardE₁ : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hE₁le_range : E₁ ≤ (e6F4EmbedFixed K).range := by
    rw [range_e6F4EmbedFixed]
    exact hE₁le
  set E₃ : Subgroup (adjointGroup .F4 K) := E₁.comap (e6F4EmbedFixed K) with hE₃def
  have hE₃ : IsElemAbelian 3 E₃ :=
    isElemAbelian_comap_of_injective (e6F4EmbedFixed K) (e6F4EmbedFixed_injective K) hE₁
  have hmap : E₃.map (e6F4EmbedFixed K) = E₁ := Subgroup.map_comap_eq_self hE₁le_range
  have hcardE₃ : Nat.card E₃ = Nat.card E₁ := by
    rw [← Subgroup.card_map_of_injective (f := e6F4EmbedFixed K)
      (e6F4EmbedFixed_injective K), hmap]
  have h4 : Nat.card E₃ ≤ 3 ^ 4 :=
    ExcFieldAutCentRankF4.card_le_pow_four (K := K) (p := 3) Nat.prime_three
      (by norm_num) hd3 hE₃
  calc Nat.card E = Nat.card E₁ := hcardE₁.symm
    _ = Nat.card E₃ := hcardE₃.symm
    _ ≤ 3 ^ 4 := h4

end TwoThree

theorem rankLE_E6 {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    GGElemAbelianRankLE (adjointGroup .E6 K) p (degCount .E6 e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hpdiv : ¬ p ∣ Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    intro h
    obtain ⟨f, -, hfcard⟩ := FiniteField.card (K := K) 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hfcard]
    rw [hK] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  intro E hE
  by_cases he1 : e = 1
  · rw [he1] at he ⊢
    have hpq1 : p ∣ Nat.card K - 1 := by
      have h := (dvd_pow_sub_one_iff_orderOf (d := 1) hq he).2 (dvd_refl 1)
      simpa using h
    have hp_cases : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
      by_cases h7 : 7 ≤ p
      · exact Or.inr (Or.inr h7)
      · have hp2' : 2 ≤ p := hp.two_le
        interval_cases p <;>
          first
            | exact Or.inl rfl
            | exact Or.inr (Or.inl rfl)
            | exact absurd rfl hp2
            | exact absurd hp (by decide)
    have hdeg : degCount .E6 1 = 6 := by decide
    rcases hp_cases with rfl | rfl | hp7
    · have h6 := rankLE_E6_one_three (K := K) hpq1 hE
      rwa [hdeg]
    · have hV : Nat.card (TableBExc.torusPow .E6 K 5) = 5 ^ 6 :=
        TableBExc.card_torusPow_E6 (K := K) Nat.prime_five (by norm_num) hpq1
      have hT := TableBExc.ggExcToralRankInput_E6_five (K := K) hpq1
      calc Nat.card E ≤ 5 ^ 6 := hT.card_le hV hE
        _ = 5 ^ degCount .E6 1 := by rw [hdeg]
    · have hV : Nat.card (TableBExc.torusPow .E6 K p) = p ^ 6 :=
        TableBExc.card_torusPow_E6 (K := K) hp (by omega) hpq1
      have hT := TableBExc.ggExcToralRankInput_E6_of_seven_le (K := K) hp hp7 hpq1
      calc Nat.card E ≤ p ^ 6 := hT.card_le hV hE
        _ = p ^ degCount .E6 1 := by rw [hdeg]
  by_cases he2 : e = 2
  · rw [he2] at he ⊢
    have hpq2 : p ∣ Nat.card K ^ 2 - 1 :=
      (dvd_pow_sub_one_iff_orderOf (d := 2) hq he).2 (by norm_num : 2 ∣ 2)
    have hdeg : degCount .E6 2 = 4 := by decide
    by_cases hp3 : p = 3
    · subst p
      have h4 := rankLE_E6_two_three (K := K) hE he
      rwa [hdeg]
    · have hp5 : 5 ≤ p := by
        have hp2' : 2 ≤ p := hp.two_le
        by_contra h
        have hp4 : p ≤ 4 := by omega
        interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp (by decide)
      have hp3lt : 3 < p := by omega
      have hS : SylowTorus (adjointGroup .E6 K) p 4 :=
        sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3lt hpdiv
          (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2] e6Two_charpoly
          (by simpa using e6Two_pow) he
          (by
            intro d hd hd2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
            all_goals first | exact hp.not_dvd_one | exact absurd rfl hd2)
          (by
            intro d hd h2d
            simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
            · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num)
            · exact absurd h2d (by norm_num)
            · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num)
            · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num)
            · exact absurd h2d (by norm_num)
            · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num))
          (by decide)
      calc Nat.card E ≤ p ^ 4 := hS.rank_le hp hE
        _ = p ^ degCount .E6 2 := by rw [hdeg]
  · have he0 : e ≠ 0 := fun h => orderOf_natCast_ne_zero hp hpdiv (by rw [he, h])
    have he3le : 3 ≤ e := by omega
    have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
      intro h
      exact hpdiv ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hedvd : e ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have hp3lt : 3 < p := by
      have hp2' : 2 ≤ p := hp.two_le
      have h3le : 3 ≤ p - 1 := he3le.trans (Nat.le_of_dvd (by omega) hedvd)
      omega
    have hpq : ¬ p ∣ Nat.card K := hpdiv
    by_cases h0 : degCount .E6 e = 0
    · have hE1 : Nat.card E = 1 :=
        elemAbelian_card_eq_one_of_degCount_zero (τ := .E6) (by simp) K hp hp3lt hpq he h0 hE
      rw [hE1, h0, pow_zero]
    · have hpos : 0 < degCount .E6 e := Nat.pos_of_ne_zero h0
      have h30 := le_thirty_of_degCount_pos (τ := .E6) (by simp) hpos
      have he_cases : e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 9 ∨ e = 12 := by
        have key : ∀ o, 3 ≤ o → o ≤ 30 → 0 < degCount .E6 o →
            o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 8 ∨ o = 9 ∨ o = 12 := by decide
        exact key e he3le h30 hpos
      rcases he_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      ·
        have h3dvd : 3 ∣ p - 1 := by
          rw [← he]
          exact ZMod.orderOf_dvd_card_sub_one hq0
        have hp5 : 5 ≤ p := by
          have hp2' : 2 ≤ p := hp.two_le
          by_contra h
          have hp4 : p = 4 := by
            have := Nat.le_of_dvd (by omega) h3dvd
            omega
          subst hp4
          exact absurd hp (by decide)
        have hp7 : 3 < p := by omega
        have hdeg : degCount .E6 3 = 3 := by decide
        have hS : SylowTorus (adjointGroup .E6 K) p 3 :=
          sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp7 hpdiv
            (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3] e6Three_charpoly
            e6Three_pow he
            (by
              intro d hd hd3
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
              rcases hd with rfl | rfl | rfl
              all_goals exact absurd rfl hd3)
            (by
              intro d hd h3d
              simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
              rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd h3d (by norm_num)
              · exact absurd h3d (by norm_num)
              · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num)
              · exact absurd h3d (by norm_num)
              · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num)
              · exact not_dvd_small_E6 hp hp5 (by norm_num) (by norm_num) (by norm_num))
            (by decide)
        calc Nat.card E ≤ p ^ 3 := hS.rank_le hp hE
          _ = p ^ degCount .E6 3 := by rw [hdeg]
      ·
        have hdeg : degCount .E6 4 = 2 := by decide
        have hS := sylowTorus_E6_four K hp he
        calc Nat.card E ≤ p ^ 2 := hS.rank_le hp hE
          _ = p ^ degCount .E6 4 := by rw [hdeg]
      ·
        have hdeg : degCount .E6 5 = 1 := by decide
        have hS := sylowTorus_E6_five K hp he
        calc Nat.card E ≤ p ^ 1 := hS.rank_le hp hE
          _ = p ^ degCount .E6 5 := by rw [hdeg]
      ·
        have hdeg : degCount .E6 6 = 2 := by decide
        have hS := sylowTorus_E6_six K hp he
        calc Nat.card E ≤ p ^ 2 := hS.rank_le hp hE
          _ = p ^ degCount .E6 6 := by rw [hdeg]
      ·
        have hdeg : degCount .E6 8 = 1 := by decide
        have hS := sylowTorus_E6_eight K hp he
        calc Nat.card E ≤ p ^ 1 := hS.rank_le hp hE
          _ = p ^ degCount .E6 8 := by rw [hdeg]
      ·
        have hdeg : degCount .E6 9 = 1 := by decide
        have hS := sylowTorus_E6_nine K hp he
        calc Nat.card E ≤ p ^ 1 := hS.rank_le hp hE
          _ = p ^ degCount .E6 9 := by rw [hdeg]
      ·
        have hdeg : degCount .E6 12 = 1 := by decide
        have hS := sylowTorus_E6_twelve K hp he
        calc Nat.card E ≤ p ^ 1 := hS.rank_le hp hE
          _ = p ^ degCount .E6 12 := by rw [hdeg]
  done

theorem exists_E6 {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    GGExcElemAbelianExists (adjointGroup .E6 K) p (degCount .E6 e - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hpdiv : ¬ p ∣ Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    intro h
    obtain ⟨f, -, hfcard⟩ := FiniteField.card (K := K) 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hfcard]
    rw [hK] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have he0 : e ≠ 0 := fun h => orderOf_natCast_ne_zero hp hpdiv (by rw [he, h])
  by_cases he1 : e = 1
  · rw [he1] at he ⊢
    by_cases hp3 : p = 3
    · subst p
      have hrat := relIndex_dvd_untwisted 3 (Or.inl ⟨rfl, rfl⟩) K
      obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks (by norm_num) K hrat
        (IsWeylMatrix.of_word Tag.E6 e6OneWord) [1, 1, 1, 1, 1, 1]
        e6One_charpoly e6One_pow he (by norm_num) (by decide)
      have hcard : 3 ^ 5 ≤ Nat.card E := by
        have h : 3 * 3 ^ 5 ≤ 3 * Nat.card E := by
          calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
            _ ≤ 3 * Nat.card E := hle
        exact Nat.le_of_mul_le_mul_left h (by norm_num)
      refine ⟨E, hE, ?_⟩
      have hdeg : degCount .E6 1 - 1 = 5 := by decide
      rwa [hdeg]
    · have hp3lt : 3 < p := by
        by_contra h
        have hp4 : p ≤ 3 := by omega
        have hp2' : 2 ≤ p := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
      obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E6_one K hp hp3lt he
      refine ⟨E, hE, ?_⟩
      have hdeg : degCount .E6 1 - 1 = 5 := by decide
      rw [hdeg, hcard]
      exact Nat.pow_le_pow_right hp.pos (by norm_num)
  by_cases he2 : e = 2
  · rw [he2] at he ⊢
    by_cases hp3 : p = 3
    · subst p
      have hrat := relIndex_dvd_untwisted 3 (Or.inl ⟨rfl, rfl⟩) K
      obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks (by norm_num) K hrat
        (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2]
        e6Two_charpoly e6Two_pow he (by norm_num) (by decide)
      have hcard : 3 ^ 3 ≤ Nat.card E := by
        have h : 3 * 3 ^ 3 ≤ 3 * Nat.card E := by
          calc 3 * 3 ^ 3 = 3 ^ 4 := by norm_num
            _ ≤ 3 * Nat.card E := hle
        exact Nat.le_of_mul_le_mul_left h (by norm_num)
      refine ⟨E, hE, ?_⟩
      have hdeg : degCount .E6 2 - 1 = 3 := by decide
      rwa [hdeg]
    · have hp3lt : 3 < p := by
        by_contra h
        have hp4 : p ≤ 3 := by omega
        have hp2' : 2 ≤ p := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
      obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E6_two K hp hp3lt he
      refine ⟨E, hE, ?_⟩
      have hdeg : degCount .E6 2 - 1 = 3 := by decide
      rw [hdeg, hcard]
      exact Nat.pow_le_pow_right hp.pos (by norm_num)
  · have he3le : 3 ≤ e := by omega
    have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
      intro h
      exact hpdiv ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hedvd : e ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have hp3lt : 3 < p := by
      have hp2' : 2 ≤ p := hp.two_le
      have h3le : 3 ≤ p - 1 := he3le.trans (Nat.le_of_dvd (by omega) hedvd)
      omega
    by_cases h0 : degCount .E6 e = 0
    · refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
      rw [h0]
      simp
    · have hpos : 0 < degCount .E6 e := Nat.pos_of_ne_zero h0
      have h30 := le_thirty_of_degCount_pos (τ := .E6) (by simp) hpos
      have he_cases : e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 9 ∨ e = 12 := by
        have key : ∀ o, 3 ≤ o → o ≤ 30 → 0 < degCount .E6 o →
            o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 8 ∨ o = 9 ∨ o = 12 := by decide
        exact key e he3le h30 hpos
      rcases he_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      ·
        obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E6_three K hp he
        refine ⟨E, hE, ?_⟩
        have hdeg : degCount .E6 3 - 1 = 2 := by decide
        rw [hdeg, hcard]
        exact Nat.pow_le_pow_right hp.pos (by norm_num)
      ·
        obtain ⟨E, hE, hcard⟩ := (sylowTorus_E6_four K hp he).exists_elemAbelian
        refine ⟨E, hE, ?_⟩
        have hdeg : degCount .E6 4 - 1 = 1 := by decide
        rw [hdeg, hcard]
        exact Nat.pow_le_pow_right hp.pos (by norm_num)
      ·
        refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
        have hdeg : degCount .E6 5 - 1 = 0 := by decide
        rw [hdeg]
        simp
      ·
        obtain ⟨E, hE, hcard⟩ := (sylowTorus_E6_six K hp he).exists_elemAbelian
        refine ⟨E, hE, ?_⟩
        have hdeg : degCount .E6 6 - 1 = 1 := by decide
        rw [hdeg, hcard]
        exact Nat.pow_le_pow_right hp.pos (by norm_num)
      ·
        refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
        have hdeg : degCount .E6 8 - 1 = 0 := by decide
        rw [hdeg]
        simp
      ·
        refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
        have hdeg : degCount .E6 9 - 1 = 0 := by decide
        rw [hdeg]
        simp
      ·
        refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
        have hdeg : degCount .E6 12 - 1 = 0 := by decide
        rw [hdeg]
        simp
  done

end CFSG.StandardType
