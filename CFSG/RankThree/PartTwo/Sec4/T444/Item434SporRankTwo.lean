module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporOrder
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.RankThree.Asc83Table.J4
public import CFSG.RankThree.Asc83Table.Ru
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.Asc83Table.M24
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Quasithin.EmptyFaithful.A38c9Out
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.RankThree.PartTwo.Toolkit.M12Clause
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import Certificates.Certificate10090
public import Certificates.Certificate10090Base
public import Certificates.Certificate1021
public import Certificates.Certificate16041
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2121
public import Certificates.Certificate2122
public import Certificates.Certificate2123
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2173
public import Certificates.Certificate2178
public import Certificates.Certificate2179
public import Certificates.Certificate2183
public import Certificates.Certificate2214
public import Certificates.Certificate2215
public import Certificates.Certificate2217
public import Certificates.Certificate2274
public import Certificates.Certificate2309
public import Certificates.Certificate2311
public import Certificates.Certificate2313
public import Certificates.Certificate2314
public import Certificates.Certificate2315
public import Certificates.Certificate2317
public import Certificates.Certificate2323
public import Certificates.Certificate2324
public import Certificates.Certificate2325
public import Certificates.Certificate3085
public import Certificates.Certificate3085Base

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores CFSG.Blueprint
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434Spor

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem isElementaryAbelian_of_isElemAbelian {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) : IsElementaryAbelian 3 D :=
  { toIsMulCommutative := hD.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hD.2 x x.2) }

theorem noE27_of_pRank_le_two [Finite X] (hX : CFSG.pRank 3 X ≤ 2) (D : Subgroup X)
    (hD : CFSG.Assembly.IsElemAbelian 3 D) : Nat.card D ≠ 27 := by
  intro h27
  have := CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) D
    (isElementaryAbelian_of_isElemAbelian hD) (k := 3) (by rw [h27]; norm_num)
  omega

theorem noE27_of_extraspecial_sylow [Finite X] (h3 : (Nat.card X).factorization 3 = 3)
    (hP : ∀ P : Sylow 3 X, IsExtraspecialPGroup 3 (P : Subgroup X)) (D : Subgroup X)
    (hD : CFSG.Assembly.IsElemAbelian 3 D) : Nat.card D ≠ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h27
  set S := Sylow.ofCard D (by rw [h27, h3]; norm_num) with hS
  have hSD : (S : Subgroup X) = D := Sylow.coe_ofCard _ _
  have hext := hP S
  rw [hSD] at hext
  have htop : Subgroup.center D = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hD.1.is_comm.comm y x
  have hc := hext.2.2.2
  rw [htop, Subgroup.card_top, h27] at hc
  omega

theorem false_of_noE27 (h : Ctx434Core G A M Q) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hout : ¬ 3 ∣ Nat.card (Outer X)) (hcen : Subgroup.center X = ⊥)
    (hX : ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D ≠ 27)
    (h27 : Nat.card h.layerStar = 27) : False := by
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, card_map_quotConj h e, h27]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e)
  exact hX P hPe hP27

theorem false_of_noE27_of_mulEquiv (h : Ctx434Core G A M Q) {Y : Type*} [Group Y]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (b : Y ≃* X) (hY : ¬ (Nat.card Y).Prime)
    (hout : ¬ 3 ∣ Nat.card (Outer Y))
    (hX : ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D ≠ 27)
    (h27 : Nat.card h.layerStar = 27) : False := by
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := h.isQuasisimple.2.1
  have : IsSimpleGroup X := e.symm.isSimpleGroup
  have hcen : Subgroup.center X = ⊥ :=
    center_eq_bot_of_simple (by rwa [← Nat.card_congr b.toEquiv])
  have hout' : ¬ 3 ∣ Nat.card (Outer X) := by
    rwa [← Nat.card_congr (equivalence b).toEquiv]
  exact false_of_noE27 h e hout' hcen hX h27

end Item434Spor

section Families


theorem item434SporAtCard_m24_27 :
    Item434SporAtCard .M24 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .M24 ≃* Spor .M24 := b
  have hcard : Nat.card (Spor .M24) = 244823040 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  have : Finite (Spor .M24) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank := (CFSG.RankThree.Asc83Table.M24.table (L := Spor .M24) ⟨b'.symm⟩).2.1
  refine (Item434Spor.false_of_noE27_of_mulEquiv hc e₀ b' ?_ ?_
    (Item434Spor.noE27_of_pRank_le_two hrank.le) h27).elim
  · rw [Nat.card_congr b'.toEquiv, hcard]
    norm_num
  · rw [CFSG.Quasithin.A38c9.outer_card_M24]
    norm_num

theorem item434SporAtCard_j4_27 :
    Item434SporAtCard .J4 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.J4.card_J4]
  have : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank := (CFSG.RankThree.Asc83Table.J4.table (L := Spor .J4) ⟨b'.symm⟩).2.1
  refine (Item434Spor.false_of_noE27_of_mulEquiv hc e₀ b' ?_ inputs47Core_outJ4
    (Item434Spor.noE27_of_pRank_le_two hrank.le) h27).elim
  rw [Nat.card_congr b'.toEquiv, hcard]
  norm_num

theorem item434SporAtCard_he_27
 :
    Item434SporAtCard .He 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .He ≃* Spor .He := b
  have hcard : Nat.card (Spor .He) = 4030387200 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.He.card_He]
  have : Finite (Spor .He) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite (NativeSporadic.Carrier .He) := Finite.of_equiv _ b'.symm.toEquiv
  have hrank := (CFSG.RankThree.Asc83Table.He.table (L := Spor .He) ⟨b'.symm⟩).2.1
  refine (Item434Spor.false_of_noE27_of_mulEquiv hc e₀ b' ?_ ?_
    (Item434Spor.noE27_of_pRank_le_two hrank.le) h27).elim
  · rw [Nat.card_congr b'.toEquiv, hcard]
    norm_num
  · exact Item434Spor.not_three_dvd_card_outer_of_le_two
      CFSG.Sporadic.Schreier.AT_He_Schreier.1

theorem item434SporAtCard_ru_27 :
    Item434SporAtCard .Ru 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  have bP : CFSG.Sporadic.RuSchreier.ruP ≃* Spor .Ru :=
    CFSG.Sporadic.RuSchreier.ruEquivP.symm.trans b
  have hcard : Nat.card (Spor .Ru) = 145926144000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  have : Finite (Spor .Ru) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank := (CFSG.RankThree.Asc83Table.Ru.table (L := Spor .Ru) ⟨b'.symm⟩).2.1
  refine (Item434Spor.false_of_noE27_of_mulEquiv hc e₀ bP ?_ ?_
    (Item434Spor.noE27_of_pRank_le_two hrank.le) h27).elim
  · rw [Nat.card_congr bP.toEquiv, hcard]
    norm_num
  · rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]
    norm_num

theorem item434SporAtCard_m12_27 :
    Item434SporAtCard .M12 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : NativeSporadic.M12 ≃* Spor .M12 := b
  have hcard : Nat.card (Spor .M12) = 95040 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  have : Finite (Spor .M12) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h3 : (Nat.card (Spor .M12)).factorization 3 = 3 := by
    rw [hcard, show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  have hloc := CFSG.RankThree.PartTwo.Toolkit.m12ThreeLocalData (Spor .M12) ⟨b'.symm⟩
  refine (Item434Spor.false_of_noE27_of_mulEquiv hc e₀ b' ?_ ?_
    (Item434Spor.noE27_of_extraspecial_sylow h3 fun P => (hloc P).1) h27).elim
  · rw [Nat.card_congr b'.toEquiv, hcard]
    norm_num
  · rw [CFSG.ComponentClassification.M12Cover.card_outer]
    norm_num

theorem item434SporAtCard_j2_27 :
    Item434SporAtCard .J2 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : NativeSporadic.J2 ≃* Spor .J2 := b
  have hcard : Nat.card (Spor .J2) = 604800 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J2.card_J2]
  have : Finite (Spor .J2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite NativeSporadic.J2 := Finite.of_equiv _ b'.symm.toEquiv
  have h3 : (Nat.card (Spor .J2)).factorization 3 = 3 := by
    rw [hcard, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  refine (Item434Spor.false_of_noE27_of_mulEquiv hc e₀ b' ?_ ?_
    (Item434Spor.noE27_of_extraspecial_sylow h3 fun P =>
      (CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 (Spor .J2) ⟨b'.symm⟩ P _ rfl _
        rfl).1.1.1) h27).elim
  · rw [Nat.card_congr b'.toEquiv, hcard]
    norm_num
  · exact Item434Spor.not_three_dvd_card_outer_of_le_two
      CFSG.Sporadic.Schreier.AT_J2_Schreier.1

theorem item434SporAtCard_j3_nine_of
    (hc : Item434SporAtNineCover .J3) : Item434SporAtCard .J3 9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .J3 ≃* Spor .J3 := b
  have hrank := (CFSG.RankThree.Asc83Table.J3.table (L := Spor .J3) ⟨b'.symm⟩).1
  exact Item434Spor.item434SporAtCard_nine_of
    (Item434Spor.exists_e27_of_two_lt_pRank (by omega)) hc

end Families

end CFSG.RankThree.PartTwo.Sec4
