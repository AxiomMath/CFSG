module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKFactDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactOddProps
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactWreathRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Sect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupL2
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1
import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem exists_isPGroup_two_section_of_isL2 {Q : Type} [Group Q] {X : Subgroup Q} {n : ℕ}
    (hX : IsL2 (Bar2 X) n) :
    ∃ (T₀ : Subgroup Q) (E : Type) (_ : Group E) (_ : Finite E) (π : ↥T₀ →* E),
      T₀ ≤ X ∧ IsPGroup 2 ↥T₀ ∧ Function.Surjective π ∧
        (∀ e : E, e * e = 1) ∧ Nat.card E = 2 ^ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, hFfield, hFfin, hFcard, -, ⟨eBar⟩⟩ := uc22p22g_isL2_psl hX
  let : Field F := hFfield
  let : Finite F := hFfin
  have : Finite (Bar2 X) := Finite.of_injective eBar.toMonoidHom eBar.injective
  let Gp : Type := CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F
  let P : Sylow 2 Gp := Classical.choice Sylow.nonempty
  let S : Sylow 2 (Bar2 X) :=
    Sylow.mapSurjective (f := eBar.symm.toMonoidHom) eBar.symm.surjective P
  have hScoe : (S : Subgroup (Bar2 X)) =
      (P : Subgroup Gp).map eBar.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (P := P) (f := eBar.symm.toMonoidHom) eBar.symm.surjective
  have hPel : IsElementaryAbelian 2 ↥(P : Subgroup Gp) :=
    (CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_sylow_elementary_card n hFcard P).1
  have hPcard : Nat.card ↥(P : Subgroup Gp) = 2 ^ n :=
    ((CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_sylow_elementary_card n hFcard P).2).trans
      hFcard
  have hSel : IsElementaryAbelian 2 ↥(S : Subgroup (Bar2 X)) := by
    have := hPel
    rw [hScoe]
    exact IsElementaryAbelian.map eBar.symm.toMonoidHom
  have hScard : Nat.card ↥(S : Subgroup (Bar2 X)) = 2 ^ n := by
    rw [hScoe, Subgroup.card_map_of_injective eBar.symm.injective]
    exact hPcard
  let N : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π₀ : ↥X →* Bar2 X := QuotientGroup.mk' N
  let Tpre : Subgroup ↥X := (S : Subgroup (Bar2 X)).comap π₀
  let T₀ : Subgroup Q := Tpre.map X.subtype
  let eT : ↥Tpre ≃* ↥T₀ := Subgroup.equivMapOfInjective Tpre X.subtype X.subtype_injective
  let φ : ↥Tpre →* ↥(S : Subgroup (Bar2 X)) :=
    (π₀.comp Tpre.subtype).codRestrict _ (fun t => Subgroup.mem_comap.mp t.2)
  let π : ↥T₀ →* ↥(S : Subgroup (Bar2 X)) := φ.comp eT.symm.toMonoidHom
  have hTpre : IsPGroup 2 ↥Tpre := by
    refine IsPGroup.comap_of_ker_isPGroup (p := 2)
      (H := (S : Subgroup (Bar2 X))) S.isPGroup' π₀ ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  have hT₀ : IsPGroup 2 ↥T₀ := IsPGroup.map hTpre X.subtype
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨x', hx'⟩ := QuotientGroup.mk'_surjective N (e : Bar2 X)
    refine ⟨⟨x', Subgroup.mem_comap.mpr (by rw [hx']; exact e.2)⟩, ?_⟩
    exact Subtype.ext hx'
  have hπsurj : Function.Surjective π := hφsurj.comp eT.symm.surjective
  have hpow : ∀ e : ↥(S : Subgroup (Bar2 X)), e * e = 1 := by
    intro e
    have h : e ^ 2 = 1 := by
      have := hSel
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 ↥(S : Subgroup (Bar2 X))) e
    simpa [pow_two] using h
  exact ⟨T₀, ↥(S : Subgroup (Bar2 X)), inferInstance, inferInstance, π,
    Subgroup.map_subtype_le Tpre, hT₀, hπsurj, hpow, hScard⟩

theorem kFactL2Odd_not_three_group {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    {X W T : Subgroup Q} {n r : ℕ} (c : KCfgL2Odd X W T n r) : False := by
  have h2Bar : 2 ∣ Nat.card (Bar2 X) :=
    (dvd_pow_self 2 (by have := c.five_le; omega : n ≠ 0)).trans
      (Dvd.intro _ (KNL23.card_isL2 c.isL2).2.symm)
  have hBarX : Nat.card (Bar2 X) ∣ Nat.card X :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  have hXQ : Nat.card X ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card X
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have h2Q : 2 ∣ Nat.card Q := (h2Bar.trans hBarX).trans hXQ
  rw [hk] at h2Q
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2Q) (by decide)

theorem kFactL2Odd_not_J1 {Q : Type} [Group Q] [Finite Q] (hQ : IsSpor Q .J1)
    {X W T : Subgroup Q} {n r : ℕ} (c : KCfgL2Odd X W T n r) : False := by
  have h32Bar : 2 ^ 5 ∣ Nat.card (Bar2 X) :=
    (pow_dvd_pow 2 c.five_le).trans (Dvd.intro _ (KNL23.card_isL2 c.isL2).2.symm)
  have hBarX : Nat.card (Bar2 X) ∣ Nat.card X :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  have hXQ : Nat.card X ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card X
  have h32Q : 2 ^ 5 ∣ Nat.card Q := (h32Bar.trans hBarX).trans hXQ
  have hcardQ : Nat.card Q = 175560 := KNL23.card_isJ1 hQ
  rw [hcardQ] at h32Q
  exact absurd h32Q (by decide)

theorem kFactL2Odd_L2_odd {Q : Type} [Group Q] [Finite Q] {p f : ℕ} (hp : p ≠ 2)
    (hQ : LieModel Q .PSL 2 p f) {X W T : Subgroup Q} {n r : ℕ} (c : KCfgL2Odd X W T n r) :
    False := by
  have hn5 : 5 ≤ n := c.five_le
  exact CFSG.LocalAnalysis.WeakClosure81.not_isCalL1_of_sectionalTwoRankLE_two
    (CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model hp hQ) X
    (CFSG.pCore 2 ↥X) ⟨n, c.odd, by omega, Or.inl c.isL2⟩

theorem kFactL2Odd_L3U3_odd {Q : Type} [Group Q] [Finite Q] {p f : ℕ} (hp : p ≠ 2)
    (hQ : LieModel Q .PSL 3 p f ∨ LieModel Q .PSU 3 p f) {X W T : Subgroup Q} {n r : ℕ}
    (c : KCfgL2Odd X W T n r) : False := by
  obtain ⟨T₀, E, hEgroup, hEfin, π, hT₀X, hT₀, hπ, hexp, hScard⟩ :=
    exists_isPGroup_two_section_of_isL2 c.isL2
  let : Group E := hEgroup
  let : Finite E := hEfin
  obtain ⟨B, hBT₀, hBab, hBidx⟩ :=
    exists_abelian_index_two_of_isPGroup_two_L3U3 hp hQ T₀ hT₀
  let A : Subgroup ↥T₀ := B.subgroupOf T₀
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb =>
      Subtype.ext (hBab (a : Q) (Subgroup.mem_subgroupOf.mp ha) (b : Q)
        (Subgroup.mem_subgroupOf.mp hb))
  have hcard4 : Nat.card (A.map π) ≤ 4 :=
    card_map_le_four_of_pRank_two_le_two (pRank_two_le_two_L3U3 hp hQ) π hexp hAab
  have hAidx : A.index ≤ 2 := show (B.subgroupOf T₀).index ≤ 2 from hBidx
  have hCidx : (A.map π).index ≤ 2 := by
    have hpos : 0 < A.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := A))
    exact (Nat.le_of_dvd hpos (Subgroup.index_map_dvd (H := A) (f := π) hπ)).trans hAidx
  have hle : Nat.card E ≤ 8 := by
    calc Nat.card E = Nat.card (A.map π) * (A.map π).index := (Subgroup.card_mul_index _).symm
      _ ≤ 4 * 2 := Nat.mul_le_mul hcard4 hCidx
      _ = 8 := by norm_num
  have h32 : 32 ≤ Nat.card E := by
    rw [hScard]
    have h5 : 5 ≤ n := c.five_le
    have h : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) h5
    simpa using h
  omega

theorem kFactL2Odd_L2_even {Q : Type} [Group Q] [Finite Q] {f : ℕ}
    (hQ : LieModel Q .PSL 2 2 f) (hcyc : ∀ P : Subgroup Q, IsPGroup 3 ↥P → IsCyclic ↥P)
    {X W T : Subgroup Q} {n r : ℕ} (c : KCfgL2Odd X W T n r) : W = ⊤ := by
  obtain ⟨hsimple, a, b, hab⟩ :=
    CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel c.isL2
  have hnc : ¬ IsMulCommutative (Bar2 X) := fun h => hab (h.is_comm.comm a b)
  have h3Bar : 3 ∣ Nat.card (Bar2 X) := three_dvd_card_of_isL2 c.isL2
  have hdvd : Nat.card (Bar2 X) ∣ Nat.card ↥X :=
    Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X)
  have h3X : 3 ∣ Nat.card ↥X := h3Bar.trans hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3X
  let A : Subgroup Q := (Subgroup.zpowers x).map X.subtype
  have hAX : A ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hA3 : Nat.card A = 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hx]
  have hW : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W := fun hW3 =>
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.false_of_isPSolvable_surj
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (p := 3) (X := Q) (N := W) (Y := X) hW3 c.X_le)
      ⊤ ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp
        (Subgroup.topEquiv (G := ↥X)).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := ↥X)).surjective)
      hsimple hnc h3Bar
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hQ.statedClassicalModel (by decide)
  have hL2 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.OvergroupEqTop
      (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.overgroupEqTop_psl2 (p := 2) hF
      (by norm_num : (2 : ℕ) ≠ 3)
  have e : Q ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
    eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.overgroupEqTop_of_mulEquiv
    e hL2 hcyc A W hA3 (c.N3 A hAX hA3) hW

theorem kFactL2Odd_U3_even {Q : Type} [Group Q] [Finite Q] {f : ℕ} (hQ : LieModel Q .PSU 3 2 f)
    {X W T : Subgroup Q} {n r : ℕ} (c : KCfgL2Odd X W T n r) : W = ⊤ := by
  have : IsSimpleGroup Q := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hQ
  have hB : fusionIsBenderGroup Q := uc22p2214_bor_bender_U3 hQ
  have hBor : fusionBenderBorel Q (2 ^ f) 3 :=
    CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_PSU3 hQ
  obtain ⟨S, hS⟩ := uc22p2214_bor_sylow c.T_sylow
  by_contra hW
  have hQle : (S : Subgroup Q) ≤ W := hS ▸ c.T_le
  have hle : W ≤ Subgroup.normalizer ((S : Subgroup Q) : Set Q) :=
    CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB S hQle hW
  have hsolvN : Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup Q) : Set Q)) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_normalizer_of_benderBorel hBor S
  have hsolvW : Group.IsSolvable ↥W := by
    have := hsolvN
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hsolvX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion c.X_le)
      (Subgroup.inclusion_injective c.X_le)
  obtain ⟨hsimpleBar, a, b, hab⟩ :=
    CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel c.isL2
  have : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal (p := 2) (G := ↥X)
  have hsolvBar : Group.IsSolvable (Bar2 X) := by
    have := hsolvX
    exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolvBar a b)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
