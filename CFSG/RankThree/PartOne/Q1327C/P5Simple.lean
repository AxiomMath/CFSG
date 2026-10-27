module

public import CFSG.RankThree.PartOne.N143X.Item613Plane
public import CFSG.RankThree.PartOne.N143X.InnerPlaneClassical
public import CFSG.RankThree.PartOne.N143X.InnerPlaneG2
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartOne.N143.Item613IdxDefs
public import CFSG.RankThree.PartOne.S11c.OddClassicalPlane
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneRu
public import CFSG.RankThree.PartOne.SPOR.I613Item3
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.RankThree.PartOne.CTP.SeitzExc
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneTh

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Census3 CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.N143X TauCeti
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped commutatorElement

theorem center_eq_bot_of_nonabelian {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact (hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)).elim

theorem hasDihedralSylowTwo_of_item1 {Y : Type} [Group Y] [Finite Y] (h : ThmThreeItem1 Y) :
    GorensteinWalter.HasDihedralSylowTwo Y := by
  obtain ⟨q, hq2, -, hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.eq_two_or_odd'.resolve_left hq2, q.exponent_pos, hcard⟩
  let eP : Y ≃* GorensteinWalter.PSL2 (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  exact CFSG.ComponentClassification.OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv eP
    (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hodd)

theorem p5_item1 {Y : Type} [Group Y] [Finite Y] (h : ThmThreeItem1 Y) {E S : Subgroup Y}
    [IsElementaryAbelian 5 E] (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hEN : E ≤ Subgroup.normalizer (S : Set Y)) (hSE : ⁅S, E⁆ = S) : False := by
  have hEp : ∀ x ∈ E, x ^ 5 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hcent := no_action_of_dihedral (hasDihedralSylowTwo_of_item1 h) Nat.prime_five le_rfl
    hEp hS2 hEN
  have hcomm : ⁅E, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  apply hS1
  rw [← hSE, Subgroup.commutator_comm]
  exact hcomm

theorem p5_item2 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] (h : ThmThreeItem2 Y)
    {E S : Subgroup Y} [IsElementaryAbelian 5 E] (hE : 5 ^ 2 ≤ Nat.card E) (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hEN : E ≤ Subgroup.normalizer (S : Set Y)) (hSE : ⁅S, E⁆ = S) :
    False := by
  have hZ : Subgroup.center Y = ⊥ :=
    center_eq_bot_of_nonabelian (SPOR.nonabelian_of_plane Nat.prime_five hE)
  obtain ⟨q, hq2, -, hA | hU⟩ := h
  · obtain ⟨hv, ⟨e⟩⟩ := hA
    have hmod : StatedClassicalModel Y .PSL 3 q.p q.exponent :=
      statedClassicalModel_of_isoLie_A (r := 2) hv e
    exact item613_false_of_inner_planes hZ Nat.prime_five le_rfl
      (fun E' U hplane hE' => planeCentralizes_inner_psl hZ (by norm_num) (by norm_num)
        q.prime_p hq2 hmod hplane hE' degreeFourPlane) hE hS1 hS2 hEN hSE
  · obtain ⟨hv, ⟨e⟩⟩ := hU
    have hmod : StatedClassicalModel Y .PSU 3 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    exact item613_false_of_inner_planes hZ Nat.prime_five le_rfl
      (fun E' U hplane hE' => planeCentralizes_inner_psu hZ (by norm_num) (by norm_num)
        q.prime_p hq2 hmod hplane hE' degreeFourPlane) hE hS1 hS2 hEN hSE

theorem p5_item3
    {Y : Type} [Group Y] [Finite Y] (h : ThmThreeItem3 Y) (h5 : 5 ^ 2 ∣ Nat.card Y) : False := by
  have hX := SPOR.card_smallRee_model (f := 3) (ℓ := 3) rfl (CTP.reeTitsModel_reeG2 1 h)
  have hdvd : 5 ^ 2 ∣ 3 ^ 0 * ((3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1)) := by
    rw [pow_zero, one_mul, ← hX]
    exact h5
  exact CTP.not_sq_dvd_smallRee_aut Nat.prime_five le_rfl hdvd

theorem p5_item4
    {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] (h : ThmThreeItem4 Y)
    {E S : Subgroup Y} [IsElementaryAbelian 5 E] (hE : 5 ^ 2 ≤ Nat.card E) (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hEN : E ≤ Subgroup.normalizer (S : Set Y)) (hSE : ⁅S, E⁆ = S) :
    False := by
  have hZ : Subgroup.center Y = ⊥ :=
    center_eq_bot_of_nonabelian (SPOR.nonabelian_of_plane Nat.prime_five hE)
  obtain ⟨q, hq2, -, hG | hB | hU | hA⟩ := h
  · obtain ⟨hv, ⟨e⟩⟩ := hG
    have hmod : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 q.p q.exponent :=
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
        (CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv hq2)
    exact item613_false_of_inner_planes hZ Nat.prime_five le_rfl
      (fun E' U hplane hE' => planeCentralizes_inner_G2 q.prime_p hq2 hmod hplane hE') hE hS1
      hS2 hEN hSE
  · obtain ⟨hv, ⟨e⟩⟩ := hB
    have hmod : StatedClassicalModel Y .PSp 2 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    exact item613_false_of_inner_planes hZ Nat.prime_five le_rfl
      (fun E' U hplane hE' => planeCentralizes_inner_psp_four hZ q.prime_p hq2 hmod hplane hE'
        degreeFourPlane) hE hS1 hS2 hEN hSE
  · obtain ⟨hv, ⟨e⟩⟩ := hU
    have hmod : StatedClassicalModel Y .PSU 4 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    exact item613_false_of_inner_planes hZ Nat.prime_five le_rfl
      (fun E' U hplane hE' => planeCentralizes_inner_psu hZ (by norm_num) (by norm_num)
        q.prime_p hq2 hmod hplane hE' degreeFourPlane) hE hS1 hS2 hEN hSE
  · obtain ⟨hv, ⟨e⟩⟩ := hA
    have hmod : StatedClassicalModel Y .PSL 4 q.p q.exponent :=
      statedClassicalModel_of_isoLie_A (r := 3) hv e
    exact item613_false_of_inner_planes hZ Nat.prime_five le_rfl
      (fun E' U hplane hE' => planeCentralizes_inner_psl hZ (by norm_num) (by norm_num)
        q.prime_p hq2 hmod hplane hE' degreeFourPlane) hE hS1 hS2 hEN hSE

theorem not_five_cube_dvd_factorial {n : ℕ} (hn : n ≤ 12) : ¬ 5 ^ 3 ∣ Nat.factorial n := by
  interval_cases n <;> decide

theorem p5_item5 {Y : Type} [Group Y] [Finite Y] (h : ThmThreeItem5 Y)
    (h5 : 5 ^ 3 ∣ Nat.card Y) : False := by
  obtain ⟨n, hn5, hn12, ⟨e⟩⟩ := h
  have hX : Nat.card Y = Nat.factorial n / 2 := by
    have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  rw [hX] at h5
  have h2n : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  exact not_five_cube_dvd_factorial hn12 (h5.trans (Nat.div_dvd_of_dvd h2n))

theorem sporadic_cube_thirteen
    {s : SporadicName} (hs : s ∈ sporadicsThm3)
    (h5 : 5 ^ 3 ∣ Nat.card (Carrier s))
    (h13 : 13 ∣ Nat.card (Carrier s)) : s = .Ru ∨ s = .Th := by
  simp only [sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    rw [show Nat.card (Carrier .M11) = _ from CFSG.Sporadic.Mathieu.card_M11] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .M12) = _ from CFSG.Sporadic.Mathieu.card_M12] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .M22) = _ from CFSG.Sporadic.Mathieu.card_M22] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .M23) = _ from CTP.card_M23] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .M24) = _ from CFSG.Sporadic.Mathieu.card_M24] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .J1) = _ from CFSG.Sporadic.J1.card_J1] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .J2) = _ from CFSG.Sporadic.J2.card_J2] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .J3) = _ from CFSG.Sporadic.J3.card_J3] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .J4) = _ from CFSG.Sporadic.J4.card_J4] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .McL) = _ from CFSG.Sporadic.McL.card_McL] at h13
    norm_num at h13
  · exfalso
    rw [show Nat.card (Carrier .Ly) = _ from CFSG.Sporadic.Ly.card_Ly] at h13
    norm_num at h13
  · exfalso
    rw [show Nat.card (Carrier .HS) = _ from CFSG.Sporadic.HS.card_HS] at h13
    norm_num at h13
  · exfalso
    rw [show Nat.card (Carrier .He) = _ from CFSG.Sporadic.He.card_He] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .Suz) = _ from CFSG.Sporadic.Suz.card_Suz] at h5
    norm_num at h5
  · exact Or.inl rfl
  · exfalso
    rw [show Nat.card (Carrier .ONan) = _ from CFSG.Sporadic.ON.card_ON_eq] at h5
    norm_num at h5
  · exfalso
    rw [show Nat.card (Carrier .Co3) = _ from CFSG.Sporadic.Co3.card_Co3] at h13
    norm_num at h13
  · exfalso
    rw [show Nat.card (Carrier .Co2) = _ from CFSG.Sporadic.Co2.card_Co2] at h13
    norm_num at h13
  · exfalso
    rw [show Nat.card (Carrier .HN) = _ from CFSG.Sporadic.HN.card_HN] at h13
    norm_num at h13
  · exact Or.inr rfl

theorem p5_item6
    {Y : Type} [Group Y] [Finite Y] [hs : IsSimpleGroup Y] (h6 : ThmThreeItem6 Y)
    (h5 : 5 ^ 3 ∣ Nat.card Y) (h13 : 13 ∣ Nat.card Y) {E S : Subgroup Y}
    [IsElementaryAbelian 5 E] (hE : 5 ^ 2 ≤ Nat.card E) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hEN : E ≤ Subgroup.normalizer (S : Set Y)) (hSE : ⁅S, E⁆ = S) : False := by
  obtain ⟨s, hsmem, ⟨e⟩⟩ := h6
  have : IsSimpleGroup s.Group := e.symm.isSimpleGroup
  obtain ⟨eC⟩ := nonempty_carrier_mulEquiv_of_mem hsmem
  let eXC : Y ≃* Carrier s := e.trans eC.symm
  rw [Nat.card_congr eXC.toEquiv] at h5 h13
  rcases sporadic_cube_thirteen hsmem h5 h13 with rfl | rfl
  · exact SPOR.item613_false_of_planes Nat.prime_five le_rfl (fun hnab E' U hpl =>
      sporadicPlanesCentralize_Ru Y hs hnab ⟨eXC⟩ _ E' U hpl) hE hS1 hS2 hEN hSE
  · exact SPOR.item613_false_of_planes Nat.prime_five le_rfl (fun hnab E' U hpl =>
      sporadicPlanesCentralize_Th Y hs hnab ⟨eXC⟩ _ E' U hpl) hE hS1 hS2 hEN hSE

theorem p5_simple
    {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] (hlist : TheoremThreeList Y)
    (h5 : 5 ^ 3 ∣ Nat.card Y) (h13 : 13 ∣ Nat.card Y) {E S : Subgroup Y}
    [IsElementaryAbelian 5 E] (hE : 5 ^ 2 ≤ Nat.card E) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hEN : E ≤ Subgroup.normalizer (S : Set Y)) (hSE : ⁅S, E⁆ = S) : ListEvenItem Y := by
  have h25 : 5 ^ 2 ∣ Nat.card Y := (pow_dvd_pow 5 (by norm_num : 2 ≤ 3)).trans h5
  rcases hlist with h | h | h | h | h | h | h | h | h
  · exact (p5_item1 h hS1 hS2 hEN hSE).elim
  · exact (p5_item2 h hE hS1 hS2 hEN hSE).elim
  · exact (p5_item3 h h25).elim
  · exact (p5_item4 h hE hS1 hS2 hEN hSE).elim
  · exact (p5_item5 h h5).elim
  · exact (p5_item6 h h5 h13 hE hS1 hS2 hEN hSE).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end CFSG.RankThree.PartOne.Q1327C
