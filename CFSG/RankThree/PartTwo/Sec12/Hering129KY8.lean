module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HShape
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec12.Hering129GCore
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofSetup

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Gap129ClaimEX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y → Typ129IIIcType L Y →
        ∃ E : Subgroup G, Typ129IIIcE A c Y x E

@[expose] def Gap129ClaimShapeX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∃ Y : Subgroup G, Y ∈ thetaComponentsAt 3 x ∧ ⁅Y, Subgroup.zpowers c⁆ = Y ∧
        resCent K x ≤ Y ∧
        (Typ129I K Y ∨ Typ129II K Y ∨ Typ129IV q Y ∨ Typ129IIIcType L Y)

theorem gap129ClaimShapeX_of (hY : Gap129YShape) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hK : KFacts.KS12NormalizerMoves) (hKK : Gap129KFKStrong) : Gap129ClaimShapeX := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAF : A ∈ partTwoF G := hstd.partTwoF_eq ▸ cfg.mem_E
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcA := hstd.mem_A
  have hc1 := hstd.ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  obtain ⟨hcX, hSX, hXq, hZ2⟩ := hKK G A c L b a K S cfg ⟨q, hq⟩ x hxD hxb
  have hG4x : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    (Proof128.centralizer_setup hstd.toPartTwoStanding hAF hA27 hxA hx1).1
  obtain ⟨Yx, hYx, hXYx⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4x hstd.isE27
    hbA hxA hb1 cfg.hK hXq
  have hAHx : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := fun y hy =>
    mem_normalizer_zpowers_of_commute (hAc y hy x hxA)
  have hAN : A ≤ Subgroup.normalizer (Yx : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hstd.toTheoremFourHyp
      (orderOf_eq_prime hx3 hx1) hYx hA3 hAHx
  have hcnot : c ∉ Sec4.thetaQuotCentralizer Yx :=
    not_mem_thetaQuotCentralizer_of_central_sq hXYx hcX hc3 hc1 hZ2
  have hcomm : ⁅Yx, Subgroup.zpowers c⁆ = Yx :=
    commutator_eq_self_of_not_mem_thetaQuotCentralizer hYx (hAN hcA) hcnot
  have hcore := core129_of h45 hK hstd cfg.list hxA hx1 hYx hcomm
  exact ⟨Yx, hYx, hcomm, hXYx, hY G A c L b a K S cfg q hq x hxD hxb Yx hcore hXYx⟩

theorem gap129ClaimG2M_ofX (hS : Gap129ClaimShapeX) (hE : Gap129ClaimEX) (h45 : Sec4.Item4_5)
    (hK : KFacts.KS12NormalizerMoves) : Gap129ClaimG2M := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb
  obtain ⟨Y, hY, hYc, hXY, hty⟩ := hS G A c L b a K S cfg q hq x hxD hxb
  refine ⟨Y, hY, hYc, ?_⟩
  rcases hty with h1 | h2 | h4 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h4))
  · refine Or.inr (Or.inr (Or.inr (typ129IIIcMinus_iff.mpr ⟨h3, ?_⟩)))
    obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
    have hDA : D129 a b ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
    have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
    have hcore := core129_of h45 hK cfg.std cfg.list (hDA hxD) hx1 hY hYc
    exact hE G A c L b a K S cfg q hq x hxD hxb Y hcore hXY h3

end CFSG.RankThree.PartTwo.Sec12
