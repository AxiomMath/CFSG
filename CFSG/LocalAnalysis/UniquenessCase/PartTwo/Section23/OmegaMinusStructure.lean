module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.NormalizerLeN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.GroupTheory.OffenderCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyResidual
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs3
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

@[expose] def QV (c : Ctx23L D Ch) : Subgroup G :=
  (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)

private theorem sup_le_normalizer_QV (c : Ctx23L D Ch) : c.L ⊔ D.T ≤
    Subgroup.normalizer (c.QV : Set G) := by
  have hH : c.L ⊔ D.T ≤ Subgroup.normalizer ((c.L ⊔ D.T : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    c.L_le_stabTil.trans (stabTil_le_normalizer (⊥ : Subgroup G) c.V)
  have hTV : D.T ≤ Subgroup.normalizer (c.V : Set G) :=
    c.T_le_stabTil.trans (stabTil_le_normalizer (⊥ : Subgroup G) c.V)
  have hLC : c.L ≤ Subgroup.normalizer (Subgroup.centralizer (c.V : Set G) : Set G) :=
    hLV.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.V)
  have hTC : D.T ≤ Subgroup.normalizer (Subgroup.centralizer (c.V : Set G) : Set G) :=
    hTV.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.V)
  have hL : c.L ≤ Subgroup.normalizer (c.QV : Set G) :=
    (le_inf (le_sup_left.trans hH) hLC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hT : D.T ≤ Subgroup.normalizer (c.QV : Set G) :=
    (le_inf (le_sup_right.trans hH) hTC).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact sup_le hL hT

private theorem exists_sylow_of_sup_QV (c : Ctx23L D Ch) :
    ∃ QH : Sylow 2 ↥(c.L ⊔ D.T),
      (QH : Subgroup ↥(c.L ⊔ D.T)) = D.T.subgroupOf (c.L ⊔ D.T) ∧
        c.L.subgroupOf (c.L ⊔ D.T) ⊔ D.T.subgroupOf (c.L ⊔ D.T) = ⊤ := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  have hLH : c.L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hKsup : c.L.subgroupOf H ⊔ D.T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := c.L) (A' := D.T) (B := H) hLH hTH,
      show c.L ⊔ D.T = H from rfl, Subgroup.subgroupOf_self]
  obtain ⟨QH, hQH⟩ := (D.sylowG.of_le hTH le_top).exists_sylow_eq_subgroupOf
  exact ⟨QH, hQH, hKsup⟩

private theorem isPGroup_ker_phiQ (c : Ctx23L D Ch)
    [hK : (c.L.subgroupOf (c.L ⊔ D.T)).Normal]
    (f : ↥c.QV →* (↥(c.L ⊔ D.T) ⧸ c.L.subgroupOf (c.L ⊔ D.T)))
    (hmem : ∀ x : ↥f.ker, ((x : ↥c.QV) : G) ∈ CFSG.Open.pCoreOf 2 c.L) :
    IsPGroup 2 f.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype
  let ψ : ↥f.ker →* ↥(CFSG.Open.pCoreOf 2 c.L) :=
    { toFun := fun x => ⟨((x : ↥c.QV) : G), hmem x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : ((ψ x : ↥(CFSG.Open.pCoreOf 2 c.L)) : G) =
        ((ψ y : ↥(CFSG.Open.pCoreOf 2 c.L)) : G) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  exact IsPGroup.of_injective hL2 ψ hψ

private theorem isPGroup_QV (c : Ctx23L D Ch)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    IsPGroup 2 ↥c.QV := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  have hLH : c.L ≤ H := le_sup_left
  have hQVH : c.QV ≤ H := inf_le_left
  haveI hKnormal : (c.L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2
      (sup_le Subgroup.le_normalizer c.hL.1.1)
  obtain ⟨QH, hQHcoe, hKsup⟩ := c.exists_sylow_of_sup_QV
  have hT2 : IsPGroup 2 (D.T.subgroupOf H) := by
    rw [← hQHcoe]
    exact QH.isPGroup'
  have hquot : IsPGroup 2 (↥H ⧸ c.L.subgroupOf H) :=
    CFSG.QuasithinUnique.Setup.Family.isPGroup_quotient_of_sup_eq_top
      (c.L.subgroupOf H) (D.T.subgroupOf H) hT2 hKsup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype
  let f : ↥c.QV →* (↥H ⧸ c.L.subgroupOf H) :=
    (QuotientGroup.mk' (c.L.subgroupOf H)).comp (Subgroup.inclusion hQVH)
  have hfker : IsPGroup 2 f.ker :=
    isPGroup_ker_phiQ c f (by
      intro x
      have hxL : ((x : ↥c.QV) : G) ∈ c.L := by
        have h1 : f (x : ↥c.QV) = 1 := x.2
        exact Subgroup.mem_subgroupOf.mp
          ((QuotientGroup.eq_one_iff (N := c.L.subgroupOf H) _).1 h1)
      have hxQV : ((x : ↥c.QV) : G) ∈ c.QV := (x : ↥c.QV).2
      exact hCLV (Subgroup.mem_inf.mpr
        ⟨hxL, (Subgroup.mem_inf.mp hxQV).2⟩))
  have hquotTop : IsPGroup 2 (⊤ : Subgroup (↥H ⧸ c.L.subgroupOf H)) :=
    hquot.of_equiv (Subgroup.topEquiv (G := ↥H ⧸ c.L.subgroupOf H)).symm
  exact CFSG.Quasithin.H13.S126P31.isPGroup_of_ker_range f hfker
    (hquotTop.to_le le_top)

theorem QV_le_T (c : Ctx23L D Ch)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    c.QV ≤ D.T := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  have hQVH : c.QV ≤ H := inf_le_left
  obtain ⟨QH, hQHcoe, -⟩ := c.exists_sylow_of_sup_QV
  have hQV2H : IsPGroup 2 (c.QV.subgroupOf H) :=
    (c.isPGroup_QV hCLV).of_equiv (Subgroup.subgroupOfEquivOfLe hQVH).symm
  haveI hQVnormal : (c.QV.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQVH).2 (c.sup_le_normalizer_QV)
  have hle := IsPGroup.le_sylow_of_normal hQV2H QH
  rw [hQHcoe] at hle
  intro x hx
  have hxH : (⟨x, hQVH hx⟩ : ↥H) ∈ c.QV.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hle hxH)

theorem le_normalizer_QV (c : Ctx23L D Ch) :
    c.L ⊔ D.T ≤ Subgroup.normalizer (c.QV : Set G) :=
  c.sup_le_normalizer_QV

theorem fixV_sylowStar_eq_Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map (c.H hV).subtype) =
      c.Ztil hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have h := c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  ext z
  constructor
  · intro hz
    rw [← h, FixedPoints.mem_subgroup]
    intro s
    have hzs := hz (s : ↥(c.H hV)) (Subgroup.mem_map_of_mem _ s.2)
    exact hzs
  · intro hz
    rw [CFSG.Quasithin.mem_fixV]
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hzS : z ∈ fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) := h ▸ hz
    have hzs := hzS ⟨s, hs⟩
    exact hzs

theorem phiT_eq_one_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (t : ↥D.T) :
    c.phiT hV t = 1 ↔ (t : G) ∈ Subgroup.centralizer (c.V : Set G) := by
  change actTil (⊥ : Subgroup G) c.V hV ⟨t, c.T_le_stabTil t.2⟩ = 1 ↔ _
  rw [actTil_eq_one_iff]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' := h v hv
    rw [Subgroup.mem_bot] at hv'
    have h2 : (t : G) * v * (t : G)⁻¹ = v := mul_inv_eq_one.mp hv'
    have h3 := congrArg (· * (t : G)) h2
    simpa [mul_assoc] using h3.symm
  · intro h v hv
    rw [Subgroup.mem_bot]
    have hc := (Subgroup.mem_centralizer_iff.mp h) v hv
    rw [← hc]
    group

theorem map_phiT_eq_barSub (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {A : Subgroup G} (hAT : A ≤ D.T) :
    (A.subgroupOf D.T).map (c.phiT hV) = barSub (⊥ : Subgroup G) c.V hV A := by
  have hsub : (A.subgroupOf D.T).map (Subgroup.inclusion c.T_le_stabTil) =
      A.subgroupOf (stabTil (⊥ : Subgroup G) c.V) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy)
    · intro hx
      have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
      let y : ↥(A.subgroupOf D.T) := ⟨⟨(x : G), hAT hxA⟩, hxA⟩
      exact ⟨y, y.2, rfl⟩
  have hcomp : c.phiT hV =
      (actTil (⊥ : Subgroup G) c.V hV).comp (Subgroup.inclusion c.T_le_stabTil) := rfl
  rw [hcomp]
  calc (A.subgroupOf D.T).map
        ((actTil (⊥ : Subgroup G) c.V hV).comp (Subgroup.inclusion c.T_le_stabTil))
      = ((A.subgroupOf D.T).map (Subgroup.inclusion c.T_le_stabTil)).map
          (actTil (⊥ : Subgroup G) c.V hV) := by
        rw [Subgroup.map_map]
    _ = barSub (⊥ : Subgroup G) c.V hV A := by rw [hsub]; rfl

theorem omegaMinusFrame_of
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) :
    OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z) (c.sylowStar hV) (c.Tstar hV) := by
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inl ⟨isOmegaMinus_of_natOmegaMinus_four hNat, hNat⟩)
  refine ⟨hn2, hNat, c.Tstar_le_normalizer hV, c.isPGroup_Tstar hV,
    c.sylowStar_le_Tstar hV, ?_⟩
  intro t ht w hw
  have hwZ : w ∈ c.Ztil hV := by
    have hfix := c.fixV_sylowStar_eq_Ztil hV hA hnat h4 h1930
    rw [hfix] at hw
    exact hw
  obtain ⟨t', rfl⟩ := (c.mem_Tstar_iff hV t).1 ht
  rw [Ctx23L.Ztil, mem_imgTil] at hwZ
  obtain ⟨v, hvZ, rfl⟩ := hwZ
  rw [show c.phiT hV t' =
      actTil (⊥ : Subgroup G) c.V hV ⟨t', c.T_le_stabTil t'.2⟩ from rfl,
    actTil_mk, mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val]
  have hcent : (t' : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T t'.2
  have hcomm : (t' : G) * v.val * (t' : G)⁻¹ = v.val := by
    have hc := (Subgroup.mem_centralizer_iff.mp hcent) v.val hvZ
    calc (t' : G) * v.val * (t' : G)⁻¹ = v.val * (t' : G) * (t' : G)⁻¹ := by rw [← hc]
      _ = v.val := by group
  rw [hcomm, mul_inv_cancel]

private theorem card_map_phiT_mul_card_inf (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {A : Subgroup G} (hAT : A ≤ D.T) :
    Nat.card ↥((A.subgroupOf D.T).map (c.phiT hV)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer (c.V : Set G)) = Nat.card A := by
  let e := TwelveShort.mkTilEquiv c.V hV
  have hAN : A ≤ Subgroup.normalizer (c.V : Set G) :=
    hAT.trans (c.T_le_stabTil.trans (stabTil_le_normalizer (⊥ : Subgroup G) c.V))
  have hbar : (A.subgroupOf D.T).map (c.phiT hV) = barSub (⊥ : Subgroup G) c.V hV A :=
    c.map_phiT_eq_barSub hV hAT
  rw [hbar, CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.barSub_bot_eq_map_autI
      c.V hV A,
    Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective]
  exact CFSG.Quasithin.card_autI_mul_card_inf hV hAN

private theorem card_fixV_phiT (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {A : Subgroup G} (hAT : A ≤ D.T) :
    Nat.card ↥(CFSG.Quasithin.fixV ((A.subgroupOf D.T).map (c.phiT hV))) =
      Nat.card ↥(c.V ⊓ Subgroup.centralizer (A : Set G)) := by
  let e := TwelveShort.mkTilEquiv c.V hV
  have hAN : A ≤ Subgroup.normalizer (c.V : Set G) :=
    hAT.trans (c.T_le_stabTil.trans (stabTil_le_normalizer (⊥ : Subgroup G) c.V))
  have hbar : (A.subgroupOf D.T).map (c.phiT hV) = barSub (⊥ : Subgroup G) c.V hV A :=
    c.map_phiT_eq_barSub hV hAT
  rw [hbar, CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.barSub_bot_eq_map_autI
      c.V hV A,
    CFSG.Quasithin.fixV_map_congr_equiv e,
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact CFSG.Quasithin.card_fixV_autI hV hAN

theorem card_W_le_of_pRank (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D) {A : Subgroup G}
    (hAel : IsElemAbelian 2 A) (hAT : A ≤ D.T) {i : ℕ}
    (hrk : CFSG.Open.pRank 2 D.T ≤ CFSG.Open.pRank 2 A + i) :
    Nat.card (c.W hV) ≤ 2 ^ i *
      (Nat.card ↥((A.subgroupOf D.T).map (c.phiT hV)) *
        Nat.card ↥(CFSG.Quasithin.fixV ((A.subgroupOf D.T).map (c.phiT hV)))) := by
  let e := TwelveShort.mkTilEquiv c.V hV
  have hAstar := c.card_map_phiT_mul_card_inf hV hAT
  have hfixcard := c.card_fixV_phiT hV hAT
  have hcardW : Nat.card (c.W hV) = Nat.card c.V :=
    (Nat.card_congr e.toEquiv).symm
  have h := CFSG.GroupTheory.card_mul_card_inf_centralizer_le hAel hV hAT
    (c.V_le_T h4 h1930) hrk
  rw [← hAstar] at h
  have hKpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (c.V : Set G)) := Nat.card_pos
  have h' : Nat.card c.V ≤ 2 ^ i *
      (Nat.card ↥((A.subgroupOf D.T).map (c.phiT hV)) *
        Nat.card ↥(c.V ⊓ Subgroup.centralizer (A : Set G))) := by
    refine Nat.le_of_mul_le_mul_right ?_ hKpos
    calc Nat.card c.V * Nat.card ↥(A ⊓ Subgroup.centralizer (c.V : Set G))
        ≤ 2 ^ i * (Nat.card ↥((A.subgroupOf D.T).map (c.phiT hV)) *
            Nat.card ↥(A ⊓ Subgroup.centralizer (c.V : Set G)) *
              Nat.card ↥(c.V ⊓ Subgroup.centralizer (A : Set G))) := h
      _ = (2 ^ i * (Nat.card ↥((A.subgroupOf D.T).map (c.phiT hV)) *
            Nat.card ↥(c.V ⊓ Subgroup.centralizer (A : Set G)))) *
              Nat.card ↥(A ⊓ Subgroup.centralizer (c.V : Set G)) := by ring
  simpa [hcardW, hfixcard] using h'

private theorem pRank_map_subtype_eq_of_family_zero {A : Subgroup ↥D.T}
    (hAfam : A ∈ CFSG.higherElemThompsonFamily ↥D.T 0) :
    CFSG.Open.pRank 2 (A.map D.T.subtype) = CFSG.Open.pRank 2 D.T := by
  have hAfam' := (CFSG.mem_higherElemThompsonFamily_iff 0 A).mp hAfam
  have hAelT : IsElemAbelian 2 A :=
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr hAfam'.1
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 A :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hAelT
  have hfamcard : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T := by
    rw [hAfam'.2, Nat.sub_zero, CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
  have hrankA : CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 D.T := by
    have h : (2 : ℕ) ^ CFSG.Open.pRank 2 A = 2 ^ CFSG.Open.pRank 2 D.T := by
      rw [← hcardA, hfamcard]
    exact Nat.pow_right_injective (by norm_num : (1 : ℕ) < 2) h
  have eA := Subgroup.equivMapOfInjective A D.T.subtype D.T.subtype_injective
  calc CFSG.Open.pRank 2 (A.map D.T.subtype) =
        CFSG.Open.pRank 2 (⊤ : Subgroup ↥(A.map D.T.subtype)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
    _ = CFSG.Open.pRank 2 (⊤ : Subgroup ↥A) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eA.symm
    _ = CFSG.Open.pRank 2 A := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup A).symm
    _ = CFSG.Open.pRank 2 D.T := hrankA

private theorem max_family_image_le_centralizer
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    {A : Subgroup ↥D.T} (hAfam : A ∈ CFSG.higherElemThompsonFamily ↥D.T 0) :
    A.map D.T.subtype ≤ Subgroup.centralizer (c.V : Set G) := by
  have hframe := c.omegaMinusFrame_of hV hA h4 h1930 hn2 hNat
  have hAfam' := (CFSG.mem_higherElemThompsonFamily_iff 0 A).mp hAfam
  have hAelT : IsElemAbelian 2 A :=
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr hAfam'.1
  let AG : Subgroup G := A.map D.T.subtype
  have hAGel : IsElemAbelian 2 AG := hAelT.map D.T.subtype
  have hAGT : AG ≤ D.T := Subgroup.map_subtype_le A
  have hrankAG : CFSG.Open.pRank 2 AG = CFSG.Open.pRank 2 D.T :=
    pRank_map_subtype_eq_of_family_zero hAfam
  have hrk : CFSG.Open.pRank 2 D.T ≤ CFSG.Open.pRank 2 AG + 0 := by
    rw [hrankAG]; omega
  have hWle := c.card_W_le_of_pRank hV h4 h1930 hAGel hAGT (i := 0) hrk
  have hWle' : Nat.card (c.W hV) ≤
      Nat.card ↥((AG.subgroupOf D.T).map (c.phiT hV)) *
        Nat.card ↥(CFSG.Quasithin.fixV ((AG.subgroupOf D.T).map (c.phiT hV))) := by
    simpa using hWle
  have hEel : IsElemAbelian 2 ((AG.subgroupOf D.T).map (c.phiT hV)) :=
    (CFSG.Open.IsElemAbelian.subgroupOf hAGel D.T).map (c.phiT hV)
  have hEle : (AG.subgroupOf D.T).map (c.phiT hV) ≤ c.Tstar hV := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hEbot := hKA (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) (c.sylowStar hV)
    (c.Tstar hV) hframe ((AG.subgroupOf D.T).map (c.phiT hV)) hEle hEel hWle'
  intro x hx
  have hxT : x ∈ D.T := hAGT hx
  have hxE : (c.phiT hV ⟨x, hxT⟩) ∈ (AG.subgroupOf D.T).map (c.phiT hV) := by
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hxT⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [hEbot, Subgroup.mem_bot] at hxE
  exact (c.phiT_eq_one_iff hV ⟨x, hxT⟩).1 hxE

private theorem jOf_le_QV (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA) :
    F12.jOf D.T ≤ c.QV := by
  have hJeq : F12.jOf D.T = (CFSG.higherElemThompson ↥D.T 0).map D.T.subtype := by
    rw [F12.jOf, CFSG.inSubgroup, ← CFSG.higherElemThompson_zero]
  have hJleC : F12.jOf D.T ≤ Subgroup.centralizer (c.V : Set G) := by
    rw [hJeq, CFSG.higherElemThompson]
    refine (Subgroup.map_le_iff_le_comap).mpr ?_
    rw [Subgroup.comap_subtype]
    exact sSup_le fun A hAfam =>
      (Subgroup.map_le_iff_le_comap).mp
        (max_family_image_le_centralizer c hV hA h4 h1930 hn2 hNat hKA hAfam)
  have hJleT : F12.jOf D.T ≤ D.T := by
    rw [hJeq]
    exact Subgroup.map_subtype_le _
  exact le_inf (hJleT.trans le_sup_right) hJleC

theorem V_le_jOf (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA) :
    c.V ≤ F12.jOf D.T := by
  have hJeq : F12.jOf D.T = (CFSG.higherElemThompson ↥D.T 0).map D.T.subtype := by
    rw [F12.jOf, CFSG.inSubgroup, ← CFSG.higherElemThompson_zero]
  obtain ⟨A0, hA0⟩ := CFSG.Quasithin.SteinbergBK.exists_mem_higherElemThompsonFamily
    (S := ↥D.T) 0
  let A0G : Subgroup G := A0.map D.T.subtype
  have hA0C : A0G ≤ Subgroup.centralizer (c.V : Set G) :=
    max_family_image_le_centralizer c hV hA h4 h1930 hn2 hNat hKA hA0
  have hA0fam := (CFSG.mem_higherElemThompsonFamily_iff 0 A0).mp hA0
  have hA0elT : IsElemAbelian 2 A0 :=
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr hA0fam.1
  have hA0el : IsElemAbelian 2 A0G := hA0elT.map D.T.subtype
  have hA0rank : CFSG.Open.pRank 2 A0G = CFSG.Open.pRank 2 D.T :=
    pRank_map_subtype_eq_of_family_zero hA0
  have hcomm : ∀ v ∈ c.V, ∀ a ∈ A0G, v * a = a * v := by
    intro v hv a ha
    exact Subgroup.mem_centralizer_iff.mp (hA0C ha) v hv
  have hsupE : IsElemAbelian 2 (c.V ⊔ A0G) := hV.sup_of_commute hA0el hcomm
  have hsupT : c.V ⊔ A0G ≤ D.T := sup_le (c.V_le_T h4 h1930) (Subgroup.map_subtype_le A0)
  have hcardSup : Nat.card ↥(c.V ⊔ A0G) ≤ Nat.card A0G := by
    have h1 : Nat.card ↥(c.V ⊔ A0G) = 2 ^ CFSG.Open.pRank 2 (c.V ⊔ A0G) :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hsupE
    have h2 : CFSG.Open.pRank 2 (c.V ⊔ A0G) ≤ CFSG.Open.pRank 2 D.T :=
      CFSG.SectionRank.pRank_mono (by norm_num) hsupT
    have h3 : Nat.card A0G = 2 ^ CFSG.Open.pRank 2 D.T := by
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hA0el, hA0rank]
    rw [h1, h3]
    exact Nat.pow_le_pow_right (by norm_num) h2
  have hA0le : A0G ≤ c.V ⊔ A0G := le_sup_right
  have hEq : A0G = c.V ⊔ A0G := Subgroup.eq_of_le_of_card_ge hA0le hcardSup
  have hVleA0 : c.V ≤ A0G := by
    rw [hEq]
    exact le_sup_left
  have hA0leJ : A0G ≤ F12.jOf D.T := by
    rw [hJeq]
    exact Subgroup.map_mono (le_sSup hA0)
  exact hVleA0.trans hA0leJ

private theorem normalizer_jOf_le_N (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hVleJ : c.V ≤ F12.jOf D.T) (hJleQV : F12.jOf D.T ≤ c.QV) :
    Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N := by
  have hJeq : F12.jOf D.T = (CFSG.higherElemThompson ↥D.T 0).map D.T.subtype := by
    rw [F12.jOf, CFSG.inSubgroup, ← CFSG.higherElemThompson_zero]
  have hJleT : F12.jOf D.T ≤ D.T := by
    rw [hJeq]
    exact Subgroup.map_subtype_le _
  have hJne : F12.jOf D.T ≠ ⊥ := by
    intro hbot
    exact c.V_ne_bot h4 h1930 (le_bot_iff.mp (hVleJ.trans (le_of_eq hbot)))
  have hJ2 : IsPGroup 2 (F12.jOf D.T) := D.sylowG.isPGroup.to_le hJleT
  have hJthomp : F12.jOf D.T = CFSG.Quasithin.thompsonJ D.T := by
    rw [F12.jOf, CFSG.inSubgroup,
      CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]
  have hQVleT : c.QV ≤ D.T := c.QV_le_T hCLV
  have hJQV : CFSG.Quasithin.thompsonJ c.QV = CFSG.Quasithin.thompsonJ D.T := by
    have hJ' : CFSG.Quasithin.thompsonJ D.T ≤ c.QV := by
      rw [← hJthomp]
      exact hJleQV
    exact (CFSG.Quasithin.thompsonJ_eq_of_le (S := D.T) (R := c.QV) hJ' hQVleT).symm
  have hNT : Subgroup.normalizer (c.QV : Set G) ≤
      Subgroup.normalizer (F12.jOf D.T : Set G) := by
    rw [hJthomp]
    refine (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ c.QV).trans ?_
    exact le_of_eq (by rw [hJQV])
  have hNT' : Subgroup.normalizer (D.T : Set G) ≤
      Subgroup.normalizer (F12.jOf D.T : Set G) := by
    rw [hJthomp]
    exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ D.T
  have hLT : c.L ⊔ D.T ≤ Subgroup.normalizer (F12.jOf D.T : Set G) :=
    sup_le ((le_sup_left.trans c.le_normalizer_QV).trans hNT)
      ((le_sup_right.trans c.le_normalizer_QV).trans hNT)
  exact c.normalizer_le_N_of_isPGroup hJne hJ2 hLT

theorem jZero_facts (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    c.V ≤ F12.jOf D.T ∧ F12.jOf D.T ≤ c.QV ∧
      Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N := by
  have hJleQV := c.jOf_le_QV hV hA h4 h1930 hn2 hNat hKA
  have hVleJ := c.V_le_jOf hV hA h4 h1930 hn2 hNat hKA
  exact ⟨hVleJ, hJleQV,
    c.normalizer_jOf_le_N hV h4 h1930 hCLV hVleJ hJleQV⟩

theorem V_le_jOne (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    c.V ≤ jOneOf D.T := by
  have hVJ := (c.jZero_facts hV hA h4 h1930 hn2 hNat hKA hCLV).1
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have h1 : CFSG.Open.pRank 2 D.Z ≤ CFSG.Open.pRank 2 c.V :=
    CFSG.SectionRank.pRank_mono (by norm_num) hZV
  have h2 : CFSG.Open.pRank 2 c.V ≤ CFSG.Open.pRank 2 D.T :=
    CFSG.SectionRank.pRank_mono (by norm_num) (c.V_le_T h4 h1930)
  have hm : 1 < CFSG.Open.pRank 2 D.T := by omega
  have hm' : 1 < CFSG.pRank 2 ↥D.T := by
    rwa [CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
  have hchain : F12.jOf D.T ≤ jOneOf D.T := by
    have hJeq : F12.jOf D.T = (CFSG.higherElemThompson ↥D.T 0).map D.T.subtype := by
      rw [F12.jOf, CFSG.inSubgroup, ← CFSG.higherElemThompson_zero]
    rw [hJeq, jOneOf, CFSG.inSubgroup]
    refine Subgroup.map_mono ?_
    rw [CFSG.higherElemThompson]
    refine sSup_le fun A hA => ?_
    have hAfam := (CFSG.mem_higherElemThompsonFamily_iff 0 A).mp hA
    haveI : CFSG.IsElementaryAbelian 2 ↥A := hAfam.1
    have hrankA : CFSG.pRank 2 ↥A = CFSG.pRank 2 ↥D.T := by
      rw [CFSG.pRank_eq_of_card_eq_pow (p := 2) one_lt_two hAfam.2, Nat.sub_zero]
    exact CFSG.Quasithin.SteinbergBK.le_higherElemThompson_of_le_pRank hm' hAfam.1
      (by rw [hrankA]; exact Nat.sub_le _ _)
  exact hVJ.trans hchain

theorem Z_le_zOne (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    D.Z ≤ zOneOf D.T := by
  have hVJ1 : c.V ≤ jOneOf D.T :=
    c.V_le_jOne hV hA h4 h1930 hn2 hNat hKA hCLV
  intro z hz
  have hzV : z ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hz
  have hzT : z ∈ D.T := c.V_le_T h4 h1930 hzV
  have hzJ1 : (⟨z, hzT⟩ : ↥D.T) ∈ CFSG.higherElemThompson ↥D.T 1 := by
    have hmem : z ∈ jOneOf D.T := hVJ1 hzV
    rw [jOneOf, CFSG.inSubgroup] at hmem
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hmem
    have hy' : y = (⟨z, hzT⟩ : ↥D.T) := Subtype.ext hyz
    rwa [hy'] at hy
  have hzZ : z ∈ Subgroup.centralizer (D.T : Set G) :=
    (Subgroup.mem_inf.mp
      (CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T hz)).2
  have hzC : ∀ y ∈ CFSG.higherElemThompson ↥D.T 1,
      y * (⟨z, hzT⟩ : ↥D.T) = (⟨z, hzT⟩ : ↥D.T) * y := by
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzZ (y : G) y.2
  have hz2 : (⟨z, hzT⟩ : ↥D.T) ^ 2 = 1 := by
    apply Subtype.ext
    have h : z ^ 2 = 1 := (c.isElemAbelian_Z h4 h1930).2 z hz
    simpa using h
  have hzO : (⟨z, hzT⟩ : ↥D.T) ∈
      CFSG.omegaOneCenter (CFSG.higherElemThompson ↥D.T 1) :=
    (CFSG.Quasithin.SteinbergBK.mem_omegaOneCenter_iff _ _).mpr ⟨hzJ1, hzC, hz2⟩
  rw [zOneOf]
  change z ∈ (CFSG.higherElemThompsonOmega ↥D.T 1).map D.T.subtype
  exact Subgroup.mem_map.mpr ⟨⟨z, hzT⟩, hzO, rfl⟩

theorem pRank_map_subtype_eq_of_family_one {A : Subgroup ↥D.T}
    (hAfam : A ∈ CFSG.higherElemThompsonFamily ↥D.T 1) :
    CFSG.Open.pRank 2 (A.map D.T.subtype) = CFSG.Open.pRank 2 D.T - 1 := by
  have hAfam' := (CFSG.mem_higherElemThompsonFamily_iff 1 A).mp hAfam
  have hAelT : IsElemAbelian 2 A :=
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr hAfam'.1
  have hfamcard : Nat.card A = 2 ^ (CFSG.Open.pRank 2 D.T - 1) := by
    rw [hAfam'.2, CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 A :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hAelT
  have hrankA : CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 D.T - 1 := by
    have h : (2 : ℕ) ^ CFSG.Open.pRank 2 A = 2 ^ (CFSG.Open.pRank 2 D.T - 1) := by
      rw [← hcardA, hfamcard]
    exact Nat.pow_right_injective (by norm_num : (1 : ℕ) < 2) h
  have eA := Subgroup.equivMapOfInjective A D.T.subtype D.T.subtype_injective
  calc CFSG.Open.pRank 2 (A.map D.T.subtype) =
        CFSG.Open.pRank 2 (⊤ : Subgroup ↥(A.map D.T.subtype)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
    _ = CFSG.Open.pRank 2 (⊤ : Subgroup ↥A) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eA.symm
    _ = CFSG.Open.pRank 2 A := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup A).symm
    _ = CFSG.Open.pRank 2 D.T - 1 := hrankA

theorem exists_family_one_not_le_centralizer (c : Ctx23L D Ch)
    (hnot : ¬ S23_23OmegaCaseA c) :
    ∃ A ∈ CFSG.higherElemThompsonFamily ↥D.T 1,
      ¬ A ≤ (Subgroup.centralizer (c.V : Set G)).subgroupOf D.T := by
  have hnot' : ¬ (CFSG.higherElemThompson ↥D.T 1).map D.T.subtype ≤
      Subgroup.centralizer (c.V : Set G) := by
    intro hle
    exact hnot hle
  have hnotfam : ¬ CFSG.higherElemThompson ↥D.T 1 ≤
      (Subgroup.centralizer (c.V : Set G)).subgroupOf D.T := by
    intro hle
    apply hnot'
    rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
    exact hle
  rw [CFSG.higherElemThompson] at hnotfam
  by_contra h
  apply hnotfam
  exact sSup_le fun A hA => by
    by_contra hA'
    exact h ⟨A, hA, hA'⟩

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
