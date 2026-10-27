module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundShape
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SzJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact31Holds
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Component
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

theorem K14_5SmallFor.mono {S₁ S₂ : ∀ (L : Type) [Group L], ℕ → Prop}
    (h : ∀ (L : Type) [Group L] (e : ℕ), CFSG.Open.IsQuasisimple L → S₁ L e → S₂ L e)
    (h₂ : K14_5SmallFor S₂) : K14_5SmallFor S₁ := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS
  exact h₂ I hI X L P e n hLX hLn hq hirr (h _ e hq hS)

variable {I : Type} [CommGroup I]

theorem o2Trivial_of_isIrrOn [Finite I] (hI : ∀ w : I, w ^ 2 = 1) {L : Subgroup (MulAut I)}
    (hirr : IsIrrOn L ⊤ ⊥) : O2Trivial L := by
  intro P hPL hPn hP2
  obtain ⟨hlt, -, -, hJ⟩ := hirr
  have : Nontrivial I := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨v, 1, fun h => hv (h ▸ Subgroup.one_mem _)⟩⟩
  have hconj := (Subgroup.normal_subgroupOf_iff hPL).mp hPn
  have hst : StableUnder L (fixV P) := by
    intro l hl v hv p hp
    have h1 : l⁻¹ * p * l⁻¹⁻¹ ∈ P := hconj p l⁻¹ hp (L.inv_mem hl)
    rw [inv_inv] at h1
    have h2 := hv _ h1
    calc p (l v) = (l * l⁻¹) (p (l v)) := by rw [mul_inv_cancel]; rfl
      _ = l ((l⁻¹ * p * l) v) := rfl
      _ = l v := by rw [h2]
  rcases hJ (fixV P) hst bot_le le_top with h | h
  · exact absurd h (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.fixV_ne_bot_of_isPGroup' hI hP2)
  · rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    ext v
    exact (show v ∈ fixV P from h ▸ Subgroup.mem_top v) p hp

theorem eq_of_parabolic_of_rankOne [Finite I] {L P : Subgroup (MulAut I)} {e : ℕ}
    (hO2 : O2Trivial L) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hshape : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) : P = L := by
  obtain ⟨S, hS⟩ := hpar
  set T : Subgroup (MulAut I) := (S : Subgroup ↥L).map L.subtype with hT
  have hTL : T ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTP : T ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hS (Subgroup.le_normalizer hx)
  have hTsyl : IsSylowIn 2 T L := by
    refine ⟨hTL, S.isPGroup'.map L.subtype, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hrel : T.relIndex L = (S : Subgroup ↥L).index := by
      rw [Subgroup.relIndex, hT,
        show ((S : Subgroup ↥L).map L.subtype).subgroupOf L = S from
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    rw [hrel]
    exact S.not_dvd_index
  refine eq_of_rankOne hO2 ⟨le_rfl, CFSG.Open.IsSubnormal.refl L, hq⟩ hTsyl hshape hPL hinf ?_
  intro x hx
  exact Subgroup.le_normalizer (hTP hx.1)

@[expose] noncomputable def bar2EquivOfPCore {G : Type} [Group G] {L : Subgroup G}
    (h : CFSG.pCore 2 ↥L = ⊥) : Bar2 L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem nParam_eq_of_isSz {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {e n : ℕ} (hO : CFSG.pCore 2 ↥L = ⊥) (hq : CFSG.Open.IsQuasisimple ↥L)
    (he : IsSz ↥L e) (hn : NParam L n) : n = e := by
  let φ := bar2EquivOfPCore hO
  have hq' : CFSG.Open.IsQuasisimple (Bar2 L) := CFSG.Open.IsQuasisimple.of_mulEquiv φ hq
  have he' : IsSz (Bar2 L) e := LieModel.of_mulEquiv φ.symm he
  have h3 := CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 he'
  rcases nParamSingle_of_nParam_of_isQuasisimple hn hq' with hSz | hL2 | hSU3 | hSL3 | hSp4
  · have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hSz).2.1
    have he1 : 1 ≤ e := (CFSG.Blueprint.LieModel.admissible he').2.1
    have p1 := CFSG.Timmesfeld.Orders.profile_ordSuzuki hn1
    have p2 := CFSG.Timmesfeld.Orders.profile_ordSuzuki he1
    rw [← CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 hSz] at p1
    rw [← CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 he'] at p2
    have := (p1.transfer p2).1
    omega
  · exact absurd (three_dvd_card_of_isL2 hL2) h3
  · exfalso
    apply h3
    have h3U : 3 ∣ Nat.card (Bar2 L ⧸ center (Bar2 L)) := by
      rw [show Nat.card (Bar2 L ⧸ center (Bar2 L)) = ordTwistedA 2 (2 ^ n) from by
        simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSU3.2.card_eq_lieOrd (by norm_num)]
      exact uc22p21k_three_dvd_ordTwistedA_two n
    exact h3U.trans (Subgroup.card_quotient_dvd_card _)
  · exact absurd hSL3 (not_isSL3_of_isSz he')
  · exact absurd he' (not_isSz_of_isSp4 hSp4)

theorem isSU3_of_mulEquiv {A B : Type} [Group A] [Group B] (φ : A ≃* B) {e : ℕ} (h : IsSU3 A e) :
    IsSU3 B e :=
  ⟨CFSG.Open.IsQuasisimple.of_mulEquiv φ.symm h.1,
    LieModel.of_mulEquiv (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)) h.2⟩

theorem center_eq_bot_of_isQuasisimple {A : Type} [Group A] [IsSimpleGroup A]
    (hq : CFSG.Open.IsQuasisimple A) : center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have := hq.2.toNontrivial
    have : Subsingleton (A ⧸ center A) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_nontrivial (A ⧸ center A) ‹_›

theorem isSU3_of_isU3 {A : Type} [Group A] {e : ℕ} (hq : CFSG.Open.IsQuasisimple A)
    (h : IsU3 A e) : IsSU3 A e := by
  have := uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) h
  have hZ := center_eq_bot_of_isQuasisimple hq
  exact ⟨hq, LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h⟩

theorem nParam_eq_of_isSU3 {G : Type} [Group G] [Finite G] {L : Subgroup G} {e n : ℕ}
    (hO : CFSG.pCore 2 ↥L = ⊥) (he : IsSU3 ↥L e) (hn : NParam L n) : n = e := by
  let φ := bar2EquivOfPCore hO
  have he' : IsSU3 (Bar2 L) e := isSU3_of_mulEquiv φ.symm he
  have hcU : ∀ {A : Type} [Group A] {a : ℕ}, IsU3 A a → Nat.card A = ordTwistedA 2 (2 ^ a) :=
    fun h => by simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have h3 : 3 ∣ Nat.card (Bar2 L) := by
    have h3U : 3 ∣ Nat.card (Bar2 L ⧸ center (Bar2 L)) := by
      rw [hcU he'.2]
      exact uc22p21k_three_dvd_ordTwistedA_two e
    exact h3U.trans (Subgroup.card_quotient_dvd_card _)
  rcases nParamSingle_of_nParam_of_isQuasisimple hn he'.1 with hSz | hL2 | hSU3 | hSL3 | hSp4
  · exact absurd h3 (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
  · have := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
    have hZ := center_eq_bot_of_isQuasisimple he'.1
    have hU : IsU3 (Bar2 L) e := LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) he'.2
    exact absurd hL2 (not_isL2_of_isU3 hU)
  · have hn1 : 1 ≤ n := hSU3.2.admissible.2.1
    have he1 : 1 ≤ e := he'.2.admissible.2.1
    have p1 := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) le_rfl hn1
    have p2 := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) le_rfl he1
    rw [← hcU hSU3.2] at p1
    rw [← hcU he'.2] at p2
    have := (p1.transfer p2).1
    norm_num at this
    omega
  · exact absurd hSL3 (not_isSL3_of_isSU3 he')
  · exact absurd hSp4 (not_isSp4_of_isSU3 he')

theorem lgConj_subgroupOf_eq {X L : Subgroup (MulAut I)} (hLn : (L.subgroupOf X).Normal) :
    UC22.Ext.lgConj (L.subgroupOf X) = L.subgroupOf X := by
  unfold UC22.Ext.lgConj
  simp only [map_conj_subgroupOf_eq hLn, iSup_const]

theorem k14_5SmallFor_sz :
    K14_5SmallFor fun L _ e => IsSz L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  exfalso
  have hO2 := o2Trivial_of_isIrrOn hI hirr
  have hO := CFSG.GroupTheory.pCore_two_eq_bot_of_o2Trivial hO2
  obtain rfl := (eq_of_parabolic_of_rankOne hO2 hq (Or.inr (Or.inl hS)) hPL hpar hinf).symm
  rw [hinf_eq_self hq] at hN
  obtain rfl := nParam_eq_of_isSz hO hq hS hN
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary
    (V := I) fun v => by rw [← pow_two]; exact hI v
  have h147 := UC22.Ext.k147SzJ1_holds ↥X W (subRep θ X) (subRep_injective θ X)
    (subRep_isIrreducible θ hLX hirr) (L.subgroupOf X) (isComponentOf_subgroupOf hLX hLn hq) n
    ⟨Or.inl ⟨hn, LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm hS⟩,
      by rw [numConj_subgroupOf_eq_one hLn]; norm_num⟩
  rw [mGV_subRep] at h147
  omega

theorem k14_5SmallFor_su3 :
    K14_5SmallFor fun L _ e => IsSU3 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  exfalso
  have hO2 := o2Trivial_of_isIrrOn hI hirr
  have hO := CFSG.GroupTheory.pCore_two_eq_bot_of_o2Trivial hO2
  obtain rfl := (eq_of_parabolic_of_rankOne hO2 hq (Or.inr (Or.inr (Or.inr hS))) hPL hpar
    hinf).symm
  rw [hinf_eq_self hq] at hN
  obtain rfl := nParam_eq_of_isSU3 hO hS hN
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary
    (V := I) fun v => by rw [← pow_two]; exact hI v
  have hS' : IsSU3 ↥(UC22.Ext.lgConj (L.subgroupOf X)) n := by
    rw [lgConj_subgroupOf_eq hLn]
    exact isSU3_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm hS
  have h147 := UC22.K147SpU.k147SpU_su3 (subRep θ X) (subRep_injective θ X)
    (subRep_isIrreducible θ hLX hirr) (isComponentOf_subgroupOf hLX hLn hq) hS'
  rw [mGV_subRep] at h147
  omega

theorem k14_5SmallFor_u3 :
    K14_5SmallFor fun L _ e => IsU3 L e :=
  K14_5SmallFor.mono (fun _ _ _ hq h => isSU3_of_isU3 hq h) k14_5SmallFor_su3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
