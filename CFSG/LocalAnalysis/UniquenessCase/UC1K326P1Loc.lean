module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
public import CFSG.Quasithin.EmptyFaithful.S146D2
public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Tools
public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Comp
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGenericCatalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

@[expose] def ExcludedCover (L : Type) [Group L] : Prop :=
  UCK.ThreeCover (fun Y _ => IsAlt Y 6) L ∨ UCK.ThreeCover (fun Y _ => IsAlt Y 7) L ∨
    UCK.ThreeCover (fun Y _ => IsSpor Y .M22) L ∨ UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) L

@[expose] def LieSporSimple : Prop :=
  (∀ (X : Type) [Group X] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (a p f : ℕ),
      LieModel X t a p f → IsSimpleGroup X) ∧
    ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨
        s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4 ∨ s = .J3) →
      IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s)

@[expose] def K326AtlasData : Prop :=
  CFSG.Quasithin.OddInner (alternatingGroup (Fin 6)) ∧
    CFSG.Quasithin.OddInner (alternatingGroup (Fin 7)) ∧
    CFSG.Quasithin.OddInner (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
    CFSG.Quasithin.OddInner (CFSG.Blueprint.NativeSporadic.Carrier .ONan) ∧
    Nat.card (alternatingGroup (Fin 6)) = 360 ∧ Nat.card (alternatingGroup (Fin 7)) = 2520 ∧
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 ∧
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem comp_three_dvd_card (hO : CFSG.pPrimeCore 3 G = ⊥) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) : 3 ∣ Nat.card ↥L :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.three_dvd_card_component hO hL

theorem comp_center_isPGroup (hO : CFSG.pPrimeCore 3 G = ⊥) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) : IsPGroup 3 (Subgroup.center ↥L) :=
  CFSG.RankThree.PartTwo.Sec4.Item432Proof.isPGroup_center_of_isSubnormal hO
    (CFSG.Goldschmidt.G310.isSubnormal_of_isComponentOf hL)

theorem comp_isSylowOf_inf (hP : IsSylowOf 3 P ⊤) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) : IsSylowOf 3 (P ⊓ L) L :=
  CFSG.GH74.GLS.Stage2.Final.Thm6.I414.isSylowOf_inf_of_isSubnormal hP
    (CFSG.Goldschmidt.G310.isSubnormal_of_isComponentOf hL)

theorem comp_isCatalogGroup (hK : CFSG.Open.IsKGroup G) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) :
    CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup hL.2.2
    (hK.subgroup L)

theorem comp_sylow_not_commutative {L T : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (h3 : IsPGroup 3 (Subgroup.center ↥L)) (hz : Subgroup.center ↥L ≠ ⊥)
    (hT : IsSylowOf 3 T L) : ¬ IsMulCommutative ↥T := by
  intro hcomm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 ↥L, (Q : Subgroup ↥L).map L.subtype = T := hT
  haveI hQc : IsMulCommutative (Q : Subgroup ↥L) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : L.subtype (x : ↥L) ∈ T := hQ ▸ Subgroup.mem_map_of_mem L.subtype x.2
    have hy : L.subtype (y : ↥L) ∈ T := hQ ▸ Subgroup.mem_map_of_mem L.subtype y.2
    have hc := congrArg Subtype.val (hcomm.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hc
  obtain ⟨z, hzne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hz
  have hzQ : (z : ↥L) ∈ (Q : Subgroup ↥L) := h3.le_sylow_of_normal Q z.2
  have hzc : (z : ↥L) ∈ commutator ↥L := by
    rw [hq.1]
    exact Subgroup.mem_top _
  have := CFSG.Walter.eq_one_of_mem_sylow_of_commute_normalizer Q hzQ hzc
    (fun m _ => Subgroup.mem_center_iff.1 z.2 m)
  exact hzne (Subtype.ext this)

theorem exists_elemAbelian_nine {T : Subgroup G} (hT : IsPGroup 3 ↥T)
    (hnc : ¬ IsMulCommutative ↥T) :
    ∃ E : Subgroup G, E ≤ T ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card ↥E = 9 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.exists_E9_le_of_not_isCyclic hT
    (fun hc => hnc (@IsCyclic.isMulCommutative _ _ hc))

theorem pRank_top_le_three (h : Hyp326 G n P) : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ew⟩ := h.wr
  have hsyl : ¬ 3 ∣ P.index := by
    have h3 := ((CFSG.ABGLocalTools.isSylowOf_iff (p := 3) (P := P) (K := ⊤)).1 h.sylow).2.2
    simpa using h3
  let Q : Sylow 3 G := h.sylow.isPGroup.toSylow hsyl
  have h1 : CFSG.Open.pRank 3 (Q : Subgroup G) = CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    (CFSG.SectionRank.pRank_sylow Q).1
  have h2 : CFSG.Open.pRank 3 P = 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact zwr_pRank h.one_le ew
  have hQ : (Q : Subgroup G) = P := rfl
  rw [hQ] at h1
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
