module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Cover
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Noncentral
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22SemiComp
import CFSG.LocalAnalysis.ComponentClassification.PerfectCyclicActions
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.Quasithin.EmptyFaithful.S146D1
import CFSG.LocalAnalysis.GL83PartI.I713.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem pRank_quotient_le_pRank_add_pRank_quotient {p : ℕ} (hp : p.Prime)
    {Y : Type*} [Group Y] [Finite Y] (P R I : Subgroup Y) [P.Normal] [R.Normal]
    (hIP : I ⊓ P = ⊥) (hR : R = I ⊔ P) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P)) ≤
      CFSG.Open.pRank p I + CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) := by
  classical
  let Rbar : Subgroup (Y ⧸ P) := R.map (QuotientGroup.mk' P)
  have hRbarn : Rbar.Normal :=
    Subgroup.Normal.map (inferInstance : R.Normal) (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P)
  have hPmap : P.map (QuotientGroup.mk' P) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa only [QuotientGroup.ker_mk'] using (le_refl P)
  have hmap : I.map (QuotientGroup.mk' P) = Rbar := by
    change I.map (QuotientGroup.mk' P) = R.map (QuotientGroup.mk' P)
    rw [hR, Subgroup.map_sup, hPmap, sup_bot_eq]
  have hinj : Function.Injective ((QuotientGroup.mk' P).comp I.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxP : ((x : Y)) ∈ P := (QuotientGroup.eq_one_iff (x : Y)).mp hx
    have hxbot : ((x : Y)) ∈ I ⊓ P := Subgroup.mem_inf.mpr ⟨x.2, hxP⟩
    rw [hIP, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  have hrange : ((QuotientGroup.mk' P).comp I.subtype).range =
      I.map (QuotientGroup.mk' P) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let eI : I ≃* Rbar :=
    (MonoidHom.ofInjective (f := (QuotientGroup.mk' P).comp I.subtype) hinj).trans
      (MulEquiv.subgroupCongr (hrange.trans hmap))
  have hRbar : CFSG.Open.pRank p (⊤ : Subgroup Rbar) = CFSG.Open.pRank p I :=
    ((CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eI).symm).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup I).symm
  have hPR : P ≤ R := by
    rw [hR]
    exact le_sup_right
  let eQ : ((Y ⧸ P) ⧸ Rbar) ≃* Y ⧸ R :=
    QuotientGroup.quotientQuotientEquivQuotient P R hPR
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup ((Y ⧸ P) ⧸ Rbar)) =
      CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eQ
  calc
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P))
        ≤ CFSG.Open.pRank p (⊤ : Subgroup Rbar) +
          CFSG.Open.pRank p (⊤ : Subgroup ((Y ⧸ P) ⧸ Rbar)) :=
          CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_top_le_add_of_normal hp Rbar
    _ = CFSG.Open.pRank p I + CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) := by
      rw [hRbar, hquot]

theorem pRank_le_three_of_center_eq_bot (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) (H : Subgroup G)
    {T : Type} [Group T] [Finite T] (π : H →* T) (hπ : Function.Surjective π)
    (hE : CFSG.layer T = ⊤) (hZ : Subgroup.center T = ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup T) ≤ 3 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hTperf : Group.IsPerfect T :=
    Group.IsPerfect.top_iff.mp (hE ▸ CFSG.LocalCores.layer_isPerfect)
  obtain ⟨Y, hGY, hFinY, P, hPN, hYperf, hPp, ⟨e⟩, hmin, hrkY, hKY⟩ :=
    exists_perfect_pCover_of_surjective (G := G) (S := T) hp H π hπ
  have hss := CFSG.SectionRank.centerless_semisimple_quotient hE hZ
    e.symm.toMonoidHom e.symm.surjective
  have hE' : CFSG.layer (Y ⧸ P) = ⊤ := hss.1
  have hZ' : Subgroup.center (Y ⧸ P) = ⊥ := hss.2
  have hperf : ∀ N : Subgroup (Y ⧸ P), N.Normal → ⁅N, N⁆ = N :=
    fun N hN => commutator_eq_self_of_normal_of_layer_eq_top hE' hZ' hN
  let C : Subgroup Y := Subgroup.centralizer (P : Set Y)
  have hCn : C.Normal := inferInstance
  let R : Subgroup Y := C ⊔ P
  have hRn : (C ⊔ P).Normal := Subgroup.sup_normal C P
  obtain ⟨I, hIC, hIP, hIR⟩ :=
    exists_le_centralizer_inf_eq_bot hC5 hp hp5 (hKY hK) (hrkY.trans hrk) P hPp hE' hZ'
  have hrk' : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 := hrkY.trans hrk
  have hquot2 : CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) ≤ 2 :=
    pRank_quotient_centralizer_sup_le_two hp hp2 P hPp hmin hperf hrk' R rfl
  have hdecomp : CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P)) ≤
      CFSG.Open.pRank p I + CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) :=
    pRank_quotient_le_pRank_add_pRank_quotient hp P R I hIP hIR.symm
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P)) ≤ 3 := by
    by_cases hcyc : IsCyclic P
    · have hcycI : IsCyclic P := hcyc
      have hPcent : P ≤ Subgroup.center Y :=
        CFSG.ComponentClassification.PerfectCyclicActions.central_of_perfect P
      have hCtop : C = ⊤ := by
        change Subgroup.centralizer (P : Set Y) = ⊤
        exact Subgroup.centralizer_eq_top_iff_subset.mpr
          (SetLike.coe_subset_coe.mpr hPcent)
      have hRtop : R = ⊤ := by
        change C ⊔ P = ⊤
        rw [hCtop, top_sup_eq]
      have hRsub : Subsingleton (Y ⧸ R) :=
        hRtop ▸ (QuotientGroup.subsingleton_quotient_top :
          Subsingleton (Y ⧸ (⊤ : Subgroup Y)))
      have hzero : CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) = 0 := by
        refine GL83.I713.pRank_top_eq_zero_of_not_dvd hp ?_
        have hcard : Nat.card (Y ⧸ R) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
        rw [hcard]
        exact hp.not_dvd_one
      have hIle : CFSG.Open.pRank p I ≤ 3 :=
        (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrk'
      calc
        CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P))
            ≤ CFSG.Open.pRank p I +
              CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) := hdecomp
        _ = CFSG.Open.pRank p I := by rw [hzero, add_zero]
        _ ≤ 3 := hIle
    · have h2P : 2 ≤ CFSG.Open.pRank p P :=
        CFSG.AGLEmbedding.two_le_pRank_of_isPGroup_not_isCyclic hp hp2 hPp hcyc
      have hcomm : ∀ x ∈ I, ∀ y ∈ P, x * y = y * x := by
        intro x hx y hy
        exact (Subgroup.mem_centralizer_iff.mp (hIC hx) y hy).symm
      have hadd : CFSG.Open.pRank p I + CFSG.Open.pRank p P ≤
          CFSG.Open.pRank p (I ⊔ P) :=
        CFSG.Quasithin.pRank_add_le_pRank_sup hp hcomm hIP
      have hsup : CFSG.Open.pRank p (I ⊔ P) ≤ 3 := by
        rw [show I ⊔ P = Subgroup.centralizer (P : Set Y) ⊔ P from hIR]
        exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrk'
      have hIle : CFSG.Open.pRank p I ≤ 1 := by omega
      calc
        CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P))
            ≤ CFSG.Open.pRank p I +
              CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) := hdecomp
        _ ≤ 1 + 2 := Nat.add_le_add hIle hquot2
        _ ≤ 3 := by norm_num
  calc
    CFSG.Open.pRank p (⊤ : Subgroup T)
        = CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
    _ ≤ 3 := hbound

end CFSG.LocalAnalysis.WeakClosure81.Asch22
