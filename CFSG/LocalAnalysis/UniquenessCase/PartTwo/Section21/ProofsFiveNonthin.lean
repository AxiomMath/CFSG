module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveDiagonal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
import CFSG.GroupTheory.CommutingElementaryAbelian
import CFSG.GroupTheory.PerfectSylowCenter
import CFSG.GroupTheory.SquarefreeOrder
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.GroupTheory
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}

private theorem Ctx215.a_mem (e : Ctx215 D Ch) : e.a ∈ D.M :=
  e.hBM (e.hle e.haB)

theorem Ctx215.normalizer_ne_top (e : Ctx215 D Ch) :
    Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ≠ ⊤ := by
  have hcard : Nat.card (Subgroup.zpowers e.a) = orderOf e.a := Nat.card_zpowers e.a
  exact CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_ne_top_of_card_prime_uc6
    D.standing.simple D.standing.nonab e.ha_prime hcard

theorem Ctx215.not_normalizer_le (e : Ctx215 D Ch) (h1930 : H1930 D) :
    ¬ Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ≤ D.M := by
  exact s21_2 D Ch h1930 e.toCtx21 (Subgroup.zpowers e.a) (Subgroup.zpowers_le.mpr e.haB)

private theorem le_normalizer_zpowers_of_le_centralizer (e : Ctx215 D Ch) {X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer ({e.a} : Set G)) :
    X ≤ Subgroup.normalizer (Subgroup.zpowers e.a : Set G) := by
  have hcent : Subgroup.centralizer ({e.a} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers e.a : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hX.trans (hcent.trans (Subgroup.centralizer_le_normalizer _))

private theorem p_dvd_bar2_of_not_isCyclic (e : Ctx215 D Ch) {p : ℕ} (hp : p.Prime)
    (P : Sylow p (Bar2 e.L)) (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    p ∣ Nat.card (Bar2 e.L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvdP : p ∣ Nat.card (P : Subgroup (Bar2 e.L)) := by
    rcases P.isPGroup'.card_eq_or_dvd with h1 | hd
    · haveI : Subsingleton ↥(P : Subgroup (Bar2 e.L)) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      exact absurd isCyclic_of_subsingleton hPnc
    · exact hd
  exact hpdvdP.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup (Bar2 e.L)))

private theorem exists_three_calC_conjugates (e : Ctx215 D Ch) {p : ℕ}
    (hpdvd : p ∣ Nat.card (Bar2 e.L)) :
    ∃ L0 L1 L2 : Subgroup G,
      L0 ∈ calC D.M ∧ L1 ∈ calC D.M ∧ L2 ∈ calC D.M ∧
      L0 ≠ L1 ∧ L0 ≠ L2 ∧ L1 ≠ L2 ∧ L0 = e.L ∧
      p ∣ Nat.card (Bar2 L1) ∧ p ∣ Nat.card (Bar2 L2) := by
  have hr3 : 2 < orderOf e.a := lt_of_le_of_ne e.ha_prime.two_le (Ne.symm e.ha_ne_two)
  have h0r : (0 : ℕ) ∈ Set.Iio (orderOf e.a) := by
    simpa [Set.mem_Iio] using e.ha_prime.pos
  have h1r : (1 : ℕ) ∈ Set.Iio (orderOf e.a) := by
    simpa [Set.mem_Iio] using e.ha_prime.one_lt
  have h2r : (2 : ℕ) ∈ Set.Iio (orderOf e.a) := by
    simpa [Set.mem_Iio] using hr3
  have hinj := conjugatePower_injOn (L := e.L) (a := e.a) e.ha_prime e.ha_not_mem
  let L0 := conjugatePower e.a e.L 0
  let L1 := conjugatePower e.a e.L 1
  let L2 := conjugatePower e.a e.L 2
  have hL0 : L0 ∈ calC D.M := conjugatePower_mem_calC e.hL e.a_mem 0
  have hL1 : L1 ∈ calC D.M := conjugatePower_mem_calC e.hL e.a_mem 1
  have hL2 : L2 ∈ calC D.M := conjugatePower_mem_calC e.hL e.a_mem 2
  have h01 : L0 ≠ L1 := fun h => absurd (hinj h0r h1r h) (by omega)
  have h02 : L0 ≠ L2 := fun h => absurd (hinj h0r h2r h) (by omega)
  have h12 : L1 ≠ L2 := fun h => absurd (hinj h1r h2r h) (by omega)
  have hL0eq : L0 = e.L := by
    have hconj1 : MulAut.conj (1 : G) = 1 := map_one (MulAut.conj : G →* MulAut G)
    change conjugatePower e.a e.L 0 = e.L
    rw [conjugatePower, pow_zero, hconj1]
    exact Subgroup.map_id e.L
  have hpdvd1 : p ∣ Nat.card (Bar2 L1) := by
    obtain ⟨f⟩ := uc22p20d_bar2_conj (e.a ^ 1) e.L
    rw [show Nat.card (Bar2 L1) = Nat.card (Bar2 e.L) from
      (Nat.card_congr f.toEquiv).symm]
    exact hpdvd
  have hpdvd2 : p ∣ Nat.card (Bar2 L2) := by
    obtain ⟨f⟩ := uc22p20d_bar2_conj (e.a ^ 2) e.L
    rw [show Nat.card (Bar2 L2) = Nat.card (Bar2 e.L) from
      (Nat.card_congr f.toEquiv).symm]
    exact hpdvd
  exact ⟨L0, L1, L2, hL0, hL1, hL2, h01, h02, h12, hL0eq, hpdvd1, hpdvd2⟩

private theorem exists_elemAbelian_card_sq_barImage (e : Ctx215 D Ch) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Sylow p (Bar2 e.L))
    (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    ∃ E0 : Subgroup (Bar2 D.M), IsElemAbelian p E0 ∧ Nat.card E0 = p ^ 2 ∧
      E0 ≤ barImage D.M e.L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨B, hBelem, hBcard⟩ :=
    CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two (p := p) hodd
      P.isPGroup' hPnc
  obtain ⟨e0, -⟩ := uc22p22l_barImage_equiv (L := D.M) (K := e.L) e.hL
  let E0 : Subgroup (Bar2 D.M) :=
    ((B.map (P : Subgroup (Bar2 e.L)).subtype).map e0.toMonoidHom).map
      (barImage D.M e.L).subtype
  have hE0ea : IsElemAbelian p E0 := by
    refine CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map ?_ e0.toMonoidHom)
      (barImage D.M e.L).subtype
    exact CFSG.Open.IsElemAbelian.map
      ((isElemAbelian_iff_isElementaryAbelian (p := p) (E := B)).mpr hBelem)
      (P : Subgroup (Bar2 e.L)).subtype
  have hE0card : Nat.card E0 = p ^ 2 := by
    have h1 : Nat.card E0 =
        Nat.card ((B.map (P : Subgroup (Bar2 e.L)).subtype).map e0.toMonoidHom) :=
      Subgroup.card_map_of_injective (barImage D.M e.L).subtype_injective
    rw [h1, Subgroup.card_map_of_injective e0.injective,
      Subgroup.card_map_of_injective (P : Subgroup (Bar2 e.L)).subtype_injective, hBcard]
  exact ⟨E0, hE0ea, hE0card, Subgroup.map_subtype_le _⟩

private theorem exists_elemAbelian_card_cube {M L0 L1 L2 : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL0 : L0 ∈ calC M) (hL1 : L1 ∈ calC M)
    (hL2 : L2 ∈ calC M) (h01 : L0 ≠ L1) (h02 : L0 ≠ L2) (h12 : L1 ≠ L2)
    (E0 : Subgroup (Bar2 M)) (hE0ea : IsElemAbelian p E0)
    (hE0card : Nat.card E0 = p ^ 2) (hE0le : E0 ≤ barImage M L0)
    (u1 : ↥(barImage M L1)) (hu1ord : orderOf u1 = p)
    (hu1nc : u1 ∉ Subgroup.center ↥(barImage M L1)) :
    ∃ E1 : Subgroup (Bar2 M), IsElemAbelian p E1 ∧ Nat.card E1 = p ^ 3 ∧
      E1 ≤ Subgroup.centralizer (barImage M L2 : Set (Bar2 M)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let E1 : Subgroup (Bar2 M) := E0 ⊔ Subgroup.zpowers (u1 : Bar2 M)
  obtain ⟨hE1ea, hE1card⟩ :=
    CFSG.GroupTheory.sup_zpowers_isElemAbelian_of_commute
      (H := barImage M L0) (K := barImage M L1) (E := E0)
      (uc22p22l_barImage_commute hL0 hL1 h01) hE0ea hE0le hu1ord hu1nc
  have hcardE1 : Nat.card E1 = p ^ 3 := by
    rw [show Nat.card E1 = p * Nat.card E0 from hE1card, hE0card]
    ring
  have hE1cent : E1 ≤ Subgroup.centralizer (barImage M L2 : Set (Bar2 M)) := by
    have hE0cent : E0 ≤ Subgroup.centralizer (barImage M L2 : Set (Bar2 M)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (uc22p22l_barImage_commute hL0 hL2 h02 x (hE0le hx) b hb).symm
    have hzp : Subgroup.zpowers (u1 : Bar2 M) ≤
        Subgroup.centralizer (barImage M L2 : Set (Bar2 M)) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (uc22p22l_barImage_commute hL1 hL2 h12 u1 u1.2 b hb).symm
    exact sup_le hE0cent hzp
  exact ⟨E1, hE1ea, hcardE1, hE1cent⟩

private theorem exists_elemAbelian_card_pow_four_barImage (e : Ctx215 D Ch) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p (Bar2 e.L))
    (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    ∃ E : Subgroup (Bar2 D.M), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ Nat.card (Bar2 e.L) := p_dvd_bar2_of_not_isCyclic e hp P hPnc
  obtain ⟨L0, L1, L2, hL0, hL1, hL2, h01, h02, h12, hL0eq, hpdvd1, hpdvd2⟩ :=
    exists_three_calC_conjugates e hpdvd
  obtain ⟨E0, hE0ea, hE0card, hE0le0⟩ :=
    exists_elemAbelian_card_sq_barImage e hp hp2 P hPnc
  have hE0le : E0 ≤ barImage D.M L0 := by
    rwa [hL0eq]
  obtain ⟨u1, hu1ord, hu1nc⟩ :=
    exists_orderOf_prime_not_mem_center_barImage (M := D.M) (L := L1) hL1 hp hp2 hpdvd1
  obtain ⟨E1, hE1ea, hE1card, hE1cent⟩ :=
    exists_elemAbelian_card_cube hp hp2 hL0 hL1 hL2 h01 h02 h12 E0 hE0ea hE0card hE0le
      u1 hu1ord hu1nc
  obtain ⟨u2, hu2ord, hu2nc⟩ :=
    exists_orderOf_prime_not_mem_center_barImage (M := D.M) (L := L2) hL2 hp hp2 hpdvd2
  let E2 : Subgroup (Bar2 D.M) := E1 ⊔ Subgroup.zpowers (u2 : Bar2 D.M)
  obtain ⟨hE2ea, hE2card⟩ :=
    CFSG.GroupTheory.sup_zpowers_isElemAbelian_of_commute
      (H := E1) (K := barImage D.M L2) (E := E1)
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hE1cent ha) b hb).symm)
      hE1ea le_rfl hu2ord hu2nc
  refine ⟨E2, hE2ea, ?_⟩
  rw [show Nat.card E2 = p * Nat.card E1 from hE2card, hE1card]
  ring

theorem Ctx215.four_le_pRank_of_not_isCyclic (e : Ctx215 D Ch) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Sylow p (Bar2 e.L))
    (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    4 ≤ CFSG.Open.pRank p D.M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E2, hE2ea, hE2card⟩ := exists_elemAbelian_card_pow_four_barImage e hp hp2 P hPnc
  obtain ⟨F, -, hFea, hFcard⟩ :=
    uc22p20d_lift_elemAbelian (A := ↥D.M) (CFSG.pCore 2 ↥D.M) CFSG.pCore_isPGroup hp hp2
      (⊤ : Subgroup ↥D.M) E2 hE2ea hE2card (by
        rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        exact le_top)
  have hFea' : IsElemAbelian p (F.map D.M.subtype) := hFea.map D.M.subtype
  have hFcard' : Nat.card (F.map D.M.subtype) = p ^ 4 := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective, hFcard]
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le F) hFea' hFcard'

private theorem exists_surjective_range_orbitDiagonal {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (ha : a ∈ M) (hr : (orderOf a).Prime)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    ∃ φE : ↥((orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩)
        (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
        (conjugatesCommute_barImage hL ha hr haL)).range) →*
        (Bar2 L ⧸ Subgroup.center (Bar2 L)),
      Function.Surjective φE := by
  classical
  let qM : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let δ : ↥(barImage M L) →* Bar2 M :=
    orbitDiagonalHom (qM ⟨a, ha⟩) (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)
  have hδker : δ.ker ≤ Subgroup.center ↥(barImage M L) :=
    orbitDiagonalHom_ker_le_center (qM ⟨a, ha⟩) (barImage M L) (orderOf a)
      (mk_pow_orderOf_eq_one ha) (conjugatesCommute_barImage hL ha hr haL) hr.pos
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  let δ' : Bar2 L →* Bar2 M := δ.comp e.toMonoidHom
  have hδ'ker : δ'.ker ≤ Subgroup.center (Bar2 L) :=
    ker_comp_le_center_of_ker_le_center e hδker
  have hδ'range : δ'.range = δ.range := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective,
      ← MonoidHom.range_eq_map]
  let qmap : Bar2 L ⧸ δ'.ker →* (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
    QuotientGroup.lift δ'.ker (QuotientGroup.mk' (Subgroup.center (Bar2 L)))
      (by simpa [QuotientGroup.ker_mk'] using hδ'ker)
  have hqmap : Function.Surjective qmap :=
    QuotientGroup.lift_surjective_of_surjective δ'.ker
      (QuotientGroup.mk' (Subgroup.center (Bar2 L)))
      (QuotientGroup.mk'_surjective (Subgroup.center (Bar2 L)))
      (by simpa [QuotientGroup.ker_mk'] using hδ'ker)
  let eE : Bar2 L ⧸ δ'.ker ≃* ↥δ.range :=
    (QuotientGroup.quotientKerEquivRange δ').trans (MulEquiv.subgroupCongr hδ'range)
  let φE : ↥δ.range →* (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
    qmap.comp eE.symm.toMonoidHom
  exact ⟨φE, hqmap.comp eE.symm.surjective⟩

private theorem exists_surjective_center_quotient {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (ha : a ∈ M) (hr : (orderOf a).Prime)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) {D : Subgroup G} (hDM : D ≤ M)
    (hDmap : (D.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
      (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
        (orderOf a) (mk_pow_orderOf_eq_one ha)
        (conjugatesCommute_barImage hL ha hr haL)).range) :
    ∃ f : ↥D →* (Bar2 L ⧸ Subgroup.center (Bar2 L)), Function.Surjective f := by
  classical
  obtain ⟨φE, hφE⟩ := exists_surjective_range_orbitDiagonal hL ha hr haL
  let qM : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let δ : ↥(barImage M L) →* Bar2 M :=
    orbitDiagonalHom (qM ⟨a, ha⟩) (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)
  let ψ : ↥D →* Bar2 M := qM.comp (Subgroup.inclusion hDM)
  have hψrange : ψ.range = δ.range := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hDmap
  let fD : ↥D →* ↥δ.range :=
    (MulEquiv.subgroupCongr hψrange).toMonoidHom.comp ψ.rangeRestrict
  have hfD : Function.Surjective fD :=
    (MulEquiv.subgroupCongr hψrange).surjective.comp (MonoidHom.rangeRestrict_surjective ψ)
  exact ⟨φE.comp fD, hφE.comp hfD⟩

private theorem subgroupOf_inf_le_ker_of_isSimple {G' : Type} [Group G'] [Finite G']
    {S : Type} [Group S] [IsSimpleGroup S] {D K : Subgroup G'} {p : ℕ}
    (f : ↥D →* S) (hf : Function.Surjective f)
    (hKn : (K.subgroupOf D).Normal) (hpS : p ∣ Nat.card S)
    (hpK : ¬ p ∣ Nat.card ↥K) :
    (D ⊓ K).subgroupOf D ≤ f.ker := by
  have hL0n : ((D ⊓ K).subgroupOf D).Normal := by
    simpa [inf_comm, Subgroup.inf_subgroupOf_left] using hKn
  haveI hmapn : (((D ⊓ K).subgroupOf D).map f).Normal := hL0n.map f hf
  have hne : ((D ⊓ K).subgroupOf D).map f ≠ ⊤ := by
    intro htop
    have hp_map : p ∣ Nat.card (((D ⊓ K).subgroupOf D).map f) := by
      rw [htop, Subgroup.card_top]
      exact hpS
    have hpD : p ∣ Nat.card ((D ⊓ K).subgroupOf D) :=
      hp_map.trans (Subgroup.card_map_dvd (H := (D ⊓ K).subgroupOf D) f)
    have hcard : Nat.card ↥((D ⊓ K).subgroupOf D) = Nat.card ↥(D ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hpK' : p ∣ Nat.card ↥(D ⊓ K) := by
      rwa [hcard] at hpD
    exact hpK (hpK'.trans (Subgroup.card_dvd_of_le inf_le_right))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((D ⊓ K).subgroupOf D).map f) with hbot | htop
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hmem : f x ∈ ((D ⊓ K).subgroupOf D).map f := Subgroup.mem_map_of_mem f hx
    rw [hbot] at hmem
    simpa using hmem
  · exact absurd htop hne

private theorem pPrimeCoreIn_subgroupOf_normal {p : ℕ} {H D0 : Subgroup G}
    (hD0H : D0 ≤ H) :
    ((F07.PPrimeCoreIn p H).subgroupOf D0).Normal := by
  haveI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  have hK_H : ((F07.PPrimeCoreIn p H).subgroupOf H).Normal := by
    simpa [F07.PPrimeCoreIn] using
      (show (CFSG.pPrimeCore p ↥H).Normal from inferInstance)
  haveI : ((F07.PPrimeCoreIn p H).subgroupOf H).Normal := hK_H
  have h := Subgroup.inf_subgroupOf_inf_normal_of_left
    (A' := F07.PPrimeCoreIn p H) (A := H) D0
  rw [inf_eq_right.mpr hD0H] at h
  simpa [inf_comm] using h

private theorem not_dvd_card_pPrimeCoreIn {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    ¬ p ∣ Nat.card ↥(F07.PPrimeCoreIn p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card ↥(F07.PPrimeCoreIn p H)) := by
    rw [show Nat.card ↥(F07.PPrimeCoreIn p H) = Nat.card ↥(CFSG.pPrimeCore p ↥H) from
      Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  exact hp.coprime_iff_not_dvd.mp hcop

private theorem imageModK_opp_normal {p : ℕ} {H : Subgroup G} :
    (F07.ImageModK p H (Opp p H)).Normal := by
  have hOppH : ((Opp p H).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (Opp p H : Set G) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_Opp_uc6
        (Subgroup.le_normalizer g.2) p
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have h := hOppH.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    (QuotientGroup.mk'_surjective _)
  simpa [F07.ImageModK] using h

theorem kf7Use_of_r72 (h72 : F07.R72 D) (hKF7 : KStrongEmbedded72) : KF7Use D := by
  classical
  intro p _ H hSec7
  have h72' := r72Shape_of_r72 h72 hSec7
  obtain ⟨hp, hp2, hM, -, hHM, hrank⟩ := hSec7
  haveI : Fact p.Prime := ⟨hp⟩
  have hrankH : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) := by omega
  have hLHnorm : (F07.ImageModK p H (Opp p H)).Normal := imageModK_opp_normal
  have hNstrong : IsStronglyPEmbedded p
      (((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore
      hp hM hHM hrankH
  have hOp : CFSG.pPrimeCore p (F07.QuotK7 p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot hp
  have hKF := hKF7 p hp hp2 (F07.QuotK7 p H) hOp
    (F07.ImageModK p H (Opp p H)) hLHnorm h72'.1 h72'.2
    (((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) hNstrong
  rcases hKF with hsol | ⟨hp5, -, hquot⟩
  · exact Or.inl hsol
  · refine Or.inr ⟨hp5, ?_⟩
    intro Y hY hYperf S hGrp hS f hf
    exact @hquot Y hY hYperf S hGrp hS f hf

private theorem kf7_dichotomy (e : Ctx215 D Ch) (h1930 : H1930 D) (hU : KF7Use D) {p : ℕ}
    (hpσ : p ∈ D.sig) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : IsStronglyPEmbedded p D.M)
    (hrank : 2 ≤ CFSG.Open.pRank p
      (Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ⊓ D.M))
    {H : Subgroup G} (hH : H = Subgroup.normalizer (Subgroup.zpowers e.a : Set G)) :
    IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) ∨
      (p = 5 ∧ ∀ Y : Subgroup (F07.QuotK7 p H),
        Y ≤ ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) →
        ⁅Y, Y⁆ = Y → ∀ (S : Type) [Group S], IsSimpleGroup S →
          ∀ f : ↥Y →* S, Function.Surjective f → IsAlt S 5) := by
  have hHne : H ≠ ⊤ := by rw [hH]; exact e.normalizer_ne_top
  have hHM : ¬ H ≤ D.M := by rw [hH]; exact e.not_normalizer_le h1930
  have hrankH : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) := by rw [hH]; exact hrank
  exact hU p hpσ H ⟨hp, hp2, hM, hHne, hHM, by omega⟩

private theorem exists_diagonal_surjection_killing_K (e : Ctx215 D Ch) {p : ℕ}
    (hp : p.Prime)
    (hpS : p ∣ Nat.card (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)))
    {H : Subgroup G} (hH : H = Subgroup.normalizer (Subgroup.zpowers e.a : Set G)) :
    ∃ (D0 : Subgroup G) (f : ↥D0 →* (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))),
      D0 ≤ D.M ∧ D0 ≤ H ∧ ⁅D0, D0⁆ = D0 ∧ Function.Surjective f ∧
        (D0 ⊓ F07.PPrimeCoreIn p H).subgroupOf D0 ≤ f.ker := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hSsimple : IsSimpleGroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) := e.hL.2.2.2
  have haM : e.a ∈ D.M := e.a_mem
  obtain ⟨D0, hD0M, hD0cent, hD0perf, -, hD0map⟩ :=
    exists_diagonal_perfect e.hL haM e.ha_prime e.ha_ne_two e.ha_not_mem
  have hD0H : D0 ≤ H := by
    rw [hH]
    exact le_normalizer_zpowers_of_le_centralizer e hD0cent
  obtain ⟨f, hfsurj⟩ :=
    exists_surjective_center_quotient e.hL haM e.ha_prime e.ha_not_mem hD0M hD0map
  have hK_D : ((F07.PPrimeCoreIn p H).subgroupOf D0).Normal :=
    pPrimeCoreIn_subgroupOf_normal hD0H
  have hpK : ¬ p ∣ Nat.card ↥(F07.PPrimeCoreIn p H) := not_dvd_card_pPrimeCoreIn hp H
  exact ⟨D0, f, hD0M, hD0H, hD0perf, hfsurj,
    subgroupOf_inf_le_ker_of_isSimple f hfsurj hK_D hpS hpK⟩

private theorem ker_quotK_inclusion_eq_inf_pPrimeCore {p : ℕ} {H D0 : Subgroup G}
    (hD0H : D0 ≤ H) :
    ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hD0H)).ker =
      (D0 ⊓ F07.PPrimeCoreIn p H).subgroupOf D0 := by
  ext x
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk (Subgroup.inclusion hD0H x) : F07.QuotK7 p H) = 1 ↔
    x ∈ (D0 ⊓ F07.PPrimeCoreIn p H).subgroupOf D0
  have hmemK_iff : Subgroup.inclusion hD0H x ∈ CFSG.pPrimeCore p ↥H ↔
      (x : G) ∈ F07.PPrimeCoreIn p H := by
    change _ ↔ (x : G) ∈ (CFSG.pPrimeCore p ↥H).map H.subtype
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem H.subtype hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hy' : y = Subgroup.inclusion hD0H x := Subtype.ext hyx
      simpa [hy'] using hy
  rw [QuotientGroup.eq_one_iff, hmemK_iff, Subgroup.mem_subgroupOf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

private theorem exists_perfect_surjection_le_image (e : Ctx215 D Ch) {p : ℕ}
    {H D0 : Subgroup G} {f : ↥D0 →* (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))}
    (hD0H : D0 ≤ H) (hD0M : D0 ≤ D.M) (hD0perf : ⁅D0, D0⁆ = D0)
    (hfsurj : Function.Surjective f)
    (hker : (D0 ⊓ F07.PPrimeCoreIn p H).subgroupOf D0 ≤ f.ker) :
    ∃ (Y : Subgroup (F07.QuotK7 p H))
      (φY : ↥Y →* (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))),
      Y ≤ ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ∧
      ⁅Y, Y⁆ = Y ∧ Function.Surjective φY := by
  classical
  let qH : ↥H →* F07.QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  let g : ↥D0 →* F07.QuotK7 p H := qH.comp (Subgroup.inclusion hD0H)
  let Y : Subgroup (F07.QuotK7 p H) := g.range
  have hgker : g.ker = (D0 ⊓ F07.PPrimeCoreIn p H).subgroupOf D0 := by
    change (qH.comp (Subgroup.inclusion hD0H)).ker = _
    exact ker_quotK_inclusion_eq_inf_pPrimeCore hD0H
  have hYleN : Y ≤ ((H ⊓ D.M).subgroupOf H).map qH := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    exact Subgroup.mem_map_of_mem qH
      (Subgroup.mem_subgroupOf.mpr (le_inf hD0H hD0M x.2))
  haveI hD0perfect : Group.IsPerfect ↥D0 := Subgroup.isPerfect_iff.mpr hD0perf
  have hYperf : ⁅Y, Y⁆ = Y := by
    have hYpf : Group.IsPerfect ↥Y :=
      Group.IsPerfect.ofSurjective (f := g.rangeRestrict)
        (MonoidHom.rangeRestrict_surjective g)
    exact Subgroup.isPerfect_iff.mp hYpf
  let η : ↥D0 ⧸ g.ker →* (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) :=
    QuotientGroup.lift g.ker f (by rw [hgker]; exact hker)
  have hηsurj : Function.Surjective η :=
    QuotientGroup.lift_surjective_of_surjective g.ker f hfsurj
      (by rw [hgker]; exact hker)
  let eY : ↥D0 ⧸ g.ker ≃* ↥Y := QuotientGroup.quotientKerEquivRange g
  let φY : ↥Y →* (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) := η.comp eY.symm.toMonoidHom
  exact ⟨Y, φY, hYleN, hYperf, hηsurj.comp eY.symm.surjective⟩

theorem Ctx215.eq_five_of_isStronglyPEmbedded (e : Ctx215 D Ch) (h1930 : H1930 D)
    (hU : KF7Use D) {p : ℕ} (hpσ : p ∈ D.sig) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : IsStronglyPEmbedded p D.M)
    (hrank : 2 ≤ CFSG.Open.pRank p
      (Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ⊓ D.M))
    (hpS : p ∣ Nat.card (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))) :
    p = 5 ∧ IsAlt (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) 5 := by
  classical
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers e.a : Set G)
  have hH : H = Subgroup.normalizer (Subgroup.zpowers e.a : Set G) := rfl
  have hKF := kf7_dichotomy e h1930 hU hpσ hp hp2 hM hrank (H := H) hH
  obtain ⟨D0, f, hD0M, hD0H, hD0perf, hfsurj, hker⟩ :=
    exists_diagonal_surjection_killing_K e hp hpS (H := H) hH
  obtain ⟨Y, φY, hYleN, hYperf, hφYsurj⟩ :=
    exists_perfect_surjection_le_image e hD0H hD0M hD0perf hfsurj hker
  haveI hSsimple : IsSimpleGroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) := e.hL.2.2.2
  rcases hKF with hNsolv | ⟨hp5, hquot⟩
  · let N : Subgroup (F07.QuotK7 p H) :=
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    haveI : Group.IsSolvable ↥N := hNsolv
    have hYsolv : Group.IsSolvable ↥Y := by
      have hsub : Group.IsSolvable ↥(Y.subgroupOf N) := inferInstance
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hYleN).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hYleN).symm.injective
    haveI : Group.IsSolvable ↥Y := hYsolv
    have hSsolv : Group.IsSolvable (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) :=
      Group.isSolvable_of_surjective (f := φY) hφYsurj
    haveI : Group.IsPerfect (Bar2 e.L) := Group.isPerfect_def.mpr e.hL.2.2.1
    haveI : Group.IsPerfect (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) := inferInstance
    exact (Group.IsPerfect.not_isSolvable
      (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))) hSsolv |>.elim
  · exact ⟨hp5, hquot Y hYleN hYperf
      (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) hSsimple φY hφYsurj⟩

private theorem stronglyPEmbedded_of_noncyclic_sylow (e : Ctx215 D Ch)
    (hσ : UC6S846.SigmaStd D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Sylow p (Bar2 e.L)) (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    IsStronglyPEmbedded p D.M := by
  have h4 : 4 ≤ CFSG.Open.pRank p D.M :=
    e.four_le_pRank_of_not_isCyclic hp hp2 P hPnc
  by_contra hnot
  have h3 := s21_15_pRank_le_three hσ hp hp2 e.hL hnot
  omega

private theorem two_le_pRank_normalizer_inf (e : Ctx215 D Ch) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Sylow p (Bar2 e.L))
    (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    2 ≤ CFSG.Open.pRank p
      (Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ⊓ D.M) := by
  obtain ⟨D0, hD0M, hD0cent, hD0perf, -, hD0map⟩ :=
    exists_diagonal_perfect e.hL e.a_mem e.ha_prime e.ha_ne_two e.ha_not_mem
  have h2D : 2 ≤ CFSG.Open.pRank p D0 :=
    two_le_pRank_diagonal e.hL e.a_mem e.ha_prime e.ha_ne_two e.ha_not_mem hD0M hD0map
      hp hp2 ⟨P, hPnc⟩
  have hD0H : D0 ≤ Subgroup.normalizer (Subgroup.zpowers e.a : Set G) :=
    le_normalizer_zpowers_of_le_centralizer e hD0cent
  exact h2D.trans (CFSG.SectionRank.pRank_mono hp.one_lt (le_inf hD0H hD0M))

private theorem p_dvd_card_center_quotient (e : Ctx215 D Ch) {p : ℕ} (hp : p.Prime)
    (P : Sylow p (Bar2 e.L)) (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    p ∣ Nat.card (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect (Bar2 e.L) := Group.isPerfect_def.mpr e.hL.2.2.1
  have hPncAll : ∀ S' : Sylow p (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)),
      ¬ IsCyclic ↥(S' : Subgroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))) :=
    not_isCyclic_sylow_quotient_of_center P hPnc
      (Subgroup.center (Bar2 e.L)) le_rfl
  let S' : Sylow p (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) :=
    Classical.choice Sylow.nonempty
  rcases S'.isPGroup'.card_eq_or_dvd with h1 | hd
  · haveI : Subsingleton
        ↥(S' : Subgroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))) :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    exact absurd isCyclic_of_subsingleton (hPncAll S')
  · exact hd.trans (Subgroup.card_subgroup_dvd_card
      (S' : Subgroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))))

private theorem card_quotient_center_eq_sixty_of_isAlt_five (e : Ctx215 D Ch)
    (hA5 : IsAlt (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) 5) :
    Nat.card (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) = 60 := by
  obtain ⟨eA⟩ := hA5
  rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
  norm_num

private theorem card_sylow_eq_five_of_card_sixty {S : Type} [Group S] [Finite S] {p : ℕ}
    [Fact p.Prime] (S' : Sylow p S) (hPnc : ¬ IsCyclic ↥(S' : Subgroup S))
    (hcardS : Nat.card S = 60) (hp5 : p = 5) :
    Nat.card ↥(S' : Subgroup S) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP5 : IsPGroup 5 ↥(S' : Subgroup S) := by simpa [hp5] using S'.isPGroup'
  obtain ⟨n, hn⟩ := hP5.exists_card_eq
  have hdvd : 5 ^ n ∣ 60 := by
    rw [← hn, ← hcardS]
    exact Subgroup.card_subgroup_dvd_card (S' : Subgroup S)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have h1 : Nat.card ↥(S' : Subgroup S) = 1 := by rw [hn, h0, pow_zero]
      haveI : Subsingleton ↥(S' : Subgroup S) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hPnc isCyclic_of_subsingleton
    · exact hpos
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · omega
    · rfl
    · exfalso
      have h25 : 5 ^ 2 ∣ 60 :=
        (pow_dvd_pow 5 (by omega : 2 ≤ n + 1 + 1)).trans hdvd
      norm_num at h25
  rw [hn, hn1, pow_one]

theorem Ctx215.isCyclic_sylow (e : Ctx215 D Ch) (h1930 : H1930 D)
    (hσ : UC6S846.SigmaStd D) (hU : KF7Use D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p (Bar2 e.L)) :
    IsCyclic ↥(P : Subgroup (Bar2 e.L)) := by
  classical
  by_contra hPnc
  haveI : Fact p.Prime := ⟨hp⟩
  have hM : IsStronglyPEmbedded p D.M :=
    stronglyPEmbedded_of_noncyclic_sylow e hσ hp hp2 P hPnc
  have hpσ : p ∈ D.sig :=
    hσ.four_mem p hp hp2 (e.four_le_pRank_of_not_isCyclic hp hp2 P hPnc)
  have h2HM := two_le_pRank_normalizer_inf e hp hp2 P hPnc
  have hpS := p_dvd_card_center_quotient e hp P hPnc
  obtain ⟨hp5, hA5⟩ :=
    e.eq_five_of_isStronglyPEmbedded h1930 hU hpσ hp hp2 hM h2HM hpS
  haveI : Group.IsPerfect (Bar2 e.L) := Group.isPerfect_def.mpr e.hL.2.2.1
  have hPncAll : ∀ S' : Sylow p (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)),
      ¬ IsCyclic ↥(S' : Subgroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))) :=
    not_isCyclic_sylow_quotient_of_center P hPnc
      (Subgroup.center (Bar2 e.L)) le_rfl
  let S' : Sylow p (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) :=
    Classical.choice Sylow.nonempty
  have hcardS := card_quotient_center_eq_sixty_of_isAlt_five e hA5
  have hcard5 := card_sylow_eq_five_of_card_sixty S' (hPncAll S') hcardS hp5
  exact hPncAll S' (isCyclic_of_prime_card
    (p := p) (α := ↥(S' : Subgroup (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))))
    (by rw [hcard5, hp5]))

theorem Ctx215.pRank_three_le_one (e : Ctx215 D Ch) (h1930 : H1930 D)
    (hU : KF7Use D) (h3σ : 3 ∈ D.sig) (hM3 : IsStronglyPEmbedded 3 D.M)
    (h3S : 3 ∣ Nat.card (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L))) :
    CFSG.Open.pRank 3
      (Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ⊓ D.M) ≤ 1 := by
  by_contra h
  have hrank : 2 ≤ CFSG.Open.pRank 3
      (Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ⊓ D.M) := by omega
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have h53 := e.eq_five_of_isStronglyPEmbedded h1930 hU h3σ hp3 hp32 hM3 hrank h3S
  exact absurd h53.1 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22
