module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K6a K6b LieFam811 IsLie811)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

theorem card_map_lbar (c : Ctx82E3 D) {B : Subgroup G} (hBL : B ≤ c.L)
    (hB : ¬ 2 ∣ Nat.card B) :
    Nat.card ((B.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) =
      Nat.card B := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* (↥c.L ⧸ N) := QuotientGroup.mk' N
  show Nat.card ((B.subgroupOf c.L).map π) = Nat.card B
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hK : Nat.card ↥(B.subgroupOf c.L) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hdisj : B.subgroupOf c.L ⊓ N = ⊥ := by
    have hcop : Nat.Coprime (Nat.card ↥(B.subgroupOf c.L)) (Nat.card N) := by
      obtain ⟨k, hk⟩ := hN2.exists_card_eq
      rw [hK, hk]
      exact Nat.Coprime.pow_right k
        (Nat.coprime_comm.mp
          ((Nat.Prime.coprime_iff_not_dvd (p := 2) (n := Nat.card B) (by norm_num)).2 hB))
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hinj : Function.Injective (π.comp (B.subgroupOf c.L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : ↥c.L) ∈ N := (QuotientGroup.eq_one_iff (N := N) (x : ↥c.L)).1 hx
    have hxbot : (x : ↥c.L) ∈ B.subgroupOf c.L ⊓ N := ⟨x.2, hxN⟩
    rw [hdisj, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  have hrange : (π.comp (B.subgroupOf c.L).subtype).range = (B.subgroupOf c.L).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc Nat.card ((B.subgroupOf c.L).map π)
      = Nat.card ↥(π.comp (B.subgroupOf c.L).subtype).range := by rw [hrange]
    _ = Nat.card ↥(B.subgroupOf c.L) :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    _ = Nat.card B := hK

theorem centralizer_map_lbar (c : Ctx82E3 D) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {B : Subgroup G} (hBL : B ≤ c.L) (hB : IsPGroup q B) :
    Subgroup.centralizer (((B.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) :
        Subgroup (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) : Set (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) =
      ((c.L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* (↥c.L ⧸ N) := QuotientGroup.mk' N
  haveI : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hNq : ¬ q ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := q) hN2 Fact.out hq2
  have hQ : IsPGroup q (B.subgroupOf c.L) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  show Subgroup.centralizer (((B.subgroupOf c.L).map π : Subgroup (↥c.L ⧸ N)) :
        Set (↥c.L ⧸ N)) =
      ((c.L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf c.L).map π
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := q) (N := N)
    (Q := B.subgroupOf c.L) hNq hQ, CFSG.centralizer_subgroupOf_eq B c.L hBL,
    Subgroup.inf_subgroupOf_left]

theorem pRank_centralizer_lbar (c : Ctx82E3 D) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B : Subgroup G} (hBL : B ≤ c.L)
    (hB : IsPGroup q B) :
    CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (B : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer
        (((B.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) :
          Subgroup (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) :
            Set (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* (↥c.L ⧸ N) := QuotientGroup.mk' N
  let C : Subgroup ↥c.L := (c.L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf c.L
  haveI : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hCmap : Subgroup.centralizer (((B.subgroupOf c.L).map π : Subgroup (↥c.L ⧸ N)) :
        Set (↥c.L ⧸ N)) = C.map π :=
    centralizer_map_lbar c hq2 hBL hB
  have hCsub : C.map c.L.subtype = c.L ⊓ Subgroup.centralizer (B : Set G) :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hCD : CFSG.Open.pRank p C = CFSG.Open.pRank p (C.map c.L.subtype) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p C,
      ← CFSG.SectionRank.pRank_coe_eq_openPRank p (C.map c.L.subtype)]
    exact CFSG.pRank_congr_of_mulEquiv
      (Subgroup.equivMapOfInjective C c.L.subtype c.L.subtype_injective) p
  let f : ↥C →* (↥c.L ⧸ N) := π.comp C.subtype
  have hker : f.ker = N.subgroupOf C := by
    rw [← MonoidHom.comap_ker π C.subtype, QuotientGroup.ker_mk']
    rfl
  have hO2 : IsPGroup 2 f.ker := by
    rw [hker]
    exact hN2.comap_subtype
  have hOp : ¬ p ∣ Nat.card f.ker :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p) hO2 Fact.out hp2
  have hquot := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
    (G := ↥C) (p := p) Fact.out f.ker hOp
  have hrange : f.range = C.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : (C ⧸ f.ker) ≃* ↥(C.map π) :=
    (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)
  have hcongr : CFSG.pRank p (C ⧸ f.ker) = CFSG.pRank p ↥(C.map π) :=
    CFSG.pRank_congr_of_mulEquiv e p
  rw [hCmap, ← hCsub, ← hCD, ← CFSG.SectionRank.pRank_coe_eq_openPRank p C,
    ← CFSG.SectionRank.pRank_coe_eq_openPRank p (C.map π)]
  exact hquot.symm.trans hcongr

theorem dvd_card_centralizer_lbar_iff (c : Ctx82E3 D) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B : Subgroup G} (hBL : B ≤ c.L)
    (hB : IsPGroup q B) :
    p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer
        (((B.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) :
          Subgroup (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) :
            Set (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* (↥c.L ⧸ N) := QuotientGroup.mk' N
  let C : Subgroup ↥c.L := (c.L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf c.L
  haveI : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hCmap : Subgroup.centralizer (((B.subgroupOf c.L).map π : Subgroup (↥c.L ⧸ N)) :
        Set (↥c.L ⧸ N)) = C.map π :=
    centralizer_map_lbar c hq2 hBL hB
  have hCint : Nat.card ↥C = Nat.card ↥(c.L ⊓ Subgroup.centralizer (B : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let f : ↥C →* (↥c.L ⧸ N) := π.comp C.subtype
  have hker : f.ker = N.subgroupOf C := by
    rw [← MonoidHom.comap_ker π C.subtype, QuotientGroup.ker_mk']
    rfl
  have hO2 : IsPGroup 2 f.ker := by
    rw [hker]
    exact hN2.comap_subtype
  have hOp : ¬ p ∣ Nat.card f.ker :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p) hO2 Fact.out hp2
  have hrange : f.range = C.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : (C ⧸ f.ker) ≃* ↥(C.map π) :=
    (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)
  have hcardquot : Nat.card (C ⧸ f.ker) = Nat.card ↥(C.map π) :=
    Nat.card_congr e.toEquiv
  have hcardC : Nat.card ↥C = Nat.card (C ⧸ f.ker) * Nat.card ↥f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [hCmap, ← hCint, hcardC, hcardquot]
  constructor
  · intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hOp
  · intro h
    exact dvd_mul_of_dvd_left h _

theorem exists_mem_normalizer_of_mem_normalizer_lbar (c : Ctx82E3 D) {q : ℕ}
    [Fact q.Prime] (hq2 : q ≠ 2) {B : Subgroup G} (hBL : B ≤ c.L) (hB : IsPGroup q B)
    {x : ↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L}
    (hx : x ∈ Subgroup.normalizer (((B.subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) :
        Subgroup (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) :
          Set (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) :
    ∃ g : ↥c.L, (g : G) ∈ Subgroup.normalizer (B : Set G) ∧
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) g = x := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* (↥c.L ⧸ N) := QuotientGroup.mk' N
  haveI : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hNq : ¬ q ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := q) hN2 Fact.out hq2
  have hQ : IsPGroup q (B.subgroupOf c.L) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer q N hNq
    (B.subgroupOf c.L) hQ
  have hx' : x ∈ (Subgroup.normalizer (B.subgroupOf c.L : Set ↥c.L)).map π := by
    rw [hnorm]
    exact hx
  obtain ⟨g, hg, hgx⟩ := hx'
  refine ⟨g, ?_, hgx⟩
  have hg' : g ∈ (Subgroup.normalizer (B : Set G)).subgroupOf c.L := by
    rw [Subgroup.subgroupOf_normalizer_eq hBL]
    exact hg
  exact Subgroup.mem_subgroupOf.mp hg'

theorem exists_case811Sylow (c : Ctx82E3 D)
    (ha : ∀ P : Sylow 3 (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L),
      ∃! A : Subgroup (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L),
        A ≤ P ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27)
    (hb : ∀ A : Subgroup (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L),
      CFSG.Open.IsElemAbelian 3 A → Nat.card A = 27 →
        ∀ x : ↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L, orderOf x = 3 → ∃ g, g * x * g⁻¹ ∈ A)
    (hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L) :
    Nonempty (Case811Sylow c) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let Lbar := ↥c.L ⧸ N
  let π : ↥c.L →* Lbar := QuotientGroup.mk' N
  haveI : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hN2 (by norm_num) (by norm_num)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  have hP_L : P ≤ c.L := hPL P hP
  have hP_L_sylow : CFSG.ABGLocalTools.IsSylowOf 3 P c.L := hP.of_le hP_L c.hyp81.1
  let Q : Subgroup ↥c.L := P.subgroupOf c.L
  let Pbar : Subgroup Lbar := Q.map π
  have hQ3 : IsPGroup 3 Q := hP.isPGroup.comap_subtype
  have hP2 : ¬ 2 ∣ Nat.card P :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 3) (q := 2) hP.isPGroup
      (by norm_num) (by norm_num)
  have hPbar_card : Nat.card Pbar = Nat.card P := card_map_lbar c hP_L hP2
  have hcardL : Nat.card ↥c.L = Nat.card Lbar * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hfac : (Nat.card Lbar).factorization 3 = (Nat.card ↥c.L).factorization 3 := by
    conv_rhs => rw [hcardL]
    rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN3, add_zero]
  have hPbar_card' : Nat.card Pbar = 3 ^ (Nat.card Lbar).factorization 3 := by
    rw [hPbar_card, hP_L_sylow.card_eq, ← hfac]
  let PbarSylow : Sylow 3 Lbar := Sylow.ofCard Pbar hPbar_card'
  have hPbarSylow_coe : (PbarSylow : Subgroup Lbar) = Pbar := Sylow.coe_ofCard Pbar hPbar_card'
  obtain ⟨Abar, hAbar, hAbar_uniq⟩ := ha PbarSylow
  rw [hPbarSylow_coe] at hAbar hAbar_uniq
  let AL : Subgroup ↥c.L := Q ⊓ Abar.comap π
  let A : Subgroup G := AL.map c.L.subtype
  have hAL_le_Q : AL ≤ Q := inf_le_left
  have hAL_le_H : AL ≤ Abar.comap π := inf_le_right
  have hAL_map : AL.map π = Abar := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro a ha
      obtain ⟨q, hqQ, hqπ⟩ := Subgroup.mem_map.mp (hAbar.1 ha)
      exact Subgroup.mem_map.mpr
        ⟨q, ⟨hqQ, Subgroup.mem_comap.mpr (by rw [hqπ]; exact ha)⟩, hqπ⟩
  have hAL3 : IsPGroup 3 AL := hQ3.to_le hAL_le_Q
  have hinj : Function.Injective (π.comp AL.subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := N)
      (Q := AL) hN3 hAL3
  have hrange : (π.comp AL.subtype).range = Abar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hAL_map]
  let e : AL ≃* Abar :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hALcard : Nat.card AL = 27 := by
    rw [Nat.card_congr e.toEquiv, hAbar.2.2]
  have hALab : CFSG.Open.IsElemAbelian 3 AL :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv e.symm hAbar.2.1.isElementaryAbelian)
  have hAab : CFSG.Open.IsElemAbelian 3 A := hALab.map c.L.subtype
  have hAcard : Nat.card A = 27 := by
    rw [Subgroup.card_map_of_injective c.L.subtype_injective, hALcard]
  have hA_le_L : A ≤ c.L := Subgroup.map_subtype_le AL
  have hA_le_P : A ≤ P := by
    have h1 : A ≤ Q.map c.L.subtype := Subgroup.map_mono hAL_le_Q
    rwa [Subgroup.map_subgroupOf_eq_of_le hP_L] at h1
  have hA_unique : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian 3 B →
      Nat.card B = 27 → B = A := by
    intro B hBP hBab hBcard
    have hBL : B ≤ c.L := hBP.trans hP_L
    have hB2 : ¬ 2 ∣ Nat.card B := by rw [hBcard]; norm_num
    let Bbar : Subgroup Lbar := (B.subgroupOf c.L).map π
    have hBbar_card : Nat.card Bbar = 27 := by
      rw [card_map_lbar c hBL hB2, hBcard]
    have hBbar_ab : CFSG.Open.IsElemAbelian 3 Bbar := (hBab.subgroupOf c.L).map π
    have hBbar_le : Bbar ≤ Pbar := Subgroup.map_mono (Subgroup.comap_mono hBP)
    have hBbar_eq : Bbar = Abar := hAbar_uniq Bbar ⟨hBbar_le, hBbar_ab, hBbar_card⟩
    have hB_le_A : B ≤ A := by
      intro b hb
      have hbL : b ∈ c.L := hBL hb
      have hbQ : (⟨b, hbL⟩ : ↥c.L) ∈ Q := Subgroup.mem_subgroupOf.mpr (hBP hb)
      have hbB : (⟨b, hbL⟩ : ↥c.L) ∈ B.subgroupOf c.L := Subgroup.mem_subgroupOf.mpr hb
      have hbAbar : π ⟨b, hbL⟩ ∈ Abar := by
        rw [← hBbar_eq]
        exact Subgroup.mem_map_of_mem π hbB
      exact Subgroup.mem_map.mpr ⟨⟨b, hbL⟩, ⟨hbQ, hbAbar⟩, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hB_le_A (by rw [hAcard, hBcard])
  let H : Subgroup ↥c.L := Abar.comap π
  let HG : Subgroup G := H.map c.L.subtype
  have hH_eq : H = N ⊔ AL := by
    refine le_antisymm ?_ (sup_le ?_ inf_le_right)
    · intro h hh
      have hhAbar : π h ∈ Abar := hh
      have hhmap : π h ∈ AL.map π := by rw [hAL_map]; exact hhAbar
      obtain ⟨a, haAL, haπ⟩ := Subgroup.mem_map.mp hhmap
      have hna : h * a⁻¹ ∈ N := by
        refine (QuotientGroup.eq_one_iff (N := N) (h * a⁻¹)).mp ?_
        show π (h * a⁻¹) = 1
        rw [map_mul, map_inv, haπ, mul_inv_cancel]
      exact (Subgroup.mem_sup_of_normal_left (s := N) (t := AL)).mpr
        ⟨h * a⁻¹, hna, a, haAL, by group⟩
    · intro n hn
      exact Subgroup.mem_comap.mpr (by
        have h1 : π n = 1 := (QuotientGroup.eq_one_iff (N := N) n).2 hn
        rw [h1]
        exact Abar.one_mem)
  have hHG_eq : HG = CFSG.Open.pCoreOf 2 c.L ⊔ A := by
    change (H.map c.L.subtype) = CFSG.Open.pCoreOf 2 c.L ⊔ A
    rw [hH_eq, Subgroup.map_sup]
    rfl
  have hA_le_HG : A ≤ HG := Subgroup.map_mono hAL_le_H
  have hNG2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hdisj : Disjoint (CFSG.Open.pCoreOf 2 c.L) A :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) (CFSG.Open.pCoreOf 2 c.L) A hNG2 hAab.isPGroup
  have hAnorm : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    hA_le_L.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L)
  have hcard_sup : Nat.card ↥(CFSG.Open.pCoreOf 2 c.L ⊔ A) =
      Nat.card ↥(CFSG.Open.pCoreOf 2 c.L) * Nat.card ↥A :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (CFSG.Open.pCoreOf 2 c.L) A hAnorm hdisj
  have hcardHG : Nat.card ↥HG = Nat.card ↥A * Nat.card ↥(CFSG.Open.pCoreOf 2 c.L) := by
    rw [hHG_eq, hcard_sup, mul_comm]
  have hrel : A.relIndex HG = Nat.card ↥(CFSG.Open.pCoreOf 2 c.L) := by
    have h := Subgroup.relIndex_mul_card A HG
    rw [inf_eq_left.mpr hA_le_HG] at h
    rw [hAcard] at h
    rw [hcardHG, hAcard] at h
    rw [mul_comm 27 (Nat.card ↥(CFSG.Open.pCoreOf 2 c.L))] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hnotdvd : ¬ 3 ∣ A.relIndex HG := by
    rw [hrel]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hNG2
      (by norm_num) (by norm_num)
  have hAsylow : CFSG.ABGLocalTools.IsSylowOf 3 A HG := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hA_le_HG, hAab.isPGroup, hnotdvd⟩
  refine ⟨Case811Sylow.mk P A hP hP_L hA_le_P hAab hAcard hA_unique ?_⟩
  intro x hxM hxord
  obtain ⟨m₁, hm₁M, hm₁x⟩ :=
    CFSG.RankThree.PartOne.exists_conj_mem_of_isSylowOf hP hxM ⟨1, by rw [hxord]; norm_num⟩
  let y : G := m₁ * x * m₁⁻¹
  have hyP : y ∈ P := hm₁x
  have hyL : y ∈ c.L := hP_L hyP
  have hy3 : y ^ 3 = 1 := by
    have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    dsimp [y]
    rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hyne : y ≠ 1 := by
    intro hy1
    have hx1 : x = 1 := by
      have h : m₁ * x * m₁⁻¹ = 1 := hy1
      calc x = m₁⁻¹ * (m₁ * x * m₁⁻¹) * m₁ := by group
        _ = 1 := by rw [h]; group
    have : orderOf x = 1 := by rw [hx1]; exact orderOf_one
    omega
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hyne
  let ybar : Lbar := π ⟨y, hyL⟩
  have hybar3 : ybar ^ 3 = 1 := by
    have hsub : (⟨y, hyL⟩ : ↥c.L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [show ybar = π ⟨y, hyL⟩ from rfl, ← map_pow, hsub, map_one]
  have hybar_ne : ybar ≠ 1 := by
    intro h1
    have hyN : (⟨y, hyL⟩ : ↥c.L) ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (⟨y, hyL⟩)).1 h1
    have hyQ : (⟨y, hyL⟩ : ↥c.L) ∈ Q := Subgroup.mem_subgroupOf.mpr hyP
    have hdisjQN : Q ⊓ N = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q N hQ3 hN2).eq_bot
    have hybot : (⟨y, hyL⟩ : ↥c.L) ∈ Q ⊓ N := ⟨hyQ, hyN⟩
    rw [hdisjQN, Subgroup.mem_bot] at hybot
    exact hyne (Subtype.ext_iff.mp hybot)
  have hybar_ord : orderOf ybar = 3 := orderOf_eq_prime hybar3 hybar_ne
  obtain ⟨g, hg⟩ := hb Abar hAbar.2.1 hAbar.2.2 ybar hybar_ord
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective N g
  let z : G := (g₀ : G) * y * (g₀ : G)⁻¹
  have hzL : z ∈ c.L := c.L.mul_mem (c.L.mul_mem g₀.2 hyL) (c.L.inv_mem g₀.2)
  have hzAbar : π ⟨z, hzL⟩ ∈ Abar := by
    have h1 : π ⟨z, hzL⟩ = g * ybar * g⁻¹ := by
      rw [show (⟨z, hzL⟩ : ↥c.L) = g₀ * ⟨y, hyL⟩ * g₀⁻¹ by
        ext
        simp [z]]
      rw [map_mul, map_mul, map_inv, hg₀]
    rw [h1]
    exact hg
  have hzH : z ∈ HG :=
    Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, Subgroup.mem_comap.mpr hzAbar, rfl⟩
  have hz3 : z ^ 3 = 1 := by
    dsimp [z]
    rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hzne : z ≠ 1 := by
    intro hz1
    have hy1 : y = 1 := by
      have h : (g₀ : G)⁻¹ * z * (g₀ : G) = y := by dsimp [z]; group
      rw [hz1] at h
      simpa using h.symm
    exact hyne hy1
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hzne
  obtain ⟨h, hhH, hhz⟩ :=
    CFSG.RankThree.PartOne.exists_conj_mem_of_isSylowOf hAsylow hzH ⟨1, by rw [hzord]; norm_num⟩
  have hhL : h ∈ c.L := Subgroup.map_subtype_le H hhH
  refine ⟨h * (g₀ : G) * m₁, ?_, ?_⟩
  · exact D.M.mul_mem (D.M.mul_mem (c.hyp81.1 hhL) (c.hyp81.1 g₀.2)) hm₁M
  · have hfinal : (h * (g₀ : G) * m₁) * x * (h * (g₀ : G) * m₁)⁻¹ = h * z * h⁻¹ := by
      dsimp [z, y]
      group
    rw [hfinal]
    exact hhz

theorem exists_case811Sylow_of_K6 (c : Ctx82E3 D) (hK6a : K6a) (hK6b : K6b)
    {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) fam r f)
    (hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L) :
    Nonempty (Case811Sylow c) :=
  exists_case811Sylow c
    (fun P => hK6a (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) fam r f hlie P)
    (fun A hA hA27 x hx =>
      hK6b (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) fam r f hlie A hA hA27 x hx)
    hPL

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
