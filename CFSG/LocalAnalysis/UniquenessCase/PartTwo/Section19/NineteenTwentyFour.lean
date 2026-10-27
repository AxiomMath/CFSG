module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.GroupTheory.OddCoreNormalizerOfTI
public import CFSG.GroupTheory.ComponentNormalizerOfTI
public import CFSG.GroupTheory.TISylowNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_twentyfour_one (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    R19_24_1At D V₀ V p L A t B r A₀ H h := by
  change ⁅V₀, Oodd H⁆ = ⊥
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hV0p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV0el
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
  have hV0card : 4 ≤ Nat.card V₀ := by
    have hcard : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV0p
    have hm2 : 2 ≤ mSub V₀ := by have := h.ctx22.ctx.hyp.big; omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) hm2
      _ = Nat.card V₀ := hcard.symm
  have hOleN : Oodd H ≤ normalizer (V₀ : Set G) :=
    CFSG.GroupTheory.pPrimeCore_map_subtype_le_normalizer_of_isTI hV0H hV0el hV0card hTI
  have hOodd_le : Oodd H ≤ H := Subgroup.map_subtype_le _
  have hEq : (Oodd H).subgroupOf H = CFSG.pPrimeCore 2 ↥H := by
    ext x
    simp [Oodd, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hHnormO : H ≤ normalizer (Oodd H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOodd_le).mp (by
      rw [hEq]
      infer_instance)
  have hcommV : ⁅V₀, Oodd H⁆ ≤ V₀ := by
    rw [Subgroup.commutator_le]
    intro v hv m hm
    rw [commutatorElement_def]
    have hmv : m * v⁻¹ * m⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (hOleN hm) v⁻¹).1 (V₀.inv_mem hv)
    have hgroup : v * m * v⁻¹ * m⁻¹ = v * (m * v⁻¹ * m⁻¹) := by group
    rw [hgroup]
    exact V₀.mul_mem hv hmv
  have hcommO : ⁅V₀, Oodd H⁆ ≤ Oodd H := by
    rw [Subgroup.commutator_le]
    intro v hv m hm
    rw [commutatorElement_def]
    exact (Oodd H).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hHnormO (hV0H hv)) m).1 hm) ((Oodd H).inv_mem hm)
  have hinf : V₀ ⊓ Oodd H = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    have hp : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV0p
    have hOodd_card : Nat.card (Oodd H) = Nat.card (CFSG.pPrimeCore 2 ↥H) :=
      Subgroup.card_map_of_injective (K := CFSG.pPrimeCore 2 ↥H) (f := H.subtype)
        H.subtype_injective
    rw [hp, hOodd_card]
    exact CFSG.pPrimeCore_coprime_card.pow_left _
  rw [eq_bot_iff]
  exact (le_inf hcommV hcommO).trans (le_of_eq hinf)

theorem nineteen_twentyfour_two (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    R19_24_2At D V₀ V p L A t B r A₀ H h := by
  change Concl19_24_2 V₀ H
  intro K hKH hKcomp
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
  have hV0card : 4 ≤ Nat.card V₀ := by
    have hcard : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub (CFSG.Open.IsElemAbelian.isPGroup hV0el)
    have hm2 : 2 ≤ mSub V₀ := by have := h.ctx22.ctx.hyp.big; omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) hm2
      _ = Nat.card V₀ := hcard.symm
  let Vh : Subgroup ↥H := V₀.subgroupOf H
  have hVh2 : ∀ v ∈ Vh, v ^ 2 = 1 := by
    intro v hv
    have hv0 : (v : G) ∈ V₀ := hv
    have hv2 : (v : G) ^ 2 = 1 := hV0el.2 (v : G) hv0
    apply Subtype.ext
    simpa using hv2
  have hVhcard : 2 < Nat.card Vh := by
    have hcard : Nat.card Vh = Nat.card V₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV0H).toEquiv
    omega
  have hTIH : CFSG.CGT.Timmesfeld75.IsTI Vh :=
    CFSG.CGT.Timmesfeld75.IsTI.subgroupOf hTI H
  have hCh : ∀ v ∈ Vh, v ≠ 1 →
      Subgroup.centralizer ({v} : Set ↥H) ≤ Subgroup.normalizer (Vh : Set ↥H) := by
    intro v hv hv1
    exact CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTIH hv hv1
  have hN := CFSG.GroupTheory.le_normalizer_of_isComponent_of_centralizer_le
    hVh2 hVhcard hCh hKcomp
  rw [← Subgroup.subgroupOf_normalizer_eq hKH] at hN
  exact CFSG.LocalCores.le_of_subgroupOf_le hV0H hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
