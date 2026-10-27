module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSecMul
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SecNatRealizes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.Quasithin.Background.RonanF918FiveD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem realizes_of_surjHom {V W' : Type} [CommGroup V] [CommGroup W'] {D : FFModel}
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {K : Subgroup (MulAut W')}
    (hZU : Z ≤ U) (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z)
    (j : ↥U →* W') (hj : Function.Surjective j) (hjk : ∀ u : ↥U, j u = 1 ↔ (u : V) ∈ Z)
    (r : ↥H ≃* ↥K)
    (hr : ∀ (h : ↥H) (u : ↥U),
      ((r h : ↥K) : MulAut W') (j u) = j ⟨(h : MulAut V) u, hU _ h.2 _ u.2⟩)
    (hK : D.Realizes K ⊤ ⊥) : D.Realizes H U Z := by
  obtain ⟨π, hπs, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := hK
  let jt : ↥U →* ↥(⊤ : Subgroup W') := j.codRestrict ⊤ fun _ => Subgroup.mem_top _
  have hU' : ∀ h : ↥H, ∀ u ∈ U, ((h : MulAut V)) u ∈ U := fun h u hu => hU h h.2 u hu
  have hZ' : ∀ h : ↥H, ∀ z ∈ Z, ((h : MulAut V)) z ∈ Z := fun h z hz => hZ h h.2 z hz
  refine ⟨r.symm.toMonoidHom.comp π, r.symm.surjective.comp hπs, hZU, hks, hU', hZ', hsec, hker,
    β.comp jt, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨w, hw⟩ := hβs y
    obtain ⟨u, hu⟩ := hj (w : W')
    refine ⟨u, ?_⟩
    change β (jt u) = y
    have e : jt u = w := Subtype.ext hu
    rw [e, hw]
  · intro u
    change β (jt u) = 1 ↔ (u : V) ∈ Z
    rw [hβk, Subgroup.mem_bot]
    exact hjk u
  · intro γ u m hu hm hβu
    have e1 : ((r (r.symm (π γ)) : ↥K) : MulAut W') = π γ := by
      rw [MulEquiv.apply_symm_apply]
    have e2 : jt ⟨((r.symm (π γ) : ↥H) : MulAut V) (u : V), hu⟩ =
        ⟨((π γ : ↥K) : MulAut W') (jt u : W'), Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      change j ⟨((r.symm (π γ) : ↥H) : MulAut V) (u : V), hu⟩ =
        ((π γ : ↥K) : MulAut W') (j u)
      rw [← e1, hr]
    change β (jt ⟨((r.symm (π γ) : ↥H) : MulAut V) (u : V), hu⟩) = _
    rw [e2]
    exact hβe γ (jt u) m (Subgroup.mem_top _) hm hβu

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]

noncomputable abbrev wRep (Y : Subgroup (MulAut W)) :
    Representation (ZMod 2) ↥Y (Additive W) :=
  (CFSG.RankThree.FFModules.autRep W).comp Y.subtype

noncomputable abbrev wU (Y L : Subgroup (MulAut W)) : Submodule (ZMod 2) (Additive W) :=
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commOn (wRep Y) (L.subgroupOf Y) ⊤

noncomputable abbrev wX (Y L : Subgroup (MulAut W)) : Submodule (ZMod 2) (Additive W) :=
  wU Y L ⊓ CFSG.RankThree.FFModules.fixSub (wRep Y) (L.subgroupOf Y)

private theorem mem_wU_iff {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (w : W) :
    Additive.ofMul w ∈ wU Y L ↔ w ∈ commV L := by
  rw [wU, CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_commOn_autRep_comp Y.subtype
      (L.subgroupOf Y) w, Subgroup.map_subgroupOf_eq_of_le hLY, commV_eq_commSub]

private theorem mem_wX_iff {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (w : W) :
    Additive.ofMul w ∈ wX Y L ↔ w ∈ commV L ⊓ fixV L := by
  rw [wX, Submodule.mem_inf, mem_wU_iff hLY,
    CFSG.RankThree.FFModules.mem_fixSub_autRep_comp Y.subtype (L.subgroupOf Y)
      (Additive.ofMul w), Subgroup.map_subgroupOf_eq_of_le hLY, toMul_ofMul,
    Subgroup.mem_inf]

private theorem mem_toZModSubmodule_toAddSubgroup {J : Subgroup W} {w : W} :
    Additive.ofMul w ∈ AddSubgroup.toZModSubmodule 2 J.toAddSubgroup ↔ w ∈ J := by
  rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, toMul_ofMul]

private theorem isInvariant_wU {Y L : Subgroup (MulAut W)} :
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y) (L.subgroupOf Y)
      (wU Y L) :=
  (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.invariant_commOn_top
    (ρ := wRep Y) (A := L.subgroupOf Y) (L := L.subgroupOf Y)
    Subgroup.le_normalizer).1

theorem ffSetup [Finite W] {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hA : ∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) :
    Function.Injective (wRep Y) ∧ IsComponentOf (L.subgroupOf Y) ⊤ ∧
      ∃ A' : Subgroup ↥Y, A' ∈ UC22.Ext.calP (wRep Y) ∧ ⁅L.subgroupOf Y, A'⁆ ≠ ⊥ := by
  classical
  have hρ : Function.Injective (wRep Y) :=
    CFSG.RankThree.FFModules.autRep_injective.comp Y.subtype_injective
  have hcomp' : IsComponentOf (L.subgroupOf Y) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib hL.2.1.subgroupOf,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.2⟩
  obtain ⟨A, hA, hAL⟩ := hA
  let A' : Subgroup ↥Y := A.subgroupOf Y
  have hAmap : A'.map Y.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hrep : CFSG.RankThree.FFModules.repMulAut (wRep Y) = Y.subtype := by
    ext y w
    rfl
  have hAcal : A' ∈ UC22.Ext.calP (wRep Y) := by
    rw [UC22.K148.mem_calP_iff]
    have hiff := CFSG.RankThree.FFModules.isFFStarOffender_map_iff hρ
      (A := A') (Y := Y) (by rw [hrep]; exact hAmap.le.trans hA.1)
    rw [hrep] at hiff
    have hA' : IsFFStarOffender Y (A'.map Y.subtype) := hAmap ▸ hA
    exact hiff.1 hA'
  have hAL' : ⁅L.subgroupOf Y, A'⁆ ≠ ⊥ := by
    intro hbot
    apply hAL
    have hmap := Subgroup.map_commutator (H₁ := L.subgroupOf Y) (H₂ := A') Y.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hL.1, hAmap, hbot, Subgroup.map_bot] at hmap
    simpa [Subgroup.commutator_comm] using hmap.symm
  exact ⟨hρ, hcomp', ⟨A', hAcal, hAL'⟩⟩

theorem exists_commVSecMap [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) {H : Subgroup ↥Y}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y) H (wU Y L))
    (hX : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y) H (wX Y L)) :
    ∃ j : ↥(commV L) →* Multiplicative (K148.SecQ (wU Y L) (wX Y L)),
      Function.Surjective j ∧ (∀ u, j u = 1 ↔ (u : W) ∈ commV L ⊓ fixV L) ∧
      ∀ (h : ↥H) (u v : ↥(commV L)), (v : W) = ((h : ↥Y) : MulAut W) u →
        j v = secMul hU hX h (j u) := by
  classical
  let mkU : ↥(commV L) → ↥(wU Y L) := fun u =>
    ⟨Additive.ofMul (u : W), (mem_wU_iff hLY (u : W)).2 u.2⟩
  let j : ↥(commV L) →* Multiplicative (K148.SecQ (wU Y L) (wX Y L)) :=
    { toFun := fun u => Multiplicative.ofAdd (Submodule.Quotient.mk (mkU u))
      map_one' := by
        apply Multiplicative.toAdd.injective
        show Submodule.Quotient.mk (mkU 1) = 0
        rw [← Submodule.Quotient.mk_zero]
        congr 1
      map_mul' := by
        intro a b
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd, toAdd_mul]
        show Submodule.Quotient.mk (mkU (a * b)) =
          Submodule.Quotient.mk (mkU a) + Submodule.Quotient.mk (mkU b)
        rw [← Submodule.Quotient.mk_add]
        congr 1 }
  refine ⟨j, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
      (p := (wX Y L).comap (wU Y L).subtype) (Multiplicative.toAdd q)
    refine ⟨⟨Additive.toMul (x : Additive W), (mem_wU_iff hLY _).1 x.2⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    show Submodule.Quotient.mk (mkU ⟨Additive.toMul (x : Additive W), _⟩) =
      Multiplicative.toAdd q
    rw [show mkU ⟨Additive.toMul (x : Additive W), _⟩ = x from
      Subtype.ext (ofMul_toMul (x : Additive W)), hx]
  · intro u
    constructor
    · intro hu
      have h0 : Submodule.Quotient.mk
          (p := (wX Y L).comap (wU Y L).subtype) (mkU u) = 0 :=
        congrArg Multiplicative.toAdd hu
      rw [Submodule.Quotient.mk_eq_zero] at h0
      exact (mem_wX_iff hLY (u : W)).1 h0
    · intro hu
      apply Multiplicative.toAdd.injective
      show Submodule.Quotient.mk (mkU u) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact (mem_wX_iff hLY (u : W)).2 hu
  · intro h u v hv
    apply Multiplicative.toAdd.injective
    show Submodule.Quotient.mk (mkU v) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.K148.secHom hU hX h
        (Submodule.Quotient.mk (mkU u))
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.K148.secHom_mk]
    congr 1
    apply Subtype.ext
    show Additive.ofMul (v : W) =
      ((CFSG.RankThree.FFModules.autRep W) ((h : ↥Y) : MulAut W)) (Additive.ofMul (u : W))
    rw [CFSG.RankThree.FFModules.autRep_apply, toMul_ofMul, hv]

theorem ffSec_realizes [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    [IsSimpleGroup ↥(L.subgroupOf Y)] {H : Subgroup ↥Y} (hLH : L.subgroupOf Y ≤ H)
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y) H (wU Y L))
    (hX : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y) H (wX Y L))
    (hnt : ∃ l ∈ L.subgroupOf Y, ∃ y ∈ wU Y L, wRep Y l y - y ∉ wX Y L)
    {D : FFModel} (hD : D.Realizes (secMulImg hU hX (L.subgroupOf Y)) ⊤ ⊥) :
    D.Realizes L (commV L) (commV L ⊓ fixV L) := by
  classical
  obtain ⟨j, hj, hjk, hjeq⟩ := exists_commVSecMap hLY hU hX
  let r : ↥L ≃* ↥(secMulImg hU hX (L.subgroupOf Y)) :=
    (Subgroup.subgroupOfEquivOfLe hLY).symm.trans (secMulEquiv hLH hU hX hnt)
  have hUmem : ∀ (h : ↥L) (u : ↥(commV L)), (h : MulAut W) (u : W) ∈ commV L :=
    fun h u => CFSG.Quasithin.RonanF918.apply_mem_commV (Subgroup.le_normalizer h.2) u.2
  have hZmem : ∀ (h : ↥L) (z : ↥(commV L ⊓ fixV L)),
      (h : MulAut W) (z : W) ∈ commV L ⊓ fixV L :=
    fun h z => ⟨hUmem h ⟨z.1, z.2.1⟩, isInv_fixV L h h.2 (z : W) z.2.2⟩
  refine realizes_of_surjHom (V := W) (W' := Multiplicative (K148.SecQ (wU Y L) (wX Y L)))
    (D := D) (H := L) (U := commV L) (Z := commV L ⊓ fixV L)
    (K := secMulImg hU hX (L.subgroupOf Y)) inf_le_left ?_ ?_ j hj hjk r ?_ hD
  · intro h hh u hu
    exact CFSG.Quasithin.RonanF918.apply_mem_commV (Subgroup.le_normalizer hh) hu
  · intro h hh z hz
    exact hZmem ⟨h, hh⟩ ⟨z, hz⟩
  · intro h u
    let l : ↥(L.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hLY).symm h
    let v : ↥(commV L) := ⟨(h : MulAut W) (u : W), hUmem h u⟩
    have hl : ((l : ↥Y) : MulAut W) = (h : MulAut W) := rfl
    have hv : (v : W) = (((Subgroup.inclusion hLH l : ↥H) : ↥Y) : MulAut W) (u : W) := by
      show (h : MulAut W) (u : W) = ((l : ↥Y) : MulAut W) (u : W)
      rw [hl]
    have h1 : j v = secMul hU hX (Subgroup.inclusion hLH l) (j u) := hjeq _ u v hv
    have h2 : ((r h : ↥(secMulImg hU hX (L.subgroupOf Y))) :
        MulAut (Multiplicative (K148.SecQ (wU Y L) (wX Y L)))) =
        secMul hU hX (Subgroup.inclusion hLH l) := by
      change ((secMulEquiv hLH hU hX hnt l : ↥(secMulImg hU hX (L.subgroupOf Y))) :
        MulAut (Multiplicative (K148.SecQ (wU Y L) (wX Y L)))) =
        secMul hU hX (Subgroup.inclusion hLH l)
      rw [secMulEquiv_apply]
    calc ((r h : ↥(secMulImg hU hX (L.subgroupOf Y))) :
          MulAut (Multiplicative (K148.SecQ (wU Y L) (wX Y L)))) (j u)
        = secMul hU hX (Subgroup.inclusion hLH l) (j u) := by rw [h2]
      _ = j v := h1.symm

private theorem commV_inf_fixV_lt {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hnt : ∃ l ∈ L.subgroupOf Y, ∃ y ∈ wU Y L, wRep Y l y - y ∉ wX Y L) :
    commV L ⊓ fixV L < commV L := by
  rw [lt_iff_le_and_ne]
  refine ⟨inf_le_left, ?_⟩
  intro heq
  obtain ⟨l, hl, y, hy, hnot⟩ := hnt
  have hcomm : Additive.toMul (wRep Y l y - y) ∈ commSub (⊤ : Subgroup W) L := by
    have hsub : Additive.toMul (wRep Y l y - y) =
        ((l : ↥Y) : MulAut W) (Additive.toMul y) * (Additive.toMul y)⁻¹ := by
      have h1 : (wRep Y) l y =
          Additive.ofMul (((l : ↥Y) : MulAut W) (Additive.toMul y)) := rfl
      rw [h1, toMul_sub]
      simp only [toMul_ofMul]
      rw [div_eq_mul_inv]
    rw [hsub]
    exact Subgroup.subset_closure ⟨((l : ↥Y) : MulAut W), Subgroup.mem_subgroupOf.mp hl,
      Additive.toMul y, Subgroup.mem_top _, rfl⟩
  have hmem : Additive.toMul (wRep Y l y - y) ∈ commV L := by
    rwa [commV_eq_commSub]
  have hfix : Additive.toMul (wRep Y l y - y) ∈ fixV L := by
    rw [← heq] at hmem
    exact hmem.2
  apply hnot
  have hfixSub : (wRep Y) l y - y ∈
      CFSG.RankThree.FFModules.fixSub (wRep Y) (L.subgroupOf Y) := by
    rw [CFSG.RankThree.FFModules.mem_fixSub_autRep_comp]
    rwa [Subgroup.map_subgroupOf_eq_of_le hLY]
  have hcommU : (wRep Y) l y - y ∈ wU Y L :=
    Submodule.sub_mem _ (isInvariant_wU (l : ↥Y) hl y hy) hy
  exact ⟨hcommU, hfixSub⟩

theorem ffSec_isIrrOn [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hirr : ∀ J : Submodule (ZMod 2) (Additive W),
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y) (L.subgroupOf Y) J →
      wX Y L ≤ J → J ≤ wU Y L → J = wX Y L ∨ J = wU Y L)
    (hnt : ∃ l ∈ L.subgroupOf Y, ∃ y ∈ wU Y L, wRep Y l y - y ∉ wX Y L) :
    IsIrrOn L (commV L) (commV L ⊓ fixV L) := by
  classical
  refine ⟨commV_inf_fixV_lt hLY hnt, ?_, ?_, ?_⟩
  · intro x hx u hu
    exact CFSG.Quasithin.RonanF918.apply_mem_commV (Subgroup.le_normalizer hx) hu
  · intro x hx z hz
    exact ⟨CFSG.Quasithin.RonanF918.apply_mem_commV (Subgroup.le_normalizer hx) hz.1,
      isInv_fixV L x hx (z : W) hz.2⟩
  · intro J hJ hZJ hJU
    have hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (wRep Y)
        (L.subgroupOf Y) (AddSubgroup.toZModSubmodule 2 J.toAddSubgroup) := by
      intro l hl x hx
      rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup] at hx ⊢
      have h := hJ ((l : ↥Y) : MulAut W) (Subgroup.mem_subgroupOf.mp hl)
        (Additive.toMul x) hx
      simpa [wRep, CFSG.RankThree.FFModules.autRep_apply] using h
    have hXJ : wX Y L ≤ AddSubgroup.toZModSubmodule 2 J.toAddSubgroup := by
      intro x hx
      rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
      have hx'' : Additive.ofMul (Additive.toMul x) ∈ wX Y L := by rwa [ofMul_toMul]
      exact hZJ ((mem_wX_iff hLY (Additive.toMul x)).1 hx'')
    have hJU' : AddSubgroup.toZModSubmodule 2 J.toAddSubgroup ≤ wU Y L := by
      intro x hx
      rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup] at hx
      exact (mem_wU_iff hLY (Additive.toMul x)).2 (hJU hx)
    rcases hirr _ hinv hXJ hJU' with h | h
    · left
      ext w
      rw [← mem_toZModSubmodule_toAddSubgroup (J := J) (w := w), ← mem_wX_iff hLY w, h]
    · right
      ext w
      rw [← mem_toZModSubmodule_toAddSubgroup (J := J) (w := w), ← mem_wU_iff hLY w, h]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
