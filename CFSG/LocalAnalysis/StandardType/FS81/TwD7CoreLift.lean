module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.SupCommute
public import CFSG.Mathlib.GroupTheory.FiniteCentralizerImage
public import CFSG.Mathlib.GroupTheory.SectionImage
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import TauCeti.GroupTheory.DerivedCentralQuotient
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Blueprint.Chevalley
open scoped commutatorElement


theorem exists_e7_section_centralizing_core
    {H : Type} [Group H] [Finite H] (R : Subgroup H) [R.Normal]
    (z : H) (hz : z ∈ center H)
    (π : H →* adjointGroup .E7 (ZMod 2)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ R ⊔ zpowers z)
    (a : H) (ha : a ∈ centralizer (R : Set H)) (haπ : π a ≠ 1) :
    ∃ σ : adjointGroup .E7 (ZMod 2) →* H,
      (∀ s, π (σ s) = s) ∧ σ.range ≤ centralizer (R : Set H) ∧ σ.range.Normal ∧
      σ.range = ⁅centralizer (R : Set H), centralizer (R : Set H)⁆ ∧
      ⁅(⊤ : Subgroup H), centralizer (R : Set H)⁆ ≤ σ.range := by
  let S := adjointGroup .E7 (ZMod 2)
  have hSQ : CFSG.IsQuasisimple S := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 (ZMod 2)
  have hZS : center S = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eS : S ⧸ center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZS).trans QuotientGroup.quotientBot
  let : IsSimpleGroup (S ⧸ center S) := hSQ.2.1
  let : IsSimpleGroup S := eS.symm.isSimpleGroup
  let C : Subgroup H := centralizer (R : Set H)
  let : C.Normal := inferInstance
  let : (C.map π).Normal := (inferInstance : C.Normal).map π hπ
  have hmap : C.map π = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map π) with h | h
    · have hm : π a ∈ C.map π := mem_map_of_mem π ha
      rw [h, mem_bot] at hm
      exact False.elim (haπ hm)
    · exact h
  let πC : C →* S := π.comp C.subtype
  have hπC : Function.Surjective πC := by
    rw [← MonoidHom.range_eq_top]
    change (π.comp C.subtype).range = ⊤
    rw [MonoidHom.range_comp, range_subtype, hmap]
  have hRC : R ≤ centralizer (C : Set H) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro c hc
    exact (mem_centralizer_iff.mp hc r hr).symm
  have hZC : zpowers z ≤ centralizer (C : Set H) := by
    refine zpowers_le.mpr ?_
    rw [mem_centralizer_iff]
    intro c hc
    exact mem_center_iff.mp hz c
  have hπCker : πC.ker ≤ center C := by
    intro c hc
    have hcπ : (c : H) ∈ π.ker := hc
    have hcCent : (c : H) ∈ centralizer (C : Set H) := (sup_le hRC hZC) (hker hcπ)
    rw [mem_center_iff]
    intro d
    apply Subtype.ext
    exact mem_centralizer_iff.mp hcCent d d.2
  obtain ⟨-, -, hπD⟩ := CFSG.LocalCores.central_extension_derived_of_surjective
    πC hπC hπCker hSQ.1
  let D : Subgroup C := commutator C
  let πD : D →* S := πC.comp D.subtype
  have hDK : πD.ker ≤ center D := by
    intro d hd
    have hdC : (d : C) ∈ πC.ker := hd
    rw [mem_center_iff]
    intro e
    apply Subtype.ext
    exact mem_center_iff.mp (hπCker hdC) e
  have hKD : πD.ker = center D := le_antisymm hDK
    (MonoidHom.center_le_ker πD hπD hZS)
  let eDQ : D ⧸ center D ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hKD.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective πD hπD)
  let η : D ⧸ center D ≃* S ⧸ center S := eDQ.trans eS.symm
  have hDQ : CFSG.IsQuasisimple D :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective
      πC hπC hπCker hSQ
  have hZD : center D = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7
      hDQ (n := 1) (by decide) (by norm_num) η
  have hπDinj : Function.Injective πD :=
    (MonoidHom.ker_eq_bot_iff πD).mp (hKD.trans hZD)
  let eD : D ≃* S := MulEquiv.ofBijective πD ⟨hπDinj, hπD⟩
  let inc : D →* H := C.subtype.comp D.subtype
  let σ : S →* H := inc.comp eD.symm.toMonoidHom
  have hσ : ∀ s, π (σ s) = s := by
    intro s
    change πD (eD.symm s) = s
    exact eD.apply_symm_apply s
  have hσC : σ.range ≤ C := by
    rintro _ ⟨s, rfl⟩
    exact (eD.symm s).val.property
  have hσrange : σ.range = ⁅C, C⁆ := by
    change (inc.comp eD.symm.toMonoidHom).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eD.symm.surjective, Subgroup.map_top]
    change (C.subtype.comp D.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
    change (commutator C).map C.subtype = _
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, range_subtype]
  have hσN : σ.range.Normal := by
    rw [hσrange]
    infer_instance
  have hZinC : zpowers z ≤ C := by
    refine zpowers_le.mpr ?_
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_center_iff.mp hz r
  have hCker : C ⊔ π.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have hsup : R ⊔ C = ⊤ := by
    apply top_unique
    rw [← hCker]
    exact sup_le le_sup_right (hker.trans (sup_le le_sup_left (hZinC.trans le_sup_right)))
  have hRCcomm : ∀ r ∈ R, ∀ c ∈ C, Commute r c := fun r hr c hc =>
    mem_centralizer_iff.mp hc r hr
  have hHC : ⁅(⊤ : Subgroup H), C⁆ ≤ σ.range := by
    rw [Subgroup.commutator_le]
    intro h hh c hc
    obtain ⟨r, hr, d, hd, hrd⟩ := (CFSG.mem_sup_of_commute hRCcomm).mp (hsup.symm ▸ hh)
    have hdc : ⁅d, c⁆ ∈ C := (commutator_le_self C) (commutator_mem_commutator hd hc)
    have hrDC : Commute r ⁅d, c⁆ := hRCcomm r hr _ hdc
    have heq : ⁅h, c⁆ = ⁅d, c⁆ := by
      rw [← hrd, commutatorElement_mul_left_eq_conj_mul,
        (hRCcomm r hr c hc).commutator_eq, mul_one, hrDC.eq, mul_inv_cancel_right]
    rw [heq, hσrange]
    exact commutator_mem_commutator hd hc
  exact ⟨σ, hσ, hσC, hσN, hσrange, hHC⟩

theorem exists_attached_e7_of_core_quotient
    {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (H : Subgroup G) (hEH : E ≤ H)
    (hCH : centralizer ({B.b 1} : Set G) ⊓ K ≤ H)
    (hHβ : H ≤ centralizer ({b₀ * B.b 1} : Set G))
    (R : Subgroup H) [R.Normal]
    (hRE : R.map H.subtype ≤ centralizer (E : Set G))
    (hRK : R.map H.subtype ≤ centralizer (K : Set G))
    (π : H →* adjointGroup .E7 (ZMod 2)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ R ⊔ (zpowers (b₀ * B.b 1)).subgroupOf H)
    (a : H) (ha : a ∈ centralizer (R : Set H)) (haπ : π a ≠ 1)
    (τ : H) (hτ0 : (τ : G) * B.b 0 * (τ : G)⁻¹ = B.b 1) :
    ∃ J : Subgroup G, J ≤ H ∧ Nonempty (J ≃* adjointGroup .E7 (ZMod 2)) ∧
      Adapted B.twD7Beta (b₀ * B.b 1) J E ∧
      ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J ∧
      J = ⁅H ⊓ centralizer (R.map H.subtype : Set G),
        H ⊓ centralizer (R.map H.subtype : Set G)⁆ ∧
      ∃ η : J ≃* adjointGroup .E7 (ZMod 2),
        ∀ j : J, ∀ hj : (j : G) ∈ H, η j = π ⟨(j : G), hj⟩ := by
  have hb₀E : b₀ ∈ E := hstd.2.1.2.2.1
  have hb₁E : B.b 1 ∈ E := hB.1 ▸ B.b_mem_span 1
  let βH : H := ⟨b₀ * B.b 1, hEH (E.mul_mem hb₀E hb₁E)⟩
  have hβZ : βH ∈ center H := by
    rw [mem_center_iff]
    intro h
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hHβ h.2) (b₀ * B.b 1)
      (Set.mem_singleton (b₀ * B.b 1))).symm
  have hZeq : (zpowers (b₀ * B.b 1)).subgroupOf H = zpowers βH := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (zpowers_le.mpr βH.2), MonoidHom.map_zpowers]
    rfl
  obtain ⟨σ, hσ, -, -, hσD, hHC⟩ := exists_e7_section_centralizing_core R βH hβZ π hπ
    (by simpa only [hZeq] using hker) a ha haπ
  let J : Subgroup G := σ.range.map H.subtype
  have hJH : J ≤ H := Subgroup.map_subtype_le _
  obtain ⟨η, hη⟩ := Subgroup.exists_mulEquiv_map_range_of_leftInverse H σ π hσ
  have heJ : Nonempty (J ≃* adjointGroup .E7 (ZMod 2)) :=
    ⟨η⟩
  let C : Subgroup G := centralizer ({B.b 1} : Set G) ⊓ K
  let CH : Subgroup H := C.subgroupOf H
  have hCHC : CH ≤ centralizer (R : Set H) := by
    intro c hc
    have hcK : (c : G) ∈ K := (Subgroup.mem_subgroupOf.mp hc).2
    rw [mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    have hrG : (r : G) ∈ R.map H.subtype := Subgroup.mem_map_of_mem _ hr
    exact (mem_centralizer_iff.mp (hRK hrG) c hcK).symm
  have hMD : ⁅CH, CH⁆ ≤ σ.range := by
    rw [hσD]
    exact Subgroup.commutator_mono hCHC hCHC
  have hMglobal : ⁅C, C⁆ ≤ J := by
    have hm := Subgroup.map_mono (f := H.subtype) hMD
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hCH] at hm
    exact hm
  let bH : H := ⟨b₀, hEH hb₀E⟩
  have hbHC : bH ∈ centralizer (R : Set H) := by
    rw [mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    have hrG : (r : G) ∈ R.map H.subtype := Subgroup.mem_map_of_mem _ hr
    exact (mem_centralizer_iff.mp (hRE hrG) b₀ hb₀E).symm
  have hβ1H : ⁅τ, bH⁆ ∈ σ.range :=
    hHC (Subgroup.commutator_mem_commutator (Subgroup.mem_top τ) hbHC)
  have hβ1G : B.twD7Beta.b 1 ∈ J := by
    have hm : ((⁅τ, bH⁆ : H) : G) ∈ J := Subgroup.mem_map_of_mem _ hβ1H
    change ((τ : G) * b₀ * (τ : G)⁻¹ * b₀⁻¹) ∈ J at hm
    rw [← hB.2.1, hτ0] at hm
    rw [← (B.comm 0 1).inv_left.eq] at hm
    simpa only [B.twD7Beta_b_one] using hm
  have htail : ∀ i : Fin 6, B.b i.succ.succ ∈ J := fun i =>
    hMglobal (tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec i)
  have hAdapt : Adapted B.twD7Beta (b₀ * B.b 1) J E := by
    refine ⟨B.twD7Beta_span.trans hB.1, ?_, ?_⟩
    · rw [B.twD7Beta_b_zero, hB.2.1]
    · intro i hi
      refine Fin.cases (fun h => False.elim (h rfl)) ?_ i hi
      intro j hj
      refine Fin.cases hβ1G ?_ j
      intro k
      simpa only [B.twD7Beta_b_succ_succ] using htail k
  have hJderived : J = ⁅H ⊓ centralizer (R.map H.subtype : Set G),
      H ⊓ centralizer (R.map H.subtype : Set G)⁆ := by
    dsimp only [J]
    rw [hσD, Subgroup.map_commutator, CFSG.GroupTheory.map_centralizer_subtype]
  exact ⟨J, hJH, heJ, hAdapt, hMglobal, hJderived, η, hη⟩

end CFSG.StandardType.FrameRoute.FS81
