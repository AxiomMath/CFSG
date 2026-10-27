module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType
open scoped Pointwise

theorem ker_le_center_of_simple {A C : Type} [Group A] [Group C]
    (f : A →* C) (hf : Function.Surjective f)
    (hS : IsSimpleGroup (A ⧸ center A)) (hC : ∃ c c' : C, c * c' ≠ c' * c) :
    f.ker ≤ center A := by
  haveI := hS
  haveI : (f.ker.map (QuotientGroup.mk' (center A))).Normal :=
    (inferInstance : f.ker.Normal).map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' (center A))) with
    h | h
  · intro a ha
    have : QuotientGroup.mk' (center A) a ∈ f.ker.map (QuotientGroup.mk' (center A)) :=
      mem_map_of_mem _ ha
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    obtain ⟨c, c', hcc'⟩ := hC
    apply hcc'
    have key : ∀ a : A, ∃ z ∈ center A, f a = f z := by
      intro a
      have : QuotientGroup.mk' (center A) a ∈ f.ker.map (QuotientGroup.mk' (center A)) :=
        h ▸ mem_top _
      obtain ⟨n, hn, hna⟩ := this
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hna
      refine ⟨n⁻¹ * a, hna, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hn, inv_one, one_mul]
    obtain ⟨a, rfl⟩ := hf c
    obtain ⟨a', rfl⟩ := hf c'
    obtain ⟨z, hz, hza⟩ := key a
    rw [hza, ← map_mul, ← map_mul, mem_center_iff.1 hz a']

theorem quotCenter_equiv_of_surjective {A C : Type} [Group A] [Group C]
    (f : A →* C) (hf : Function.Surjective f)
    (hker : f.ker ≤ center A) (hZ : center (A ⧸ center A) = ⊥) :
    Nonempty (C ⧸ center C ≃* A ⧸ center A) := by
  have hc : (center C).comap f = center A := by
    apply le_antisymm
    · intro a ha
      have hZa : (QuotientGroup.mk a : A ⧸ center A) ∈ center (A ⧸ center A) := by
        rw [mem_center_iff]
        intro q
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        apply hker
        rw [MonoidHom.mem_ker]
        have := mem_center_iff.1 (mem_comap.1 ha) (f a')
        simp only [map_mul, map_inv]
        rw [this, inv_mul_cancel]
      rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hZa
      exact hZa
    · intro a ha
      rw [mem_comap, mem_center_iff]
      intro c
      obtain ⟨a', rfl⟩ := hf c
      rw [← map_mul, ← map_mul, mem_center_iff.1 ha a']
  set φ := (QuotientGroup.mk' (center C)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : φ.ker = center A := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hc]
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hφk)⟩

theorem marking_of_surjective {A C : Type} [Group A] [Group C]
    (f : A →* C) (hf : Function.Surjective f)
    (hker : f.ker ≤ center A) {P : LargeEvenMarkProp A}
    (h : CFSG.StandardType.LargeEvenMarking A P) :
    CFSG.StandardType.LargeEvenMarking C (fun _ _ _ _ _ _ => True) := by
  obtain ⟨hA, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hRs, ⟨u, v, huv⟩, θ, -⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  have hnc : ∃ a b : A ⧸ center A, a * b ≠ b * a :=
    ⟨θ.symm u, θ.symm v, fun h' => huv (by simpa [map_mul] using congrArg θ h')⟩
  haveI : IsSimpleGroup (A ⧸ center A) := (MulEquiv.isSimpleGroup_congr θ).2 hRs
  have hZ : center (A ⧸ center A) = ⊥ := center_eq_bot_of_noncomm hnc
  obtain ⟨e⟩ := quotCenter_equiv_of_surjective f hf hker hZ
  refine ⟨?_, lab, hlab, CFSG.StandardType.largeEvenRawDatum_mono ?_ hraw⟩
  · have h1 := congrArg (Subgroup.map f) hA
    rw [_root_.commutator_def, map_commutator, map_top_of_surjective f hf] at h1
    rw [_root_.commutator_def]
    exact h1
  · rintro R' _ I' F' ⟨hs, hna, θ', -⟩
    exact ⟨hs, hna, e.trans θ', trivial⟩

theorem o1pp_marking {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) {K : Subgroup G}
    (hKH : K ≤ centralizer ({x * zn⁻¹} : Set G)) (hXK : X ≤ K) {P : LargeEvenMarkProp K}
    (hmark : CFSG.StandardType.LargeEvenMarking K P) :
    CFSG.StandardType.LargeEvenMarking (O1ppXBar x zn K) (fun _ _ _ _ _ _ => True) := by
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥(centralizer ({x * zn⁻¹} : Set G)))
    with hπ
  set f₀ : K →* O1ppBar x zn := π.comp (inclusion hKH) with hf₀
  have hrange : f₀.range = O1ppXBar x zn K := by
    rw [hf₀, MonoidHom.range_comp, inclusion_range]
  set f : K →* O1ppXBar x zn K :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp f₀.rangeRestrict with hf
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr hrange).surjective.comp f₀.rangeRestrict_surjective
  obtain ⟨-, lab, -, hraw⟩ := id hmark
  obtain ⟨R, _, I, F, hRs, -, θ, -⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  haveI hS : IsSimpleGroup (K ⧸ center K) := (MulEquiv.isSimpleGroup_congr θ).2 hRs
  obtain ⟨⟨a₁, ha₁, b₁, hb₁, hab₁⟩, -⟩ := o1pp_Xbar_facts h
  have hXKb : O1ppXBar x zn X ≤ O1ppXBar x zn K :=
    map_mono fun a ha => mem_subgroupOf.2 (hXK (mem_subgroupOf.1 ha))
  have hC : ∃ c c' : O1ppXBar x zn K, c * c' ≠ c' * c :=
    ⟨⟨a₁, hXKb ha₁⟩, ⟨b₁, hXKb hb₁⟩, fun h' => hab₁ (congrArg Subtype.val h')⟩
  exact marking_of_surjective f hfs (ker_le_center_of_simple f hfs hS hC) hmark

theorem o1pp_cent_of_commutator {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G}
    {x zn : G} (h : O1ppData B x zn L X Xk Tk) {K : Subgroup G}
    (hKH : K ≤ centralizer ({x * zn⁻¹} : Set G))
    (hKs : CFSG.Assembly.IsSubnormal K (centralizer ({x * zn⁻¹} : Set G)))
    (hc : (⁅K, zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 K) :
    O1ppXBar x zn K ≤ centralizer ({o1ppMk x zn x} : Set (O1ppBar x zn)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hxH := o1pp_B_le_H h hxB
  have hKO : LargeEvenPPrimeCoreOf 3 K ≤ CFSG.Open.lBalancePrimeCore 3
      (centralizer ({x * zn⁻¹} : Set G)) := largeEvenPPrimeCoreOf_le_of_isSubnormal hKs
  intro β hβ
  obtain ⟨k, hk, hkH, rfl⟩ := exists_of_mem_bar hβ
  have hcO : k * x * k⁻¹ * x⁻¹ ∈ O1ppCore x zn := by
    have h1 := hKO (hc (commutator_mem_commutator hk (mem_zpowers x)))
    rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map] at h1
    rw [commutatorElement_def] at h1
    exact h1
  have hcH : k * x * k⁻¹ * x⁻¹ ∈ centralizer ({x * zn⁻¹} : Set G) :=
    mul_mem (mul_mem (mul_mem hkH hxH) (inv_mem hkH)) (inv_mem hxH)
  have h1 : o1ppMk x zn (k * x * k⁻¹ * x⁻¹) = 1 := by
    rw [← o1ppMk_one (x := x) (zn := zn)]
    exact (o1ppMk_eq_iff hcH (one_mem _)).2 (by rw [mul_one]; exact inv_mem hcO)
  rw [o1ppMk_mul (mul_mem (mul_mem hkH hxH) (inv_mem hkH)) (inv_mem hxH),
    o1ppMk_mul (mul_mem hkH hxH) (inv_mem hkH), o1ppMk_mul hkH hxH, o1ppMk_inv hkH,
    o1ppMk_inv hxH] at h1
  rw [mem_centralizer_iff]
  rintro _ rfl
  have h2 : o1ppMk x zn k * o1ppMk x zn x * (o1ppMk x zn k)⁻¹ = o1ppMk x zn x :=
    mul_inv_eq_one.1 h1
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem o1pp_false {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn zk : G}
    (hL : GGLBalanceInput) (hI : PumpUpLieInputs)
    (h : O1ppDataK B x zn zk L X Xk Tk) : False := by
  have hPU : GGPumpupInput := ggPumpupInput_of_lBalance hL
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hxH := o1pp_B_le_H h.toO1ppData hxB
  have hDJ := h.stdSub
  have hdD : x * zn⁻¹ ∈ closure {x, zn} :=
    mul_mem (subset_closure (by simp)) (inv_mem (subset_closure (by simp)))
  have hdx : x * zn⁻¹ ∉ zpowers x := fun h1 => h.zn_not_mem (by
    have : zn = (x * zn⁻¹)⁻¹ * x := by group
    rw [this]
    exact mul_mem (inv_mem h1) (mem_zpowers x))
  have hD := eq_closure_pair_of_mem h.hyp hDJ hdD hdx
  have hpJ : 3 ∣ Nat.card X := (o1pp_X_facts u52SimpleSix h.toO1ppData).2.2
  obtain ⟨hKc, hXK, hxK, hcase⟩ := pumpup_of_stdSub hPU h.hyp hDJ hpJ hD
  have hKH : ggLayerClosure 3 (centralizer ({x * zn⁻¹} : Set G)) X ≤
      centralizer ({x * zn⁻¹} : Set G) := hKc.1
  have hKbc : CFSG.Open.IsComponentOf
      (O1ppXBar x zn (ggLayerClosure 3 (centralizer ({x * zn⁻¹} : Set G)) X)) ⊤ :=
    CFSG.Assembly.isComponentOf_iff_open.1 hKc.2.2.1
  have hXKb : O1ppXBar x zn X ≤
      O1ppXBar x zn (ggLayerClosure 3 (centralizer ({x * zn⁻¹} : Set G)) X) :=
    map_mono fun a ha => mem_subgroupOf.2 (hXK (mem_subgroupOf.1 ha))
  have hxKb := o1ppMk_mem_normalizer hxH hxK
  have hXc0 := o1pp_X_comp_cent h
  have hXc : CFSG.Open.IsComponentOf (O1ppXBar x zn X)
      (O1ppXBar x zn (ggLayerClosure 3 (centralizer ({x * zn⁻¹} : Set G)) X) ⊓
        centralizer ({o1ppMk x zn x} : Set (O1ppBar x zn))) :=
    CFSG.Assembly.isComponentOf_iff_open.1
      ((CFSG.Assembly.isComponentOf_iff_open.2 hXc0).of_le_of_le (le_inf hXKb hXc0.1)
        inf_le_right)
  by_cases heq : O1ppXBar x zn X =
      O1ppXBar x zn (ggLayerClosure 3 (centralizer ({x * zn⁻¹} : Set G)) X)
  · exact prop_10_10_not_component_closed h.toO1ppData (heq ▸ hKbc)
  have hlt := lt_of_le_of_ne hXKb heq
  rcases hcase with hnbr | hcomm
  · have hmark := (h.hyp.2.2.2.2.2.2.2.2.2.1 (x * zn⁻¹) _
      (isNeighborOf_of_ggNbr hDJ hnbr)).2
    have hlie := o1pp_marking h.toO1ppData hKH hXK hmark
    obtain ⟨W, Wk, ζ, ξ, Q, A, hA⟩ :=
      pumpUpConfig_aut (o1pp_config h hKbc hxKb hlt hXc hlie)
    exact pumpUpAut_false hI hA
  · have hcent := o1pp_cent_of_commutator h.toO1ppData hKH hKc.2.1 hcomm
    rw [inf_eq_left.2 hcent] at hXc
    exact heq (CFSG.LocalAnalysis.GLTheoremA.S11.y10xF_eq_of_subnormal hKbc.2.2 hXc.1 hXc.2.1
      hXc.2.2)

end CFSG.GGQ2Prime
