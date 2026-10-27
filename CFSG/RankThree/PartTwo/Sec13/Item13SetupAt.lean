module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.AlphaMonotone
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Transport

variable {G : Type} [Group G] [Finite G] (C : Subgroup G)

@[expose] noncomputable def thetaQuotEquivSub (L' : Subgroup C) :
    L' ⧸ aschbacherSolvableCore 3 L' ≃*
      (L'.map C.subtype) ⧸ aschbacherSolvableCore 3 (L'.map C.subtype) :=
  QuotientGroup.congr _ _ (L'.equivMapOfInjective C.subtype C.subtype_injective)
    (aschbacherSolvableCore_map_mulEquiv Nat.prime_three _)

theorem thetaQuotEquivSub_mk (L' : Subgroup C) (x : L') :
    thetaQuotEquivSub C L' (x : L' ⧸ aschbacherSolvableCore 3 L') =
      ((L'.equivMapOfInjective C.subtype C.subtype_injective x : L'.map C.subtype) :
        (L'.map C.subtype) ⧸ aschbacherSolvableCore 3 (L'.map C.subtype)) :=
  rfl

theorem coe_mem_normalizer_map_iff {L' : Subgroup C} {h : C} :
    (h : G) ∈ Subgroup.normalizer ((L'.map C.subtype : Subgroup G) : Set G) ↔
      h ∈ Subgroup.normalizer (L' : Set C) := by
  constructor
  · intro hN
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : (h : G) * x * (h : G)⁻¹ ∈ L'.map C.subtype :=
      (Subgroup.mem_normalizer_iff.mp hN x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = h * x * h⁻¹ := Subtype.ext hyx
    exact this ▸ hy
  · intro hN
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨h * y * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN y).mp hy, rfl⟩

theorem congr_thetaQuotMulAut_sub (L' : Subgroup C) {h : C}
    (hN : h ∈ Subgroup.normalizer (L' : Set C))
    (hN' : (h : G) ∈ Subgroup.normalizer ((L'.map C.subtype : Subgroup G) : Set G)) :
    MulAut.congr (thetaQuotEquivSub C L')
        (Sec4.thetaQuotMulAut L' (L'.normalizerMonoidHom ⟨h, hN⟩)) =
      Sec4.thetaQuotMulAut (L'.map C.subtype)
        ((L'.map C.subtype).normalizerMonoidHom ⟨h, hN'⟩) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨x, rfl⟩ := (L'.equivMapOfInjective C.subtype C.subtype_injective).surjective y
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← thetaQuotEquivSub_mk,
      MulEquiv.symm_apply_apply, Sec4.thetaQuotMulAut_mk, thetaQuotEquivSub_mk,
      thetaQuotEquivSub_mk, Sec4.thetaQuotMulAut_mk]
    congr 1

theorem map_autThetaQuot_sub (X' L' : Subgroup C) :
    (Sec4.autThetaQuot X' L').map (MulAut.congr (thetaQuotEquivSub C L')).toMonoidHom =
      Sec4.autThetaQuot (X'.map C.subtype) (L'.map C.subtype) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h, hN, hX, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    have hN' := (coe_mem_normalizer_map_iff C).mpr hN
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN', Subgroup.mem_map_of_mem _ hX,
      (congr_thetaQuotMulAut_sub C L' hN hN').symm⟩
  · intro hσ
    obtain ⟨g, hN', ⟨h, hX, rfl⟩, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    have hN := (coe_mem_normalizer_map_iff C).mp hN'
    exact ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, hX, rfl⟩,
      congr_thetaQuotMulAut_sub C L' hN hN'⟩

end Transport

section Kernel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_inSubgroup_theta {L : Subgroup G} {l g : G} (hl : l ∈ L)
    (hg : g ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    l * g * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  obtain ⟨t, ht, rfl⟩ := hg
  exact ⟨⟨l, hl⟩ * t * (⟨l, hl⟩ : L)⁻¹,
    (inferInstance : (aschbacherSolvableCore 3 L).Normal).conj_mem t ht _, rfl⟩

theorem sectionCentralizer_eq_inf {A L : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
  ext a
  change (a ∈ A ∧ ∀ x ∈ L, a * x * a⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) ↔
    a ∈ A ∧ a ∈ Sec4.thetaQuotCentralizer L
  rw [Sec6.mem_thetaQuotCentralizer_iff]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, hAN ha, fun l hl => ?_⟩
    have := conj_mem_inSubgroup_theta (L.inv_mem hl) (h l hl)
    simpa [mul_assoc] using this
  · rintro ⟨ha, -, h⟩
    refine ⟨ha, fun x hx => ?_⟩
    have := conj_mem_inSubgroup_theta hx (h x hx)
    simpa [mul_assoc] using this

theorem card_inf_mul_card_autThetaQuot {A L : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) *
      Nat.card (Sec4.autThetaQuot A L) = Nat.card A := by
  let ρ : A →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp (L.normalizerMonoidHom.comp (Subgroup.inclusion hAN))
  have hrange : ρ.range = Sec4.autThetaQuot A L := by
    ext σ
    rw [MonoidHom.mem_range, Sec4.mem_autThetaQuot_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, hAN a.2, a.2, rfl⟩
    · rintro ⟨h, hN, hA, rfl⟩
      exact ⟨⟨h, hA⟩, rfl⟩
  have hker : Nat.card ρ.ker = Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
    have h1 : ρ.ker = (Sec4.thetaQuotCentralizer L).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro ha
        exact ⟨⟨a, hAN a.2⟩, ha, rfl⟩
      · rintro ⟨y, hy, hya⟩
        have : y = ⟨a, hAN a.2⟩ := Subtype.ext hya
        rw [this] at hy
        exact hy
    rw [h1, ← Subgroup.inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

end Kernel

section Alpha

variable {M : Type*} [Group M] [Finite M]

theorem thetaAlpha_ne_bot_of_le {B N X : Subgroup M} (hBN : B ≤ N) (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (h : thetaAlpha 3 (B.subgroupOf N) ≠ ⊥) :
    thetaAlpha 3 (B.subgroupOf X) ≠ ⊥ := by
  refine thetaAlpha_ne_bot_of_subgroupOf hN (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hBN (Subgroup.mem_subgroupOf.mp hx))) ?_
  let e : (N.subgroupOf X) ≃* N := Subgroup.subgroupOfEquivOfLe hNX
  have he : ((B.subgroupOf X).subgroupOf (N.subgroupOf X)).map e.toMonoidHom =
      B.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp
        (Subgroup.mem_subgroupOf.mp hz))
    · intro hy
      refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_), by simp⟩
      exact Subgroup.mem_subgroupOf.mp hy
  intro hbot
  apply h
  rw [← he, ← thetaAlpha_map_equiv Nat.prime_three, hbot, Subgroup.map_bot]

end Alpha

section Setup

variable {G : Type} [Group G] [Finite G]

theorem autThetaQuot_centralizer_normal (c : G) (L : Subgroup G) :
    ((Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨h, hN, hH, hσ⟩ := Sec4.mem_autThetaQuot_iff.mp g.2
  obtain ⟨k, hkN, hkC, hτ⟩ := Sec4.mem_autThetaQuot_iff.mp hn
  have hkH : k ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_le_normalizer_zpowers c hkC
  have hkC' : h * k * h⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    have := (centralizer_normal_in_normalizer_zpowers c).conj_mem ⟨k, hkH⟩
      (Subgroup.mem_subgroupOf.mpr hkC) ⟨h, hH⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hhkN : h * k * h⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hN hkN) (Subgroup.inv_mem _ hN)
  refine Sec4.mem_autThetaQuot_iff.mpr ⟨h * k * h⁻¹, hhkN, hkC', ?_⟩
  change _ = (g : MulAut (L ⧸ aschbacherSolvableCore 3 L)) * (n : MulAut _) * (g : MulAut _)⁻¹
  rw [← hσ, ← hτ, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem item13SetupAt_of (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) : Item13SetupAt := by
  intro G _ _ hst hS A hAF hAT c hc
  obtain ⟨hcA, hc3, hstar⟩ := zpowers_mem_omegaA_iff.mp hc
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    norm_num at hc3
  have hFE := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hAE : A ∈ partTwoE G := hFE ▸ hAF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha c hcA)
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hsimple := hst.isSimpleGroup
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  have hmax : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'e, fun B hB hAB => ?_⟩
    have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x, hx, rfl⟩ := x
        obtain ⟨_, y, hy, rfl⟩ := y
        apply Subtype.ext
        change (x : G) * y = y * x
        exact congrArg Subtype.val
          (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hB.2 x hx)
    have hAB' : A ≤ B.map C.subtype := fun a ha =>
      ⟨⟨a, hAC ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have hBA := hAF.2.1 _ hBe hAB'
    intro x hx
    have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr this
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
  have hc'Z : c' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  rcases h422 C hS4 A' hmax h27' c' hc'A hc'Z hc'1 with h1 | ⟨L', hL', h9, hα⟩
  · exact absurd h1 hstar
  set L := L'.map C.subtype with hLdef
  have hLc : L ∈ thetaComponentsAt 3 c := ⟨L', hL', rfl⟩
  have hA'N : A' ≤ Subgroup.normalizer (L' : Set C) :=
    h45 C hS4 A' (fun x => ⟨1, Subtype.ext (by simpa using hA'e.2 x x.2)⟩)
      (Or.inr ⟨hA'e, 3, le_rfl, by rw [h27']; norm_num⟩) L' hL'
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    have hmem : (⟨a, hAC ha⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr ha
    exact (coe_mem_normalizer_map_iff C).mpr (hA'N hmem)
  have hAut : Nat.card (Sec4.autThetaQuot A L) = 9 := by
    rw [← hA'map, hLdef, ← map_autThetaQuot_sub C A' L',
      Subgroup.card_map_of_injective (MulAut.congr (thetaQuotEquivSub C L')).injective, h9]
  have hcT : c ∈ Sec4.thetaQuotCentralizer L :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc
  have hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [sectionCentralizer_eq_inf hAN]
    congr 1
    have h3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
      have := card_inf_mul_card_autThetaQuot hAN
      rw [hAut, h27] at this
      omega
    have hcmem : c ∈ A ⊓ Sec4.thetaQuotCentralizer L := Subgroup.mem_inf.mpr ⟨hcA, hcT⟩
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcmem)
      (by rw [h3, hc3])).symm
  have hαC : thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf (Sec4.autThetaQuot C L)) ≠ ⊥ := by
    have hC' : (⊤ : Subgroup C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← (thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr (thetaQuotEquivSub C L'))
      (Sec4.autThetaQuot A' L') (Sec4.autThetaQuot ⊤ L'))] at hα
    rwa [map_autThetaQuot_sub, map_autThetaQuot_sub, hA'map, hC'] at hα
  refine ⟨L, hLc, hAN, hsc, thetaAlpha_ne_bot_of_le (autThetaQuot_mono hAC L)
    (autThetaQuot_mono (centralizer_le_normalizer_zpowers c) L)
    (autThetaQuot_centralizer_normal c L) hαC⟩

end Setup

end CFSG.RankThree.PartTwo.Sec13
