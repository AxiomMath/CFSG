module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.GroupTheory.PRankCommutingPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section RsTwo

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

@[expose] def RSchur2_153 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    (UC22.IsAlt (X ⧸ Subgroup.center X) 5 ∨ IsL3 (X ⧸ Subgroup.center X) 1) →
    Subgroup.center X = ⊥

private theorem k2_not_forall_comm_of_isQuasisimple {A : Type} [Group A] [Finite A]
    (hA : CFSG.Open.IsQuasisimple A) : ¬ ∀ a b : A, a * b = b * a := by
  rintro hc
  obtain ⟨-, hsimple⟩ := hA
  haveI := hsimple
  have hcenter : Subgroup.center A = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hc z y).symm
  haveI : Subsingleton (A ⧸ Subgroup.center A) := QuotientGroup.subsingleton_iff.mpr hcenter
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (A ⧸ Subgroup.center A)).exists_pair_ne
  exact hab (Subsingleton.elim a b)

private theorem k2_isComponent_subgroupOf {A : Type} [Group A] {H K : Subgroup A}
    (h : CFSG.Open.IsComponentOf K H) : CFSG.IsComponent (K.subgroupOf H) := by
  rw [CFSG.isComponent_iff_open]
  exact ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

private theorem k2_component_eq_or_commute {A : Type} [Group A] [Finite A]
    {H K L : Subgroup A} (hK : CFSG.Open.IsComponentOf K H)
    (hL : CFSG.Open.IsComponentOf L H) :
    K = L ∨ ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute (k2_isComponent_subgroupOf hK)
    (k2_isComponent_subgroupOf hL) with h | h
  · left
    have h' := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at h'
  · right
    intro a ha b hb
    have ha' : (⟨a, hK.1 ha⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha
    have hb' : (⟨b, hL.1 hb⟩ : ↥H) ∈ L.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
    have hc := Subgroup.commutator_mem_commutator ha' hb'
    rw [h, Subgroup.mem_bot] at hc
    have hcomm : Commute (⟨a, hK.1 ha⟩ : ↥H) ⟨b, hL.1 hb⟩ :=
      commutatorElement_eq_one_iff_commute.mp hc
    exact congrArg Subtype.val hcomm.eq

private theorem k2_iSup_le_normalizer_of_eq_or_comm {A : Type} [Group A] {ι : Type}
    {T : ι → Subgroup A}
    (hcomm : ∀ i j, T i = T j ∨ ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x) (i : ι) :
    (⨆ j, T j) ≤ Subgroup.normalizer (T i : Set A) := by
  refine iSup_le fun j => ?_
  rcases hcomm i j with h | h
  · rw [h]; exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h x hx y hy

private theorem k2_isComponentOf_iSup_of_eq_or_comm {A : Type} [Group A] {ι : Type}
    {T : ι → Subgroup A}
    (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i))
    (hcomm : ∀ i j, T i = T j ∨ ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x) (i : ι) :
    CFSG.Open.IsComponentOf (T i) (⨆ j, T j) := by
  refine ⟨le_iSup T i, ?_, hq i⟩
  exact CFSG.Open.IsSubnormal.step (le_iSup T i)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup T i)).mpr
      (k2_iSup_le_normalizer_of_eq_or_comm hcomm i))
    (CFSG.Open.IsSubnormal.refl _)

private theorem s15_Three_component_eq {A : Type} [Group A] [Finite A]
    {ι : Type} {T : ι → Subgroup A}
    (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i))
    (hcomm : ∀ i j, T i = T j ∨ ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x)
    {B : Subgroup A} (hB : CFSG.Open.IsComponentOf B (⨆ i, T i)) :
    ∃ i, B = T i := by
  by_contra h
  push Not at h
  have hcommB : ∀ i, ∀ b ∈ B, ∀ y ∈ T i, b * y = y * b := fun i =>
    (k2_component_eq_or_commute hB (k2_isComponentOf_iSup_of_eq_or_comm hq hcomm i)).resolve_left
      (h i)
  have hcent : (⨆ i, T i) ≤ Subgroup.centralizer (B : Set A) := by
    refine iSup_le fun i => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcommB i b hb x hx
  have hcommB' : ∀ x y : ↥B, x * y = y * x := by
    intro x y
    have hxsup : (x : A) ∈ ⨆ i, T i := hB.1 x.2
    have h1 := hcent hxsup
    rw [Subgroup.mem_centralizer_iff] at h1
    exact Subtype.ext (h1 y y.2).symm
  exact (k2_not_forall_comm_of_isQuasisimple hB.2.2) hcommB'

private theorem s15_Three_solvable_normal_le_center {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (N : Subgroup Q) (hN : N.Normal) (hs : IsSolvable ↥N) :
    N ≤ Subgroup.center Q := by
  obtain ⟨hperf, hsimple⟩ := hQ
  haveI := hsimple
  let π := QuotientGroup.mk' (Subgroup.center Q)
  have hNbar_normal : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have hNbar_solv : IsSolvable ↥(N.map π) := by
    haveI : Group.IsSolvable ↥N := hs
    let m : ↥N →* ↥(N.map π) :=
      (π.comp N.subtype).codRestrict (N.map π) (fun x => Subgroup.mem_map_of_mem π x.2)
    have hm : Function.Surjective m := by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Group.isSolvable_of_surjective (f := m) hm
  haveI := hNbar_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · rw [Subgroup.map_eq_bot_iff] at h
    rwa [QuotientGroup.ker_mk'] at h
  · haveI : Group.IsSolvable ↥(⊤ : Subgroup (Q ⧸ Subgroup.center Q)) := h ▸ hNbar_solv
    have hQZsolv : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
        (MulEquiv.surjective _)
    have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr hQZsolv
    have hcommutator : commutator Q ≤ Subgroup.center Q := by
      change ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ Subgroup.center Q
      rw [Subgroup.commutator_le]
      intro a _ b _
      have hmem : ⁅a, b⁆ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm (π a) (π b))
      rwa [QuotientGroup.ker_mk'] at hmem
    have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := by
      rw [← hperf]
      exact hcommutator
    rw [top_le_iff.mp htop]
    exact le_top

private theorem s15_Three_quot_center_iso {Q T : Type} [Group Q] [Group T] (π : Q →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Q)
    (hT : Subgroup.center T = ⊥) : Nonempty ((Q ⧸ Subgroup.center Q) ≃* T) := by
  have hZker : Subgroup.center Q ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzT : π z ∈ Subgroup.center T :=
      Subgroup.map_center_le_center hπ (Subgroup.mem_map_of_mem π hz)
    rwa [hT, Subgroup.mem_bot] at hzT
  have hker_eq : π.ker = Subgroup.center Q := le_antisymm hker hZker
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩

private theorem s15_Three_barLift_exists (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥) :
    ∃ ψ : Bar2 Y →* MulAut (Vtil V₀ V hV),
      ∀ y : ↥Y, ψ (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hY y.2⟩ := by
  let f : ↥Y →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hY)
  have hker : CFSG.pCore 2 ↥Y ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 Y := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hY x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 Y) :=
      actTil_mem_barSub V₀ V hV hxP (hY x.2)
    rw [h2, Subgroup.mem_bot] at h1
    exact h1
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥Y) f hker, ?_⟩
  intro y
  rfl

private theorem s15_Three_barSub_comap_map (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ stabTil V₀ V) (ψ : Bar2 Y →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ y : ↥Y, ψ (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hY y.2⟩)
    (C : Subgroup (Bar2 Y)) :
    barSub V₀ V hV ((C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype) =
      C.map ψ := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
    obtain ⟨y, hyC, hyg⟩ := Subgroup.mem_map.1 hg
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y, hyC, ?_⟩
    change ψ (QuotientGroup.mk y) = actTil V₀ V hV g
    rw [hψ y]
    exact congrArg (actTil V₀ V hV) (Subtype.ext (by
      change y.1 = (g : G)
      exact hyg))
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) c
    refine (mem_barSub V₀ V hV _ (ψ c)).2 ⟨⟨(y : G), hY y.2⟩, ?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_comap, hy]
      exact hc
    · change actTil V₀ V hV ⟨(y : G), hY y.2⟩ = ψ c
      rw [← hy]
      change actTil V₀ V hV ⟨(y : G), hY y.2⟩ = ψ (QuotientGroup.mk y)
      rw [hψ y]

private theorem k2_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    QuotientGroup.mk'_surjective _
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [hYE, hTop]
  have h := Subgroup.map_comap_eq_self_of_surjective hπ
    (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
  rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
  exact h.symm

private theorem k2_map_component_eq_bot_or_isComponentOf {D : Data G} {V₀ V K₀ : Subgroup G}
    {Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (ψ : Bar2 Y →* MulAut (Vtil V₀ V hV))
    (hXbar : (⊤ : Subgroup (Bar2 Y)).map ψ = s15XBar D V₀ V hV K₀)
    {C : Subgroup (Bar2 Y)} (hC : CFSG.Open.IsComponentOf C ⊤) :
    C.map ψ = ⊥ ∨ CFSG.Open.IsComponentOf (C.map ψ) (s15XBar D V₀ V hV K₀) := by
  by_cases hCbot : C.map ψ = ⊥
  · exact Or.inl hCbot
  · right
    have hqC : CFSG.Open.IsQuasisimple ↥(C.map ψ) := by
      let f : ↥C →* ↥(C.map ψ) :=
        (ψ.comp C.subtype).codRestrict (C.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
      have hf : Function.Surjective f := by
        rintro ⟨z, hz⟩
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
        exact ⟨⟨c, hc⟩, rfl⟩
      haveI : Nontrivial ↥(C.map ψ) := (Subgroup.nontrivial_iff_ne_bot _).2 hCbot
      exact uc22br4_isQuasisimple_of_surjective hC.2.2 f hf
    refine ⟨?_, ?_, hqC⟩
    · rw [← hXbar]
      rintro φ ⟨c, hc, rfl⟩
      exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_top c, rfl⟩
    · have hsub := A3.subnormal_map ψ hC.2.1
      rwa [hXbar] at hsub

private theorem s15_Three_le_stabTil (h : Hyp151 D V₀ V L) : D.M ≤ stabTil V₀ V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀

private theorem s15_Three_isQuasisimple_conj (hV : IsElemAbelian 2 V) (h : Hyp151 D V₀ V L)
    (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀)) {m : G} (hm : m ∈ D.M)
    (hK : K₀ ≤ D.M) :
    CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV (conjSubgroup K₀ m)) := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  rw [s15_Three_barSub_conj_eq hV hMs hK hm]
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    ((barSub V₀ V hV K₀).equivMapOfInjective _ (MulAut.conj _).injective).symm hq

private theorem s15_Three_center_eq_bot_of_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : Subgroup.center A = ⊥) : Subgroup.center B = ⊥ := by
  have h1 : (Subgroup.center B).map e.symm.toMonoidHom ≤ Subgroup.center A :=
    Subgroup.map_center_le_center (f := e.symm.toMonoidHom) e.symm.surjective
  rw [h] at h1
  have h2 : (Subgroup.center B).map e.symm.toMonoidHom = ⊥ := le_bot_iff.1 h1
  rw [Subgroup.map_eq_bot_iff,
    MonoidHom.ker_eq_bot e.symm.toMonoidHom e.symm.injective] at h2
  exact le_bot_iff.1 h2

private theorem s15_Three_component_cover_conj (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀))
    {Y : Subgroup G} (hYM : CFSG.Open.IsSubnormal Y D.M) (hYE : F11.O2E Y = Y)
    (hYX : barSub V₀ V hV Y = s15XBar D V₀ V hV K₀)
    {m₀ : G} (hm₀ : m₀ ∈ D.M) :
    ∃ C : Subgroup (Bar2 Y), CFSG.Open.IsComponentOf C ⊤ ∧
      barSub V₀ V hV ((C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype) =
        barSub V₀ V hV (conjSubgroup K₀ m₀) := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  have hYs : Y ≤ stabTil V₀ V := hYM.le.trans hMs
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hYM
      (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
  obtain ⟨ψ, hψ⟩ := s15_Three_barLift_exists hV hYs h2
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hXmap : (⊤ : Subgroup (Bar2 Y)).map ψ = s15XBar D V₀ V hV K₀ := by
    have h := s15_Three_barSub_comap_map hV hYs ψ hψ ⊤
    rw [Subgroup.comap_top, hTop] at h
    rw [← hYX]; exact h.symm
  have hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ :=
    k2_layer_top_of_O2E_eq hYE
  have hsup : s15XBar D V₀ V hV K₀ =
      ⨆ C ∈ {C : Subgroup (Bar2 Y) | CFSG.Open.IsComponentOf C ⊤}, C.map ψ := by
    rw [hXmap.symm]
    conv_lhs => rw [← hlayer]
    rw [CFSG.Open.rankThreeLayer, sSup_eq_iSup]
    simp only [Subgroup.map_iSup]
  let T : ↥D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup K₀ (m : G))
  have hXbar_eq : s15XBar D V₀ V hV K₀ = ⨆ m : ↥D.M, T m := by
    unfold s15XBar
    refine le_antisymm ?_ ?_
    · refine iSup_le fun m => iSup_le fun hm => le_iSup T ⟨m, hm⟩
    · refine iSup_le fun m => le_iSup₂_of_le (m : G) m.2 le_rfl
  have hqA : ∀ m : ↥D.M, CFSG.Open.IsQuasisimple ↥(T m) := by
    intro m
    have hKs : K₀ ≤ stabTil V₀ V := hshape.1.trans (h.le.trans hMs)
    have hgm : (m : G)⁻¹ ∈ stabTil V₀ V := hMs (D.M.inv_mem m.2)
    have hconj : T m = (barSub V₀ V hV K₀).map
        (MulAut.conj (actTil V₀ V hV ⟨(m : G)⁻¹, hgm⟩)).toMonoidHom :=
      TwelveTwentyThree.barSub_map_conj hV hKs hgm
    rw [hconj]
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      ((barSub V₀ V hV K₀).equivMapOfInjective _
        (MulAut.conj (actTil V₀ V hV ⟨(m : G)⁻¹, hgm⟩)).injective).symm hq
  have hcommA : ∀ m₁ m₂ : ↥D.M,
      T m₁ = T m₂ ∨ ∀ x ∈ T m₁, ∀ y ∈ T m₂, x * y = y * x :=
    fun m₁ m₂ => s15_Three_xbar_comm h hV hshape m₁.2 m₂.2
  have hex : ∃ C : Subgroup (Bar2 Y), CFSG.Open.IsComponentOf C ⊤ ∧
      C.map ψ = T ⟨m₀, hm₀⟩ := by
    by_contra hcontra
    push Not at hcontra
    have hcentral : s15XBar D V₀ V hV K₀ ≤
        Subgroup.centralizer (T ⟨m₀, hm₀⟩ : Set (MulAut (Vtil V₀ V hV))) := by
      rw [hsup]
      refine iSup_le fun C => iSup_le fun hC => ?_
      rcases k2_map_component_eq_bot_or_isComponentOf hV ψ hXmap hC with hbot | hcomp
      · rw [hbot]; exact bot_le
      · rw [hXbar_eq] at hcomp
        obtain ⟨m, hm⟩ := s15_Three_component_eq hqA hcommA hcomp
        have hTmne : T m ≠ T ⟨m₀, hm₀⟩ := by
          intro heq
          exact hcontra C hC (by rw [hm, heq])
        have hcommm := (hcommA m ⟨m₀, hm₀⟩).resolve_left hTmne
        rw [hm]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcommm x hx y hy).symm
    have hTleX : T ⟨m₀, hm₀⟩ ≤ s15XBar D V₀ V hV K₀ := by
      rw [hXbar_eq]
      exact le_iSup T ⟨m₀, hm₀⟩
    have hcommK : ∀ x y : ↥(T ⟨m₀, hm₀⟩), x * y = y * x := by
      intro x y
      have hxX : (x : MulAut (Vtil V₀ V hV)) ∈ s15XBar D V₀ V hV K₀ := hTleX x.2
      have h1 := hcentral hxX
      rw [Subgroup.mem_centralizer_iff] at h1
      exact Subtype.ext (h1 y y.2).symm
    exact (k2_not_forall_comm_of_isQuasisimple (hqA ⟨m₀, hm₀⟩)) hcommK
  obtain ⟨C, hC, hCmap⟩ := hex
  refine ⟨C, hC, ?_⟩
  rw [s15_Three_barSub_comap_map hV hYs ψ hψ C, hCmap]

private theorem s15_Three_barSub_core_eq_map (hV : IsElemAbelian 2 V) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hYKstab : Y ≤ stabTil V₀ V)
    (ψ : Bar2 Y →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ y : ↥Y, ψ (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hYKstab y.2⟩)
    {C : Subgroup (Bar2 Y)}
    (hKmap : (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C) :
    barSub V₀ V hV K = C.map ψ := by
  rw [← hKmap]
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_barSub V₀ V hV K φ).1 hφ
    have hgY : (g : G) ∈ Y := hKY hgK
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨(g : G), hgY⟩, ?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨⟨(g : G), hgY⟩, ?_, rfl⟩
      exact (Subgroup.mem_subgroupOf).2 hgK
    · change ψ (QuotientGroup.mk ⟨(g : G), hgY⟩) = actTil V₀ V hV g
      rw [hψ ⟨(g : G), hgY⟩]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hc
    have hyK : (y : G) ∈ K := (Subgroup.mem_subgroupOf).1 hy
    refine (mem_barSub V₀ V hV K (ψ c)).2 ⟨⟨(y : G), hYKstab y.2⟩, hyK, ?_⟩
    change actTil V₀ V hV ⟨(y : G), hYKstab y.2⟩ = ψ c
    rw [← hyc]
    change actTil V₀ V hV ⟨(y : G), hYKstab y.2⟩ = ψ (QuotientGroup.mk y)
    rw [hψ y]

private theorem s15_Three_component_normal {A : Type} [Group A] [Finite A] {C : Subgroup A}
    (hC : CFSG.Open.IsComponentOf C ⊤) (hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup A) = ⊤) :
    C.Normal := by
  have hle : (⊤ : Subgroup A) ≤ Subgroup.normalizer (C : Set A) := by
    rw [← hlayer, CFSG.Open.rankThreeLayer, sSup_eq_iSup]
    refine iSup_le fun D => iSup_le fun hD => ?_
    rcases k2_component_eq_or_commute hD hC with h | h
    · rw [h]; exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (C : Set A))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (h x hx y hy).symm
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hle)

private theorem s15_Three_one_le_pRank_of_dvd {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card X) : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := X) p hd
  have hle : Subgroup.zpowers h ≤ (⊤ : Subgroup X) := le_top
  have hcard : Nat.card (Subgroup.zpowers h) = p ^ 1 := by
    rw [Nat.card_zpowers, hh, pow_one]
  refine CFSG.SectionRank.le_pRank hp.one_lt hle ?_ hcard
  refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun x hx => ?_⟩
  · refine Subtype.ext ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show (a : X) * (b : X) = (b : X) * (a : X)
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self h i j).eq
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hi]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hh, pow_orderOf_eq_one,
      one_zpow]

private theorem s15_Three_pRank3_eq_one_of_card {X : Type} [Group X] [Finite X]
    (h3 : 3 ∣ Nat.card X) (h9 : ¬ 9 ∣ Nat.card X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
  refine le_antisymm ?_ (s15_Three_one_le_pRank_of_dvd Nat.prime_three h3)
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by omega
  have hle : 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∣ Nat.card X := by
    obtain ⟨E, -, hE, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  exact h9 (by
    have hpow : 3 ^ 2 ∣ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) := Nat.pow_dvd_pow 3 h2
    simpa using hpow.trans hle)

private theorem s15_Three_pRank3_of_L3_or_Alt5 {X : Type} [Group X] [Finite X]
    (h : IsL3 X 1 ∨ UC22.IsAlt X 5) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
  rcases h with h3 | h5
  · refine s15_Three_pRank3_eq_one_of_card ?_ ?_
    · rw [card_eq_of_isL3 h3]; norm_num
    · rw [card_eq_of_isL3 h3]; norm_num
  · obtain ⟨e⟩ := h5
    refine s15_Three_pRank3_eq_one_of_card ?_ ?_
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num [Nat.factorial]
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num [Nat.factorial]

private theorem s15_Three_pRank3_join {A : Type} [Group A] [Finite A]
    {C₁ C₂ C₃ : Subgroup A}
    (h₁ : CFSG.Open.pRank 3 C₁ = 1)
    (hperf₂ : ⁅C₂, C₂⁆ = C₂) (hperf₃ : ⁅C₃, C₃⁆ = C₃)
    (hdiv₂ : 3 ∣ Nat.card C₂) (hdiv₃ : 3 ∣ Nat.card C₃)
    (hc₁₂ : ⁅C₁, C₂⁆ = ⊥) (hc₁₃ : ⁅C₁, C₃⁆ = ⊥) (hc₂₃ : ⁅C₂, C₃⁆ = ⊥) :
    2 < CFSG.Open.pRank 3 (C₁ ⊔ C₂ ⊔ C₃) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcent₁ : C₃ ≤ Subgroup.centralizer (C₁ : Set A) := by
    rw [Subgroup.commutator_comm C₁ C₃] at hc₁₃
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hc₁₃
  have hcent₂ : C₃ ≤ Subgroup.centralizer (C₂ : Set A) := by
    rw [Subgroup.commutator_comm C₂ C₃] at hc₂₃
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hc₂₃
  have hcent : C₃ ≤ Subgroup.centralizer ((C₁ ⊔ C₂ : Subgroup A) : Set A) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le ((Subgroup.le_centralizer_iff).2 hcent₁)
      ((Subgroup.le_centralizer_iff).2 hcent₂)
  have hc : ⁅C₁ ⊔ C₂, C₃⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2 ((Subgroup.le_centralizer_iff).1 hcent)
  have hstep1 : CFSG.Open.pRank 3 C₁ + 1 ≤ CFSG.Open.pRank 3 (C₁ ⊔ C₂) :=
    CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 3) (by norm_num)
      le_sup_left le_sup_right (hc₁₂ ▸ bot_le) hperf₂ hdiv₂
  have hstep2 : CFSG.Open.pRank 3 (C₁ ⊔ C₂) + 1 ≤ CFSG.Open.pRank 3 (C₁ ⊔ C₂ ⊔ C₃) :=
    CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 3) (by norm_num)
      le_sup_left le_sup_right (hc ▸ bot_le) hperf₃ hdiv₃
  omega


section CoreNormal

variable {Y : Subgroup G}

private theorem s15_Three_core_map (C : Subgroup (Bar2 Y)) (hC : ⁅C, C⁆ = C) :
    (perfectCore (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C := by
  have hmap : (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C
  calc (perfectCore (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
      = perfectCore ((C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
        map_perfectCore (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) _
    _ = perfectCore C := by rw [hmap]
    _ = C := (perfectCore_eq_self_iff C).mpr hC

private theorem s15_Three_pCoreOf_eq_inf {K : Subgroup G} (hK : IsSubnormal K Y) :
    pCoreOf 2 K = K ⊓ pCoreOf 2 Y := by
  refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    (A4.pCoreOf_le_of_subnormal 2 hK)) ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_right)
  refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact hK.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)

private theorem s15_Three_ker_eq {K : Subgroup G} (hKY : K ≤ Y) (hK : IsSubnormal K Y) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY)).ker =
      CFSG.pCore 2 ↥K := by
  have hY : (pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y :=
    A4.subgroupOf_map_subtype' Y (CFSG.pCore 2 ↥Y)
  have hK' : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
    A4.subgroupOf_map_subtype' K (CFSG.pCore 2 ↥K)
  have hmemY : ∀ y : ↥Y, y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ pCoreOf 2 Y := by
    intro y
    rw [← hY, Subgroup.mem_subgroupOf]
  have hmemK : ∀ x : ↥K, x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K := by
    intro x
    rw [← hK', Subgroup.mem_subgroupOf]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hmemY (Subgroup.inclusion hKY x), hmemK x,
    s15_Three_pCoreOf_eq_inf hK, Subgroup.coe_inclusion]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩


private theorem s15_Three_core_normal {Y : Subgroup G} {C : Subgroup (Bar2 Y)}
    (hC : CFSG.Open.IsComponentOf C ⊤) (hCn : C.Normal) :
    ∃ K : Subgroup G, K ≤ Y ∧ (K.subgroupOf Y).Normal ∧ CFSG.Open.IsSubnormal K Y ∧
      ⁅K, K⁆ = K ∧ CFSG.Open.IsQuasisimple (Bar2 K) ∧ Nonempty (Bar2 K ≃* ↥C) ∧
      (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let P : Subgroup ↥Y := C.comap π
  let Kt : Subgroup ↥Y := perfectCore P
  let K : Subgroup G := Kt.map Y.subtype
  have hCC : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp ⟨hC.2.2.1⟩
  have hKtmap : Kt.map π = C := s15_Three_core_map C hCC
  have hKsubgroup : K.subgroupOf Y = Kt := A4.subgroupOf_map_subtype' Y Kt
  have hKY : K ≤ Y := Subgroup.map_subtype_le Kt
  have hmapY : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hPsub : CFSG.Open.IsSubnormal P ⊤ := by
    have h := A3.subnormal_comap π hC.2.1
    rw [Subgroup.comap_top] at h
    exact h
  have hKtsub : CFSG.Open.IsSubnormal Kt ⊤ := A3.subnormal_perfectCore hPsub
  have hKsub : CFSG.Open.IsSubnormal K Y := by
    change CFSG.Open.IsSubnormal (Kt.map Y.subtype) Y
    have h := A3.subnormal_map Y.subtype hKtsub
    rwa [hmapY] at h
  have hKK : ⁅K, K⁆ = K := by
    change ⁅(perfectCore P).map Y.subtype, (perfectCore P).map Y.subtype⁆ =
      (perfectCore P).map Y.subtype
    rw [← Subgroup.map_commutator (H₁ := perfectCore P) (H₂ := perfectCore P)
        (f := Y.subtype), perfectCore_perfect P]
  have h_incl : (⊤ : Subgroup ↥K).map (Subgroup.inclusion hKY) = K.subgroupOf Y := by
    rw [Subgroup.map_top, Subgroup.inclusion_range]
  have hφrange : (π.comp (Subgroup.inclusion hKY)).range = C := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, h_incl, hKsubgroup, hKtmap]
  have hker : (π.comp (Subgroup.inclusion hKY)).ker = CFSG.pCore 2 ↥K :=
    s15_Three_ker_eq hKY hKsub
  let e : Bar2 K ≃* ↥C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (π.comp (Subgroup.inclusion hKY))).trans
        (MulEquiv.subgroupCongr hφrange))
  have hKgroup : (K.subgroupOf Y).map π = C := by
    rw [hKsubgroup, hKtmap]
  have hPN : P.Normal := hCn.comap π
  have hKtN : Kt.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp ?_
    rw [eq_top_iff, ← Subgroup.normalizer_eq_top_iff.mpr hPN]
    exact normalizer_le_normalizer_perfectCore P
  have hKN : (K.subgroupOf Y).Normal := by
    rw [hKsubgroup]; exact hKtN
  exact ⟨K, hKY, hKN, hKsub, hKK, CFSG.Open.IsQuasisimple.of_mulEquiv e hC.2.2,
    ⟨e⟩, hKgroup⟩


end CoreNormal

private theorem s15_Three_isL3_or_isAlt_of_mulEquiv {X Z : Type} [Group X] [Group Z]
    (e : X ≃* Z) (h : IsL3 X 1 ∨ UC22.IsAlt X 5) : IsL3 Z 1 ∨ UC22.IsAlt Z 5 := by
  rcases h with h3 | h5
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h3)
  · obtain ⟨e5⟩ := h5
    exact Or.inr ⟨e.symm.trans e5⟩

private theorem s15_Three_pRank3_image {Y L' : Subgroup G} (hL'Y : L' ≤ Y)
    (hN : ¬ 3 ∣ Nat.card ↥(L' ⊓ pCoreOf 2 Y)) :
    CFSG.Open.pRank 3 L' =
      CFSG.Open.pRank 3 ((L'.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥L' →* Bar2 Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hL'Y)
  have hY : (pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y :=
    A4.subgroupOf_map_subtype' Y (CFSG.pCore 2 ↥Y)
  have hmemY : ∀ y : ↥Y, y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ pCoreOf 2 Y := by
    intro y
    rw [← hY, Subgroup.mem_subgroupOf]
  have hker : φ.ker = (L' ⊓ pCoreOf 2 Y).subgroupOf L' := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      simpa only [Subgroup.coe_inclusion] using (hmemY (Subgroup.inclusion hL'Y x)).1 hx
    · rintro ⟨-, hx⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      simpa only [Subgroup.coe_inclusion] using (hmemY (Subgroup.inclusion hL'Y x)).2 hx
  have hN' : ¬ 3 ∣ Nat.card ↥φ.ker := by
    rw [hker]
    exact fun hd => hN (by
      rwa [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : L' ⊓ pCoreOf 2 Y ≤ L')).toEquiv] at hd)
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥L' ⧸ φ.ker)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥L') :=
    CFSG.SectionRank.pRank_quotient_eq φ.ker hN'
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥L' ⧸ φ.ker)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥φ.range) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
      (QuotientGroup.quotientKerEquivRange φ)
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L') = CFSG.Open.pRank 3 L' :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 L').symm.trans
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 L')
  have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥φ.range) = CFSG.Open.pRank 3 φ.range :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 φ.range).symm.trans
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 φ.range)
  have h5 : φ.range = (L'.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.2
        ⟨⟨(x : G), hL'Y x.2⟩, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), (Subgroup.mem_subgroupOf).1 hy⟩, rfl⟩
  calc CFSG.Open.pRank 3 L' = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L') := h3.symm
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup (↥L' ⧸ φ.ker)) := h1.symm
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥φ.range) := h2
    _ = CFSG.Open.pRank 3 φ.range := h4
    _ = CFSG.Open.pRank 3 ((L'.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) := by
        rw [h5]

private theorem s15_Three_pRank3_conj (hV : IsElemAbelian 2 V) (h : Hyp151 D V₀ V L)
    (hK : K₀ ≤ D.M) {m : G} (hm : m ∈ D.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barSub V₀ V hV (conjSubgroup K₀ m))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barSub V₀ V hV K₀)) := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  have hiso : Nonempty (↥(barSub V₀ V hV K₀) ≃*
      ↥(barSub V₀ V hV (conjSubgroup K₀ m))) := by
    rw [s15_Three_barSub_conj_eq hV hMs hK hm]
    exact ⟨(barSub V₀ V hV K₀).equivMapOfInjective _ (MulAut.conj _).injective⟩
  obtain ⟨e⟩ := hiso
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e.symm

private theorem s15_Three_core_rank_one (hS2 : RSchur2_153) (hV : IsElemAbelian 2 V)
    (h : Hyp151 D V₀ V L) (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀))
    (hZ : Subgroup.center ↥(barSub V₀ V hV K₀) = ⊥)
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hMs : D.M ≤ stabTil V₀ V) (hK0M : K₀ ≤ D.M) {Y : Subgroup G}
    (hYMsub : CFSG.Open.IsSubnormal Y D.M)
    (hYC : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y) (hYKstab : Y ≤ stabTil V₀ V)
    (h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥)
    (ψ : Bar2 Y →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ y : ↥Y, ψ (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hYKstab y.2⟩)
    {m : G} (hm : m ∈ D.M) {C : Subgroup (Bar2 Y)} (hC : CFSG.Open.IsComponentOf C ⊤)
    (hCmap : C.map ψ = barSub V₀ V hV (conjSubgroup K₀ m)) {K : Subgroup G}
    (hKY : K ≤ Y) (hKs : CFSG.Open.IsSubnormal K Y) (hKperf : ⁅K, K⁆ = K)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hKmap : (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C) :
    CFSG.Open.pRank 3 K = 1 := by
  have hTq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV (conjSubgroup K₀ m)) :=
    s15_Three_isQuasisimple_conj hV h hq hm hK0M
  have hTiso : Nonempty (↥(barSub V₀ V hV K₀) ≃*
      ↥(barSub V₀ V hV (conjSubgroup K₀ m))) := by
    rw [s15_Three_barSub_conj_eq hV hMs hK0M hm]
    exact ⟨(barSub V₀ V hV K₀).equivMapOfInjective _ (MulAut.conj _).injective⟩
  have hTZ : Subgroup.center ↥(barSub V₀ V hV (conjSubgroup K₀ m)) = ⊥ := by
    obtain ⟨e⟩ := hTiso
    exact s15_Three_center_eq_bot_of_mulEquiv e hZ
  have hKT : barSub V₀ V hV K = barSub V₀ V hV (conjSubgroup K₀ m) :=
    (s15_Three_barSub_core_eq_map hV hKY hYKstab ψ hψ hKmap).trans hCmap
  have hiso : Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃*
      ↥(barSub V₀ V hV (conjSubgroup K₀ m))) :=
    s15_Three_cover_iso (K₀ := conjSubgroup K₀ m) hV hMs hKY hKs hYC hYMsub.le h2
      hKq hTq hTZ hKT
  have hKC : K ∈ calC D.M := ⟨A3.subnormal_trans hKs hYMsub, hKperf, hKq⟩
  have hKodd : Odd (Nat.card (Subgroup.center (Bar2 K))) := (s15_Three_bar2_facts hKC).2
  have hL2' : IsL3 (Bar2 K ⧸ Subgroup.center (Bar2 K)) 1 ∨
      UC22.IsAlt (Bar2 K ⧸ Subgroup.center (Bar2 K)) 5 := by
    obtain ⟨e⟩ := hiso
    have hL2T : IsL3 ↥(barSub V₀ V hV (conjSubgroup K₀ m)) 1 ∨
        UC22.IsAlt ↥(barSub V₀ V hV (conjSubgroup K₀ m)) 5 :=
      s15_Three_isL3_or_isAlt_of_mulEquiv hTiso.some hL2
    exact s15_Three_isL3_or_isAlt_of_mulEquiv e.symm hL2T
  have hZK : Subgroup.center (Bar2 K) = ⊥ :=
    hS2 _ hKq hKodd (hL2'.elim (fun h3 => Or.inr h3) (fun h5 => Or.inl h5))
  have hbar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) = 1 := by
    have hN : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 K)) := by rw [hZK]; norm_num
    have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (Subgroup.center (Bar2 K)) hN
    obtain ⟨e⟩ := hiso
    have h2' := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    have h3 := s15_Three_pRank3_conj hV h hK0M hm
    have h4 := s15_Three_pRank3_of_L3_or_Alt5 hL2
    omega
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥K) (p := 2)).exists_card_eq
    rw [hn]
    intro h3d
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    omega
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) hN
  have h2'' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 3 K :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 K).symm.trans
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 K)
  omega

private theorem s15_Three_map_conj_mul {A : Type} [Group A] (H : Subgroup A) (φ ψ : A) :
    (H.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj ψ).toMonoidHom =
      H.map (MulAut.conj (ψ * φ)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem s15_Three_map_conj_inv_eq_iff {A : Type} [Group A] (X : Subgroup A) (a b : A) :
    X.map (MulAut.conj a⁻¹).toMonoidHom = X.map (MulAut.conj b⁻¹).toMonoidHom ↔
      X.map (MulAut.conj (b * a⁻¹)).toMonoidHom = X := by
  constructor
  · intro h
    have h1 := congrArg (Subgroup.map (MulAut.conj b).toMonoidHom) h
    rw [s15_Three_map_conj_mul, s15_Three_map_conj_mul, mul_inv_cancel, map_one] at h1
    rw [show X.map (MulEquiv.toMonoidHom (1 : MulAut A)) = X from Subgroup.map_id X] at h1
    exact h1
  · intro h
    have h1 := congrArg (Subgroup.map (MulAut.conj b⁻¹).toMonoidHom) h
    rw [s15_Three_map_conj_mul] at h1
    rw [show b⁻¹ * (b * a⁻¹) = a⁻¹ from by group] at h1
    exact h1

private theorem s15_Three_mem_nBar_of_kBar_eq (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hnab : ¬ ∀ x y : ↥(barSub V₀ V hV K₀), x * y = y * x)
    {k : G} (hk : k ∈ D.M)
    (heq : barSub V₀ V hV (conjSubgroup K₀ k) = barSub V₀ V hV K₀) :
    k ∈ nBar D.M V₀ V hV L := by
  by_contra hkn
  have hcomm : ⁅barSub V₀ V hV L, barSub V₀ V hV (conjSubgroup L k)⁆ = ⊥ :=
    (h.commute k hk hkn).1
  have hKleL : barSub V₀ V hV K₀ ≤ barSub V₀ V hV L :=
    hshape.2.2.1.1 (barSub V₀ V hV K₀)
      ⟨1, (s15NBar D V₀ V hV L).one_mem, by ext x; simp⟩
  have hKleB : barSub V₀ V hV K₀ ≤ barSub V₀ V hV (conjSubgroup L k) := by
    rw [← heq]
    exact barSub_mono V₀ V hV (Subgroup.map_mono hshape.1)
  exact hnab (fun x y => Subtype.ext
    (s15_Three_mul_comm_of_commutator_eq_bot hcomm x (hKleL x.2) y (hKleB y.2)))

private theorem s15_Three_lBar_eq_of_kBar_eq (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hnab : ¬ ∀ x y : ↥(barSub V₀ V hV K₀), x * y = y * x)
    {g g' : G} (hg : g ∈ D.M) (hg' : g' ∈ D.M)
    (heq : barSub V₀ V hV (conjSubgroup K₀ g) = barSub V₀ V hV (conjSubgroup K₀ g')) :
    barSub V₀ V hV (conjSubgroup L g) = barSub V₀ V hV (conjSubgroup L g') := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  have hk : g' * g⁻¹ ∈ D.M := D.M.mul_mem hg' (D.M.inv_mem hg)
  have hgk : (⟨g', hMs hg'⟩ : ↥(stabTil V₀ V)) * (⟨g, hMs hg⟩ : ↥(stabTil V₀ V))⁻¹ =
      ⟨g' * g⁻¹, hMs hk⟩ := Subtype.ext (by simp)
  have hswap : actTil V₀ V hV ⟨g', hMs hg'⟩ * (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹ =
      actTil V₀ V hV ⟨g' * g⁻¹, hMs hk⟩ := by
    rw [← hgk, map_mul, map_inv]
  have hKinv : (barSub V₀ V hV K₀).map
      (MulAut.conj (actTil V₀ V hV ⟨g', hMs hg'⟩ *
        (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹)).toMonoidHom = barSub V₀ V hV K₀ := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hg) K₀,
      s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hg') K₀] at heq
    exact (s15_Three_map_conj_inv_eq_iff (barSub V₀ V hV K₀)
      (actTil V₀ V hV ⟨g, hMs hg⟩) (actTil V₀ V hV ⟨g', hMs hg'⟩)).1 heq
  have hK : barSub V₀ V hV (conjSubgroup K₀ (g' * g⁻¹)) = barSub V₀ V hV K₀ := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hk) K₀]
    rw [show actTil V₀ V hV ⟨g' * g⁻¹, hMs hk⟩ =
        actTil V₀ V hV ⟨g', hMs hg'⟩ * (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹ from hswap.symm]
    have h1 := congrArg (Subgroup.map
      (MulAut.conj (actTil V₀ V hV ⟨g', hMs hg'⟩ *
        (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹)⁻¹).toMonoidHom) hKinv
    rw [s15_Three_map_conj_mul, inv_mul_cancel, map_one] at h1
    rw [show (barSub V₀ V hV K₀).map
        (MulEquiv.toMonoidHom (1 : MulAut (MulAut (Vtil V₀ V hV)))) =
        barSub V₀ V hV K₀ from
      Subgroup.map_id (barSub V₀ V hV K₀)] at h1
    exact h1.symm
  have h2 : g' * g⁻¹ ∈ nBar D.M V₀ V hV L :=
    s15_Three_mem_nBar_of_kBar_eq h hV hshape hnab hk hK
  have h3 : barSub V₀ V hV (conjSubgroup L (g' * g⁻¹)) = barSub V₀ V hV L :=
    (s15_Infra_mem_nBar_iff h.hyp125 hV hk).1 h2
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hk) L] at h3
  rw [show actTil V₀ V hV ⟨g' * g⁻¹, hMs hk⟩ =
      actTil V₀ V hV ⟨g', hMs hg'⟩ * (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹ from hswap.symm] at h3
  have hL : (barSub V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV ⟨g', hMs hg'⟩ *
        (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹)).toMonoidHom = barSub V₀ V hV L := by
    have h1 := congrArg (Subgroup.map
      (MulAut.conj (actTil V₀ V hV ⟨g', hMs hg'⟩ *
        (actTil V₀ V hV ⟨g, hMs hg⟩)⁻¹)).toMonoidHom) h3
    rw [s15_Three_map_conj_mul, mul_inv_cancel, map_one] at h1
    rw [show (barSub V₀ V hV L).map
        (MulEquiv.toMonoidHom (1 : MulAut (MulAut (Vtil V₀ V hV)))) =
        barSub V₀ V hV L from
      Subgroup.map_id (barSub V₀ V hV L)] at h1
    exact h1.symm
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hg) L,
    s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hg') L]
  exact (s15_Three_map_conj_inv_eq_iff (barSub V₀ V hV L)
    (actTil V₀ V hV ⟨g, hMs hg⟩) (actTil V₀ V hV ⟨g', hMs hg'⟩)).2 hL

private theorem s15_Three_three_conj_gap (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hnab : ¬ ∀ x y : ↥(barSub V₀ V hV K₀), x * y = y * x)
    (hrs : 3 ≤ s15Rs D V₀ V hV L K₀) :
    ∃ m₁ ∈ D.M, ∃ m₂ ∈ D.M, ∃ m₃ ∈ D.M,
      barSub V₀ V hV (conjSubgroup K₀ m₁) ≠ barSub V₀ V hV (conjSubgroup K₀ m₂) ∧
      barSub V₀ V hV (conjSubgroup K₀ m₁) ≠ barSub V₀ V hV (conjSubgroup K₀ m₃) ∧
      barSub V₀ V hV (conjSubgroup K₀ m₂) ≠ barSub V₀ V hV (conjSubgroup K₀ m₃) := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  let T : ↥D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup K₀ (m : G))
  let U : ↥D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup L (m : G))
  have hTU : ∀ m m' : ↥D.M, T m = T m' → U m = U m' :=
    fun m m' heq => s15_Three_lBar_eq_of_kBar_eq h hV hshape hnab m.2 m'.2 heq
  have hU1 : U ⟨1, D.M.one_mem⟩ = barSub V₀ V hV L := by
    show barSub V₀ V hV (conjSubgroup L (1 : G)) = _
    rw [conjSubgroup_one]
  have hTsub : conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) ⊆ Set.range T := by
    rintro X ⟨n, hn, rfl⟩
    obtain ⟨g, hgM, hgn⟩ := (mem_barSub V₀ V hV D.M n).1 hn.1
    refine ⟨⟨g⁻¹, D.M.inv_mem hgM⟩, ?_⟩
    show barSub V₀ V hV (conjSubgroup K₀ g⁻¹) = _
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs (D.M.inv_mem hgM)) K₀, ← hgn]
    congr 1
    rw [show (actTil V₀ V hV ⟨g⁻¹, hMs (D.M.inv_mem hgM)⟩)⁻¹ =
        actTil V₀ V hV ⟨g, hMs hgM⟩ from by
      rw [show (⟨g⁻¹, hMs (D.M.inv_mem hgM)⟩ : ↥(stabTil V₀ V)) = ⟨g, hMs hgM⟩⁻¹ from
        Subtype.ext rfl, map_inv, inv_inv]]
  have hU_of_mem : ∀ X : Subgroup (MulAut (Vtil V₀ V hV)),
      X ∈ conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV) → ∃ g : ↥D.M, U g = X := by
    rintro X ⟨n, hn, rfl⟩
    obtain ⟨g, hgM, hgn⟩ := (mem_barSub V₀ V hV D.M n).1 hn
    refine ⟨⟨g⁻¹, D.M.inv_mem hgM⟩, ?_⟩
    show barSub V₀ V hV (conjSubgroup L g⁻¹) = _
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs (D.M.inv_mem hgM)) L, ← hgn]
    congr 1
    rw [show (actTil V₀ V hV ⟨g⁻¹, hMs (D.M.inv_mem hgM)⟩)⁻¹ =
        actTil V₀ V hV ⟨g, hMs hgM⟩ from by
      rw [show (⟨g⁻¹, hMs (D.M.inv_mem hgM)⟩ : ↥(stabTil V₀ V)) = ⟨g, hMs hgM⟩⁻¹ from
        Subtype.ext rfl, map_inv, inv_inv]]
  have hrs' : 3 ≤ (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard *
      (conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := by
    have h : (conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)).ncard = s15 D.M V₀ V hV L :=
      rfl
    rw [h]
    simpa only [s15Rs] using hrs
  have hr1 : 1 ≤ (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard := by
    rw [Nat.succ_le_iff]
    exact Set.ncard_pos (Set.toFinite _) |>.2
      ⟨barSub V₀ V hV K₀, ⟨1, (s15NBar D V₀ V hV L).one_mem, by ext x; simp⟩⟩
  have h3 : 3 ≤ (Set.range T).ncard := by
    by_cases hr3 : 3 ≤ (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard
    · exact le_trans hr3 (Set.ncard_le_ncard hTsub)
    · have hr2 : (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard ≤ 2 := by omega
      have hs2 : 2 ≤ (conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := by
        nlinarith [hrs', hr1, hr2]
      by_cases hs3 : 3 ≤ (conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)).ncard
      · obtain ⟨t, ht_sub, ht3⟩ := Set.exists_subset_card_eq
          (s := conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)) hs3
        obtain ⟨X₁, X₂, X₃, hX12, hX13, hX23, htX⟩ := Set.ncard_eq_three.mp ht3
        have hX1 : X₁ ∈ conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV) :=
          ht_sub (by rw [htX]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
        have hX2 : X₂ ∈ conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV) :=
          ht_sub (by rw [htX]; simp)
        have hX3 : X₃ ∈ conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV) :=
          ht_sub (by rw [htX]; simp)
        obtain ⟨g₁, hg₁⟩ := hU_of_mem X₁ hX1
        obtain ⟨g₂, hg₂⟩ := hU_of_mem X₂ hX2
        obtain ⟨g₃, hg₃⟩ := hU_of_mem X₃ hX3
        have hT12 : T g₁ ≠ T g₂ := fun heq => hX12 (hg₁ ▸ hg₂ ▸ hTU g₁ g₂ heq)
        have hT13 : T g₁ ≠ T g₃ := fun heq => hX13 (hg₁ ▸ hg₃ ▸ hTU g₁ g₃ heq)
        have hT23 : T g₂ ≠ T g₃ := fun heq => hX23 (hg₂ ▸ hg₃ ▸ hTU g₂ g₃ heq)
        have hsub : ({T g₁, T g₂, T g₃} :
            Set (Subgroup (MulAut (Vtil V₀ V hV)))) ⊆ Set.range T := by
          intro Y hY
          rw [Set.mem_insert_iff] at hY
          rcases hY with rfl | hY
          · exact ⟨g₁, rfl⟩
          rw [Set.mem_insert_iff] at hY
          rcases hY with rfl | hY
          · exact ⟨g₂, rfl⟩
          rw [Set.mem_singleton_iff] at hY
          exact ⟨g₃, hY.symm⟩
        have hcard : ({T g₁, T g₂, T g₃} : Set (Subgroup (MulAut (Vtil V₀ V hV)))).ncard = 3 := by
          rw [Set.ncard_eq_three]
          exact ⟨T g₁, T g₂, T g₃, hT12, hT13, hT23, rfl⟩
        calc 3 = ({T g₁, T g₂, T g₃} : Set (Subgroup (MulAut (Vtil V₀ V hV)))).ncard := hcard.symm
          _ ≤ (Set.range T).ncard := Set.ncard_le_ncard hsub
      · have hs_eq : (conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)).ncard = 2 := by omega
        have hr_eq : (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard = 2 := by
          nlinarith [hrs', hr1, hr2, hs_eq]
        have hLbar_mem : barSub V₀ V hV L ∈ conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV) :=
          ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext x; simp⟩
        have hLc1 : 1 < (conjSet (barSub V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := by omega
        obtain ⟨X, hX_mem, hX_ne⟩ := Set.exists_ne_of_one_lt_ncard hLc1 (barSub V₀ V hV L)
        obtain ⟨g, hg⟩ := hU_of_mem X hX_mem
        have hUg : U g ≠ U ⟨1, D.M.one_mem⟩ := by
          intro heq
          exact hX_ne (hg.symm.trans (heq.trans hU1))
        have hnotR : T g ∉ conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) := by
          rintro ⟨n, hn, hnX⟩
          obtain ⟨hh, hhh, hhn⟩ := (mem_barSub V₀ V hV D.M n).1 hn.1
          have hnorm : actTil V₀ V hV ⟨hh, hMs hhh⟩ ∈
              Subgroup.normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
            rw [hhn]; exact hn.2
          have hUh : U ⟨hh⁻¹, D.M.inv_mem hhh⟩ = U ⟨1, D.M.one_mem⟩ := by
            dsimp only [U]
            rw [conjSubgroup_one]
            rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs (D.M.inv_mem hhh)) L]
            rw [show (actTil V₀ V hV ⟨hh⁻¹, hMs (D.M.inv_mem hhh)⟩)⁻¹ =
                actTil V₀ V hV hh from by
              rw [show (⟨hh⁻¹, hMs (D.M.inv_mem hhh)⟩ : ↥(stabTil V₀ V)) = hh⁻¹ from rfl,
                map_inv, inv_inv]]
            exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hnorm
          have heqK : barSub V₀ V hV (conjSubgroup K₀ g) =
              barSub V₀ V hV (conjSubgroup K₀ hh⁻¹) := by
            have h1 : T g = (barSub V₀ V hV K₀).map
                (MulAut.conj (actTil V₀ V hV ⟨hh, hMs hhh⟩)).toMonoidHom := by
              rw [hnX, hhn]
            show barSub V₀ V hV (conjSubgroup K₀ g) = barSub V₀ V hV (conjSubgroup K₀ hh⁻¹)
            rw [show barSub V₀ V hV (conjSubgroup K₀ g) = T g from rfl, h1,
              s15_Infra_barSub_conjSubgroup V₀ V hV (hMs (D.M.inv_mem hhh)) K₀]
            congr 1
            rw [show (actTil V₀ V hV ⟨hh⁻¹, hMs (D.M.inv_mem hhh)⟩)⁻¹ =
                actTil V₀ V hV ⟨hh, hMs hhh⟩ from by
              rw [show (⟨hh⁻¹, hMs (D.M.inv_mem hhh)⟩ : ↥(stabTil V₀ V)) = ⟨hh, hMs hhh⟩⁻¹ from
                Subtype.ext rfl, map_inv, inv_inv]]
          exact hUg (hTU g ⟨hh⁻¹, D.M.inv_mem hhh⟩ heqK |>.trans hUh)
        have hproper : conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) ⊂ Set.range T := by
          refine ⟨hTsub, ?_⟩
          intro hsub
          exact hnotR (hsub ⟨g, rfl⟩)
        have := Set.ncard_lt_ncard hproper
        omega
  obtain ⟨t, ht_sub, ht3⟩ := Set.exists_subset_card_eq (s := Set.range T) h3
  obtain ⟨x, y, z, hxy, hxz, hyz, htz⟩ := Set.ncard_eq_three.mp ht3
  have hx : x ∈ Set.range T := ht_sub (by rw [htz]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
  have hy : y ∈ Set.range T :=
    ht_sub (by rw [htz]; simp)
  have hz : z ∈ Set.range T :=
    ht_sub (by rw [htz]; simp)
  obtain ⟨m₁, hm₁⟩ := hx
  obtain ⟨m₂, hm₂⟩ := hy
  obtain ⟨m₃, hm₃⟩ := hz
  exact ⟨m₁, m₁.2, m₂, m₂.2, m₃, m₃.2,
    show T m₁ ≠ T m₂ from by rw [hm₁, hm₂]; exact hxy,
    show T m₁ ≠ T m₃ from by rw [hm₁, hm₃]; exact hxz,
    show T m₂ ≠ T m₃ from by rw [hm₂, hm₃]; exact hyz⟩

private theorem s15_Three_hyp81_of_three_gap
    (hS2 : RSchur2_153)
    (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : 3 ≤ s15Rs D V₀ V hV L K₀) :
    ∃ (Y : Subgroup G) (K₁ K₂ K₃ : Subgroup G),
      CFSG.Open.IsSubnormal Y D.M ∧ K₁ ≤ Y ∧ K₂ ≤ Y ∧ K₃ ≤ Y ∧
      (K₁.subgroupOf Y).Normal ∧ (K₂.subgroupOf Y).Normal ∧ (K₃.subgroupOf Y).Normal ∧
      K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₃ ∈ calC D.M ∧
      CFSG.Open.pRank 3 K₁ = 1 ∧ CFSG.Open.pRank 3 K₂ = 1 ∧ CFSG.Open.pRank 3 K₃ = 1 ∧
      2 < CFSG.Open.pRank 3 (K₁ ⊔ K₂ ⊔ K₃) := by
  obtain ⟨hq, hZ⟩ := hSimple (V := Vtil (v1Sub D.M V₀ V hV L) V hV)
    (X := ↥(barSub V₀ V hV K₀))
    (K := barSub (v1Sub D.M V₀ V hV L) V hV K₀)
    (Z := commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) hperf
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  have hK0M : K₀ ≤ D.M := hshape.1.trans h.le
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  obtain ⟨X, Y, hCTX, hXM, hXnorm, hXbar, hYX, hYstar, hYrest⟩ :=
    s15_Three_Y119 hSimple h127 h119 h1217 h hV hshape hperf
  obtain ⟨hY119, -⟩ := hYrest
  have hYXsub : CFSG.Open.IsSubnormal Y X :=
    A3.subnormal_of_normal hY119.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hY119.1).mpr hY119.2.2.2.1)
  have hXMsub : CFSG.Open.IsSubnormal X D.M := A3.subnormal_of_normal hXM hXnorm
  have hYMsub : CFSG.Open.IsSubnormal Y D.M := A3.subnormal_trans hYXsub hXMsub
  have hYE : F11.O2E Y = Y := hY119.2.2.1
  have hYC : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y := hY119.2.2.2.2.1
  have hYKstab : Y ≤ stabTil V₀ V := hYMsub.le.trans hMs
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hYMsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
  obtain ⟨ψ, hψ⟩ := s15_Three_barLift_exists hV hYKstab h2
  have hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ :=
    k2_layer_top_of_O2E_eq hYE
  obtain ⟨m₁, hm₁, m₂, hm₂, m₃, hm₃, hne₁₂, hne₁₃, hne₂₃⟩ :=
    s15_Three_three_conj_gap h hV hshape (k2_not_forall_comm_of_isQuasisimple hq) hrs
  obtain ⟨C₁, hC₁, hC₁map⟩ := s15_Three_component_cover_conj h hV hshape hq hYMsub hYE hYX hm₁
  obtain ⟨C₂, hC₂, hC₂map⟩ := s15_Three_component_cover_conj h hV hshape hq hYMsub hYE hYX hm₂
  obtain ⟨C₃, hC₃, hC₃map⟩ := s15_Three_component_cover_conj h hV hshape hq hYMsub hYE hYX hm₃
  have hC₁n : C₁.Normal := s15_Three_component_normal hC₁ hlayer
  have hC₂n : C₂.Normal := s15_Three_component_normal hC₂ hlayer
  have hC₃n : C₃.Normal := s15_Three_component_normal hC₃ hlayer
  obtain ⟨K₁, hK₁Y, hK₁N, hK₁sub, hK₁perf, hK₁q, ⟨e₁⟩, hK₁map⟩ :=
    s15_Three_core_normal hC₁ hC₁n
  obtain ⟨K₂, hK₂Y, hK₂N, hK₂sub, hK₂perf, hK₂q, ⟨e₂⟩, hK₂map⟩ :=
    s15_Three_core_normal hC₂ hC₂n
  obtain ⟨K₃, hK₃Y, hK₃N, hK₃sub, hK₃perf, hK₃q, ⟨e₃⟩, hK₃map⟩ :=
    s15_Three_core_normal hC₃ hC₃n
  have hK₁C : K₁ ∈ calC D.M := ⟨A3.subnormal_trans hK₁sub hYMsub, hK₁perf, hK₁q⟩
  have hK₂C : K₂ ∈ calC D.M := ⟨A3.subnormal_trans hK₂sub hYMsub, hK₂perf, hK₂q⟩
  have hK₃C : K₃ ∈ calC D.M := ⟨A3.subnormal_trans hK₃sub hYMsub, hK₃perf, hK₃q⟩
  have hC₁map' : C₁.map ψ = barSub V₀ V hV (conjSubgroup K₀ m₁) :=
    (s15_Three_barSub_comap_map hV hYKstab ψ hψ C₁).symm.trans hC₁map
  have hC₂map' : C₂.map ψ = barSub V₀ V hV (conjSubgroup K₀ m₂) :=
    (s15_Three_barSub_comap_map hV hYKstab ψ hψ C₂).symm.trans hC₂map
  have hC₃map' : C₃.map ψ = barSub V₀ V hV (conjSubgroup K₀ m₃) :=
    (s15_Three_barSub_comap_map hV hYKstab ψ hψ C₃).symm.trans hC₃map
  have hr₁ : CFSG.Open.pRank 3 K₁ = 1 :=
    s15_Three_core_rank_one hS2 hV h hq hZ hL2 hMs hK0M hYMsub hYC hYKstab h2 ψ hψ hm₁
      hC₁ hC₁map' hK₁Y hK₁sub hK₁perf hK₁q hK₁map
  have hr₂ : CFSG.Open.pRank 3 K₂ = 1 :=
    s15_Three_core_rank_one hS2 hV h hq hZ hL2 hMs hK0M hYMsub hYC hYKstab h2 ψ hψ hm₂
      hC₂ hC₂map' hK₂Y hK₂sub hK₂perf hK₂q hK₂map
  have hr₃ : CFSG.Open.pRank 3 K₃ = 1 :=
    s15_Three_core_rank_one hS2 hV h hq hZ hL2 hMs hK0M hYMsub hYC hYKstab h2 ψ hψ hm₃
      hC₃ hC₃map' hK₃Y hK₃sub hK₃perf hK₃q hK₃map
  have hC₁rank : CFSG.Open.pRank 3 C₁ = 1 := by
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₁)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥C₁) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e₁
    have h2' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C₁) = CFSG.Open.pRank 3 C₁ :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 C₁).symm.trans
        (CFSG.SectionRank.pRank_coe_eq_openPRank 3 C₁)
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₁)) = 1 := by
      have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K₁) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥K₁) (p := 2)).exists_card_eq
        rw [hn]
        intro h3d
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
        omega
      have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₁)) =
          CFSG.Open.pRank 3 (⊤ : Subgroup ↥K₁) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K₁) hN
      have h5 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K₁) = CFSG.Open.pRank 3 K₁ :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top 3 K₁).symm.trans
          (CFSG.SectionRank.pRank_coe_eq_openPRank 3 K₁)
      omega
    omega
  have hC₂rank : CFSG.Open.pRank 3 C₂ = 1 := by
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₂)) = 1 := by
      have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K₂) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥K₂) (p := 2)).exists_card_eq
        rw [hn]
        intro h3d
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
        omega
      have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₂)) =
          CFSG.Open.pRank 3 (⊤ : Subgroup ↥K₂) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K₂) hN
      have h5 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K₂) = CFSG.Open.pRank 3 K₂ :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top 3 K₂).symm.trans
          (CFSG.SectionRank.pRank_coe_eq_openPRank 3 K₂)
      omega
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₂)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥C₂) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e₂
    have h2' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C₂) = CFSG.Open.pRank 3 C₂ :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 C₂).symm.trans
        (CFSG.SectionRank.pRank_coe_eq_openPRank 3 C₂)
    omega
  have hC₃rank : CFSG.Open.pRank 3 C₃ = 1 := by
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₃)) = 1 := by
      have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K₃) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥K₃) (p := 2)).exists_card_eq
        rw [hn]
        intro h3d
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
        omega
      have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₃)) =
          CFSG.Open.pRank 3 (⊤ : Subgroup ↥K₃) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K₃) hN
      have h5 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K₃) = CFSG.Open.pRank 3 K₃ :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top 3 K₃).symm.trans
          (CFSG.SectionRank.pRank_coe_eq_openPRank 3 K₃)
      omega
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K₃)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥C₃) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e₃
    have h2' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C₃) = CFSG.Open.pRank 3 C₃ :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 C₃).symm.trans
        (CFSG.SectionRank.pRank_coe_eq_openPRank 3 C₃)
    omega
  have hC₂perf : ⁅C₂, C₂⁆ = C₂ := Subgroup.isPerfect_iff.mp ⟨hC₂.2.2.1⟩
  have hC₃perf : ⁅C₃, C₃⁆ = C₃ := Subgroup.isPerfect_iff.mp ⟨hC₃.2.2.1⟩
  have hdiv₂ : 3 ∣ Nat.card C₂ := by
    obtain ⟨E, hE, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) C₂
    have h3 : Nat.card E = 3 := by rw [hEcard, hC₂rank]; norm_num
    have hcard : Nat.card (E.subgroupOf C₂) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
    rw [← h3, ← hcard]
    exact Subgroup.card_subgroup_dvd_card (E.subgroupOf C₂)
  have hdiv₃ : 3 ∣ Nat.card C₃ := by
    obtain ⟨E, hE, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) C₃
    have h3 : Nat.card E = 3 := by rw [hEcard, hC₃rank]; norm_num
    have hcard : Nat.card (E.subgroupOf C₃) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
    rw [← h3, ← hcard]
    exact Subgroup.card_subgroup_dvd_card (E.subgroupOf C₃)
  have hC₁₂ne : C₁ ≠ C₂ := by
    intro heq
    exact hne₁₂ (by rw [← hC₁map', ← hC₂map', heq])
  have hC₁₃ne : C₁ ≠ C₃ := by
    intro heq
    exact hne₁₃ (by rw [← hC₁map', ← hC₃map', heq])
  have hC₂₃ne : C₂ ≠ C₃ := by
    intro heq
    exact hne₂₃ (by rw [← hC₂map', ← hC₃map', heq])
  have hcommut : ∀ {D₁ D₂ : Subgroup (Bar2 Y)}, CFSG.Open.IsComponentOf D₁ ⊤ →
      CFSG.Open.IsComponentOf D₂ ⊤ → D₁ ≠ D₂ → ⁅D₁, D₂⁆ = ⊥ := by
    intro D₁ D₂ hD₁ hD₂ hne
    rcases k2_component_eq_or_commute hD₁ hD₂ with h | h
    · exact absurd h hne
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (h x hx y hy).symm
  have hjoinC : 2 < CFSG.Open.pRank 3 (C₁ ⊔ C₂ ⊔ C₃) :=
    s15_Three_pRank3_join hC₁rank hC₂perf hC₃perf hdiv₂ hdiv₃
      (hcommut hC₁ hC₂ hC₁₂ne) (hcommut hC₁ hC₃ hC₁₃ne) (hcommut hC₂ hC₃ hC₂₃ne)
  have hL'Y : K₁ ⊔ K₂ ⊔ K₃ ≤ Y := sup_le (sup_le hK₁Y hK₂Y) hK₃Y
  have himage : ((K₁ ⊔ K₂ ⊔ K₃).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) =
      C₁ ⊔ C₂ ⊔ C₃ := by
    rw [Subgroup.subgroupOf_sup (sup_le hK₁Y hK₂Y) hK₃Y,
      Subgroup.subgroupOf_sup hK₁Y hK₂Y, Subgroup.map_sup, Subgroup.map_sup,
      hK₁map, hK₂map, hK₃map]
  have hN3 : ¬ 3 ∣ Nat.card ↥((K₁ ⊔ K₂ ⊔ K₃) ⊓ pCoreOf 2 Y) := by
    have h2g : IsPGroup 2 ↥((K₁ ⊔ K₂ ⊔ K₃) ⊓ pCoreOf 2 Y) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_right
    obtain ⟨n, hn⟩ := h2g.exists_card_eq
    rw [hn]
    intro h3d
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    omega
  have hjoin : 2 < CFSG.Open.pRank 3 (K₁ ⊔ K₂ ⊔ K₃) := by
    have h1 := s15_Three_pRank3_image hL'Y hN3
    rw [himage] at h1
    omega
  exact ⟨Y, K₁, K₂, K₃, hYMsub, hK₁Y, hK₂Y, hK₃Y, hK₁N, hK₂N, hK₃N, hK₁C, hK₂C, hK₃C,
    hr₁, hr₂, hr₃, hjoin⟩

theorem s15_Three_hyp81_of_three (hS2 : RSchur2_153) (hSimple : RSimple153) (h127 : R127 D)
    (h119 : F11.R119 D)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : 3 ≤ s15Rs D V₀ V hV L K₀) : ∃ L' : Subgroup G, F08.Hyp81 D.M L' := by
  obtain ⟨Y, K₁, K₂, K₃, hYM, hK₁Y, hK₂Y, hK₃Y, hN₁, hN₂, hN₃, hK₁C, hK₂C, hK₃C,
    hr₁, hr₂, hr₃, hrank⟩ :=
    s15_Three_hyp81_of_three_gap hS2 hSimple h127 h119 h1217 h hV hshape hperf hL2 hrs
  let L' : Subgroup G := K₁ ⊔ K₂ ⊔ K₃
  have hK₁L' : K₁ ≤ L' := le_sup_left.trans le_sup_left
  have hK₂L' : K₂ ≤ L' := le_sup_right.trans le_sup_left
  have hK₃L' : K₃ ≤ L' := le_sup_right
  have hK₁₂Y : K₁ ⊔ K₂ ≤ Y := sup_le hK₁Y hK₂Y
  have hL'Y : L' ≤ Y := sup_le hK₁₂Y hK₃Y
  have hN₁₂ : ((K₁ ⊔ K₂).subgroupOf Y).Normal := by
    rw [Subgroup.subgroupOf_sup hK₁Y hK₂Y]
    haveI : (K₁.subgroupOf Y).Normal := hN₁
    haveI : (K₂.subgroupOf Y).Normal := hN₂
    exact Subgroup.sup_normal _ _
  have hNL' : (L'.subgroupOf Y).Normal := by
    change ((K₁ ⊔ K₂ ⊔ K₃).subgroupOf Y).Normal
    rw [Subgroup.subgroupOf_sup hK₁₂Y hK₃Y]
    haveI : ((K₁ ⊔ K₂).subgroupOf Y).Normal := hN₁₂
    haveI : (K₃.subgroupOf Y).Normal := hN₃
    exact Subgroup.sup_normal _ _
  have hL'Msub : CFSG.Open.IsSubnormal L' D.M :=
    A3.subnormal_trans (A3.subnormal_of_normal hL'Y hNL') hYM
  have hL'perf : ⁅L', L'⁆ = L' := by
    refine le_antisymm ?_ ?_
    · refine Subgroup.commutator_le.mpr ?_
      intro x hx y hy
      rw [commutatorElement_def]
      exact L'.mul_mem (L'.mul_mem (L'.mul_mem hx hy) (L'.inv_mem hx)) (L'.inv_mem hy)
    · have h1 : K₁ ≤ ⁅L', L'⁆ := by
        rw [← hK₁C.2.1]
        exact Subgroup.commutator_mono hK₁L' hK₁L'
      have h2 : K₂ ≤ ⁅L', L'⁆ := by
        rw [← hK₂C.2.1]
        exact Subgroup.commutator_mono hK₂L' hK₂L'
      have h3 : K₃ ≤ ⁅L', L'⁆ := by
        rw [← hK₃C.2.1]
        exact Subgroup.commutator_mono hK₃L' hK₃L'
      exact sup_le (sup_le h1 h2) h3
  have hYnorm23 : Y ≤ Subgroup.normalizer ((K₂ ⊔ K₃ : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hK₂Y hK₃Y)).mp (by
      rw [Subgroup.subgroupOf_sup hK₂Y hK₃Y]
      exact Subgroup.sup_normal _ _)
  have hK₁norm : K₁ ≤ Subgroup.normalizer ((K₂ ⊔ K₃ : Subgroup G) : Set G) :=
    hK₁Y.trans hYnorm23
  have hYnorm3 : Y ≤ Subgroup.normalizer (K₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₃Y).mp hN₃
  have hK₂norm : K₂ ≤ Subgroup.normalizer (K₃ : Set G) := hK₂Y.trans hYnorm3
  have hprod₁ : ((K₁ ⊔ (K₂ ⊔ K₃) : Subgroup G) : Set G) =
      (K₁ : Set G) * (K₂ ⊔ K₃ : Subgroup G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K₁ (K₂ ⊔ K₃) hK₁norm
  have hprod₂ : ((K₂ ⊔ K₃ : Subgroup G) : Set G) = (K₂ : Set G) * K₃ :=
    Subgroup.coe_mul_of_left_le_normalizer_right K₂ K₃ hK₂norm
  have hprod : (L' : Set G) = (K₁ : Set G) * K₂ * K₃ := by
    change ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup G) : Set G) = (K₁ : Set G) * K₂ * K₃
    rw [sup_assoc, hprod₁, hprod₂, mul_assoc]
  exact ⟨L', hL'Msub, hL'perf, hrank,
    Or.inr ⟨K₁, K₂, K₃, hK₁C, hK₂C, hK₃C, hr₁, hr₂, hr₃, hK₁L', hK₂L', hK₃L', hprod⟩⟩

theorem s15_Three_rs_le_two (h82 : F08.R82 D) (hS2 : RSchur2_153) (hSimple : RSimple153)
    (h127 : R127 D)
    (h119 : F11.R119 D) (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    s15Rs D V₀ V hV L K₀ ≤ 2 := by
  by_contra hlt
  obtain ⟨L', hL'⟩ :=
    s15_Three_hyp81_of_three hS2 hSimple h127 h119 h1217 h hV hshape hperf hL2 (by omega)
  exact hns (h82 L' hL')

end RsTwo

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
