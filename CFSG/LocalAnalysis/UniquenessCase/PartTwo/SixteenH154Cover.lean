module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_not_forall_comm_of_isQuasisimple {A : Type} [Group A] [Finite A]
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

private theorem s16h_rankThreeLayer_le {A : Type} [Group A] (H : Subgroup A) :
    rankThreeLayer H ≤ H :=
  sSup_le fun _ hL => hL.1

private theorem s16h_isComponent_subgroupOf {A : Type} [Group A] {H K : Subgroup A}
    (h : CFSG.Open.IsComponentOf K H) : CFSG.IsComponent (K.subgroupOf H) := by
  rw [CFSG.isComponent_iff_open]
  exact ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

private theorem s16h_component_eq_or_commute {A : Type} [Group A] [Finite A]
    {H K L : Subgroup A} (hK : CFSG.Open.IsComponentOf K H)
    (hL : CFSG.Open.IsComponentOf L H) :
    K = L ∨ ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute (s16h_isComponent_subgroupOf hK)
    (s16h_isComponent_subgroupOf hL) with h | h
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

private theorem s16h_iSup_le_normalizer_of_eq_or_comm {A : Type} [Group A] {ι : Type}
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

private theorem s16h_isComponentOf_iSup_of_eq_or_comm {A : Type} [Group A] {ι : Type}
    {T : ι → Subgroup A}
    (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i))
    (hcomm : ∀ i j, T i = T j ∨ ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x) (i : ι) :
    CFSG.Open.IsComponentOf (T i) (⨆ j, T j) := by
  refine ⟨le_iSup T i, ?_, hq i⟩
  exact CFSG.Open.IsSubnormal.step (le_iSup T i)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup T i)).mpr
      (s16h_iSup_le_normalizer_of_eq_or_comm hcomm i))
    (CFSG.Open.IsSubnormal.refl _)

private theorem s16h_component_eq {A : Type} [Group A] [Finite A]
    {ι : Type} {T : ι → Subgroup A}
    (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i))
    (hcomm : ∀ i j, T i = T j ∨ ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x)
    {B : Subgroup A} (hB : CFSG.Open.IsComponentOf B (⨆ i, T i)) :
    ∃ i, B = T i := by
  by_contra h
  push Not at h
  have hcommB : ∀ i, ∀ b ∈ B, ∀ y ∈ T i, b * y = y * b := fun i =>
    (s16h_component_eq_or_commute hB
      (s16h_isComponentOf_iSup_of_eq_or_comm hq hcomm i)).resolve_left (h i)
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
  exact (s16h_not_forall_comm_of_isQuasisimple hB.2.2) hcommB'

private theorem s16h_map_component_of_not_le_ker {Q A : Type} [Group Q] [Finite Q] [Group A]
    [Finite A] (ψ : Q →* A) {C : Subgroup Q} (hC : CFSG.Open.IsComponentOf C ⊤)
    (hker : ¬ C ≤ ψ.ker) : CFSG.Open.IsComponentOf (C.map ψ) ψ.range := by
  have hCbot : C.map ψ ≠ ⊥ := fun h => hker ((Subgroup.map_eq_bot_iff C).1 h)
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨c, -, rfl⟩
    rw [MonoidHom.range_eq_map]
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_top c)
  · rw [MonoidHom.range_eq_map]
    exact A3.subnormal_map ψ hC.2.1
  · let f : ↥C →* ↥(C.map ψ) :=
      (ψ.comp C.subtype).codRestrict (C.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨c, hc⟩, rfl⟩
    haveI : Nontrivial ↥(C.map ψ) := (Subgroup.nontrivial_iff_ne_bot _).2 hCbot
    exact uc22br4_isQuasisimple_of_surjective hC.2.2 f hf

private theorem s16h_iSup_subgroupOf {A : Type} [Group A] {S : Subgroup A}
    {ι : Sort*} (H : ι → Subgroup A) (hH : ∀ i, H i ≤ S) :
    (⨆ i, H i).subgroupOf S = ⨆ i, (H i).subgroupOf S := by
  apply Subgroup.map_injective (Subgroup.subtype_injective S)
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_iSup]
  rw [show (⨆ i, map S.subtype ((H i).subgroupOf S)) = ⨆ i, H i by
    apply iSup_congr
    intro i
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hH i)]]
  exact inf_eq_left.2 (iSup_le hH)

private theorem s16h_isComponentOf_map_mulEquiv_apply {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {L H : Subgroup A} (h : CFSG.Open.IsComponentOf L H) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (H.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map e.toMonoidHom h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective).symm
      h.2.2⟩

private theorem s16h_map_mulEquiv_map_symm {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup A) : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A from by
    ext x; simp, Subgroup.map_id]

private theorem s16h_map_symm_map {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup B) : (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B from by
    ext x; simp, Subgroup.map_id]

private theorem s16h_isComponentOf_map_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {L H : Subgroup A} :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (H.map e.toMonoidHom) ↔
      CFSG.Open.IsComponentOf L H := by
  refine ⟨fun h => ?_, s16h_isComponentOf_map_mulEquiv_apply e⟩
  have h' := s16h_isComponentOf_map_mulEquiv_apply e.symm h
  rwa [s16h_map_mulEquiv_map_symm e L, s16h_map_mulEquiv_map_symm e H] at h'

private theorem s16h_isComponentOf_subgroupOf {A : Type} [Group A] {S L H : Subgroup A}
    (hLS : L ≤ S) (hHS : H ≤ S) :
    CFSG.Open.IsComponentOf (L.subgroupOf S) (H.subgroupOf S) ↔ CFSG.Open.IsComponentOf L H := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact h.1 (show (⟨x, hLS hx⟩ : ↥S) ∈ L.subgroupOf S from hx)
    · have h' := CFSG.Open.IsSubnormal.map S.subtype h.2.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hLS, Subgroup.map_subgroupOf_eq_of_le hHS] at h'
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLS).symm h.2.2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact h.1 hx
    · have h' := CFSG.Open.IsSubnormal.comap S.subtype h.2.1
      rwa [Subgroup.comap_subtype, Subgroup.comap_subtype] at h'
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLS) h.2.2

private theorem s16h_layer_map_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (H : Subgroup A) :
    rankThreeLayer (H.map e.toMonoidHom) = (rankThreeLayer H).map e.toMonoidHom := by
  apply le_antisymm
  · refine sSup_le fun K hK => ?_
    have hK' : CFSG.Open.IsComponentOf (K.map e.symm.toMonoidHom) H := by
      refine (s16h_isComponentOf_map_mulEquiv e).1 ?_
      rwa [s16h_map_symm_map e K]
    have hle : K.map e.symm.toMonoidHom ≤ rankThreeLayer H := by
      rw [rankThreeLayer]
      exact le_sSup hK'
    have hle2 := Subgroup.map_mono (f := e.toMonoidHom) hle
    rwa [s16h_map_symm_map e K] at hle2
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro L hL
    have hle : L.map e.toMonoidHom ≤ rankThreeLayer (H.map e.toMonoidHom) := by
      rw [rankThreeLayer]
      exact le_sSup (s16h_isComponentOf_map_mulEquiv_apply e hL)
    exact (Subgroup.map_le_iff_le_comap).1 hle

private theorem s16h_layer_subgroupOf {A : Type} [Group A] {S H : Subgroup A} (hHS : H ≤ S) :
    rankThreeLayer (H.subgroupOf S) = (rankThreeLayer H).subgroupOf S := by
  have hsub : (rankThreeLayer H).subgroupOf S =
      ⨆ L : {L : Subgroup A // CFSG.Open.IsComponentOf L H},
        (L : Subgroup A).subgroupOf S := by
    rw [rankThreeLayer, sSup_eq_iSup']
    exact s16h_iSup_subgroupOf (S := S)
      (H := fun L : {L : Subgroup A // CFSG.Open.IsComponentOf L H} => (L : Subgroup A))
      (fun L => L.2.1.trans hHS)
  rw [hsub, rankThreeLayer, sSup_eq_iSup']
  refine le_antisymm ?_ ?_
  · apply iSup_le
    intro K
    have hKsub : (K.1.map S.subtype).subgroupOf S = K.1 := by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective S)]
    have hKmap : CFSG.Open.IsComponentOf (K.1.map S.subtype) H := by
      refine (s16h_isComponentOf_subgroupOf (hLS := ?_) hHS).1 ?_
      · rintro x ⟨y, hy, rfl⟩
        exact y.2
      · rw [hKsub]
        exact K.2
    have hle := le_iSup (fun L : {L : Subgroup A // CFSG.Open.IsComponentOf L H} =>
      (L : Subgroup A).subgroupOf S) ⟨K.1.map S.subtype, hKmap⟩
    rwa [hKsub] at hle
  · apply iSup_le
    intro L
    have hL : CFSG.Open.IsComponentOf (L.1.subgroupOf S) (H.subgroupOf S) :=
      (s16h_isComponentOf_subgroupOf (hLS := L.2.1.trans hHS) hHS).2 L.2
    exact le_iSup (fun K : {K : Subgroup ↥S // CFSG.Open.IsComponentOf K (H.subgroupOf S)} =>
      K.1) ⟨L.1.subgroupOf S, hL⟩

private theorem s16h_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
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

private theorem s16h_barLift_exists {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
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

private theorem s16h_barSub_comap_map {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
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

theorem s16h_exists_component_over {Q A : Type} [Group Q] [Finite Q] [Group A] [Finite A]
    (ψ : Q →* A) (hQ : rankThreeLayer (⊤ : Subgroup Q) = ⊤) {B : Subgroup A}
    (hB : IsComponentOf B ψ.range) :
    ∃ C : Subgroup Q, IsComponentOf C ⊤ ∧ C.map ψ = B := by
  let ι₀ := {C : Subgroup Q // IsComponentOf C ⊤}
  let ι := {C : ι₀ // ¬ (C : Subgroup Q) ≤ ψ.ker}
  let T : ι → Subgroup A := fun C => (C.1 : Subgroup Q).map ψ
  have hfull : ψ.range = ⨆ C : ι₀, (C : Subgroup Q).map ψ := by
    rw [MonoidHom.range_eq_map]
    conv_lhs => rw [← hQ]
    rw [CFSG.Open.rankThreeLayer, sSup_eq_iSup']
    exact Subgroup.map_iSup ψ fun C : ι₀ => (C : Subgroup Q)
  have hrange : ψ.range = ⨆ C : ι, T C := by
    rw [hfull]
    apply le_antisymm
    · refine iSup_le fun C => ?_
      by_cases hker : (C : Subgroup Q) ≤ ψ.ker
      · have hbot : (C : Subgroup Q).map ψ = ⊥ :=
          (Subgroup.map_eq_bot_iff (C : Subgroup Q) (f := ψ)).2 hker
        rw [hbot]
        exact bot_le
      · exact le_iSup (fun C : ι => T C) ⟨C, hker⟩
    · refine iSup_le fun C => le_iSup (fun C : ι₀ => (C : Subgroup Q).map ψ) C.1
  have hTqs : ∀ C : ι, CFSG.Open.IsQuasisimple ↥(T C) := fun C => by
    dsimp only [T]
    exact (s16h_map_component_of_not_le_ker ψ C.1.2 C.2).2.2
  have hTcomm : ∀ C D : ι, T C = T D ∨ ∀ x ∈ T C, ∀ y ∈ T D, x * y = y * x := fun C D => by
    dsimp only [T]
    exact s16h_component_eq_or_commute
      (s16h_map_component_of_not_le_ker ψ C.1.2 C.2)
      (s16h_map_component_of_not_le_ker ψ D.1.2 D.2)
  have hB' : IsComponentOf B (⨆ C : ι, T C) := hrange ▸ hB
  obtain ⟨C, hC⟩ := s16h_component_eq hTqs hTcomm hB'
  exact ⟨C.1.1, C.1.2, hC.symm⟩

theorem s16h_exists_Y_layer (D : Data G) (h127 : R127 D) (h119 : F11.R119 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsSubnormal Y D.M ∧ F11.O2E Y = Y ∧
      barSub V₀ V h.isElemAbelian Y = rankThreeLayer (Mbar D.M V₀ V h.isElemAbelian) := by
  let hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  set Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    rankThreeLayer (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) with hXbardef
  have hXbarN : Xbar.Normal := CFSG.ComponentClassification.Layer.normal (F11.MBar11 D.M V₀ V)
  set X : Subgroup G := F11.barPreimage11 D.M V₀ V Xbar with hXdef
  have hX_le : X ≤ D.M := Subgroup.map_subtype_le _
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    intro x hx
    have hxM : x ∈ D.M := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx 1) V.one_mem).1
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨x, hxM⟩ ∈ Xbar
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact Xbar.one_mem
  have hbarXimg : F11.barImage11 D.M V₀ V X = Xbar := by
    unfold F11.barImage11
    rw [hXdef]
    unfold F11.barPreimage11
    have h1 : ((Xbar.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M))).map
        D.M.subtype).subgroupOf D.M =
          Xbar.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)) :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Xbar
  have hXnormal : (X.subgroupOf D.M).Normal := by
    have h1 : X.subgroupOf D.M =
        Xbar.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)) := by
      rw [hXdef]
      unfold F11.barPreimage11
      exact Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact hXbarN.comap _
  have hlayer : rankThreeLayer Xbar = Xbar := by
    apply le_antisymm
    · exact sSup_le fun L hL => hL.1
    · change rankThreeLayer (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) ≤ rankThreeLayer Xbar
      conv_lhs => rw [CFSG.Open.rankThreeLayer]
      refine sSup_le fun C hC => ?_
      have hq : ∀ i : {C : Subgroup (F11.MBar11 D.M V₀ V) // IsComponentOf C ⊤},
          CFSG.Open.IsQuasisimple ↥(i : Subgroup (F11.MBar11 D.M V₀ V)) := fun i => i.2.2.2
      have hcomm : ∀ i j : {C : Subgroup (F11.MBar11 D.M V₀ V) // IsComponentOf C ⊤},
          (i : Subgroup (F11.MBar11 D.M V₀ V)) = (j : Subgroup (F11.MBar11 D.M V₀ V)) ∨
            ∀ x ∈ (i : Subgroup (F11.MBar11 D.M V₀ V)),
              ∀ y ∈ (j : Subgroup (F11.MBar11 D.M V₀ V)), x * y = y * x :=
        fun i j => s16h_component_eq_or_commute i.2 j.2
      have hsup : (⨆ i : {C : Subgroup (F11.MBar11 D.M V₀ V) // IsComponentOf C ⊤},
            (i : Subgroup (F11.MBar11 D.M V₀ V))) = Xbar := by
        rw [hXbardef, CFSG.Open.rankThreeLayer, sSup_eq_iSup']
        rfl
      have hcomp : IsComponentOf C Xbar := by
        have := s16h_isComponentOf_iSup_of_eq_or_comm hq hcomm ⟨C, hC⟩
        rwa [hsup] at this
      rw [CFSG.Open.rankThreeLayer]
      exact le_sSup hcomp
  obtain ⟨Y, hY, -⟩ := h119 V₀ V (Hyp125.hyp11 h127 h) X hCX hX_le (by rw [hbarXimg]; exact hlayer)
  obtain ⟨hYX, -, hO2E, hYn, -, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hX_le
  have hYXsub : CFSG.Open.IsSubnormal Y X :=
    A3.subnormal_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hYn)
  have hXMsub : CFSG.Open.IsSubnormal X D.M := A3.subnormal_of_normal hX_le hXnormal
  have hYMsub : CFSG.Open.IsSubnormal Y D.M := A3.subnormal_trans hYXsub hXMsub
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hbarX : barSub V₀ V hV X = rankThreeLayer (Mbar D.M V₀ V hV) := by
    have hsub : (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) =
        (rankThreeLayer (Mbar D.M V₀ V hV)).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he X hX_le]
      rw [hbarXimg]
      rw [hXbardef]
      rw [← s16h_layer_map_equiv e (⊤ : Subgroup (F11.MBar11 D.M V₀ V)),
        Subgroup.map_top_of_surjective _ e.surjective]
      simpa [Subgroup.subgroupOf_self] using
        s16h_layer_subgroupOf (S := Mbar D.M V₀ V hV) (H := Mbar D.M V₀ V hV) le_rfl
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hX_le),
      inf_eq_left.2 (s16h_rankThreeLayer_le _)] at h2
    exact h2
  have hbarY : barSub V₀ V hV Y = rankThreeLayer (Mbar D.M V₀ V hV) := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hYM, ← he X hX_le, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hYM),
      inf_eq_left.2 (barSub_mono V₀ V hV hX_le)] at h2
    exact h2.trans hbarX
  exact ⟨Y, hYM, hYMsub, hO2E, hbarY⟩

theorem s16h_exists_cover (D : Data G) (h127 : R127 D) (h119 : F11.R119 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {B : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hB : IsComponentOf B (Mbar D.M V₀ V h.isElemAbelian)) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub V₀ V h.isElemAbelian K = B := by
  let hV := h.isElemAbelian
  obtain ⟨Y, hYM, hYsub, hYE, hYbar⟩ := s16h_exists_Y_layer D h127 h119 h
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hYs : Y ≤ stabTil V₀ V := hYM.trans hMs
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hYsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  obtain ⟨ψ, hψ⟩ := s16h_barLift_exists hV hYs h2
  have hψrange : ψ.range = barSub V₀ V hV Y := by
    have h := s16h_barSub_comap_map hV hYs ψ hψ ⊤
    rw [Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype] at h
    rw [MonoidHom.range_eq_map]
    exact h.symm
  have hQ : rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := s16h_layer_top_of_O2E_eq hYE
  have hB' : IsComponentOf B ψ.range := by
    rw [hψrange, hYbar]
    refine ⟨?_, ?_, hB.2.2⟩
    · rw [CFSG.Open.rankThreeLayer]
      exact le_sSup hB
    · have hle : B ≤ rankThreeLayer (Mbar D.M V₀ V hV) := by
        rw [CFSG.Open.rankThreeLayer]
        exact le_sSup hB
      have h := A3.subnormal_inf_right hB.2.1
        (s16h_rankThreeLayer_le (Mbar D.M V₀ V hV))
      rwa [inf_eq_left.2 hle] at h
  obtain ⟨C, hC, hCmap⟩ := s16h_exists_component_over ψ hQ hB'
  obtain ⟨K, hKY, hKs, hKperf, hKq, -, hKmap⟩ := s15_Three_core_of_component hC
  refine ⟨K, ⟨A3.subnormal_trans hKs hYsub, hKperf, hKq⟩, ?_⟩
  have hbarK : barSub V₀ V hV K = C.map ψ := by
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
      refine (mem_barSub V₀ V hV K (ψ c)).2 ⟨⟨(y : G), hYs y.2⟩, hyK, ?_⟩
      change actTil V₀ V hV ⟨(y : G), hYs y.2⟩ = ψ c
      rw [← hyc]
      change actTil V₀ V hV ⟨(y : G), hYs y.2⟩ = ψ (QuotientGroup.mk y)
      rw [hψ y]
  exact hbarK.trans hCmap

theorem s16h_not_thin_of_barSub_pRank {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank q (barSub V₀ V hV K)) : ¬ F08.Thin8 K := by
  intro hthin
  let S : Subgroup G := stabTil V₀ V
  let A : Subgroup ↥S := K.subgroupOf S
  let f : ↥S →* MulAut (Vtil V₀ V hV) := actTil V₀ V hV
  have hbar : barSub V₀ V hV K = A.map f := rfl
  rw [hbar] at h
  obtain ⟨E₀, hE₀le, hE₀ea, hE₀card⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (A.map f)
  have hk2 : 2 ≤ CFSG.Open.pRank q E₀ :=
    h.trans (CFSG.SectionRank.le_pRank hq.one_lt (le_refl E₀) hE₀ea hE₀card)
  have hE₀nc : ¬ IsCyclic E₀ :=
    CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank hq hk2
  have hE₀p : IsPGroup q E₀ := IsPGroup.of_card hE₀card
  let φ : ↥A →* MulAut (Vtil V₀ V hV) := f.comp A.subtype
  have hφrange : φ.range = A.map f := by
    rw [MonoidHom.range_eq_map]
    show (⊤ : Subgroup ↥A).map (f.comp A.subtype) = A.map f
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  have hE₀le' : E₀ ≤ φ.range := by rw [hφrange]; exact hE₀le
  obtain ⟨B, hBp, hBnc, -⟩ := exists_noncyclic_pGroup_map_le φ hq hE₀le' hE₀p hE₀nc
  let ψ : ↥A →* G := (Subgroup.subtype S).comp A.subtype
  let X : Subgroup G := B.map ψ
  have hψinj : Function.Injective ψ := S.subtype_injective.comp A.subtype_injective
  have hXp : IsPGroup q X := hBp.map ψ
  have hXnc : ¬ IsCyclic X := by
    intro hc
    apply hBnc
    have e : ↥B ≃* ↥X := B.equivMapOfInjective ψ hψinj
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hXK : X ≤ K := by
    have h1 : B.map A.subtype ≤ A := by
      rintro _ ⟨b, -, rfl⟩
      exact b.2
    have h2 : (B.map A.subtype).map S.subtype ≤ A.map S.subtype := Subgroup.map_mono h1
    have h3 : A.map S.subtype ≤ K := by
      change (K.subgroupOf S).map S.subtype ≤ K
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    have hXeq : X = (B.map A.subtype).map S.subtype := by
      change B.map ((Subgroup.subtype S).comp A.subtype) = (B.map A.subtype).map S.subtype
      rw [Subgroup.map_map]
    rw [hXeq]
    exact h2.trans h3
  have hKrank : 2 ≤ CFSG.Open.pRank q K :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6.two_le_pRank_of_not_isCyclic hq hq2 hXp hXnc).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt hXK)
  have := hthin q hq hq2
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
