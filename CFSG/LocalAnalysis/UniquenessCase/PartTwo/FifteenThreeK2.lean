module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Cover

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

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

theorem s15_Three_component_cover (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀))
    {Y : Subgroup G} (hYM : CFSG.Open.IsSubnormal Y D.M) (hYE : F11.O2E Y = Y)
    (hYX : barSub V₀ V hV Y = s15XBar D V₀ V hV K₀) :
    ∃ C : Subgroup (Bar2 Y), CFSG.Open.IsComponentOf C ⊤ ∧
      barSub V₀ V hV ((C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype) =
        barSub V₀ V hV K₀ := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
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
  have hKbar : barSub V₀ V hV K₀ = T ⟨1, D.M.one_mem⟩ := by
    simp [T, conjSubgroup_one]
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
      C.map ψ = barSub V₀ V hV K₀ := by
    by_contra hcontra
    push Not at hcontra
    have hcentral : s15XBar D V₀ V hV K₀ ≤
        Subgroup.centralizer (barSub V₀ V hV K₀ : Set (MulAut (Vtil V₀ V hV))) := by
      rw [hsup]
      refine iSup_le fun C => iSup_le fun hC => ?_
      rcases k2_map_component_eq_bot_or_isComponentOf hV ψ hXmap hC with hbot | hcomp
      · rw [hbot]; exact bot_le
      · rw [hXbar_eq] at hcomp
        obtain ⟨m, hm⟩ := s15_Three_component_eq hqA hcommA hcomp
        have hTmne : T m ≠ T ⟨1, D.M.one_mem⟩ := by
          intro heq
          exact hcontra C hC (by rw [hm, heq, ← hKbar])
        have hcommm := (hcommA m ⟨1, D.M.one_mem⟩).resolve_left hTmne
        rw [hm]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ T ⟨1, D.M.one_mem⟩ := by rwa [← hKbar]
        exact (hcommm x hx y hy').symm
    have hKleX : barSub V₀ V hV K₀ ≤ s15XBar D V₀ V hV K₀ := by
      rw [hXbar_eq, hKbar]
      exact le_iSup T ⟨1, D.M.one_mem⟩
    have hcommK : ∀ x y : ↥(barSub V₀ V hV K₀), x * y = y * x := by
      intro x y
      have hxX : (x : MulAut (Vtil V₀ V hV)) ∈ s15XBar D V₀ V hV K₀ := hKleX x.2
      have h1 := hcentral hxX
      rw [Subgroup.mem_centralizer_iff] at h1
      exact Subtype.ext (h1 y y.2).symm
    exact (k2_not_forall_comm_of_isQuasisimple hq) hcommK
  obtain ⟨C, hC, hCmap⟩ := hex
  refine ⟨C, hC, ?_⟩
  rw [s15_Three_barSub_comap_map hV hYs ψ hψ C, hCmap]

theorem s15_Three_cover_iso (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hKs : CFSG.Open.IsSubnormal K Y)
    (hYC : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y)
    (hYM : Y ≤ D.M) (h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hT : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀))
    (hZ : Subgroup.center ↥(barSub V₀ V hV K₀) = ⊥)
    (hKT : barSub V₀ V hV K = barSub V₀ V hV K₀) :
    Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥(barSub V₀ V hV K₀)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hKstab : K ≤ stabTil V₀ V := hKY.trans (hYM.trans hMs)
  let φ : ↥K →* ↥(barSub V₀ V hV K₀) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hKstab)).codRestrict (barSub V₀ V hV K₀)
      (fun x => by rw [← hKT]; exact actTil_mem_barSub V₀ V hV x.2 (hKstab x.2))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    have hψ' : ψ ∈ barSub V₀ V hV K := hKT ▸ hψ
    obtain ⟨g, hgK, hgψ⟩ := (mem_barSub V₀ V hV K ψ).1 hψ'
    refine ⟨⟨(g : G), hgK⟩, Subtype.ext ?_⟩
    change actTil V₀ V hV ⟨(g : G), hKstab hgK⟩ = ψ
    rw [show (⟨(g : G), hKstab hgK⟩ : ↥(stabTil V₀ V)) = g from Subtype.ext rfl]
    exact hgψ
  have hker : φ.ker = (K ⊓ F11.CTilde D.M V₀ V).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      refine (mem_cTilde_iff hV hMnorm).2 ⟨hYM (hKY x.2), hKstab x.2, ?_⟩
      exact congrArg Subtype.val hx
    · rintro ⟨-, hxCT⟩
      apply Subtype.ext
      change actTil V₀ V hV ⟨(x : G), hKstab x.2⟩ = 1
      obtain ⟨h, hh⟩ := ((mem_cTilde_iff hV hMnorm).1 hxCT).2
      rw [show (⟨(x : G), hKstab x.2⟩ : ↥(stabTil V₀ V)) =
        (⟨(x : G), h⟩ : ↥(stabTil V₀ V)) from Subtype.ext rfl]
      exact hh
  have hkerSolv : IsSolvable ↥φ.ker := by
    rw [hker]
    have hmap : (((K ⊓ F11.CTilde D.M V₀ V).subgroupOf K).map K.subtype) ≤ OInf Y := by
      rintro z ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ K ⊓ F11.CTilde D.M V₀ V := (Subgroup.mem_subgroupOf).1 hx
      rw [Subgroup.mem_inf] at hx'
      exact hYC ⟨hKY hx'.1, hx'.2⟩
    let g : ↥((K ⊓ F11.CTilde D.M V₀ V).subgroupOf K) →* ↥(OInf Y) :=
      ((K.subtype.comp (Subgroup.subtype _))).codRestrict (OInf Y)
        (fun x => hmap ⟨x, x.2, rfl⟩)
    haveI hRad : Group.IsSolvable ↥(CFSG.solvableRadical ↥Y) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    haveI : Group.IsSolvable ↥(OInf Y) := by
      unfold OInf
      exact Group.isSolvable_of_surjective
        (f := ((CFSG.solvableRadical ↥Y).equivMapOfInjective Y.subtype
          Y.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(OInf Y) => (z : G)) hxy
  have hpCore : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 K := ⟨x, hx, rfl⟩
    have hPK : pCoreOf 2 K ≤ pCoreOf 2 Y := A4.pCoreOf_le_of_subnormal 2 hKs
    have h1 : actTil V₀ V hV ⟨(x : G), hKstab x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 Y) :=
      barSub_mono V₀ V hV hPK (actTil_mem_barSub V₀ V hV hxP (hKstab x.2))
    rw [h2, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  let φ' : Bar2 K →* ↥(barSub V₀ V hV K₀) := QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hpCore
  have hφ'surj : Function.Surjective φ' := by
    intro y
    obtain ⟨x, rfl⟩ := hφsurj y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker' : φ'.ker = (φ.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
    QuotientGroup.ker_lift (N := CFSG.pCore 2 ↥K) φ hpCore
  have hsoln' : IsSolvable ↥φ'.ker := by
    rw [hker']
    haveI : Group.IsSolvable ↥φ.ker := hkerSolv
    let m : ↥φ.ker →* ↥((φ.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) :=
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp φ.ker.subtype).codRestrict _
        (fun x => Subgroup.mem_map_of_mem _ x.2)
    have hm : Function.Surjective m := by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Group.isSolvable_of_surjective (f := m) hm
  exact s15_Three_quot_center_iso φ' hφ'surj
    (s15_Three_solvable_normal_le_center hKq φ'.ker inferInstance hsoln') hZ

theorem s15_Three_cover_K (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀))) :
    ∃ K : Subgroup G, s15Covers D V₀ V hV K₀ K := by
  obtain ⟨hq, hZ⟩ := hSimple (V := Vtil (v1Sub D.M V₀ V hV L) V hV)
    (X := ↥(barSub V₀ V hV K₀))
    (K := barSub (v1Sub D.M V₀ V hV L) V hV K₀)
    (Z := commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) hperf
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  obtain ⟨X, Y, hCTX, hXM, hXnorm, hXbar, hYX, -, hYrest⟩ :=
    s15_Three_Y119 hSimple h127 h119 h1217 h hV hshape hperf
  obtain ⟨hY119, -⟩ := hYrest
  have hYXsub : CFSG.Open.IsSubnormal Y X :=
    A3.subnormal_of_normal hY119.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hY119.1).mpr hY119.2.2.2.1)
  have hXMsub : CFSG.Open.IsSubnormal X D.M :=
    A3.subnormal_of_normal hXM hXnorm
  have hYMsub : CFSG.Open.IsSubnormal Y D.M := A3.subnormal_trans hYXsub hXMsub
  have hYE : F11.O2E Y = Y := hY119.2.2.1
  have hYC : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y := hY119.2.2.2.2.1
  obtain ⟨C, hC, hCbar⟩ :=
    s15_Three_component_cover h hV hshape hq hYMsub hYE hYX
  obtain ⟨K, hKY, hKs, hKperf, hKq, -, hKmap⟩ := s15_Three_core_of_component hC
  have hYKstab : Y ≤ stabTil V₀ V := hYMsub.le.trans hMs
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hYMsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
  obtain ⟨ψ, hψ⟩ := s15_Three_barLift_exists hV hYKstab h2
  have hbarK : barSub V₀ V hV K = barSub V₀ V hV K₀ := by
    have h1 : barSub V₀ V hV K = C.map ψ := by
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
    rw [h1, ← s15_Three_barSub_comap_map hV hYKstab ψ hψ C, hCbar]
  have hKMsub : CFSG.Open.IsSubnormal K D.M := A3.subnormal_trans hKs hYMsub
  have hKmem : K ∈ calC D.M := ⟨hKMsub, hKperf, hKq⟩
  have hiso : Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥(barSub V₀ V hV K₀)) :=
    s15_Three_cover_iso hV hMs hKY hKs hYC hYMsub.le h2 hKq hq hZ hbarK
  exact ⟨K, hKmem, 1, D.M.one_mem, by rw [conjSubgroup_one]; exact hbarK, hiso⟩

end Cover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
