module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Apply

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

private noncomputable def s15BarHom2 (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
  ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict _
    (fun m => by
      change actTil V₀ V hV ⟨(m : G), hMs m.2⟩ ∈ Mbar D.M V₀ V hV
      exact actTil_mem_barSub V₀ V hV m.2 (hMs m.2))

private theorem s15BarHom2_surjective (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : Function.Surjective (s15BarHom2 D hV hMs) := by
  intro y
  obtain ⟨g, hgM, hgy⟩ := (mem_barSub V₀ V hV D.M y).1 y.2
  refine ⟨⟨(g : G), hgM⟩, Subtype.ext ?_⟩
  show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = (y : MulAut (Vtil V₀ V hV))
  rw [show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = actTil V₀ V hV g from
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
  exact hgy

private theorem s15BarHom2_ker (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) :
    (s15BarHom2 D hV hMs).ker = (F11.CTilde D.M V₀ V).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer V₀ V))]
  constructor
  · intro hm
    refine ⟨m.2, hMs m.2, ?_⟩
    have h2 := congrArg Subtype.val hm
    change actTil V₀ V hV (Subgroup.inclusion hMs m) = 1 at h2
    rwa [show Subgroup.inclusion hMs m = (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) from
      Subtype.ext rfl] at h2
  · rintro ⟨-, hst, hact⟩
    apply Subtype.ext
    show actTil V₀ V hV ⟨(m : G), hMs m.2⟩ = 1
    rw [show (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) = ⟨(m : G), hst⟩ from Subtype.ext rfl]
    exact hact

private noncomputable def s15BarEquiv2 (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    F11.MBar11 D.M V₀ V ≃* ↥(Mbar D.M V₀ V hV) :=
  QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    (s15BarHom2_surjective D hV hMs) (s15BarHom2_ker D hV hMs).symm

private theorem s15BarEquiv2_mk (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] (m : ↥D.M) :
    s15BarEquiv2 D hV hMs
        (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M) m) =
      s15BarHom2 D hV hMs m :=
  QuotientGroup.liftEquiv_mk _ _ _ m

private theorem s15_Three_map_barImage11 (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] (X : Subgroup G)
    (hX : X ≤ D.M) :
    (F11.barImage11 D.M V₀ V X).map (s15BarEquiv2 D hV hMs).toMonoidHom =
      (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
  ext ψ
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [F11.barImage11, Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change (s15BarEquiv2 D hV hMs
      (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M) x)).1 ∈ barSub V₀ V hV X
    rw [s15BarEquiv2_mk]
    exact actTil_mem_barSub V₀ V hV (Subgroup.mem_subgroupOf.1 hx) (hMs x.2)
  · intro hψ
    obtain ⟨g, hgX, hgψ⟩ := (mem_barSub V₀ V hV X ψ).1 hψ
    refine ⟨QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M) ⟨(g : G), hX hgX⟩, ?_, ?_⟩
    · rw [F11.barImage11, Subgroup.mem_map]
      refine ⟨⟨(g : G), hX hgX⟩, ?_, rfl⟩
      exact (Subgroup.mem_subgroupOf).2 hgX
    · change s15BarEquiv2 D hV hMs
          (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M) ⟨(g : G), hX hgX⟩) = ψ
      rw [s15BarEquiv2_mk]
      apply Subtype.ext
      show actTil V₀ V hV ⟨(g : G), hMs (hX hgX)⟩ = ψ
      rw [show actTil V₀ V hV ⟨(g : G), hMs (hX hgX)⟩ = actTil V₀ V hV g from
        congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
      exact hgψ

private theorem s15_Three_iSup_subgroupOf {A : Type} [Group A] {S : Subgroup A}
    {ι : Sort*} (H : ι → Subgroup A) (hH : ∀ i, H i ≤ S) :
    (⨆ i, H i).subgroupOf S = ⨆ i, (H i).subgroupOf S := by
  apply Subgroup.map_injective (Subgroup.subtype_injective S)
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_iSup]
  rw [show (⨆ i, map S.subtype ((H i).subgroupOf S)) = ⨆ i, H i by
    apply iSup_congr
    intro i
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hH i)]]
  exact inf_eq_left.2 (iSup_le hH)

private theorem s15_Three_isComponentOf_map_mulEquiv_apply {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {L H : Subgroup A} (h : CFSG.Open.IsComponentOf L H) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (H.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map e.toMonoidHom h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective).symm
      h.2.2⟩

private theorem s15_Three_map_mulEquiv_map_symm {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup A) : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A from by
    ext x; simp, Subgroup.map_id]

private theorem s15_Three_map_symm_map {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup B) : (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B from by
    ext x; simp, Subgroup.map_id]

private theorem s15_Three_isComponentOf_map_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {L H : Subgroup A} :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (H.map e.toMonoidHom) ↔
      CFSG.Open.IsComponentOf L H := by
  refine ⟨fun h => ?_, s15_Three_isComponentOf_map_mulEquiv_apply e⟩
  have h' := s15_Three_isComponentOf_map_mulEquiv_apply e.symm h
  rwa [s15_Three_map_mulEquiv_map_symm e L, s15_Three_map_mulEquiv_map_symm e H] at h'

private theorem s15_Three_isComponentOf_subgroupOf {A : Type} [Group A] {S L H : Subgroup A}
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

private theorem s15_Three_layer_map_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (H : Subgroup A) :
    rankThreeLayer (H.map e.toMonoidHom) = (rankThreeLayer H).map e.toMonoidHom := by
  apply le_antisymm
  · refine sSup_le fun K hK => ?_
    have hK' : CFSG.Open.IsComponentOf (K.map e.symm.toMonoidHom) H := by
      refine (s15_Three_isComponentOf_map_mulEquiv e).1 ?_
      rwa [s15_Three_map_symm_map e K]
    have hle : K.map e.symm.toMonoidHom ≤ rankThreeLayer H := by
      rw [rankThreeLayer]
      exact le_sSup hK'
    have hle2 := Subgroup.map_mono (f := e.toMonoidHom) hle
    rwa [s15_Three_map_symm_map e K] at hle2
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro L hL
    have hle : L.map e.toMonoidHom ≤ rankThreeLayer (H.map e.toMonoidHom) := by
      rw [rankThreeLayer]
      exact le_sSup (s15_Three_isComponentOf_map_mulEquiv_apply e hL)
    exact (Subgroup.map_le_iff_le_comap).1 hle

private theorem s15_Three_layer_subgroupOf {A : Type} [Group A] {S H : Subgroup A} (hHS : H ≤ S) :
    rankThreeLayer (H.subgroupOf S) = (rankThreeLayer H).subgroupOf S := by
  have hsub : (rankThreeLayer H).subgroupOf S =
      ⨆ L : {L : Subgroup A // CFSG.Open.IsComponentOf L H},
        (L : Subgroup A).subgroupOf S := by
    rw [rankThreeLayer, sSup_eq_iSup']
    exact s15_Three_iSup_subgroupOf (S := S)
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
      refine (s15_Three_isComponentOf_subgroupOf (hLS := ?_) hHS).1 ?_
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
      (s15_Three_isComponentOf_subgroupOf (hLS := L.2.1.trans hHS) hHS).2 L.2
    exact le_iSup (fun K : {K : Subgroup ↥S // CFSG.Open.IsComponentOf K (H.subgroupOf S)} =>
      K.1) ⟨L.1.subgroupOf S, hL⟩

private theorem s15_Three_barSub_iSup₂ (hV : IsElemAbelian 2 V) (X : G → Subgroup G) (S : Set G)
    (hX : ∀ m ∈ S, X m ≤ stabTil V₀ V) :
    barSub V₀ V hV (⨆ m ∈ S, X m) = ⨆ m ∈ S, barSub V₀ V hV (X m) := by
  rw [← iSup_subtype'' S X, ← iSup_subtype'' S (fun m => barSub V₀ V hV (X m))]
  unfold barSub
  rw [s15_Three_iSup_subgroupOf (S := stabTil V₀ V) (H := fun m : S => X m.1)
    (fun m => hX m.1 m.2)]
  rw [Subgroup.map_iSup]

theorem s15_Three_barImage_equiv (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ e : F11.MBar11 D.M V₀ V ≃* ↥(Mbar D.M V₀ V hV), ∀ X : Subgroup G, X ≤ D.M →
      (F11.barImage11 D.M V₀ V X).map e.toMonoidHom =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) :=
  ⟨s15BarEquiv2 D hV hMs, fun X hX => s15_Three_map_barImage11 D hV hMs X hX⟩

theorem s15_Three_xstar_eq (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) :
    barSub (v1Sub D.M V₀ V hV L) V hV (preBarSub D.M V₀ V hV (s15XBar D V₀ V hV K₀)) =
      s15XStar D V₀ V hV L K₀ := by
  have hVeq : hV = h.isElemAbelian := Subsingleton.elim hV h.isElemAbelian
  subst hV
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hK0M : K₀ ≤ D.M := hshape.1.trans h.le
  have hconjM : ∀ m ∈ D.M, conjSubgroup K₀ m ≤ D.M := by
    intro m hm
    have hmap : D.M.map (MulAut.conj m⁻¹).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (D.M.inv_mem hm))
    calc conjSubgroup K₀ m = K₀.map (MulAut.conj m⁻¹).toMonoidHom := rfl
      _ ≤ D.M.map (MulAut.conj m⁻¹).toMonoidHom := Subgroup.map_mono hK0M
      _ = D.M := hmap
  have hgen0 : ∀ m ∈ D.M, conjSubgroup K₀ m ≤ stabTil V₀ V :=
    fun m hm => (hconjM m hm).trans hMs
  set Xbar : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    s15XBar D V₀ V h.isElemAbelian K₀ with hXbardef
  set X' : Subgroup G := ⨆ m ∈ D.M, conjSubgroup K₀ m with hX'def
  have hX'M : X' ≤ D.M := by
    rw [hX'def]
    exact iSup_le fun m => iSup_le fun hm => hconjM m hm
  have hpreM : preBarSub D.M V₀ V h.isElemAbelian Xbar ≤ D.M := inf_le_left
  have hbar_pre : barSub V₀ V h.isElemAbelian (preBarSub D.M V₀ V h.isElemAbelian Xbar) =
      Xbar := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 (s15_Three_xbar_le h h.isElemAbelian hshape)
  have hbar_X' : barSub V₀ V h.isElemAbelian X' = Xbar := by
    rw [hX'def]
    exact s15_Three_barSub_iSup₂ h.isElemAbelian (fun m => conjSubgroup K₀ m) D.M hgen0
  have hstar : barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (preBarSub D.M V₀ V h.isElemAbelian Xbar) =
      barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X' :=
    (s15_Three_barSub_star_iff D h1217 h hpreM hX'M).1 (hbar_pre.trans hbar_X'.symm)
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 h.isElemAbelian)
  have hgen1 : ∀ m ∈ D.M,
      conjSubgroup K₀ m ≤ stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
    fun m hm => (hconjM m hm).trans hMs1
  have hbar_X'star : barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X' =
      s15XStar D V₀ V h.isElemAbelian L K₀ := by
    rw [hX'def]
    exact s15_Three_barSub_iSup₂ h.isElemAbelian (fun m => conjSubgroup K₀ m) D.M hgen1
  exact hstar.trans hbar_X'star

private theorem s15_Three_conjSubgroup_le {K M : Subgroup G} (hK : K ≤ M) {m : G} (hm : m ∈ M) :
    conjSubgroup K m ≤ M := by
  intro x hx
  rw [conjSubgroup, Subgroup.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  show (MulAut.conj m⁻¹) k ∈ M
  rw [MulAut.conj_apply, inv_inv]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) (hK hk)) hm

private theorem s15_Three_barSub_conj2 {W₀ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil W₀ V) (hK : K₀ ≤ D.M) {m : G} (hm : m ∈ D.M) :
    barSub W₀ V hV (conjSubgroup K₀ m) =
      (barSub W₀ V hV K₀).map
        (MulAut.conj (actTil W₀ V hV ⟨m⁻¹, hMs (D.M.inv_mem hm)⟩)).toMonoidHom :=
  TwelveTwentyThree.barSub_map_conj (V₀ := W₀) (V := V) hV (hK.trans hMs) (hMs (D.M.inv_mem hm))

private theorem s15_Three_preBarSub_mono (hV : IsElemAbelian 2 V)
    {Xbar Ybar : Subgroup (MulAut (Vtil V₀ V hV))} (h : Xbar ≤ Ybar) :
    preBarSub D.M V₀ V hV Xbar ≤ preBarSub D.M V₀ V hV Ybar := by
  unfold preBarSub
  exact inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

private theorem s15_Three_map_conj_subgroupOf {H : Type} [Group H] {S K : Subgroup H}
    (hK : K ≤ S) {φ : H} (hφ : φ ∈ S) :
    (K.map (MulAut.conj φ).toMonoidHom).subgroupOf S =
      (K.subgroupOf S).map (MulAut.conj (⟨φ, hφ⟩ : ↥S)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
    apply Subtype.ext
    simpa [MulAut.conj_apply] using hkx
  · rintro ⟨k, hk, hkx⟩
    refine ⟨(k : H), Subgroup.mem_subgroupOf.1 hk, ?_⟩
    simpa [MulAut.conj_apply] using congrArg Subtype.val hkx

private theorem s15_Three_map_conj_comp {A B : Type} [Group A] [Group B] (f : A ≃* B)
    (K : Subgroup A) (g : A) :
    ((K.map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom) =
      (K.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul]

private theorem s15_Three_preBarSub_conj_mem (hV : IsElemAbelian 2 V) (h : Hyp151 D V₀ V L)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV)))
    (hXbar_le : Xbar ≤ Mbar D.M V₀ V hV)
    (hXbarN : (Xbar.subgroupOf (Mbar D.M V₀ V hV)).Normal) {m x : G} (hm : m ∈ D.M) :
    x ∈ preBarSub D.M V₀ V hV Xbar ↔
      m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Xbar := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hXbar_le).1 hXbarN
  constructor
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M V₀ V hV Xbar).1 hx
    have hst : m * x * m⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem (hMs hm) hxs)
        ((stabTil V₀ V).inv_mem (hMs hm))
    refine (mem_preBarSub D.M V₀ V hV Xbar).2
      ⟨D.M.mul_mem (D.M.mul_mem hm hxM) (D.M.inv_mem hm), hst, ?_⟩
    have hact : actTil V₀ V hV ⟨m * x * m⁻¹, hst⟩ =
        actTil V₀ V hV ⟨m, hMs hm⟩ * actTil V₀ V hV ⟨x, hxs⟩ *
          (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹ := by
      rw [show (⟨m * x * m⁻¹, hst⟩ : stabTil V₀ V) =
          ⟨m, hMs hm⟩ * ⟨x, hxs⟩ * (⟨m, hMs hm⟩ : stabTil V₀ V)⁻¹ from
        Subtype.ext (by simp [mul_assoc]), map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub V₀ V hV hm (hMs hm)))
    exact (hmem (actTil V₀ V hV ⟨x, hxs⟩)).1 hxXbar
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M V₀ V hV Xbar).1 hx
    have hx_eq : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    have hxM' : x ∈ D.M := by
      rw [hx_eq]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hm) hxM) hm
    have hxs' : x ∈ stabTil V₀ V := by
      rw [hx_eq]
      exact (stabTil V₀ V).mul_mem
        ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem (hMs hm)) hxs) (hMs hm)
    refine (mem_preBarSub D.M V₀ V hV Xbar).2 ⟨hxM', hxs', ?_⟩
    have hmsi : m⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem (hMs hm)
    have hact : actTil V₀ V hV ⟨x, hxs'⟩ =
        actTil V₀ V hV ⟨m⁻¹, hmsi⟩ * actTil V₀ V hV ⟨m * x * m⁻¹, hxs⟩ *
          (actTil V₀ V hV ⟨m⁻¹, hmsi⟩)⁻¹ := by
      rw [show (⟨x, hxs'⟩ : stabTil V₀ V) =
          ⟨m⁻¹, hmsi⟩ * ⟨m * x * m⁻¹, hxs⟩ * (⟨m⁻¹, hmsi⟩ : stabTil V₀ V)⁻¹ from
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group),
          map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub V₀ V hV (D.M.inv_mem hm) hmsi))
    exact (hmem (actTil V₀ V hV ⟨m * x * m⁻¹, hxs⟩)).1 hxXbar

private theorem s15_Three_xbar_subgroupOf_iSup (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) :
    (s15XBar D V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV) =
      ⨆ h : ↥(Mbar D.M V₀ V hV),
        ((barSub V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).map
          (MulAut.conj h).toMonoidHom := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hK0M : K₀ ≤ D.M := hshape.1.trans h.le
  let ψ : {m // m ∈ D.M} → ↥(Mbar D.M V₀ V hV) := fun m =>
    ⟨actTil V₀ V hV ⟨m.1⁻¹, hMs (D.M.inv_mem m.2)⟩,
      actTil_mem_barSub V₀ V hV (D.M.inv_mem m.2) (hMs (D.M.inv_mem m.2))⟩
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M y.1).1 y.2
    refine ⟨⟨(g : G)⁻¹, D.M.inv_mem hgM⟩, ?_⟩
    apply Subtype.ext
    change actTil V₀ V hV ⟨((g : G)⁻¹)⁻¹, _⟩ = (y : ↥(Mbar D.M V₀ V hV)).1
    rw [show (⟨((g : G)⁻¹)⁻¹, _⟩ : stabTil V₀ V) = g from Subtype.ext (by simp)]
    exact hgφ
  have hgen : ∀ m : {m // m ∈ D.M},
      (barSub V₀ V hV (conjSubgroup K₀ m.1)).subgroupOf (Mbar D.M V₀ V hV) =
        ((barSub V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).map
          (MulAut.conj (ψ m)).toMonoidHom := by
    intro m
    rw [s15_Three_barSub_conj2 hV hMs hK0M m.2,
      s15_Three_map_conj_subgroupOf (K := barSub V₀ V hV K₀)
        (barSub_mono V₀ V hV hK0M)
        (actTil_mem_barSub V₀ V hV (D.M.inv_mem m.2) (hMs (D.M.inv_mem m.2)))]
  let f : G → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup K₀ m)
  have hXbar : s15XBar D V₀ V hV K₀ = ⨆ m : {m // m ∈ D.M}, f m.1 := by
    rw [s15XBar]
    apply le_antisymm
    · apply iSup_le
      intro m
      apply iSup_le
      intro hm
      exact le_iSup (fun m : {m // m ∈ D.M} => f m.1) ⟨m, hm⟩
    · apply iSup_le
      intro m
      exact le_iSup₂ (f := fun m (_ : m ∈ D.M) => f m) m.1 m.2
  rw [hXbar]
  have hsub := @s15_Three_iSup_subgroupOf (MulAut (Vtil V₀ V hV)) _
    (Mbar D.M V₀ V hV) {m // m ∈ D.M} (fun m : {m // m ∈ D.M} => f m.1)
    (fun m => by
      show f m.1 ≤ Mbar D.M V₀ V hV
      exact barSub_mono V₀ V hV (s15_Three_conjSubgroup_le hK0M m.2))
  rw [hsub]
  have hcongr : (⨆ m : {m // m ∈ D.M},
        (barSub V₀ V hV (conjSubgroup K₀ m.1)).subgroupOf (Mbar D.M V₀ V hV)) =
      ⨆ m : {m // m ∈ D.M},
        ((barSub V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).map
          (MulAut.conj (ψ m)).toMonoidHom :=
    iSup_congr hgen
  rw [hcongr]
  apply le_antisymm
  · apply iSup_le
    intro m
    exact le_iSup (fun h : ↥(Mbar D.M V₀ V hV) =>
      ((barSub V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).map
        (MulAut.conj h).toMonoidHom) (ψ m)
  · apply iSup_le
    intro h
    obtain ⟨m, hm⟩ := hψ h
    rw [← hm]
    exact le_iSup (fun m : {m // m ∈ D.M} =>
      ((barSub V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).map
        (MulAut.conj (ψ m)).toMonoidHom) m

private theorem s15_Three_barImage11_layer (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀)) (X : Subgroup G) (hX_le : X ≤ D.M)
    (hbarX : barSub V₀ V hV X = s15XBar D V₀ V hV K₀)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [← s15_Three_layer_map_equiv e (F11.barImage11 D.M V₀ V X), he X hX_le, hbarX,
    s15_Three_layer_subgroupOf (hHS := s15_Three_xbar_le h hV hshape),
    s15_Three_xbar_layer h hV hshape hq]

private theorem s15_Three_barImage11_iSup (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hkcomp : CFSG.Open.IsComponentOf (barSub V₀ V hV K₀) (Mbar D.M V₀ V hV))
    (X : Subgroup G) (hX_le : X ≤ D.M)
    (hbarX : barSub V₀ V hV X = s15XBar D V₀ V hV K₀)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ Lbar : Subgroup (F11.MBar11 D.M V₀ V), CFSG.Open.IsComponentOf Lbar ⊤ ∧
      F11.barImage11 D.M V₀ V X =
        ⨆ g : F11.MBar11 D.M V₀ V, Lbar.map (MulAut.conj g).toMonoidHom := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hK0M : K₀ ≤ D.M := hshape.1.trans h.le
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  let S := Mbar D.M V₀ V hV
  let Ksub : Subgroup ↥S := (barSub V₀ V hV K₀).subgroupOf S
  set Lbar : Subgroup (F11.MBar11 D.M V₀ V) := Ksub.map e.symm.toMonoidHom with hLbardef
  have hKsub_comp : CFSG.Open.IsComponentOf Ksub ⊤ := by
    have hh := (s15_Three_isComponentOf_subgroupOf
      (L := barSub V₀ V hV K₀) (H := Mbar D.M V₀ V hV) (S := Mbar D.M V₀ V hV)
      (barSub_mono V₀ V hV hK0M) le_rfl).2 hkcomp
    rw [Subgroup.subgroupOf_self] at hh
    exact hh
  have hLbar_comp : CFSG.Open.IsComponentOf Lbar ⊤ := by
    have hh := s15_Three_isComponentOf_map_mulEquiv_apply (e := e.symm) hKsub_comp
    rw [Subgroup.map_top_of_surjective _ e.symm.surjective] at hh
    exact hh
  refine ⟨Lbar, hLbar_comp, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [he X hX_le, hbarX, s15_Three_xbar_subgroupOf_iSup h hV hshape, Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro y
    have hcomp := s15_Three_map_conj_comp e.symm Ksub (e (e.symm y))
    rw [e.apply_symm_apply y] at hcomp
    have hcomp' : (Lbar.map (MulAut.conj (e.symm y)).toMonoidHom).map e.toMonoidHom =
        Ksub.map (MulAut.conj y).toMonoidHom := by
      rw [hLbardef, hcomp,
        s15_Three_map_symm_map e (Ksub.map (MulAut.conj y).toMonoidHom)]
    rw [← hcomp']
    exact le_iSup (fun g : F11.MBar11 D.M V₀ V =>
      (Lbar.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom) (e.symm y)
  · apply iSup_le
    intro g
    have hcomp := s15_Three_map_conj_comp e.symm Ksub (e g)
    rw [e.symm_apply_apply g] at hcomp
    have hcomp' : (Lbar.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
        Ksub.map (MulAut.conj (e g)).toMonoidHom := by
      rw [hLbardef, hcomp,
        s15_Three_map_symm_map e (Ksub.map (MulAut.conj (e g)).toMonoidHom)]
    rw [hcomp']
    exact le_iSup (fun h : ↥S => Ksub.map (MulAut.conj h).toMonoidHom) (e g)

theorem s15_Three_Y119 (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀))) :
    ∃ X Y : Subgroup G, F11.CTilde D.M V₀ V ≤ X ∧ X ≤ D.M ∧ (X.subgroupOf D.M).Normal ∧
      barSub V₀ V hV X = s15XBar D V₀ V hV K₀ ∧ barSub V₀ V hV Y = s15XBar D V₀ V hV K₀ ∧
      barSub (v1Sub D.M V₀ V hV L) V hV Y = s15XStar D V₀ V hV L K₀ ∧
      ∀ [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal],
        F11.IsY119 D.M V₀ V X Y ∧ (¬ F09.Thin9 Y → ⁅Y, V₀⁆ = ⊥) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀) :=
    (hSimple (Vtil (v1Sub D.M V₀ V hV L) V hV) ↥(barSub V₀ V hV K₀)
      (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) hperf).1
  have hkcomp : CFSG.Open.IsComponentOf (barSub V₀ V hV K₀) (Mbar D.M V₀ V hV) :=
    s15_Three_kbar_component h hV hshape hq
  have hXbar_le : s15XBar D V₀ V hV K₀ ≤ Mbar D.M V₀ V hV := s15_Three_xbar_le h hV hshape
  have hXbarN : ((s15XBar D V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    s15_Three_xbar_normal h hV hshape
  let inst₀ : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  haveI := inst₀
  set Xbar : Subgroup (MulAut (Vtil V₀ V hV)) := s15XBar D V₀ V hV K₀ with hXbardef
  set X : Subgroup G := preBarSub D.M V₀ V hV Xbar with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV h.hyp125.pairFacts.le_normalizer]
    exact s15_Three_preBarSub_mono hV bot_le
  have hbarX : barSub V₀ V hV X = s15XBar D V₀ V hV K₀ := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 (s15_Three_xbar_le h hV hshape)
  have hXnormal : (X.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX_le]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ preBarSub D.M V₀ V hV Xbar ↔ m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Xbar
    exact s15_Three_preBarSub_conj_mem hV h Xbar hXbar_le hXbarN hm
  have hlayerim : rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X :=
    s15_Three_barImage11_layer h hV hshape hq X hX_le hbarX
  obtain ⟨Lbar, hLbar_comp, hunion⟩ :=
    s15_Three_barImage11_iSup h hV hshape hkcomp X hX_le hbarX
  have hLbar : ∃ Lbar : Subgroup (F11.MBar11 D.M V₀ V),
      CFSG.Open.IsComponentOf Lbar ⊤ ∧
        F11.barImage11 D.M V₀ V X =
          ⨆ g : F11.MBar11 D.M V₀ V, Lbar.map (MulAut.conj g).toMonoidHom :=
    ⟨Lbar, hLbar_comp, hunion⟩
  obtain ⟨Y, hY, hYthin⟩ :=
    h119 V₀ V (Hyp125.hyp11 h127 h.hyp125) X hCX hX_le hlayerim
  have hY_le : Y ≤ D.M := hY.1.trans hX_le
  have hYbar : F11.barImage11 D.M V₀ V Y = F11.barImage11 D.M V₀ V X := hY.2.2.2.2.2
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hbarY : barSub V₀ V hV Y = s15XBar D V₀ V hV K₀ := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he X hX_le, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le),
      inf_eq_left.2 (barSub_mono V₀ V hV hX_le), hbarX] at h2
    exact h2
  have hbarYstar : barSub (v1Sub D.M V₀ V hV L) V hV Y =
      s15XStar D V₀ V hV L K₀ := by
    have hbarY' : barSub V₀ V h.isElemAbelian Y = barSub V₀ V h.isElemAbelian X := by
      rw [show h.isElemAbelian = hV from Subsingleton.elim h.isElemAbelian hV]
      exact hbarY.trans hbarX.symm
    have hstarY' : barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian Y =
        barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X :=
      (s15_Three_barSub_star_iff D h1217 h hY_le hX_le).1 hbarY'
    have hstarY : barSub (v1Sub D.M V₀ V hV L) V hV Y =
        barSub (v1Sub D.M V₀ V hV L) V hV X := by
      rw [show hV = h.isElemAbelian from Subsingleton.elim hV h.isElemAbelian]
      exact hstarY'
    exact hstarY.trans (s15_Three_xstar_eq h1217 h hV hshape)
  exact ⟨X, Y, hCX, hX_le, hXnormal, hbarX, hbarY, hbarYstar, by
    intro inst
    rw [show inst = inst₀ from Subsingleton.elim inst inst₀]
    exact ⟨hY, hYthin hLbar⟩⟩
end Apply

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
