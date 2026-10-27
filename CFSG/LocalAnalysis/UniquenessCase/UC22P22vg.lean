module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge2
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem uc22p22vg_layer_eq_rankThreeLayer_top (X : Type) [Group X] :
    CFSG.layer X = rankThreeLayer (⊤ : Subgroup X) := by
  rw [CFSG.layer.eq_sSup]
  unfold rankThreeLayer
  congr 1
  ext L
  exact CFSG.isComponent_iff_open L

private theorem uc22p22vg_rankThreeLayer_eq_self {A : Type} [Group A] {L : Subgroup A}
    (hq : CFSG.Open.IsQuasisimple ↥L) : rankThreeLayer L = L :=
  le_antisymm (sSup_le fun _ hK => hK.1) (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩)

private theorem uc22p22vg_not_isPGroup {A : Type} [Group A] [Finite A] (hq : CFSG.Open.IsQuasisimple A) {p : ℕ}
    [Fact p.Prime] : ¬ IsPGroup p A := by
  intro hp
  haveI : Group.IsPerfect A := ⟨hq.1⟩
  haveI : Nontrivial A := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  exact Group.IsPerfect.not_isNilpotent A hp.isNilpotent

private theorem uc22p22vg_isPerfect_map {A B : Type} [Group A] [Group B] {K : Subgroup A} (hK : ⁅K, K⁆ = K)
    (f : A →* B) : Group.IsPerfect ↥(K.map f) := by
  refine ⟨Subgroup.map_injective (K.map f).subtype_injective ?_⟩
  have htop : (⊤ : Subgroup ↥(K.map f)).map (K.map f).subtype = K.map f := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [commutator_def, Subgroup.map_commutator, htop, ← Subgroup.map_commutator, hK]

private theorem uc22p22vg_commutator_subgroupOf {Y K : Subgroup G} (hKY : K ≤ Y) (hK : ⁅K, K⁆ = K) :
    ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKY, hK]

theorem uc22p22vg_exists_calC_onto {Y : Subgroup G} {Lb : Type} [Group Lb] [Finite Lb]
    (hLb : CFSG.Open.IsQuasisimple Lb) (g : ↥Y →* Lb) (hg : Function.Surjective g)
    (hlayer : CFSG.layer (Bar2 Y) = ⊤) :
    ∃ K ∈ calC Y, (K.subgroupOf Y).map g = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup Lb := (CFSG.pCore 2 ↥Y).map g
  haveI hPn : P.Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map g hg
  have hPne : P ≠ ⊤ := by
    intro hPt
    have h2 : IsPGroup 2 ↥P := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map g
    rw [hPt] at h2
    exact uc22p22vg_not_isPGroup hLb (h2.of_equiv Subgroup.topEquiv)
  by_contra hno
  push Not at hno
  have hker : CFSG.pCore 2 ↥Y ≤ ((QuotientGroup.mk' P).comp g).ker := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨y, hy, rfl⟩
  set gb : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* Lb ⧸ P := QuotientGroup.lift _ _ hker with hgb
  have hall : ∀ C : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y), CFSG.IsComponent C → C.map gb = ⊥ := by
    intro C hC
    obtain ⟨K, hK, hKC⟩ := uc22p21c_exists_calC_of_component Y hC
    have hKY : K ≤ Y := hK.1.le
    haveI : Group.IsPerfect ↥((K.subgroupOf Y).map g) :=
      uc22p22vg_isPerfect_map (uc22p22vg_commutator_subgroupOf hKY hK.2.1) g
    have hsubn : CFSG.Open.IsSubnormal ((K.subgroupOf Y).map g) ⊤ :=
      CFSG.Open.IsSubnormal.of_mathlib (hK.1.subgroupOf.map hg)
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hLb _ hsubn with
      hbot | htop
    · rw [← hKC]
      unfold barImage
      rw [Subgroup.map_map, hgb, QuotientGroup.lift_comp_mk', ← Subgroup.map_map, hbot, Subgroup.map_bot]
    · exact (hno K hK htop).elim
  have htopmap : (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).map gb = ⊥ := by
    rw [← hlayer, CFSG.layer.eq_sSup, eq_bot_iff, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap, hall C hC]
  apply hPne
  rw [eq_top_iff]
  intro l _
  obtain ⟨y, rfl⟩ := hg l
  have hmem : gb (QuotientGroup.mk y) ∈ (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).map gb :=
    ⟨_, Subgroup.mem_top _, rfl⟩
  rw [htopmap, Subgroup.mem_bot, hgb, QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem uc22p22vg_exists_calC_image (D : Data G) {V : Subgroup G}
    (hMV : D.M ≤ normalizer (V : Set G)) (hH : F11.Hyp11 D ⊥ V) (h119 : R119W D)
    {Lb : Subgroup (MBar D.M V)} (hLb : IsComponentOf Lb ⊤) :
    ∃ K ∈ calC D.M, mbarImage D.M V K = Lb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN := cTilde_bot_normal D.M V hMV
  set e := mbarEquiv D.M V
  set L' : Subgroup (F11.MBar11 D.M ⊥ V) := Lb.map e.toMonoidHom with hL'
  have hL'q : CFSG.Open.IsQuasisimple ↥L' :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Lb.equivMapOfInjective e.toMonoidHom e.injective).symm hLb.2.2
  have hL'sub : CFSG.Open.IsSubnormal L' ⊤ := by
    have h1 := CFSG.Open.IsSubnormal.map e.toMonoidHom hLb.2.1
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h1
  set Xp : Subgroup G := F11.barPreimage11 D.M ⊥ V L' with hXp
  have hXpM : Xp ≤ D.M := Subgroup.map_subtype_le _
  have hCX : F11.CTilde D.M ⊥ V ≤ Xp := by
    intro x hx
    have hxM : x ∈ D.M := by
      rw [cTilde_bot] at hx
      exact hx.1
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨x, hxM⟩ ∈ L'
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact L'.one_mem
  have hbarXp : F11.barImage11 D.M ⊥ V Xp = L' := by
    unfold F11.barImage11
    rw [hXp]
    unfold F11.barPreimage11
    have h1 : ((L'.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ V).subgroupOf D.M))).map
        D.M.subtype).subgroupOf D.M =
        L'.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ V).subgroupOf D.M)) :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L'
  have hXpsub : CFSG.Open.IsSubnormal Xp D.M := by
    have h1 := CFSG.Open.IsSubnormal.map D.M.subtype
      (CFSG.Open.IsSubnormal.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ V).subgroupOf D.M)) hL'sub)
    rwa [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  obtain ⟨Y, hY, -⟩ := h119 V hH Xp hCX hXpM
    (by rw [hbarXp]; exact uc22p22vg_rankThreeLayer_eq_self hL'q)
  obtain ⟨hYX, -, hO2E, hXY, -, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hXpM
  have hYsub : CFSG.Open.IsSubnormal Y Xp :=
    CFSG.Open.IsSubnormal.step hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY)
      (CFSG.Open.IsSubnormal.refl _)
  set f : ↥Y →* F11.MBar11 D.M ⊥ V :=
    (QuotientGroup.mk' ((F11.CTilde D.M ⊥ V).subgroupOf D.M)).comp (Subgroup.inclusion hYM) with hf
  have hfrange : f.range = L' := by
    rw [← hbarXp, ← hYbar, hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hlayer : CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ := by
    rw [uc22p22vg_layer_eq_rankThreeLayer_top]
    set L := rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y))
    have h1 : (L.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype =
        (⊤ : Subgroup ↥Y).map Y.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hO2E
    have h2 := Subgroup.map_injective Y.subtype_injective h1
    have h3 := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)) L
    rw [h2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3
    exact h3.symm
  have hfmem : ∀ y, f y ∈ L' := fun y => hfrange ▸ (⟨y, rfl⟩ : f y ∈ f.range)
  set g : ↥Y →* ↥L' := f.codRestrict L' hfmem
  have hgs : Function.Surjective g := by
    intro z
    obtain ⟨y, hy⟩ := (hfrange.symm ▸ z.2 : (z : F11.MBar11 D.M ⊥ V) ∈ f.range)
    exact ⟨y, Subtype.ext hy⟩
  obtain ⟨K, hK, htop⟩ := uc22p22vg_exists_calC_onto hL'q g hgs hlayer
  have hKY : K ≤ Y := hK.1.le
  refine ⟨K, ⟨hK.1.trans (hYsub.trans hXpsub), hK.2.1, hK.2.2⟩, ?_⟩
  apply Subgroup.map_injective (show Function.Injective e.toMonoidHom from e.injective)
  rw [map_mbarImage]
  have h1 : (K.subgroupOf Y).map f = L' := by
    have h2 : f = L'.subtype.comp g := by
      ext y
      rfl
    rw [h2, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hL', ← h1]
  unfold F11.barImage11
  rw [hf, ← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨(x : G), hKY hx⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem uc22p22vg_ncard_le_two (D : Data G) (Ch : Choice2011 G) (h1117 : S21_17 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) :
    (conjSetOf D.M K).ncard ≤ 2 := by
  rcases h1117 h1930 c K hK with h | ⟨h, _⟩ | ⟨h, _⟩
  · have hK' : ∀ K' ∈ conjSetOf D.M K, K' = K := by
      rintro K' ⟨g, hg, rfl⟩
      have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
        calc K.map (MulAut.conj g).toMonoidHom ≤ conjClosure D.M K :=
              le_iSup₂_of_le (K.map (MulAut.conj g).toMonoidHom) ⟨g, hg, rfl⟩ le_rfl
          _ = K := h.symm
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    have hsub : conjSetOf D.M K ⊆ {K} := fun K' hK'' => hK' K' hK''
    exact (Set.ncard_le_ncard hsub (Set.finite_singleton K)).trans (by simp)
  · exact h.le
  · exact h.le

theorem uc22p22vg_hyp515_components (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h119 : R119W D) (h1117 : S21_17 D Ch) (c : Ctx22b D Ch) :
    ∀ L : Subgroup (MBar D.M c.V), IsComponentOf L ⊤ → F05.numConj L ≤ 2 := by
  intro L hL
  have hH : F11.Hyp11 D ⊥ c.V :=
    uc22p22c_hyp11 D (hV h1930 c).1
      (uc22p22o_not_isTI_of_hC D (uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM) c.hC)
  obtain ⟨K, hK, rfl⟩ := uc22p22vg_exists_calC_image D c.hVM hH h119 hL
  exact (uc22br4_numConj_mbarImage_le D.M c.V K).trans
    (uc22p22vg_ncard_le_two D Ch h1117 h1930 c.toCtx21 hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22
