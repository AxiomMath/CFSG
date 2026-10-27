module

import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_layer_eq_rankThreeLayer_top (X : Type) [Group X] :
    CFSG.layer X = rankThreeLayer (⊤ : Subgroup X) := by
  rw [CFSG.layer.eq_sSup]
  unfold rankThreeLayer
  congr 1
  ext L
  exact CFSG.isComponent_iff_open L

private theorem c23ne_rankThreeLayer_eq_self {A : Type} [Group A] {L : Subgroup A}
    (hq : CFSG.Open.IsQuasisimple ↥L) : rankThreeLayer L = L :=
  le_antisymm (sSup_le fun _ hK => hK.1) (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩)

theorem c23ne_exists_calC_image (D : Data G) {V₀ V : Subgroup G}
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] (hH : F11.Hyp11 D V₀ V)
    (h119 : F11.R119 D) {Lb : Subgroup (F11.MBar11 D.M V₀ V)} (hLb : IsComponentOf Lb ⊤) :
    ∃ K ∈ calC D.M, F11.barImage11 D.M V₀ V K = Lb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLbq : CFSG.Open.IsQuasisimple ↥Lb := hLb.2.2
  have hLbsub : CFSG.Open.IsSubnormal Lb ⊤ := hLb.2.1
  set Xp : Subgroup G := F11.barPreimage11 D.M V₀ V Lb with hXp
  have hXpM : Xp ≤ D.M := Subgroup.map_subtype_le _
  have hCX : F11.CTilde D.M V₀ V ≤ Xp := by
    intro x hx
    have hxM : x ∈ D.M := WeakClosure81.cTilde_le_M D.M V₀ V hx
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨x, hxM⟩ ∈ Lb
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact Lb.one_mem
  have hbarXp : F11.barImage11 D.M V₀ V Xp = Lb := by
    unfold F11.barImage11
    rw [hXp]
    unfold F11.barPreimage11
    have h1 : ((Lb.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M))).map
        D.M.subtype).subgroupOf D.M =
        Lb.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)) :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Lb
  have hXpsub : CFSG.Open.IsSubnormal Xp D.M := by
    have h1 := CFSG.Open.IsSubnormal.map D.M.subtype
      (CFSG.Open.IsSubnormal.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M))
        hLbsub)
    rwa [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  obtain ⟨Y, hY, -⟩ := h119 V₀ V hH Xp hCX hXpM
    (by rw [hbarXp]; exact c23ne_rankThreeLayer_eq_self hLbq)
  obtain ⟨hYX, -, hO2E, hXY, -, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hXpM
  have hYsub : CFSG.Open.IsSubnormal Y Xp :=
    CFSG.Open.IsSubnormal.step hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY)
      (CFSG.Open.IsSubnormal.refl _)
  set f : ↥Y →* F11.MBar11 D.M V₀ V :=
    (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)).comp (Subgroup.inclusion hYM)
    with hf
  have hfrange : f.range = Lb := by
    rw [← hbarXp, ← hYbar, hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hlayer : CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ := by
    rw [c23ne_layer_eq_rankThreeLayer_top]
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
  have hfmem : ∀ y, f y ∈ Lb := fun y => hfrange ▸ (⟨y, rfl⟩ : f y ∈ f.range)
  set g : ↥Y →* ↥Lb := f.codRestrict Lb hfmem
  have hgs : Function.Surjective g := by
    intro z
    obtain ⟨y, hy⟩ := (hfrange.symm ▸ z.2 : (z : F11.MBar11 D.M V₀ V) ∈ f.range)
    exact ⟨y, Subtype.ext hy⟩
  obtain ⟨K, hK, htop⟩ := uc22p22vg_exists_calC_onto hLbq g hgs hlayer
  have hKY : K ≤ Y := hK.1.le
  refine ⟨K, ⟨hK.1.trans (hYsub.trans hXpsub), hK.2.1, hK.2.2⟩, ?_⟩
  have h1 : (K.subgroupOf Y).map f = Lb := by
    have h2 : f = Lb.subtype.comp g := by
      ext y
      rfl
    rw [h2, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1]
  unfold F11.barImage11
  rw [hf, ← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨(x : G), hKY hx⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem c23ne_barImage11_ne (M V₀ V : Subgroup G) [((F11.CTilde M V₀ V).subgroupOf M).Normal]
    {K K' : Subgroup G} (hK : K ∈ calC M) (hK' : K' ∈ CFSG.Quasithin.cComp M) (hne : K ≠ K')
    (hnt : F11.barImage11 M V₀ V K ≠ ⊥) :
    F11.barImage11 M V₀ V K ≠ F11.barImage11 M V₀ V K' := by
  intro heq
  have hKM : K ≤ M := uc22p22a_le_of_isSubnormal hK.1
  have hK'M : K' ≤ M := CFSG.Quasithin.le_of_mem_cComp hK'
  have hcomm : ⁅K, K'⁆ ≤ CFSG.Quasithin.solvRad M :=
    uc22p20e_comm_le_solvRad (uc22p20e_cComp_of_calC hK) hK' hne
  set π : ↥M →* F11.MBar11 M V₀ V := QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)
  have hperf : ⁅K.subgroupOf M, K.subgroupOf M⁆ = K.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKM, hK.2.1]
  have hcomm' : ⁅K.subgroupOf M, K'.subgroupOf M⁆ ≤ (CFSG.Quasithin.solvRad M).subgroupOf M := by
    show _ ≤ Subgroup.comap M.subtype _
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hKM, Subgroup.map_subgroupOf_eq_of_le hK'M]
    exact hcomm
  haveI := CFSG.Quasithin.solvRad_isSolvable M
  haveI hRs : Group.IsSolvable ↥((CFSG.Quasithin.solvRad M).subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.solvRad_le M)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.solvRad_le M)).injective
  haveI hRb : Group.IsSolvable ↥(((CFSG.Quasithin.solvRad M).subgroupOf M).map π) :=
    Group.isSolvable_of_surjective
      (MonoidHom.subgroupMap_surjective π ((CFSG.Quasithin.solvRad M).subgroupOf M))
  have hKbar : ⁅F11.barImage11 M V₀ V K, F11.barImage11 M V₀ V K⁆ =
      F11.barImage11 M V₀ V K := by
    unfold F11.barImage11
    rw [← Subgroup.map_commutator, hperf]
  have hle : F11.barImage11 M V₀ V K ≤ ((CFSG.Quasithin.solvRad M).subgroupOf M).map π := by
    calc F11.barImage11 M V₀ V K
        = ⁅F11.barImage11 M V₀ V K, F11.barImage11 M V₀ V K⁆ := hKbar.symm
      _ = ⁅F11.barImage11 M V₀ V K, F11.barImage11 M V₀ V K'⁆ := by rw [← heq]
      _ ≤ _ := by
        unfold F11.barImage11
        rw [← Subgroup.map_commutator]
        exact Subgroup.map_mono hcomm'
  haveI : Group.IsSolvable ↥(F11.barImage11 M V₀ V K) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥(F11.barImage11 M V₀ V K) := Subgroup.isPerfect_iff.2 hKbar
  haveI : Nontrivial ↥(F11.barImage11 M V₀ V K) := (Subgroup.nontrivial_iff_ne_bot _).2 hnt
  exact Group.IsPerfect.not_isSolvable ↥(F11.barImage11 M V₀ V K) inferInstance

private theorem c23ne_barSub_ne_of_ne {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) (hMV₀ : D.M ≤ normalizer (V₀ : Set G))
    {K K' : Subgroup G} (hK : K ∈ calC D.M) (hK' : K' ∈ CFSG.Quasithin.cComp D.M)
    (hne : K ≠ K') (hnt : barSub V₀ V hV K ≠ ⊥) :
    barSub V₀ V hV K ≠ barSub V₀ V hV K' := by
  haveI hN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hMV hMV₀
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have hK'M : K' ≤ D.M := CFSG.Quasithin.le_of_mem_cComp hK'
  have hnt' : F11.barImage11 D.M V₀ V K ≠ ⊥ := by
    intro hb
    apply hnt
    have h1 : (barSub V₀ V hV K).subgroupOf (Mbar D.M V₀ V hV) =
        (⊥ : Subgroup (MulAut (Vtil V₀ V hV))).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he K hKM, hb, Subgroup.map_bot, Subgroup.bot_subgroupOf]
    exact s16c7_eq_of_subgroupOf_eq (barSub_mono V₀ V hV hKM) bot_le h1
  have hne' := c23ne_barImage11_ne D.M V₀ V hK hK' hne hnt'
  intro hb
  exact hne' (Subgroup.map_injective e.injective (by rw [he K hKM, he K' hK'M, hb]))

private theorem c23ne_conjSubgroup_eq_map (A : Subgroup G) (g : G) :
    conjSubgroup A g = A.map (MulAut.conj g⁻¹).toMonoidHom := rfl

theorem c23ne_lift_factors (D : Data G) (h119 : F11.R119 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMV : D.M ≤ normalizer (V : Set G))
    (hMV₀ : D.M ≤ normalizer (V₀ : Set G)) (hH : F11.Hyp11 D V₀ V)
    {A₁ A₂ : Subgroup (MulAut (Vtil V₀ V hV))} (hA₁ : A₁ ≤ Mbar D.M V₀ V hV)
    (hA₂ : A₂ ≤ Mbar D.M V₀ V hV) (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hinf : A₁ ⊓ A₂ = ⊥) (hL₁ : IsL3 ↥A₁ 1) (hL₂ : IsL3 ↥A₂ 1)
    (hperm : ∀ φ ∈ Mbar D.M V₀ V hV,
      (A₁.map (MulAut.conj φ).toMonoidHom = A₁ ∧ A₂.map (MulAut.conj φ).toMonoidHom = A₂) ∨
      (A₁.map (MulAut.conj φ).toMonoidHom = A₂ ∧ A₂.map (MulAut.conj φ).toMonoidHom = A₁)) :
    ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
      barSub V₀ V hV K₁ = A₁ ∧ barSub V₀ V hV K₂ = A₂ ∧
      K₁ ≤ normalizer (K₂ : Set G) ∧ K₂ ≤ normalizer (K₁ : Set G) ∧
      ∀ m ∈ D.M, (conjSubgroup K₁ m = K₁ ∧ conjSubgroup K₂ m = K₂) ∨
        (conjSubgroup K₁ m = K₂ ∧ conjSubgroup K₂ m = K₁) := by
  haveI hN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hMV hMV₀
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hAsup : A₁ ⊔ A₂ ≤ Mbar D.M V₀ V hV := sup_le hA₁ hA₂
  have hMA : Mbar D.M V₀ V hV ≤
      normalizer ((A₁ ⊔ A₂ : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) := by
    intro φ hφ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (A₁ ⊔ A₂).map (MulAut.conj φ).toMonoidHom = A₁ ⊔ A₂
    rw [Subgroup.map_sup]
    rcases hperm φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hAsub : CFSG.Open.IsSubnormal (A₁ ⊔ A₂) (Mbar D.M V₀ V hV) :=
    CFSG.Open.IsSubnormal.step hAsup
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAsup).2 hMA) (CFSG.Open.IsSubnormal.refl _)
  have hA₂norm : A₂ ≤ normalizer (A₁ : Set (MulAut (Vtil V₀ V hV))) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      have h1 : b * a * b⁻¹ = a := by
        rw [show b * a = a * b from (hcomm a ha b hb).symm, mul_assoc, mul_inv_cancel,
          mul_one]
      change b * a * b⁻¹ ∈ A₁
      rwa [h1]
    · intro a ha
      exact ⟨a, ha, by
        change b * a * b⁻¹ = a
        rw [show b * a = a * b from (hcomm a ha b hb).symm, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hA₁norm : A₁ ≤ normalizer (A₂ : Set (MulAut (Vtil V₀ V hV))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x ⟨b, hb, rfl⟩
      have h1 : a * b * a⁻¹ = b := by
        rw [hcomm a ha b hb, mul_assoc, mul_inv_cancel, mul_one]
      change a * b * a⁻¹ ∈ A₂
      rwa [h1]
    · intro b hb
      exact ⟨b, hb, by
        change a * b * a⁻¹ = b
        rw [hcomm a ha b hb, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hnA₁ : (A₁.subgroupOf (A₁ ⊔ A₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hA₂norm)
  have hnA₂ : (A₂.subgroupOf (A₁ ⊔ A₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (sup_le hA₁norm Subgroup.le_normalizer)
  have hsub₁ : CFSG.Open.IsSubnormal A₁ (Mbar D.M V₀ V hV) :=
    CFSG.Open.IsSubnormal.step le_sup_left hnA₁ hAsub
  have hsub₂ : CFSG.Open.IsSubnormal A₂ (Mbar D.M V₀ V hV) :=
    CFSG.Open.IsSubnormal.step le_sup_right hnA₂ hAsub
  have hq₁ : CFSG.Open.IsQuasisimple ↥A₁ := s16c7_isQuasisimple_of_isL3 hL₁
  have hq₂ : CFSG.Open.IsQuasisimple ↥A₂ := s16c7_isQuasisimple_of_isL3 hL₂
  have hcomp₁ := s16c7_isComponentOf_map e hA₁ hsub₁ hq₁
  have hcomp₂ := s16c7_isComponentOf_map e hA₂ hsub₂ hq₂
  obtain ⟨K₁, hK₁, hK₁bar⟩ := c23ne_exists_calC_image D hH h119 hcomp₁
  obtain ⟨K₂, hK₂, hK₂bar⟩ := c23ne_exists_calC_image D hH h119 hcomp₂
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hK₂.1
  have hmapmap : ∀ S : Subgroup ↥(Mbar D.M V₀ V hV),
      (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
    intro S
    rw [Subgroup.map_map]
    have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [h, Subgroup.map_id]
  have hbar₁ : barSub V₀ V hV K₁ = A₁ := by
    have h1 : (barSub V₀ V hV K₁).subgroupOf (Mbar D.M V₀ V hV) =
        A₁.subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he K₁ hK₁M, hK₁bar, hmapmap]
    exact s16c7_eq_of_subgroupOf_eq (barSub_mono V₀ V hV hK₁M) hA₁ h1
  have hbar₂ : barSub V₀ V hV K₂ = A₂ := by
    have h1 : (barSub V₀ V hV K₂).subgroupOf (Mbar D.M V₀ V hV) =
        A₂.subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he K₂ hK₂M, hK₂bar, hmapmap]
    exact s16c7_eq_of_subgroupOf_eq (barSub_mono V₀ V hV hK₂M) hA₂ h1
  have hA₁ne : A₁ ≠ ⊥ := by
    intro h
    have := card_eq_of_isL3 hL₁
    rw [h, Subgroup.card_bot] at this
    omega
  have hA₂ne : A₂ ≠ ⊥ := by
    intro h
    have := card_eq_of_isL3 hL₂
    rw [h, Subgroup.card_bot] at this
    omega
  have hK₁₂ : K₁ ≠ K₂ := by
    intro h
    have h1 : A₁ = A₂ := by rw [← hbar₁, ← hbar₂, h]
    apply hA₁ne
    rw [← inf_idem A₁]
    nth_rewrite 2 [h1]
    exact hinf
  have hpermK : ∀ m ∈ D.M, ∀ K ∈ calC D.M,
      (barSub V₀ V hV K = A₁ ∨ barSub V₀ V hV K = A₂) →
      K.map (MulAut.conj m).toMonoidHom = K₁ ∨ K.map (MulAut.conj m).toMonoidHom = K₂ := by
    intro m hm K hK hKbar
    have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
    have hK' : K.map (MulAut.conj m).toMonoidHom ∈ calC D.M :=
      uc22p2214_calC_of_mem_conjSetOf hK ⟨m, hm, rfl⟩
    have hK'M : K.map (MulAut.conj m).toMonoidHom ≤ D.M :=
      uc22p22a_le_of_isSubnormal hK'.1
    have hmst : m ∈ stabTil V₀ V := hMs hm
    have hmb : actTil V₀ V hV ⟨m, hmst⟩ ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV hm hmst
    have hbarK' := s16c7_barSub_map_conj V₀ V hV hmst K
    have himg : barSub V₀ V hV (K.map (MulAut.conj m).toMonoidHom) = A₁ ∨
        barSub V₀ V hV (K.map (MulAut.conj m).toMonoidHom) = A₂ := by
      rw [hbarK']
      rcases hperm (actTil V₀ V hV ⟨m, hmst⟩) hmb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hKbar with h | h
        · rw [h, h1]; exact Or.inl rfl
        · rw [h, h2]; exact Or.inr rfl
      · rcases hKbar with h | h
        · rw [h, h1]; exact Or.inr rfl
        · rw [h, h2]; exact Or.inl rfl
    have key : ∀ (Kj : Subgroup G), Kj ∈ calC D.M → barSub V₀ V hV Kj ≠ ⊥ →
        barSub V₀ V hV (K.map (MulAut.conj m).toMonoidHom) = barSub V₀ V hV Kj →
        K.map (MulAut.conj m).toMonoidHom = Kj := by
      intro Kj hKj hne heq
      by_contra hne'
      exact c23ne_barSub_ne_of_ne hV hMV hMV₀ hK' (uc22p20e_cComp_of_calC hKj) hne'
        (heq.symm ▸ hne) heq
    rcases himg with h | h
    · left
      exact key K₁ hK₁ (by rw [hbar₁]; exact hA₁ne) (h.trans hbar₁.symm)
    · right
      exact key K₂ hK₂ (by rw [hbar₂]; exact hA₂ne) (h.trans hbar₂.symm)
  have hmapself : ∀ (K : Subgroup G) (k : G), k ∈ K →
      K.map (MulAut.conj k).toMonoidHom = K := fun K k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hk)
  have hn₁ : K₁ ≤ normalizer (K₂ : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show K₂.map (MulAut.conj k).toMonoidHom = K₂
    rcases hpermK k (hK₁M hk) K₂ hK₂ (Or.inr hbar₂) with h | h
    · exfalso
      apply hK₁₂
      have h2 : K₂.map (MulAut.conj k).toMonoidHom = K₁.map (MulAut.conj k).toMonoidHom := by
        rw [h, hmapself K₁ k hk]
      exact (Subgroup.map_injective (MulAut.conj k).injective h2).symm
    · exact h
  have hn₂ : K₂ ≤ normalizer (K₁ : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show K₁.map (MulAut.conj k).toMonoidHom = K₁
    rcases hpermK k (hK₂M hk) K₁ hK₁ (Or.inl hbar₁) with h | h
    · exact h
    · exfalso
      apply hK₁₂
      have h2 : K₁.map (MulAut.conj k).toMonoidHom = K₂.map (MulAut.conj k).toMonoidHom := by
        rw [h, hmapself K₂ k hk]
      exact Subgroup.map_injective (MulAut.conj k).injective h2
  refine ⟨K₁, K₂, hK₁, hK₂, hK₁₂, hbar₁, hbar₂, hn₁, hn₂, ?_⟩
  intro m hm
  have h1 := hpermK m⁻¹ (D.M.inv_mem hm) K₁ hK₁ (Or.inl hbar₁)
  have h2 := hpermK m⁻¹ (D.M.inv_mem hm) K₂ hK₂ (Or.inr hbar₂)
  rw [c23ne_conjSubgroup_eq_map K₁ m, c23ne_conjSubgroup_eq_map K₂ m]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso
    exact hK₁₂ (Subgroup.map_injective (MulAut.conj m⁻¹).injective (h1.trans h2.symm))
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exfalso
    exact hK₁₂ (Subgroup.map_injective (MulAut.conj m⁻¹).injective (h1.trans h2.symm))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
