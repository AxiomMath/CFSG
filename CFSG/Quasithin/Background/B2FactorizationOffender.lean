module

public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

theorem omegaOneOf_le (X : Subgroup G) : omegaOneOf X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem omegaOneCenterOf_le_centerOf (X : Subgroup G) : omegaOneCenterOf X ≤ centerOf X :=
  omegaOneOf_le _

theorem thompsonJ_le_baum (S : Subgroup G) : thompsonJ S ≤ baum S := by
  refine le_inf (thompsonJ_le_self S) ?_
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  exact (omegaOneCenterOf_le_centerOf _ hx).2

theorem baum_le (S : Subgroup G) : baum S ≤ S := inf_le_left

end B2F

section Lemma220

variable [Finite G] {V R : Subgroup G}

theorem inf_centralizer_thompsonJ_le (hV : IsElemAbelian 2 V) (hVR : V ≤ R) :
    V ⊓ Subgroup.centralizer (thompsonJ R : Set G) ≤ omegaOneCenterOf (thompsonJ R) := by
  rw [← (omegaOne_centralizer_thompsonJ R).1]
  intro v hv
  exact Subgroup.subset_closure ⟨⟨hVR hv.1, hv.2⟩, hV.2 v hv.1⟩

theorem B2_20 (hV : IsElemAbelian 2 V) (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G))
    {A : Subgroup (MulAut (IntMod V hV))}
    (hu : ∀ B, IsFFStarOffender (autI hV R) B → B = A)
    (hAC : A = autI hV R ⊓ centSub (fixV A)) :
    A = autI hV (thompsonJ R) ∧ autI hV (thompsonJ R) = autI hV (baum R) := by
  have hne : (offenderImages hV R).Nonempty := (offenderImages_nonempty_iff_not_le hV).2 hJ
  have hP : ∀ B ∈ offenderImages hV R, B = A := fun B hB =>
    hu B (offenderImages_isFFStarOffender hV hVR hRN hB)
  have hJA : autI hV (thompsonJ R) = A := by
    rw [autI_thompsonJ hV hRN]
    refine le_antisymm (iSup_le fun B => iSup_le fun hB => iSup_le fun _ => (hP B hB).le) ?_
    obtain ⟨B, hB⟩ := hne
    have hBA := hP B hB
    rw [← hBA]
    exact le_iSup₂_of_le B hB
      (le_iSup_of_le (offenderImages_isFFStarOffender hV hVR hRN hB).1 le_rfl)
  refine ⟨hJA.symm, le_antisymm (autI_mono hV (B2F.thompsonJ_le_baum R)) ?_⟩
  have hJN : thompsonJ R ≤ Subgroup.normalizer (V : Set G) :=
    (thompsonJ_le_self R).trans hRN
  calc autI hV (baum R) ≤ autI hV R ⊓ centSub (fixV A) := by
        refine le_inf (autI_mono hV (B2F.baum_le R)) ?_
        intro φ hφ
        obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hφ
        rw [mem_centSub]
        intro u hu'
        have hu1 : u ∈ fixV (autI hV (thompsonJ R)) := by rwa [hJA]
        have hu2 := (mem_fixV_autI hV hJN u).1 hu1
        have hE : u.val ∈ omegaOneCenterOf (thompsonJ R) :=
          inf_centralizer_thompsonJ_le hV hVR ⟨u.val_mem, hu2⟩
        have hcomm : (x : G) * u.val = u.val * x :=
          (Subgroup.mem_centralizer_iff.1 hx.2 u.val hE).symm
        refine IntMod.val_injective ?_
        rw [convI_apply_val, hcomm, mul_inv_cancel_right]
    _ = A := hAC.symm
    _ = autI hV (thompsonJ R) := hJA.symm

end Lemma220

section Lemma210

variable [Finite G] {V : Subgroup G}

@[expose] def offenderImagesConj (hV : IsElemAbelian 2 V) (R : Subgroup G) :
    Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | B ≠ ⊥ ∧ ∃ A : Subgroup G, B = autI hV A ∧ ∃ g : G, IsMaxElemAbelian R (cjSub g⁻¹ A)}

theorem map_conj_map_conj {W : Type*} [CommGroup W] (a b : MulAut W) (B : Subgroup (MulAut W)) :
    (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      B.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem conjAut_eq_map {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp

theorem isFFStarOffender_mono {W : Type*} [CommGroup W] {X Y A : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (h : IsFFStarOffender X A) : IsFFStarOffender Y A :=
  ⟨h.1.trans hXY, h.2⟩

variable (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem mem_offenderImagesConj_iff (hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G))
    {R : Subgroup G} {B : Subgroup (MulAut (IntMod V hV))} :
    B ∈ offenderImagesConj hV R ↔
      ∃ g : G, ∃ B' ∈ offenderImages hV R,
        B = B'.map (MulAut.conj (convI hV ⟨g, hN g⟩)).toMonoidHom := by
  constructor
  · rintro ⟨hB0, A, rfl, g, hg⟩
    refine ⟨g, autI hV (cjSub g⁻¹ A), ⟨cjSub g⁻¹ A, ⟨hg, ?_⟩, rfl⟩, ?_⟩
    · intro h
      apply hB0
      have h1 : cjSub g (cjSub g⁻¹ A) ≤ Subgroup.centralizer (V : Set G) :=
        cjSub_le (B2F.normalizer_le_normalizer_centralizer V (hN g)) h
      rw [cjSub_cjSub_inv] at h1
      exact autI_eq_bot_of_le_centralizer hV h1
    · have := autI_cjSub hV (hN g) (cjSub g⁻¹ A)
      rw [cjSub_cjSub_inv] at this
      exact this.symm
  · rintro ⟨g, B', ⟨A', ⟨hA', hA'C⟩, rfl⟩, rfl⟩
    have hnb : autI hV A' ≠ ⊥ := fun h => hA'C ((autI_eq_bot_iff hV (fun x _ => hN x)).1 h)
    refine ⟨?_, cjSub g A', autI_cjSub hV (hN g) A', g, ?_⟩
    · rw [← conjAut_eq_map]
      exact B1.conjAut_ne_bot hnb
    · rw [cjSub_inv_cjSub]
      exact hA'

theorem B2_10_1_stable {R : Subgroup G} (hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G))
    (hVR : V ≤ R) (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) :
    IsStableFF (autI hV ⊤) (offenderImagesConj hV R) ∧
      ffJP (offenderImagesConj hV R) (autI hV ⊤) ≤ ffJ (autI hV ⊤) := by
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun x _ => hN x
  have hne : (offenderImages hV R).Nonempty := (offenderImages_nonempty_iff_not_le hV).2 hJ
  have hRst := B2_5 hV hVR hRN hne
  have hoff : ∀ B ∈ offenderImagesConj hV R, IsFFStarOffender (autI hV ⊤) B := by
    intro B hB
    obtain ⟨g, B', hB', rfl⟩ := (mem_offenderImagesConj_iff hV hN).1 hB
    have h1 : IsFFStarOffender (autI hV ⊤) B' :=
      isFFStarOffender_mono (autI_mono hV le_top) (offenderImages_isFFStarOffender hV hVR hRN hB')
    rw [← conjAut_eq_map]
    exact B1.isFFStarOffender_conjAut h1 (convI_mem_autI hV (Subgroup.mem_top g) (hN g))
  refine ⟨⟨?_, hoff, ?_, ?_⟩, ?_⟩
  · obtain ⟨B', hB'⟩ := hne
    exact ⟨_, (mem_offenderImagesConj_iff hV hN).2 ⟨1, B', hB', rfl⟩⟩
  · intro B hB h hh
    obtain ⟨g, B', hB', rfl⟩ := (mem_offenderImagesConj_iff hV hN).1 hB
    obtain ⟨k, -, rfl⟩ := (mem_autI hV).1 hh
    refine (mem_offenderImagesConj_iff hV hN).2 ⟨(k : G) * g, B', hB', ?_⟩
    rw [map_conj_map_conj, ← map_mul]
    rfl
  · intro B hB B₁ hB₁
    obtain ⟨g, B', hB', rfl⟩ := (mem_offenderImagesConj_iff hV hN).1 hB
    set a : MulAut (IntMod V hV) := convI hV ⟨g, hN g⟩ with ha
    have haG : a ∈ autI hV ⊤ := convI_mem_autI hV (Subgroup.mem_top g) (hN g)
    have hle : FFLe (autI hV ⊤) (B1.conjAut a⁻¹ B₁) B' := by
      rw [← conjAut_eq_map] at hB₁
      have := B1.ffLe_conjAut hB₁ ((autI hV ⊤).inv_mem haG)
      rwa [B1.conjAut_inv_conjAut] at this
    have hB'off := offenderImages_isFFStarOffender hV hVR hRN hB'
    have hle' : FFLe (autI hV R) (B1.conjAut a⁻¹ B₁) B' :=
      ⟨⟨hle.2.2.1.trans hB'off.1, hle.1.2.1, hle.1.2.2⟩, hB'off.isA2, hle.2.2.1, hle.2.2.2⟩
    obtain ⟨D, hD, hDeq⟩ : B1.conjAut a⁻¹ B₁ ∈ offenderImages hV R := hRst.2.2.2 B' hB' _ hle'
    refine (mem_offenderImagesConj_iff hV hN).2 ⟨g, autI hV D, ⟨D, hD, rfl⟩, ?_⟩
    rw [← hDeq, ← conjAut_eq_map]
    exact (B1.conjAut_conjAut_inv a B₁).symm
  · exact iSup_le fun B => iSup_le fun hB => iSup_le fun _ => le_iSup₂_of_le B (hoff B hB) le_rfl

theorem B2_10_1 (hVN : V.Normal) {R : Subgroup G} (hOR : pCoreOf 2 (⊤ : Subgroup G) ≤ R)
    (hC : pCoreOf 2 (⊤ : Subgroup G) = R ⊓ Subgroup.centralizer (V : Set G)) :
    ((thompsonJ R = thompsonJ (pCoreOf 2 (⊤ : Subgroup G)) ∧
        baum R = baum (pCoreOf 2 (⊤ : Subgroup G))) ∧
      (thompsonJ R).Normal ∧ (baum R).Normal) ∨
    (IsStableFF (autI hV ⊤) (offenderImagesConj hV R) ∧
      ffJP (offenderImagesConj hV R) (autI hV ⊤) ≤ ffJ (autI hV ⊤)) := by
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hVN]
    exact Subgroup.mem_top g
  have hVQ : V ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    le_pCoreOf_of_le_normalizer 2 le_top (fun g _ => hN g) (B2F.isPGroup_of_isElemAbelian hV)
  have hVR : V ≤ R := hVQ.trans hOR
  by_cases hJ : thompsonJ R ≤ Subgroup.centralizer (V : Set G)
  · left
    have hJR : thompsonJ R ≤ R ⊓ Subgroup.centralizer (V : Set G) := le_inf (thompsonJ_le_self R) hJ
    have hJQ : thompsonJ R ≤ pCoreOf 2 (⊤ : Subgroup G) := by rw [hC]; exact hJR
    have hJeq : thompsonJ R = thompsonJ (pCoreOf 2 (⊤ : Subgroup G)) :=
      thompsonJ_eq_of_le hJQ hOR
    have hBeq : baum R = baum (pCoreOf 2 (⊤ : Subgroup G)) := by
      rw [hC]
      exact baum_eq_baum_centralizer hV hVR hJR
    have hQN : Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup G) : Set G) = ⊤ :=
      top_le_iff.1 fun g _ => le_normalizer_pCoreOf 2 (⊤ : Subgroup G) (Subgroup.mem_top g)
    refine ⟨⟨hJeq, hBeq⟩, ?_, ?_⟩
    · rw [hJeq]
      have h := normalizer_le_normalizer_thompsonJ (pCoreOf 2 (⊤ : Subgroup G))
      rw [hQN] at h
      exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h)
    · rw [hBeq]
      have h := normalizer_le_normalizer_baum (pCoreOf 2 (⊤ : Subgroup G))
      rw [hQN] at h
      exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h)
  · right
    exact B2_10_1_stable hV hN hVR hJ

end Lemma210

end CFSG.Quasithin
