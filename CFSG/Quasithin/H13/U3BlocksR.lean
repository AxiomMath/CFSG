module

public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.B1MoreTenD

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin B2F

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def offenderImagesIn (R H : Subgroup G) : Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | ∃ h ∈ H, ∃ A : Subgroup G, IsFFOffender R V A ∧ B = autI hV (cjSub h A)}

omit [Finite G] in
theorem autI_cjSub_eq {h : G} (hh : h ∈ Subgroup.normalizer (V : Set G)) (A : Subgroup G) :
    autI hV (cjSub h A) = B1.conjAut (convI hV ⟨h, hh⟩) (autI hV A) := by
  rw [conjAut_eq_map, autI_cjSub]

variable {hV}

theorem offenderImagesIn_stable {R H : Subgroup G} (hVR : V ≤ R) (hRH : R ≤ H)
    (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) :
    IsStableFF (autI hV H) (offenderImagesIn hV R H) := by
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRH.trans hHN
  have hRst := B2_5 hV hVR hRN ((offenderImages_nonempty_iff_not_le hV).2 hJ)
  have hoff : ∀ B ∈ offenderImagesIn hV R H, IsFFStarOffender (autI hV H) B := by
    rintro B ⟨h, hh, A, hA, rfl⟩
    rw [autI_cjSub_eq hV (hHN hh)]
    have h1 : IsFFStarOffender (autI hV H) (autI hV A) :=
      isFFStarOffender_mono (autI_mono hV hRH)
        (offenderImages_isFFStarOffender hV hVR hRN ⟨A, hA, rfl⟩)
    exact B1.isFFStarOffender_conjAut h1 (convI_mem_autI hV hh (hHN hh))
  refine ⟨?_, hoff, ?_, ?_⟩
  · obtain ⟨B, A, hA, rfl⟩ := (offenderImages_nonempty_iff_not_le hV).2 hJ
    exact ⟨_, 1, H.one_mem, A, hA, by rw [E2.cjSub_one]⟩
  · rintro B ⟨h, hh, A, hA, rfl⟩ g hg
    obtain ⟨k, hk, rfl⟩ := (mem_autI hV).1 hg
    refine ⟨(k : G) * h, H.mul_mem hk hh, A, hA, ?_⟩
    exact (autI_cjSub hV k.2 (cjSub h A)).trans (by rw [cjSub_mul])
  · rintro B ⟨h, hh, A, hA, rfl⟩ B₁ hB₁
    set a : MulAut (IntMod V hV) := convI hV ⟨h, hHN hh⟩ with ha
    have haX : a ∈ autI hV H := convI_mem_autI hV hh (hHN hh)
    rw [autI_cjSub_eq hV (hHN hh)] at hB₁
    have hle : FFLe (autI hV H) (B1.conjAut a⁻¹ B₁) (autI hV A) := by
      have := B1.ffLe_conjAut hB₁ ((autI hV H).inv_mem haX)
      rwa [B1.conjAut_inv_conjAut] at this
    have hAoff := offenderImages_isFFStarOffender hV hVR hRN ⟨A, hA, rfl⟩
    have hle' : FFLe (autI hV R) (B1.conjAut a⁻¹ B₁) (autI hV A) :=
      ⟨⟨hle.2.2.1.trans hAoff.1, hle.1.2.1, hle.1.2.2⟩, hAoff.isA2, hle.2.2.1, hle.2.2.2⟩
    obtain ⟨D, hD, hDeq⟩ : B1.conjAut a⁻¹ B₁ ∈ offenderImages hV R :=
      hRst.2.2.2 _ ⟨A, hA, rfl⟩ _ hle'
    refine ⟨h, hh, D, hD, ?_⟩
    rw [autI_cjSub_eq hV (hHN hh), ← hDeq, B1.conjAut_conjAut_inv]

theorem ffJP_offenderImagesIn {R H : Subgroup G} (hVR : V ≤ R) (hRH : R ≤ H)
    (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) :
    ffJP (offenderImagesIn hV R H) (autI hV H) = autI hV (conjClosure (thompsonJ R) H) := by
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRH.trans hHN
  have hP := offenderImagesIn_stable (hV := hV) hVR hRH hHN hJ
  have hCH : conjClosure (thompsonJ R) H ≤ H :=
    conjClosure_le fun h hh j hj => H.mul_mem (H.mul_mem hh ((thompsonJ_le_self R).trans hRH hj))
      (H.inv_mem hh)
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => ?_
    obtain ⟨h, hh, A, hA, rfl⟩ := hB
    refine autI_mono hV fun x hx => ?_
    have hx' := (mem_cjSub).1 hx
    have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh ((le_iSup₂_of_le A hA.1 le_rfl : A ≤ thompsonJ R) hx')
  ·
    have hJR : autI hV (thompsonJ R) ≤ ffJP (offenderImagesIn hV R H) (autI hV H) := by
      rw [autI_thompsonJ hV hRN]
      refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBR => ?_
      obtain ⟨A, hA, rfl⟩ := hB
      refine B19.le_ffJP ⟨1, H.one_mem, A, hA, by rw [E2.cjSub_one]⟩
        (hBR.trans (autI_mono hV hRH))
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    let K : Subgroup G :=
      { carrier := {x | ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
          convI hV ⟨x, hx⟩ ∈ ffJP (offenderImagesIn hV R H) (autI hV H)}
        one_mem' := ⟨one_mem _, by rw [show (⟨1, one_mem _⟩ : ↥(Subgroup.normalizer
          (V : Set G))) = 1 from rfl, map_one]; exact one_mem _⟩
        mul_mem' := by
          rintro x y ⟨hx, hxP⟩ ⟨hy, hyP⟩
          refine ⟨mul_mem hx hy, ?_⟩
          rw [show (⟨x * y, mul_mem hx hy⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
          exact mul_mem hxP hyP
        inv_mem' := by
          rintro x ⟨hx, hxP⟩
          refine ⟨inv_mem hx, ?_⟩
          rw [show (⟨x⁻¹, inv_mem hx⟩ : ↥(Subgroup.normalizer (V : Set G))) = (⟨x, hx⟩)⁻¹
            from rfl, map_inv]
          exact inv_mem hxP }
    have hle : conjClosure (thompsonJ R) H ≤ K := by
      refine conjClosure_le fun h hh j hj => ?_
      have hjN : j ∈ Subgroup.normalizer (V : Set G) := hRN ((thompsonJ_le_self R) hj)
      have hhN := hHN hh
      refine ⟨mul_mem (mul_mem hhN hjN) (inv_mem hhN), ?_⟩
      rw [show (⟨h * j * h⁻¹, mul_mem (mul_mem hhN hjN) (inv_mem hhN)⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = ⟨h, hhN⟩ * ⟨j, hjN⟩ * (⟨h, hhN⟩)⁻¹ from rfl,
        map_mul, map_mul, map_inv]
      exact B1Red.ffJP_conj_mem hP (convI_mem_autI hV hh hhN)
        (hJR (convI_mem_autI hV hj hjN))
    obtain ⟨hgN, hgP⟩ := hle hg
    exact hgP

structure BlocksR (H R : Subgroup G) (𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))) : Prop where
  hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn (autI hV H))) 𝓗
  sub : I ⊆ 𝓗
  eq : autI hV (conjClosure (thompsonJ R) H) = ⨆ L ∈ I, L
  syl : ∀ L ∈ I, ∀ S, IsSylowTwoOf S L → S ∈ offenderImagesIn hV R H

theorem exists_blocksR {H R : Subgroup G} (hred : IsTwoReducedIn H V) (hsolv : Group.IsSolvable H)
    (hVR : V ≤ R) (hRH : R ≤ H) (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) :
    ∃ 𝓗 I, BlocksR (hV := hV) H R 𝓗 I := by
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hstable := offenderImagesIn_stable (hV := hV) hVR hRH hHN hJ
  have hNeq := ffJP_offenderImagesIn (hV := hV) hVR hRH hHN hJ
  have hsolvX := isSolvable_autI hV hHN hsolv
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 => eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hJX := B1.closure_transvectionsIn_le (autI hV H)
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn (autI hV H))) :=
    B1.solvable_of_le hJX hsolvX
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn (autI hV H)))) =
      Subgroup.closure (transvectionsIn (autI hV H)) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hW hsolvJ hOJ hcl
  obtain ⟨I, hI𝓗, hJPeq, hsylI, -⟩ := hb.stable_decomposition hW hsolvX hO2 hstable
  exact ⟨𝓗, I, hb, hI𝓗, hNeq.symm.trans hJPeq, hsylI⟩

end CFSG.Quasithin.H13.U3
