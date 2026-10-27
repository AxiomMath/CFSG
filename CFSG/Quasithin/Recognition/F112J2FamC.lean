module

public import CFSG.Quasithin.Recognition.F112J2FamB
public import CFSG.Quasithin.Recognition.F112J2Ext

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.A5Model
open scoped commutatorElement

namespace F112J2

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

namespace FiveCtx

variable (C : FiveCtx K1 L2 S Zs)

include C

@[expose] noncomputable def zU : ↥(vBeta K1 L2 S Zs) :=
  ⟨C.cm 0 1, Zs_le_vBeta K1 L2 S Zs (C.cm_mem 0 1)⟩

@[expose] noncomputable def wU (j : Fin 5) : ↥(vBeta K1 L2 S Zs) := ⟨C.zf j, C.zf_mem_U j⟩

theorem fiveRel : FiveRel C.zU C.wU where
  hz := fun h => C.cm_ne_one (congrArg Subtype.val h)
  hz2 := Subtype.ext (C.Zs_sq (C.cm_mem 0 1))
  hzc := fun g => Subtype.ext (C.Zs_central g.2 (C.cm_mem 0 1))
  hw2 := fun i => Subtype.ext (C.Vf_sq (C.zf_mem i))
  hww := fun i j hij => by
    have hcm : C.cm i j = C.cm 0 1 := C.cm_const (by decide) hij
    apply Subtype.ext
    show C.zf i * C.zf j = C.cm 0 1 * (C.zf j * C.zf i)
    have h2 : C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹ = C.cm 0 1 := hcm
    calc C.zf i * C.zf j
        = (C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹) * (C.zf j * C.zf i) := by group
      _ = C.cm 0 1 * (C.zf j * C.zf i) := by rw [h2]

theorem closure_wU : Subgroup.closure (insert C.zU (Set.range C.wU)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have h1 : (u : G) ∈ Subgroup.closure (insert (C.cm 0 1) (Set.range C.zf)) := by
    have := C.U_eq_closure (C.cm_mem 0 1) C.cm_ne_one
    rw [← this]
    exact u.2
  have h2 : Subgroup.closure (insert (C.cm 0 1) (Set.range C.zf)) =
      (Subgroup.closure (insert C.zU (Set.range C.wU))).map (vBeta K1 L2 S Zs).subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_range]
    constructor
    · rintro (rfl | ⟨j, rfl⟩)
      · exact ⟨C.zU, Or.inl rfl, rfl⟩
      · exact ⟨C.wU j, Or.inr ⟨j, rfl⟩, rfl⟩
    · rintro ⟨y, (rfl | ⟨j, rfl⟩), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j, rfl⟩
  rw [h2] at h1
  obtain ⟨x, hx, hxu⟩ := h1
  have : x = u := Subtype.ext hxu
  rw [← this]
  exact hx

theorem y_mem_zpowers
    (hcenter : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs) :
    C.wU 0 * C.wU 1 * C.wU 2 * C.wU 3 * C.wU 4 ∈ Subgroup.zpowers C.zU := by
  have hfr := C.fiveRel
  set y := C.wU 0 * C.wU 1 * C.wU 2 * C.wU 3 * C.wU 4 with hy
  have hle : Subgroup.closure (insert C.zU (Set.range C.wU)) ≤
      Subgroup.centralizer ({y} : Set ↥(vBeta K1 L2 S Zs)) := by
    rw [Subgroup.closure_le]
    rintro t (rfl | ⟨j, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hfr.hzc y).symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hfr.commute_prod j
  have hcent : ∀ g : ↥(vBeta K1 L2 S Zs), g * y = y * g := by
    intro g
    have hg : g ∈ Subgroup.centralizer ({y} : Set ↥(vBeta K1 L2 S Zs)) := by
      apply hle
      rw [C.closure_wU]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hyZ : (y : G) ∈ Zs := by
    refine hcenter (y : G) y.2 fun u hu => ?_
    have := hcent ⟨u, hu⟩
    exact (congrArg Subtype.val this).symm
  have hyz : (y : G) ∈ Subgroup.zpowers (C.cm 0 1) :=
    (C.Zs_eq_zpowers (C.cm_mem 0 1) C.cm_ne_one).le hyZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [zU] using hk)⟩

theorem isQ8D8_vBeta
    (hcenter : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs) :
    IsQ8D8 ↥(vBeta K1 L2 S Zs) :=
  C.fiveRel.isQ8D8 (C.y_mem_zpowers hcenter) C.closure_wU

end FiveCtx

noncomputable def fiveCtxOfSetting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) : FiveCtx K1 L2 S Zs :=
  have hR : Hyp111R K1 L2 S := hyp111R_of_setting hRO h
  have hθ := exists_theta h hL24
  { h := h
    hR := hR
    D := ⟨hθ.choose, hθ.choose_spec.1, hθ.choose_spec.2⟩
    hcomm := by
      have hyp := amalgamHypV_of_setting hRO h
      have hS := isNaturalS3_of_setting hRO h
      have hb := critDist_eq_two_of_setting hRO h hna
      have hcard : Nat.card ↥(conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G)) = 2 :=
        F112W.card_inf_centralizer_T hyp hS
      have hle : Zs ≤ conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) :=
        le_inf (le_conjClosure Zs L2) h.Z_cent_S
      have hZ : conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) = Zs :=
        (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_Z])).symm
      have hN : K1 ⊔ S ≤ Subgroup.normalizer
          ((conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
        rw [hZ]
        exact (sup_le h.K1_cent_Z (S_le_centralizer_Z h)).trans
          (Subgroup.centralizer_le_normalizer _)
      exact (F112W.commutator_conjClosure_self hyp hS hb hN).trans hZ }

theorem isQ8D8_vBeta_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥)
    (hcenter : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs) :
    IsQ8D8 ↥(vBeta K1 L2 S Zs) :=
  (fiveCtxOfSetting hRO h hL24 hna).isQ8D8_vBeta hcenter

end F112J2

end CFSG.Quasithin
