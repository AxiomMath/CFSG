module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.G2A5
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

section Transfer

variable {G : Type} [Group G]

theorem autOn_commutator {W A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (W : Set G))
    (hB : B ≤ Subgroup.normalizer (W : Set G)) :
    autOn ⁅A, B⁆ W = ⁅autOn A W, autOn B W⁆ := by
  unfold autOn
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective (Subgroup.normalizer (W : Set G)).subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hA hB)]

theorem conjAct_mem_autOn_of_le {U W Z : Subgroup G} (hWU : W ≤ U)
    (hZW : Z ≤ Subgroup.normalizer (W : Set G)) {g : G}
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (h : conjAct U ⟨g, hgU⟩ ∈ autOn Z U) : conjAct W ⟨g, hgW⟩ ∈ autOn Z W := by
  obtain ⟨z, hzZ, hzg⟩ := Setup.mem_autOn_iff.1 h
  refine Setup.mem_autOn_iff.2 ⟨⟨z, hZW hzZ⟩, hzZ, ?_⟩
  ext w
  have h1 := congrArg (fun φ : MulAut ↥U => ((φ ⟨w, hWU w.2⟩ : ↥U) : G)) hzg
  simp only [Setup.coe_conjAct_apply] at h1
  rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
  exact h1

theorem autOn_le_of_autOn_le {U W X Z : Subgroup G} (hWU : W ≤ U)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hZW : Z ≤ Subgroup.normalizer (W : Set G))
    (h : autOn X U ≤ autOn Z U) : autOn X W ≤ autOn Z W := by
  intro φ hφ
  obtain ⟨x, hxX, rfl⟩ := Setup.mem_autOn_iff.1 hφ
  exact conjAct_mem_autOn_of_le hWU hZW (hXU hxX) x.2
    (h (Setup.mem_autOn_iff.2 ⟨⟨x, hXU hxX⟩, hxX, rfl⟩))

theorem conjAct_eq_one_of_mem_centralizer {W : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (W : Set G)) (hgC : g ∈ Subgroup.centralizer (W : Set G)) :
    conjAct W ⟨g, hgN⟩ = 1 := by
  ext w
  rw [Setup.coe_conjAct_apply, MulAut.one_apply]
  have h := Subgroup.mem_centralizer_iff.mp hgC (w : G) w.2
  show g * (w : G) * g⁻¹ = w
  rw [← h, mul_inv_cancel_right]

end Transfer

section JStar

variable {G : Type} [Group G] {Y T W : Subgroup G}

@[expose] noncomputable def jStar (Y T W : Subgroup G) : Subgroup (MulAut ↥W) :=
  ⨆ (A : Subgroup G) (_ : IsFFOffender T W A) (g : MulAut ↥W) (_ : g ∈ autOn Y W),
    B6.conjSub g (autOn A W)

theorem conjSub_le_jStar {A : Subgroup G} (hA : IsFFOffender T W A) {g : MulAut ↥W}
    (hg : g ∈ autOn Y W) : B6.conjSub g (autOn A W) ≤ jStar Y T W :=
  le_iSup₂_of_le (f := fun A (_ : IsFFOffender T W A) => ⨆ (g : MulAut ↥W)
    (_ : g ∈ autOn Y W), B6.conjSub g (autOn A W)) A hA (le_iSup₂_of_le (f := fun
      (g : MulAut ↥W) (_ : g ∈ autOn Y W) => B6.conjSub g (autOn A W)) g hg le_rfl)

theorem jStar_le (hTY : T ≤ Y) : jStar Y T W ≤ autOn Y W := by
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxY : x ∈ autOn Y W := A4.autOn_mono (hA.1.1.trans hTY) hx
  show g * x * g⁻¹ ∈ _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxY) (Subgroup.inv_mem _ hg)

theorem conjSub_jStar_le {h : MulAut ↥W} (hh : h ∈ autOn Y W) :
    B6.conjSub h (jStar Y T W) ≤ jStar Y T W := by
  unfold jStar
  simp only [OrderIso.map_iSup]
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  have e : B6.conjSub h (B6.conjSub g (autOn A W)) = B6.conjSub (h * g) (autOn A W) := by
    ext x
    simp only [B6.conjSub, MulEquiv.mapSubgroup_apply, Subgroup.mem_map]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [e]
  exact conjSub_le_jStar hA (Subgroup.mul_mem _ hh hg)

theorem le_normalizer_jStar :
    autOn Y W ≤ Subgroup.normalizer (jStar Y T W : Set (MulAut ↥W)) := by
  intro h hh
  have key : ∀ k ∈ autOn Y W, ∀ x ∈ jStar Y T W, k * x * k⁻¹ ∈ jStar Y T W := fun k hk x hx =>
    conjSub_jStar_le hk ⟨x, hx, by simp [MulAut.conj_apply]⟩
  refine B6.mem_normalizer_of_forall_mem (key h hh) fun x hx => ?_
  have := key h⁻¹ (Subgroup.inv_mem _ hh) x hx
  simpa using this

theorem autOn_thompsonJ_le_jStar (hTY : T ≤ Y) (hYW : Y ≤ Subgroup.normalizer (W : Set G)) :
    autOn (thompsonJ T) W ≤ jStar Y T W := by
  set P : Subgroup G := ((jStar Y T W).comap (conjAct W)).map
      (Subgroup.normalizer (W : Set G)).subtype with hP
  have hJP : thompsonJ T ≤ P := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (W : Set G) := (hA.1.trans (hTY.trans hYW)) ha
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    show conjAct W ⟨a, haN⟩ ∈ jStar Y T W
    by_cases hAc : A ≤ Subgroup.centralizer (W : Set G)
    · rw [conjAct_eq_one_of_mem_centralizer haN (hAc ha)]
      exact Subgroup.one_mem _
    · have h1 := conjSub_le_jStar (Y := Y) ⟨hA, hAc⟩ (Subgroup.one_mem _)
      refine h1 ⟨conjAct W ⟨a, haN⟩, ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, ?_⟩
      simp
  intro x hx
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := hx
  obtain ⟨⟨g', hg'N⟩, hg'P, hg'g⟩ := hJP (Subgroup.mem_subgroupOf.mp hg)
  have : (⟨g', hg'N⟩ : ↥(Subgroup.normalizer (W : Set G))) = ⟨g, hgN⟩ := Subtype.ext hg'g
  rw [← this]
  exact hg'P

variable [Finite G] [IsMulCommutative ↥W]

theorem isFFStarOffender_autOn (hWe : IsElemAbelian 2 W) (hWT : W ≤ T) (hTY : T ≤ Y)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) {A : Subgroup G} (hA : IsFFOffender T W A) :
    IsFFStarOffender (autOn Y W) (autOn A W) := by
  have h1 := offenderImages_isFFStarOffender hWe hWT (hTY.trans hYW) ⟨A, hA, rfl⟩
  exact ⟨h1.1.trans (A4.autOn_mono hTY), h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem jStar_eq_ffJ (hWe : IsElemAbelian 2 W) (hWT : W ≤ T) (hTY : T ≤ Y)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) : jStar Y T W = ffJ (jStar Y T W) := by
  refine le_antisymm ?_ (B6.ffJ_le _)
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  have h1 := isFFStarOffender_autOn hWe hWT hTY hYW hA
  have h2 := B6.isFFStarOffender_conjSub h1 hg
  have h3 := InternalSec.isFFStarOffender_of_le h2 (conjSub_le_jStar hA hg)
  exact le_iSup₂_of_le (f := fun B (_ : IsFFStarOffender (jStar Y T W) B) => B) _ h3 le_rfl

omit [Finite G] [IsMulCommutative ↥W] in
theorem pCoreOf_jStar (hTY : T ≤ Y) (hR : IsTwoReducedIn Y W) : pCoreOf 2 (jStar Y T W) = ⊥ := by
  have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2
    (jStar Y T W) (autOn Y W) (jStar_le hTY)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (jStar_le hTY)).2 le_normalizer_jStar)
  rw [Setup.pCoreOf_autOn_eq_bot hR] at h
  exact le_bot_iff.1 h

theorem b53Hyp_jStar (hWT : W ≤ T) (hTY : T ≤ Y) (hR : IsTwoReducedIn Y W)
    (hSQ : SQTKGroup ↥Y) : B53Hyp (jStar Y T W) := by
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hR.2.1
  set X := autOn Y W with hX
  set J := jStar Y T W with hJ
  have hJX : J ≤ X := jStar_le hTY
  set ρ := InternalSec.autOnHom hYW with hρ
  set H : Subgroup ↥Y := (J.subgroupOf X).comap ρ with hH
  let f : ↥H →* ↥J :=
    { toFun := fun h => ⟨((ρ (h : ↥Y) : ↥X) : MulAut ↥W), h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hy⟩ := InternalSec.autOnHom_surjective hYW ⟨j, hJX hj⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show ρ y ∈ J.subgroupOf X
      rw [Subgroup.mem_subgroupOf, hy]
      exact hj
    · apply Subtype.ext
      show ((ρ y : ↥X) : MulAut ↥W) = j
      rw [hy]
  refine ⟨pCoreOf_jStar hTY hR, jStar_eq_ffJ hR.2.2.1 hWT hTY hYW, ↥H, inferInstance,
    inferInstance, f.ker, inferInstance, InternalSec.sqtkGroup_subgroup hSQ H,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

theorem b56Cases_jStar (h56 : AsB56) (hWT : W ≤ T) (hTY : T ≤ Y) (hR : IsTwoReducedIn Y W)
    (hSQ : SQTKGroup ↥Y) (hJ : autOn (thompsonJ T) W ≠ ⊥) :
    B56Case1 (jStar Y T W) ∨ B56Case2 (jStar Y T W) ∨ B56Case3 (jStar Y T W) ∨
      B56Case4 (jStar Y T W) ∨ B56Case5 (jStar Y T W) := by
  have hWe := hR.2.2.1
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hWe.2 _ v.2, Subgroup.coe_one])
  have hJ1 : jStar Y T W ≠ ⊥ := fun h =>
    hJ (le_bot_iff.1 (h ▸ autOn_thompsonJ_le_jStar hTY hR.2.1))
  exact h56 ↥W hV _ hJ1 (b53Hyp_jStar hWT hTY hR hSQ)

end JStar

end CFSG.Quasithin.H13.A5
