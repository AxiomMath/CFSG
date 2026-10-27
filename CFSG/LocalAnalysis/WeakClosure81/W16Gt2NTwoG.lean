module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoC
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoD
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoDA
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section Certified


theorem commute_lift (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G} (hh : h ∈ H)
    (hcomm : ∀ x ∈ hatBarSub Mo V (conjSubgroup V h),
      ∀ y ∈ hatBarSub Mo V (V ⊔ conjSubgroup V g), x * y = y * x) :
    (∀ a ∈ Mo.img (conjSubgroup V h), ∀ l ∈ Mo.img (V ⊔ conjSubgroup V g), a * l = l * a) ∧
      IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hWhH : conjSubgroup V h ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hVH hz)) hh
  have hWhK : conjSubgroup V h ≤ conjClosure V H :=
    conjSubgroup_le_conjClosure_of_mem hh le_rfl
  have hLK : Mo.img (V ⊔ conjSubgroup V g) ≤ hatK Mo V :=
    Mo.img_mono c.L_le_conjClosure
  have hWhK' : Mo.img (conjSubgroup V h) ≤ hatK Mo V := Mo.img_mono hWhK
  have hcommimg : ∀ a ∈ Mo.img (conjSubgroup V h),
      ∀ l ∈ Mo.img (V ⊔ conjSubgroup V g), a * l = l * a := by
    intro a ha l hl
    let a' : ↥(hatK Mo V) := ⟨a, hWhK' ha⟩
    have hbar_a : hatBar Mo V a' ∈ hatBarSub Mo V (conjSubgroup V h) :=
      (mem_hatBarSub_iff (Mo := Mo) (V := V)).2 ⟨a', ha, rfl⟩
    let incl : ↥(Mo.img (V ⊔ conjSubgroup V g)) →* ↥(hatK Mo V) :=
      Subgroup.inclusion hLK
    have hcenter : ∀ z : ↥(Mo.img (V ⊔ conjSubgroup V g)),
        ⁅incl z, a'⁆ ∈ Subgroup.center ↥(hatK Mo V) := by
      intro z
      have hbar_z : hatBar Mo V (incl z) ∈ hatBarSub Mo V (V ⊔ conjSubgroup V g) :=
        (mem_hatBarSub_iff (Mo := Mo) (V := V)).2 ⟨incl z, z.2, rfl⟩
      have hbar_one : hatBar Mo V ⁅incl z, a'⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ hbar_a _ hbar_z).symm
      have hker : ⁅incl z, a'⁆ ∈ (hatBar Mo V).ker := by
        rw [MonoidHom.mem_ker]; exact hbar_one
      rwa [ker_hatBar hn h1 h5 h15 hS c Mo] at hker
    haveI : Group.IsPerfect ↥(Mo.img (V ⊔ conjSubgroup V g)) :=
      isPerfect_hatL hn h1 h5 h15 hS c Mo
    let φ : ↥(Mo.img (V ⊔ conjSubgroup V g)) →* ↥(Subgroup.center ↥(hatK Mo V)) :=
      { toFun := fun z => ⟨⁅incl z, a'⁆, hcenter z⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by
          intro x y
          apply Subtype.ext
          simp only [map_mul, Subgroup.coe_mul, Subtype.coe_mk]
          rw [commutatorElement_mul_left_eq_conj_mul]
          have hcx : incl x * ⁅incl y, a'⁆ = ⁅incl y, a'⁆ * incl x :=
            Subgroup.mem_center_iff.mp (hcenter y) (incl x)
          rw [hcx]
          have hcancel : ⁅incl y, a'⁆ * incl x * (incl x)⁻¹ = ⁅incl y, a'⁆ := by group
          rw [hcancel]
          exact Subgroup.mem_center_iff.mp (hcenter x) ⁅incl y, a'⁆ }
    have hφ1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ
    have hφa : φ ⟨l, hl⟩ = 1 := by
      have := congrArg (fun f : ↥(Mo.img (V ⊔ conjSubgroup V g)) →*
        ↥(Subgroup.center ↥(hatK Mo V)) => f ⟨l, hl⟩) hφ1
      simpa using this
    have hval : ⁅l, a⁆ = 1 := by
      have hstep : ((φ ⟨l, hl⟩ : ↥(Subgroup.center ↥(hatK Mo V))) : ↥(hatK Mo V)) = 1 := by
        simpa using congrArg Subtype.val hφa
      have hK : ⁅(Subgroup.inclusion hLK ⟨l, hl⟩ : ↥(hatK Mo V)), a'⁆ = 1 := by
        simpa [φ] using hstep
      have hvalL : ⁅(Subgroup.inclusion hLK ⟨l, hl⟩ : LGL 2 Mo.W), (a' : LGL 2 Mo.W)⁆ = 1 := by
        change ((⁅(Subgroup.inclusion hLK ⟨l, hl⟩ : ↥(hatK Mo V)), a'⁆ : ↥(hatK Mo V)) :
          LGL 2 Mo.W) = 1
        rw [hK]; rfl
      simpa [a'] using hvalL
    exact (commutatorElement_eq_one_iff_mul_comm.mp hval).symm
  refine ⟨hcommimg, ?_⟩
  have hVab : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hWhab : IsElemAbelian 2 (conjSubgroup V h) := E3.isElemAbelian_conjSubgroup hVab h
  have himg_sup : Mo.img (V ⊔ conjSubgroup V h) = Mo.img V ⊔ Mo.img (conjSubgroup V h) :=
    Mo.img_sup hVH hWhH
  rw [himg_sup]
  refine IsPGroup.to_sup_of_normal_left' ?_ ?_ ?_
  · exact Mo.isPGroup_img (B2F.isPGroup_of_isElemAbelian hVab)
  · exact Mo.isPGroup_img (B2F.isPGroup_of_isElemAbelian hWhab)
  · refine Subgroup.le_normalizer_iff.2 fun a ha l hl => ?_
    have h : a * l = l * a := hcommimg a ha l (Mo.img_mono le_sup_left hl)
    have h' : a * l * a⁻¹ = l := by rw [h]; group
    rw [h']; exact hl

theorem mem_conjSubgroup_of_hat_normalizes (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h y : G} (hh : h ∈ H) (hy : y ∈ H)
    (hn : ∀ a ∈ Mo.img (conjSubgroup V h),
      Mo.ρ ⟨y, hy⟩ * a * (Mo.ρ ⟨y, hy⟩)⁻¹ ∈ Mo.img (conjSubgroup V h)) :
    y ∈ conjSubgroup M h := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hAH : conjSubgroup V h ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hVH hz)) hh
  let A : Subgroup G := conjSubgroup V h
  have hAeq : A = conjSubgroup V h := rfl
  have hle : cj (Mo.ρ ⟨y, hy⟩) (Mo.img A) ≤ Mo.img A := by
    intro r hr
    rw [mem_cj] at hr
    have h := hn _ hr
    convert h using 1
    group
  have hcard : Nat.card (Mo.img A) ≤ Nat.card (cj (Mo.ρ ⟨y, hy⟩) (Mo.img A)) := by
    rw [cj]
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj (Mo.ρ ⟨y, hy⟩)).toMonoidHom)
      (MulAut.conj (Mo.ρ ⟨y, hy⟩)).injective]
  have hcjeq : cj (Mo.ρ ⟨y, hy⟩) (Mo.img A) = Mo.img A :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hconj := Mo.img_conj (A := A) (by rw [hAeq]; exact hAH) ⟨y, hy⟩
  have himg : Mo.img (conjSubgroup A y⁻¹) = Mo.img A := by
    rw [← hconj]; exact hcjeq
  have hAy : conjSubgroup A y⁻¹ = conjSubgroup V (h * y⁻¹) := by
    rw [hAeq, conjSubgroup_conjSubgroup]
  rw [hAy, hAeq] at himg
  have hy'H : h * y⁻¹ ∈ H := H.mul_mem hh (H.inv_mem hy)
  have hM : h * y⁻¹ * h⁻¹ ∈ M :=
    (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo hy'H hh).1 himg
  have hinv : y⁻¹ ∈ conjSubgroup M h := mem_conjSubgroup_iff.2 (by simpa using hM)
  simpa using (conjSubgroup M h).inv_mem hinv

theorem false_of_hat_fpf (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G}
    (hh : h ∈ H) (hhM : h ∉ M) (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) {y : G}
    (hyH : y ∈ H) (hyU : y ∈ centralizer (U : Set G))
    (hnorm : ∀ a ∈ Mo.img V, Mo.ρ ⟨y, hyH⟩ * a * (Mo.ρ ⟨y, hyH⟩)⁻¹ ∈ Mo.img V)
    (hcen : ∀ a ∈ Mo.img (conjSubgroup V h), Mo.ρ ⟨y, hyH⟩ * a = a * Mo.ρ ⟨y, hyH⟩)
    (hfpf : ∀ a ∈ Mo.img V, Mo.ρ ⟨y, hyH⟩ * a = a * Mo.ρ ⟨y, hyH⟩ → a = 1) : False := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVM : V ≤ M := Subgroup.le_normalizer.trans (le_of_eq c.cex.hyp.h6.normalizer_eq)
  have hUV₀H : U ⊔ V₀ ≤ H := sup_le (c.cex.le.trans hVH) (c.cex.hyp.h6.le.trans hVH)
  have hUV₀I : U ⊔ V₀ ≤ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H
  have hyM : y ∈ M := by
    have hn1 : ∀ a ∈ Mo.img (conjSubgroup V (1 : G)),
        Mo.ρ ⟨y, hyH⟩ * a * (Mo.ρ ⟨y, hyH⟩)⁻¹ ∈ Mo.img (conjSubgroup V (1 : G)) := by
      rw [conjSubgroup_one]
      exact hnorm
    have h := mem_conjSubgroup_of_hat_normalizes h1 h5 h15 hS c Mo (h := 1) (y := y)
      (H.one_mem) hyH hn1
    rwa [conjSubgroup_one] at h
  have hyMh : y ∈ conjSubgroup M h := by
    have hn' : ∀ a ∈ Mo.img (conjSubgroup V h),
        Mo.ρ ⟨y, hyH⟩ * a * (Mo.ρ ⟨y, hyH⟩)⁻¹ ∈ Mo.img (conjSubgroup V h) := by
      intro a ha
      have h := hcen a ha
      simpa [h] using ha
    exact mem_conjSubgroup_of_hat_normalizes h1 h5 h15 hS c Mo hh hyH hn'
  have hyU' : ∀ u ∈ U ⊔ V₀, ⁅u, y⁆ ∈ V₀ := by
    intro u hu
    obtain ⟨u₁, hu₁, v₀, hv₀, rfl⟩ := c.cex.exists_mul_of_mem_sup hu
    have hyN₀ : y ∈ Subgroup.normalizer (V₀ : Set G) := by
      rw [c.cex.hyp.normalizer₀]; exact hyM
    have hcommV₀ : ⁅v₀, y⁆ ∈ V₀ := by
      have h1 : y * v₀ * y⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hyN₀ v₀).1 hv₀
      have e : ⁅v₀, y⁆ = v₀ * (y * v₀ * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact V₀.mul_mem hv₀ (V₀.inv_mem h1)
    have hu₁N₀ : u₁ ∈ Subgroup.normalizer (V₀ : Set G) := by
      rw [c.cex.hyp.normalizer₀]; exact hVM (c.cex.le hu₁)
    have hu₁y : ⁅u₁, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.1 hyU u₁ hu₁)
    rw [commutatorElement_mul_left_eq_conj_mul, hu₁y, mul_one]
    exact (Subgroup.mem_normalizer_iff.1 hu₁N₀ ⁅v₀, y⁆).1 hcommV₀
  refine c.false_of_fixedPointFree h1 h5 h15 hS Mo hh hhM hP hyM hyMh hyU' ?_ ?_
  ·
    intro v hv hvcomm
    have hcommH : ⁅v, y⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      refine ⟨hUV₀H hvcomm, ?_⟩
      exact Subgroup.mem_centralizer_iff.2 fun i hi =>
        B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hi (hUV₀I hvcomm)
    have hρ1 : Mo.ρ ⟨⁅v, y⁆, hcommH.1⟩ = 1 :=
      (Mo.ρ_eq_one_iff _).2 hcommH.2
    have hρcomm : Mo.ρ ⟨⁅v, y⁆, hcommH.1⟩ =
        ⁅Mo.ρ ⟨v, hVH hv⟩, Mo.ρ ⟨y, hyH⟩⁆ := by
      have e : (⟨⁅v, y⁆, hcommH.1⟩ : ↥H) =
          ⁅(⟨v, hVH hv⟩ : ↥H), (⟨y, hyH⟩ : ↥H)⁆ := Subtype.ext rfl
      rw [e, map_commutatorElement]
    have hcommρ : Mo.ρ ⟨y, hyH⟩ * Mo.ρ ⟨v, hVH hv⟩ =
        Mo.ρ ⟨v, hVH hv⟩ * Mo.ρ ⟨y, hyH⟩ := by
      rw [hρcomm] at hρ1
      exact (commutatorElement_eq_one_iff_mul_comm.mp hρ1).symm
    have hvρ1 : Mo.ρ ⟨v, hVH hv⟩ = 1 :=
      hfpf _ (Mo.mem_img.2 ⟨⟨v, hVH hv⟩, hv, rfl⟩) hcommρ
    have hvC : v ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
      (Mo.ρ_eq_one_iff ⟨v, hVH hv⟩).1 hvρ1
    have hmem : v ∈ V ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :=
      ⟨hv, hVH hv, hvC⟩
    rwa [inf_centralizer_eq_sup h1 h5 h15 hS c] at hmem
  ·
    intro w hw
    have hWH : conjSubgroup V h ≤ H := by
      intro z hz
      rw [mem_conjSubgroup_iff] at hz
      have e : z = h⁻¹ * (h * z * h⁻¹) * h := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hVH hz)) hh
    have hwH : w ∈ H := hWH hw
    have hyNorm : y ∈ Subgroup.normalizer (conjSubgroup V h : Set G) := by
      have hnorm : Subgroup.normalizer (conjSubgroup V h : Set G) = conjSubgroup M h := by
        rw [← E3.conjSubgroup_normalizer, c.cex.hyp.h6.normalizer_eq]
      rw [hnorm]; exact hyMh
    have hcommW : ⁅w, y⁆ ∈ conjSubgroup V h := by
      have h1 : y * w * y⁻¹ ∈ conjSubgroup V h :=
        (Subgroup.mem_normalizer_iff.1 hyNorm w).1 hw
      have e : ⁅w, y⁆ = w * (y * w * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup V h).mul_mem hw ((conjSubgroup V h).inv_mem h1)
    have hcommWH : ⁅w, y⁆ ∈ H := hWH hcommW
    have hρw1 : Mo.ρ ⟨⁅w, y⁆, hcommWH⟩ = 1 := by
      have hmap : Mo.ρ ⟨⁅w, y⁆, hcommWH⟩ = ⁅Mo.ρ ⟨w, hwH⟩, Mo.ρ ⟨y, hyH⟩⁆ := by
        have e : (⟨⁅w, y⁆, hcommWH⟩ : ↥H) =
            ⁅(⟨w, hwH⟩ : ↥H), (⟨y, hyH⟩ : ↥H)⁆ := Subtype.ext rfl
        rw [e, map_commutatorElement]
      rw [hmap]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (hcen _ (Mo.mem_img.2 ⟨⟨w, hwH⟩, hw, rfl⟩)).symm
    have hcommC : ⁅w, y⁆ ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
      (Mo.ρ_eq_one_iff ⟨⁅w, y⁆, hcommWH⟩).1 hρw1
    have hCfix : conjSubgroup (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) h =
        H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
        conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hh),
        conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure (U ⊔ V₀) H hh)]
    have hmem : ⁅w, y⁆ ∈ conjSubgroup
        (V ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) h := by
      rw [E3.conjSubgroup_inf, hCfix]
      exact ⟨hcommW, hcommWH, hcommC⟩
    have hgoal := congrArg (fun X : Subgroup G => conjSubgroup X h)
      (inf_centralizer_eq_sup h1 h5 h15 hS c)
    rw [hgoal] at hmem
    exact hmem

theorem exists_lift_conj (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {γ : hatX Mo V ⧸ Subgroup.center (hatX Mo V)}
    (hγ : conjSubgroup (hatBarSub Mo V V) γ ≠ hatBarSub Mo V V)
    (hcomm : ∀ x ∈ conjSubgroup (hatBarSub Mo V V) γ,
      ∀ y ∈ hatBarSub Mo V V ⊔ hatBarSub Mo V (conjSubgroup V g), x * y = y * x) :
    ∃ h ∈ H, h ∉ M ∧ IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h)) ∧
      ∀ a ∈ Mo.img (conjSubgroup V h), ∀ l ∈ Mo.img (V ⊔ conjSubgroup V g), a * l = l * a := by
  obtain ⟨h, hhH, heq⟩ := exists_mem_conj_hatBarSub c Mo γ
  have hhM : h ∉ M := by
    intro hM
    have hconjV : conjSubgroup V h = V :=
      conjSubgroup_eq_iff_mem_normalizer.2 (by rw [c.cex.hyp.h6.normalizer_eq]; exact hM)
    have hEqV : hatBarSub Mo V (conjSubgroup V h) = hatBarSub Mo V V := by rw [hconjV]
    rw [heq] at hEqV
    exact hγ hEqV
  have hcomm' : ∀ x ∈ hatBarSub Mo V (conjSubgroup V h),
      ∀ y ∈ hatBarSub Mo V (V ⊔ conjSubgroup V g), x * y = y * x := by
    rw [heq]
    intro x hx y hy
    rw [hatBarSub_sup c Mo] at hy
    exact hcomm x hx y hy
  obtain ⟨hcomm_lift, hP⟩ := commute_lift hn h1 h5 h15 hS c Mo hhH hcomm'
  exact ⟨h, hhH, hhM, hP, hcomm_lift⟩

theorem exists_lift_elem (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {τ : hatX Mo V ⧸ Subgroup.center (hatX Mo V)}
    (hτ : τ ∈ hatBarSub Mo V V ⊔ hatBarSub Mo V (conjSubgroup V g))
    (hnorm : τ ∈ Subgroup.normalizer
      (↑(hatBarSub Mo V V) : Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V))))
    (hfpf : ∀ a ∈ hatBarSub Mo V V, τ * a = a * τ → a = 1) :
    ∃ (y : G) (hyH : y ∈ H), y ∈ centralizer (U : Set G) ∧
      Mo.ρ ⟨y, hyH⟩ ∈ Mo.img (V ⊔ conjSubgroup V g) ∧
      (∀ a ∈ Mo.img V, Mo.ρ ⟨y, hyH⟩ * a * (Mo.ρ ⟨y, hyH⟩)⁻¹ ∈ Mo.img V) ∧
      ∀ a ∈ Mo.img V, Mo.ρ ⟨y, hyH⟩ * a = a * Mo.ρ ⟨y, hyH⟩ → a = 1 := by
  have hτL : τ ∈ hatBarSub Mo V (V ⊔ conjSubgroup V g) := by
    rw [hatBarSub_sup c Mo]; exact hτ
  obtain ⟨x, hxL, hxτ⟩ := (mem_hatBarSub_iff (Mo := Mo) (V := V)).1 hτL
  obtain ⟨j, hjL, hjx⟩ := Mo.mem_img.1 hxL
  have hjx' : Mo.ρ j = (x : LGL 2 Mo.W) := hjx
  refine ⟨(j : G), j.2, c.L_le_centralizer hjL, ?_, ?_, ?_⟩
  · simpa using Mo.mem_img.2 ⟨j, hjL, rfl⟩
  · have hxnorm : hatBar Mo V x ∈ Subgroup.normalizer
        (↑(hatBarSub Mo V V) : Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V))) := by
      rw [hxτ]; exact hnorm
    have hnorm' := img_normalizes_of_bar_normalizes hn h1 h5 h15 hS c Mo
      (J := V) le_sup_left hxL hxnorm
    intro a ha
    simpa [hjx'] using hnorm' a ha
  · intro a ha hcomm
    have haK : a ∈ hatK Mo V := Mo.img_mono (le_conjClosure V H) ha
    let a' : ↥(hatK Mo V) := ⟨a, haK⟩
    have hbar_a' : hatBar Mo V a' ∈ hatBarSub Mo V V :=
      (mem_hatBarSub_iff (Mo := Mo) (V := V)).2 ⟨a', ha, rfl⟩
    have ha'L : (a' : LGL 2 Mo.W) ∈ Mo.img (V ⊔ conjSubgroup V g) :=
      Mo.img_mono le_sup_left ha
    have hax : a' * x = x * a' := Subtype.ext (by simpa [hjx'] using hcomm.symm)
    have hcommbar : hatBar Mo V a' * τ = τ * hatBar Mo V a' := by
      have := congrArg (hatBar Mo V) hax
      simpa [map_mul, hxτ] using this
    have hbar_a'1 : hatBar Mo V a' = 1 := hfpf (hatBar Mo V a') hbar_a' hcommbar.symm
    have hker : a' ∈ (hatBar Mo V).ker := by
      rw [MonoidHom.mem_ker]; exact hbar_a'1
    have hcenter : a' ∈ Subgroup.center ↥(hatK Mo V) := by
      rwa [ker_hatBar hn h1 h5 h15 hS c Mo] at hker
    have ha'1 : a' = 1 := inf_center_hatL hn h1 h5 h15 hS c Mo a' ha'L hcenter
    simpa [a'] using congrArg Subtype.val ha'1

theorem false_of_config (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (γ τ : hatX Mo V ⧸ Subgroup.center (hatX Mo V))
    (hτ : τ ∈ hatBarSub Mo V V ⊔ hatBarSub Mo V (conjSubgroup V g))
    (hγ : conjSubgroup (hatBarSub Mo V V) γ ≠ hatBarSub Mo V V)
    (hcomm : ∀ x ∈ conjSubgroup (hatBarSub Mo V V) γ,
      ∀ y ∈ hatBarSub Mo V V ⊔ hatBarSub Mo V (conjSubgroup V g), x * y = y * x)
    (hnorm : τ ∈ Subgroup.normalizer
      (↑(hatBarSub Mo V V) : Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V))))
    (hfpf : ∀ a ∈ hatBarSub Mo V V, τ * a = a * τ → a = 1) : False := by
  obtain ⟨h, hh, hhM, hP, hcen⟩ := c.exists_lift_conj hn h1 h5 h15 hS Mo hγ hcomm
  obtain ⟨y, hyH, hyU, hyL, hnorm', hfpf'⟩ :=
    c.exists_lift_elem hn h1 h5 h15 hS Mo hτ hnorm hfpf
  exact c.false_of_hat_fpf h1 h5 h15 hS Mo hh hhM hP hyH hyU hnorm'
    (fun a ha => (hcen a ha _ hyL).symm) hfpf'

theorem false_of_sp_root (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {m n' : ℕ} (hm : 4 ≤ m)
    (hRoot : IsSymplecticRootGroup (hatX Mo V) m n' (hatS Mo V)) : False := by
  obtain ⟨hcS, k, hmk, F, hFfield, hFfin, hF, e, htr⟩ := hRoot
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have hnn : E3.mQuot V (U ⊔ V₀) = n' :=
    Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hcS)
  have hk : 2 ≤ k := by omega
  have hn' : 2 ≤ n' := hnn ▸ hn
  have hVcard : Nat.card (hatBarSub Mo V V) = 2 ^ n' :=
    hnn ▸ c.card_hatBarSub_V hn h1 h5 h15 hS Mo
  obtain ⟨γ₀, hγ₀⟩ := c.exists_conj_hatBarSub_of_mem h15 hS Mo c.g_mem.1
  have hWcard : Nat.card (hatBarSub Mo V (conjSubgroup V g)) = 2 ^ n' := by
    rw [hγ₀, E3.card_conjSubgroup]
    exact hVcard
  have htV : ∀ x ∈ hatBarSub Mo V V, x ≠ 1 → SevenK.IsSymplecticTransvectionIn k (e x) := by
    intro x hx hx1
    rw [← hatS_map_eq_hatBarSub] at hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    refine htr s hs ?_
    rintro rfl
    exact hx1 (map_one _)
  have htW : ∀ x ∈ hatBarSub Mo V (conjSubgroup V g), x ≠ 1 →
      SevenK.IsSymplecticTransvectionIn k (e x) := by
    intro x hx hx1
    rw [hγ₀, mem_conjSubgroup_iff] at hx
    have hne : γ₀ * x * γ₀⁻¹ ≠ 1 := fun h => hx1 (by simpa using h)
    have h := isSymplecticTransvectionIn_conj (htV _ hx hne) (e γ₀)⁻¹
    have e1 : (e γ₀)⁻¹ * e (γ₀ * x * γ₀⁻¹) * ((e γ₀)⁻¹)⁻¹ = e x := by
      simp only [map_mul, map_inv]
      group
    rwa [e1] at h
  obtain ⟨γ, τ, hτ, hγ, hcomm, hnorm, hfpf⟩ := exists_config_sp hK hk hn' hF e
    (hatBarSub Mo V V) (hatBarSub Mo V (conjSubgroup V g)) hVcard hWcard htV htW
    (c.not_comm_hatBarSub hn h1 h5 h15 hS Mo)
  exact c.false_of_config hn h1 h5 h15 hS Mo γ τ hτ hγ hcomm hnorm hfpf

theorem false_of_su_root (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {m n' : ℕ} (hm : 4 ≤ m)
    (hRoot : IsUnitaryRootGroup (hatX Mo V) m n' (hatS Mo V)) : False := by
  obtain ⟨hcS, F, hFfield, hFfin, hF, e, htr⟩ := hRoot
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have hnn : E3.mQuot V (U ⊔ V₀) = n' :=
    Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hcS)
  have hn' : 2 ≤ n' := hnn ▸ hn
  have hVcard : Nat.card (hatBarSub Mo V V) = 2 ^ n' :=
    hnn ▸ c.card_hatBarSub_V hn h1 h5 h15 hS Mo
  obtain ⟨γ₀, hγ₀⟩ := c.exists_conj_hatBarSub_of_mem h15 hS Mo c.g_mem.1
  have hWcard : Nat.card (hatBarSub Mo V (conjSubgroup V g)) = 2 ^ n' := by
    rw [hγ₀, E3.card_conjSubgroup]
    exact hVcard
  have htV : ∀ x ∈ hatBarSub Mo V V, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n' (e x) := by
    intro x hx hx1
    rw [← hatS_map_eq_hatBarSub] at hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    refine htr s hs ?_
    rintro rfl
    exact hx1 (map_one _)
  have htW : ∀ x ∈ hatBarSub Mo V (conjSubgroup V g), x ≠ 1 →
      SevenK.IsUnitaryTransvectionIn m n' (e x) := by
    intro x hx hx1
    rw [hγ₀, mem_conjSubgroup_iff] at hx
    have hne : γ₀ * x * γ₀⁻¹ ≠ 1 := fun h => hx1 (by simpa using h)
    have h := isUnitaryTransvectionIn_conj (htV _ hx hne) (e γ₀)⁻¹
    have e1 : (e γ₀)⁻¹ * e (γ₀ * x * γ₀⁻¹) * ((e γ₀)⁻¹)⁻¹ = e x := by
      simp only [map_mul, map_inv]
      group
    rwa [e1] at h
  obtain ⟨γ, τ, hτ, hγ, hcomm, hnorm, hfpf⟩ := exists_config_su hK hm hn' hF e
    (hatBarSub Mo V V) (hatBarSub Mo V (conjSubgroup V g)) hVcard hWcard htV htW
    (c.not_comm_hatBarSub hn h1 h5 h15 hS Mo)
  exact c.false_of_config hn h1 h5 h15 hS Mo γ τ hτ hγ hcomm hnorm hfpf

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
