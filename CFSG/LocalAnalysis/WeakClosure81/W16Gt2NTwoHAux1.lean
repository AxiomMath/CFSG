module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section NoCert

private abbrev rhoB (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) : LGL 2 Mo.W :=
  Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩

private theorem rhoB_one (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) : rhoB c Mo 1 = 1 := by
  unfold rhoB
  rw [show (⟨((1 : ↥B) : G), c.mem.1 (c.B_le (1 : ↥B).2)⟩ : ↥H) = 1 from
    Subtype.ext rfl, map_one]

private theorem rhoB_mul (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b b' : ↥B) :
    rhoB c Mo (b * b') = rhoB c Mo b * rhoB c Mo b' := by
  unfold rhoB
  rw [show (⟨((b * b' : ↥B) : G), c.mem.1 (c.B_le (b * b').2)⟩ : ↥H) =
      (⟨(b : G), c.mem.1 (c.B_le b.2)⟩ : ↥H) *
        ⟨(b' : G), c.mem.1 (c.B_le b'.2)⟩ from Subtype.ext rfl, map_mul]

private theorem cj_rhoB_hatK (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) :
    cj (rhoB c Mo b) (hatK Mo V) = hatK Mo V := by
  have hbH : (b : G) ∈ H := c.mem.1 (c.B_le b.2)
  have h := Mo.img_conj (A := conjClosure V H) (conjClosure_le_H c)
    (⟨(b : G), hbH⟩ : ↥H)
  have h2 : conjSubgroup (conjClosure V H) ((⟨(b : G), hbH⟩ : ↥H) : G)⁻¹ =
      conjClosure V H := by
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact le_normalizer_conjClosure V H (H.inv_mem hbH)
  rw [h2] at h
  exact h

private noncomputable def psi (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) :
    ↥(hatK Mo V) ≃* ↥(hatK Mo V) where
  toFun x := ⟨rhoB c Mo b * (x : LGL 2 Mo.W) * (rhoB c Mo b)⁻¹, by
    have h := cj_rhoB_hatK c Mo b
    have hx : rhoB c Mo b * (x : LGL 2 Mo.W) * (rhoB c Mo b)⁻¹ ∈
        cj (rhoB c Mo b) (hatK Mo V) :=
      (mem_cj).mpr (by
        have e : (rhoB c Mo b)⁻¹ * (rhoB c Mo b * (x : LGL 2 Mo.W) *
            (rhoB c Mo b)⁻¹) * (rhoB c Mo b) = (x : LGL 2 Mo.W) := by group
        rw [e]; exact x.2)
    rwa [h] at hx⟩
  invFun x := ⟨(rhoB c Mo b)⁻¹ * (x : LGL 2 Mo.W) * (rhoB c Mo b), by
    have h := cj_rhoB_hatK c Mo b
    exact (mem_cj).mp (by rw [h]; exact x.2)⟩
  left_inv x := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  right_inv x := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem psi_apply (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) (x : ↥(hatK Mo V)) :
    (psi c Mo b x : LGL 2 Mo.W) =
      rhoB c Mo b * (x : LGL 2 Mo.W) * (rhoB c Mo b)⁻¹ :=
  rfl

private theorem psi_one_apply (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (x : ↥(hatK Mo V)) :
    psi c Mo 1 x = x := by
  apply Subtype.ext
  rw [psi_apply, rhoB_one]
  group

private theorem psi_mul_apply (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b b' : ↥B) (x : ↥(hatK Mo V)) :
    psi c Mo (b * b') x = psi c Mo b (psi c Mo b' x) := by
  apply Subtype.ext
  rw [psi_apply, psi_apply, psi_apply, rhoB_mul]
  group

private noncomputable def chi (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) : hatX Mo V ≃* hatX Mo V :=
  QuotientGroup.congr (CFSG.pCore 2 ↥(hatK Mo V)) (CFSG.pCore 2 ↥(hatK Mo V))
    (psi c Mo b) (CFSG.pCore_map_iso 2 (psi c Mo b))

private noncomputable def betaAut (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) :
    MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) :=
  QuotientGroup.congr (Subgroup.center (hatX Mo V)) (Subgroup.center (hatX Mo V))
    (chi c Mo b) (Subgroup.map_center_eq (chi c Mo b))

private theorem betaAut_apply (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (b : ↥B) (x : ↥(hatK Mo V)) :
    betaAut c Mo b (hatBar Mo V x) = hatBar Mo V (psi c Mo b x) :=
  rfl

private noncomputable def betaHom (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) where
  toFun b := betaAut c Mo b
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := hatBar_surjective Mo V y
    rw [betaAut_apply, psi_one_apply, MulAut.one_apply]
  map_mul' b b' := by
    ext y
    obtain ⟨x, rfl⟩ := hatBar_surjective Mo V y
    simp only [MulAut.mul_apply, betaAut_apply, psi_mul_apply]

theorem w16gt2NTwoH_exists_barAct (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∃ β : ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)),
      ∀ (b : ↥B) (x x' : ↥(hatK Mo V)),
        (x' : LGL 2 Mo.W) = Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩ * x *
            (Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩)⁻¹ →
          β b (hatBar Mo V x) = hatBar Mo V x' := by
  refine ⟨betaHom c Mo, ?_⟩
  intro b x x' hx'
  change betaAut c Mo b (hatBar Mo V x) = hatBar Mo V x'
  rw [betaAut_apply]
  exact congrArg (hatBar Mo V) (Subtype.ext (by rw [psi_apply]; exact hx'.symm))

end NoCert

section NoCert2

private theorem betaAut_eq_conj_apply (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (β : ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)))
    (hβ : ∀ (b : ↥B) (x x' : ↥(hatK Mo V)),
      (x' : LGL 2 Mo.W) = rhoB c Mo b * x * (rhoB c Mo b)⁻¹ →
        β b (hatBar Mo V x) = hatBar Mo V x')
    (hPerfect : Group.IsPerfect ↥(hatK Mo V))
    (hker : (hatBar Mo V).ker = Subgroup.center ↥(hatK Mo V))
    {b : ↥B} {k : ↥(hatK Mo V)}
    (hkb : β b = MulAut.conj (hatBar Mo V k)) :
    ∀ x : ↥(hatK Mo V), psi c Mo b x = k * x * k⁻¹ := by
  haveI := hPerfect
  intro x
  have hψy : ∀ y : ↥(hatK Mo V),
      hatBar Mo V (psi c Mo b y) = hatBar Mo V (k * y * k⁻¹) := by
    intro y
    have h1 : β b (hatBar Mo V y) = hatBar Mo V (psi c Mo b y) :=
      hβ b y (psi c Mo b y) (psi_apply c Mo b y).symm
    have h2 : β b (hatBar Mo V y) = hatBar Mo V (k * y * k⁻¹) := by
      rw [hkb]
      show MulAut.conj (hatBar Mo V k) (hatBar Mo V y) = hatBar Mo V (k * y * k⁻¹)
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    exact h1.symm.trans h2
  have hz : ∀ y : ↥(hatK Mo V),
      psi c Mo b y * (k * y * k⁻¹)⁻¹ ∈ Subgroup.center ↥(hatK Mo V) := by
    intro y
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hψy y, mul_inv_cancel]
  have hYψ : ∀ y : ↥(hatK Mo V),
      (k * y * k⁻¹) * psi c Mo b y = psi c Mo b y * (k * y * k⁻¹) := by
    intro y
    have h := Subgroup.mem_center_iff.1 (hz y) (k * y * k⁻¹)
    have h2 : (k * y * k⁻¹) * psi c Mo b y * (k * y * k⁻¹)⁻¹ = psi c Mo b y := by
      calc (k * y * k⁻¹) * psi c Mo b y * (k * y * k⁻¹)⁻¹
          = (k * y * k⁻¹) * (psi c Mo b y * (k * y * k⁻¹)⁻¹) := by group
        _ = (psi c Mo b y * (k * y * k⁻¹)⁻¹) * (k * y * k⁻¹) := h
        _ = psi c Mo b y := by group
    calc (k * y * k⁻¹) * psi c Mo b y
        = ((k * y * k⁻¹) * psi c Mo b y * (k * y * k⁻¹)⁻¹) * (k * y * k⁻¹) := by group
      _ = psi c Mo b y * (k * y * k⁻¹) := by rw [h2]
  have hzY : ∀ y : ↥(hatK Mo V),
      (k * y * k⁻¹)⁻¹ * psi c Mo b y = psi c Mo b y * (k * y * k⁻¹)⁻¹ := by
    intro y
    calc (k * y * k⁻¹)⁻¹ * psi c Mo b y
        = ((k * y * k⁻¹)⁻¹ * psi c Mo b y * (k * y * k⁻¹)) *
            (k * y * k⁻¹)⁻¹ := by group
      _ = ((k * y * k⁻¹)⁻¹ * (psi c Mo b y * (k * y * k⁻¹))) *
            (k * y * k⁻¹)⁻¹ := by group
      _ = ((k * y * k⁻¹)⁻¹ * ((k * y * k⁻¹) * psi c Mo b y)) *
            (k * y * k⁻¹)⁻¹ := by rw [← hYψ y]
      _ = psi c Mo b y * (k * y * k⁻¹)⁻¹ := by group
  let φ : ↥(hatK Mo V) →* ↥(hatK Mo V) :=
    (MulAut.conj k⁻¹).toMonoidHom.comp (psi c Mo b)
  have hφ_apply : ∀ y, φ y = k⁻¹ * psi c Mo b y * k := by
    intro y
    change (MulAut.conj k⁻¹) (psi c Mo b y) = k⁻¹ * psi c Mo b y * k
    rw [MulAut.conj_apply]
    group
  have hcentral : ∀ y, y⁻¹ * φ y ∈ Subgroup.center ↥(hatK Mo V) := by
    intro y
    rw [hφ_apply]
    have e : y⁻¹ * (k⁻¹ * psi c Mo b y * k) =
        k⁻¹ * ((k * y * k⁻¹)⁻¹ * psi c Mo b y) * k := by group
    rw [e, hzY y]
    exact (inferInstance : (Subgroup.center ↥(hatK Mo V)).Normal).conj_mem
      (psi c Mo b y * (k * y * k⁻¹)⁻¹) (hz y) k⁻¹
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hcentral
  have hxφ : φ x = x := by rw [hid]; rfl
  rw [hφ_apply] at hxφ
  calc psi c Mo b x = k * (k⁻¹ * psi c Mo b x * k) * k⁻¹ := by group
    _ = k * x * k⁻¹ := by rw [hxφ]

private theorem pullback_of_betaAut_conj (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (β : ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)))
    (hβ : ∀ (b : ↥B) (x x' : ↥(hatK Mo V)),
      (x' : LGL 2 Mo.W) = rhoB c Mo b * x * (rhoB c Mo b)⁻¹ →
        β b (hatBar Mo V x) = hatBar Mo V x')
    (hPerfect : Group.IsPerfect ↥(hatK Mo V))
    (hker : (hatBar Mo V).ker = Subgroup.center ↥(hatK Mo V))
    {b : ↥B} {k : G} (hkH : k ∈ H) (hk : k ∈ conjClosure V H)
    {kh : ↥(hatK Mo V)} (hρ : Mo.ρ ⟨k, hkH⟩ = (kh : LGL 2 Mo.W))
    (hkb : β b = MulAut.conj (hatBar Mo V kh)) :
    ∀ x ∈ conjClosure V H,
      (k * x * k⁻¹)⁻¹ * ((b : G) * x * (b : G)⁻¹) ∈
        H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
  intro x hx
  have hxH : x ∈ H := conjClosure_le_H c hx
  have hbH : (b : G) ∈ H := c.mem.1 (c.B_le b.2)
  have hconjB : (b : G) * x * (b : G)⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H hbH) x).1 hx
  have hconjK : k * x * k⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H hkH) x).1 hx
  have hconjBH : (b : G) * x * (b : G)⁻¹ ∈ H := conjClosure_le_H c hconjB
  have hconjKH : k * x * k⁻¹ ∈ H := conjClosure_le_H c hconjK
  let xq : ↥(hatK Mo V) :=
    ⟨Mo.ρ ⟨x, hxH⟩, Mo.mem_img.2 ⟨⟨x, hxH⟩, hx, rfl⟩⟩
  have hclaim := betaAut_eq_conj_apply c Mo β hβ hPerfect hker hkb xq
  have hpsi : (psi c Mo b xq : LGL 2 Mo.W) =
      Mo.ρ ⟨(b : G) * x * (b : G)⁻¹, hconjBH⟩ := by
    have hxq : (xq : LGL 2 Mo.W) = Mo.ρ ⟨x, hxH⟩ := rfl
    rw [psi_apply, hxq]
    unfold rhoB
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hkhat : ((kh * xq * kh⁻¹ : ↥(hatK Mo V)) : LGL 2 Mo.W) =
      Mo.ρ ⟨k * x * k⁻¹, hconjKH⟩ := by
    have hxq : (xq : LGL 2 Mo.W) = Mo.ρ ⟨x, hxH⟩ := rfl
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxq, ← hρ]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hval : Mo.ρ ⟨(b : G) * x * (b : G)⁻¹, hconjBH⟩ =
      Mo.ρ ⟨k * x * k⁻¹, hconjKH⟩ := by
    have h := congrArg (fun z : ↥(hatK Mo V) => (z : LGL 2 Mo.W)) hclaim
    rw [hpsi, hkhat] at h
    exact h
  refine ⟨H.mul_mem (H.inv_mem hconjKH) hconjBH, ?_⟩
  have hρ1 : Mo.ρ (⟨(k * x * k⁻¹)⁻¹ * ((b : G) * x * (b : G)⁻¹),
      H.mul_mem (H.inv_mem hconjKH) hconjBH⟩ : ↥H) = 1 := by
    change Mo.ρ (((⟨k * x * k⁻¹, hconjKH⟩ : ↥H)⁻¹) *
      ⟨(b : G) * x * (b : G)⁻¹, hconjBH⟩) = 1
    rw [map_mul, map_inv, hval, inv_mul_cancel]
  have hcent := (Mo.ρ_eq_one_iff (⟨(k * x * k⁻¹)⁻¹ * ((b : G) * x * (b : G)⁻¹),
      H.mul_mem (H.inv_mem hconjKH) hconjBH⟩ : ↥H)).1 hρ1
  simpa using hcent

end NoCert2

section Certified

theorem w16gt2NTwoH_barAct_properties (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (β : ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)))
    (hβ : ∀ (b : ↥B) (x x' : ↥(hatK Mo V)),
      (x' : LGL 2 Mo.W) = Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩ * x *
          (Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩)⁻¹ →
        β b (hatBar Mo V x) = hatBar Mo V x') :
    Function.Injective β ∧ IsElemAbelian 2 β.range ∧
      (∀ y : hatX Mo V ⧸ Subgroup.center (hatX Mo V), MulAut.conj y ∈ β.range →
        ∀ v ∈ hatBarSub Mo V V, y * v = v * y) ∧
      ∀ y ∈ hatBarSub Mo V V, MulAut.conj y ∈ β.range → y = 1 := by
  have hPerfect : Group.IsPerfect ↥(hatK Mo V) := c.isPerfect_hatK hn h1 h5 h15 hS Mo
  have hker : (hatBar Mo V).ker = Subgroup.center ↥(hatK Mo V) :=
    c.ker_hatBar hn h1 h5 h15 hS Mo
  haveI : Group.IsPerfect ↥(hatK Mo V) := hPerfect
  haveI : Group.IsPerfect (hatX Mo V) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK Mo V)))
  have hZ : Subgroup.center (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (hatX Mo V)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro b hb1
    have hconj1 : MulAut.conj (1 : ↥(hatK Mo V)) = 1 := by
      ext z; simp [MulAut.conj_apply]
    have hkb : β b = MulAut.conj (hatBar Mo V (1 : ↥(hatK Mo V))) := by
      rw [hb1]
      simp [MulAut.conj_apply]
    have hρ1 : Mo.ρ (⟨(1 : G), H.one_mem⟩ : ↥H) = ((1 : ↥(hatK Mo V)) : LGL 2 Mo.W) := by
      rw [show (⟨(1 : G), H.one_mem⟩ : ↥H) = 1 from Subtype.ext rfl, map_one]
      rfl
    have hbk := pullback_of_betaAut_conj c Mo β hβ hPerfect hker H.one_mem
      (conjClosure V H).one_mem (kh := 1) hρ1 hkb
    obtain ⟨-, h2⟩ := c.eq_one_of_conj_eq_of_mem_sup b.2 (conjClosure V H).one_mem hbk
    exact Subtype.ext (h2 (Subgroup.mem_sup_left V.one_mem))
  · have hV₀ea : IsElemAbelian 2 V₀ :=
      c.cex.hyp.h6.elemAbelian.mono c.cex.hyp.h6.le
    have hBea : IsElemAbelian 2 B := by
      obtain ⟨m, -, hBm⟩ := c.B_conj
      rw [hBm]
      exact E3.isElemAbelian_conjSubgroup (E3.isElemAbelian_conjSubgroup hV₀ea g) m
    haveI : IsMulCommutative ↥B := hBea.1
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hx
    have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa using hBea.2 b b.2)
    rw [← map_pow, hb2, map_one]
  · intro y hyR
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hyR
    obtain ⟨kh, hkh⟩ := hatBar_surjective Mo V y
    obtain ⟨j, hjK, hρj⟩ := Mo.mem_img.1 kh.2
    have hkb : β b = MulAut.conj (hatBar Mo V kh) := by rw [hb, ← hkh]
    have hbk := pullback_of_betaAut_conj c Mo β hβ hPerfect hker j.2 hjK hρj hkb
    obtain ⟨hcommK, -⟩ := c.eq_one_of_conj_eq_of_mem_sup b.2 hjK hbk
    intro v hv
    obtain ⟨x₀, hx₀V, hx₀eq⟩ := (mem_hatBarSub_iff (Mo := Mo) (V := V)).1 hv
    obtain ⟨jv, hjvV, hρv⟩ := Mo.mem_img.1 hx₀V
    have hcom := hcommK (jv : G) hjvV
    have hρcom : Mo.ρ ⁅j, jv⁆ = 1 := (Mo.ρ_eq_one_iff _).2 (by
      simpa [commutatorElement_def] using hcom.2)
    have hρmap : Mo.ρ ⁅j, jv⁆ = ⁅(kh : LGL 2 Mo.W), (x₀ : LGL 2 Mo.W)⁆ := by
      rw [map_commutatorElement, hρj, hρv]
    have hcommQ : (⁅kh, x₀⁆ : ↥(hatK Mo V)) = 1 := by
      apply Subtype.ext
      show ⁅(kh : LGL 2 Mo.W), (x₀ : LGL 2 Mo.W)⁆ = (1 : LGL 2 Mo.W)
      rw [← hρmap, hρcom]
    have hkcomm : kh * x₀ = x₀ * kh := commutatorElement_eq_one_iff_mul_comm.1 hcommQ
    calc y * v = hatBar Mo V kh * hatBar Mo V x₀ := by rw [← hkh, ← hx₀eq]
      _ = hatBar Mo V (kh * x₀) := (map_mul _ _ _).symm
      _ = hatBar Mo V (x₀ * kh) := by rw [hkcomm]
      _ = hatBar Mo V x₀ * hatBar Mo V kh := map_mul _ _ _
      _ = v * y := by rw [hx₀eq, hkh]
  · intro y hyV hyR
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hyR
    obtain ⟨x₀, hx₀V, hx₀eq⟩ := (mem_hatBarSub_iff (Mo := Mo) (V := V)).1 hyV
    obtain ⟨jv, hjvV, hρv⟩ := Mo.mem_img.1 hx₀V
    have hkb : β b = MulAut.conj (hatBar Mo V x₀) := by rw [hb, ← hx₀eq]
    have hbk := pullback_of_betaAut_conj c Mo β hβ hPerfect hker jv.2
      (le_conjClosure V H hjvV) hρv hkb
    obtain ⟨-, h2⟩ := c.eq_one_of_conj_eq_of_mem_sup b.2 (le_conjClosure V H hjvV) hbk
    have hb1 : (b : G) = 1 := h2 (Subgroup.mem_sup_left hjvV)
    have hb1' : b = 1 := Subtype.ext hb1
    have hconj1 : MulAut.conj y = 1 := by rw [← hb, hb1', map_one]
    have hyc : y ∈ Subgroup.center (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h := congrArg (fun f : MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) => f z)
        hconj1
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc z * y = (y * z * y⁻¹) * y := by rw [h]
        _ = y * z := by group
    exact Subgroup.mem_bot.1 (hZ ▸ hyc)

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
