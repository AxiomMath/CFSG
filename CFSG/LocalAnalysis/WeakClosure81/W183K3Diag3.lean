module

import CFSG.LocalAnalysis.WeakClosure81.W183K3Diag3Aux1
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Alpha
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)}

theorem w183k3_diag_decomp (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ≤ Y) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card ↥A = 4)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hC₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hC₂ : A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥)
    (hin₁ : alphaA Y L₁ A ≤ alphaL Y L₁) (hin₂ : alphaA Y L₂ A ≤ alphaL Y L₂)
    (hn : ∃ nb ∈ alphaL Y L₁, (∀ x ∈ alphaA Y L₁ A, nb * x * nb⁻¹ ∈ alphaA Y L₁ A) ∧
      ∀ x ∈ alphaA Y L₁ A, x ≠ 1 → nb * x * nb⁻¹ ≠ x) :
    ∃ (X₁ X₂ : Subgroup (LGL 2 V)) (φ : ↥X₁ ≃* ↥X₂), X₁ ≤ L₁ ∧ X₂ ≤ L₂ ∧
      Nat.card ↥X₁ = 4 ∧ (∀ x ∈ X₁, x * x = 1) ∧
      (∀ d, d ∈ A ↔ ∃ x : ↥X₁, d = (x : LGL 2 V) * (φ x : LGL 2 V)) ∧
      ∃ n ∈ L₁, (∀ x ∈ X₁, n * x * n⁻¹ ∈ X₁) ∧ ∀ x ∈ X₁, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  classical
  have hex : ∀ a : ↥A, ∃ p : LGL 2 V × LGL 2 V,
      p.1 ∈ L₁ ∧ p.2 ∈ L₂ ∧ (a : LGL 2 V) = p.1 * p.2 ∧
      p.1 * p.1 = 1 ∧ p.2 * p.2 = 1 := by
    intro a
    obtain ⟨x, hx, y, hy, ha, hx2, hy2⟩ :=
      w183k3_diag_split htwo hA hel hAn₁ hAn₂ hin₁ hin₂ a.2
    exact ⟨(x, y), hx, hy, ha, hx2, hy2⟩
  let xf : ↥A → LGL 2 V := fun a => (Classical.choose (hex a)).1
  let yf : ↥A → LGL 2 V := fun a => (Classical.choose (hex a)).2
  have hxf : ∀ a : ↥A, xf a ∈ L₁ := fun a => (Classical.choose_spec (hex a)).1
  have hyf : ∀ a : ↥A, yf a ∈ L₂ := fun a => (Classical.choose_spec (hex a)).2.1
  have hxy : ∀ a : ↥A, (a : LGL 2 V) = xf a * yf a :=
    fun a => (Classical.choose_spec (hex a)).2.2.1
  have hxf2 : ∀ a : ↥A, xf a * xf a = 1 := fun a => (Classical.choose_spec (hex a)).2.2.2.1
  have hyf2 : ∀ a : ↥A, yf a * yf a = 1 := fun a => (Classical.choose_spec (hex a)).2.2.2.2
  have hxq₁ : ∀ a : ↥A,
      alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ =
      alphaMk Y L₁ ⟨(a : LGL 2 V), ⟨hA a.2, hAn₁ a.2⟩⟩ := by
    intro a
    have hyC : yf a ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => htwo.comm l hl (yf a) (hyf a)
    have hyA : yf a ∈ alphaC Y L₁ := Subgroup.mem_inf.mpr ⟨htwo.le₂ (hyf a), hyC⟩
    have hyX : yf a ∈ alphaX Y L₁ :=
      ⟨htwo.le₂ (hyf a), Subgroup.centralizer_le_normalizer (L₁ : Set (LGL 2 V)) hyC⟩
    have hd : (⟨(a : LGL 2 V), ⟨hA a.2, hAn₁ a.2⟩⟩ : ↥(alphaX Y L₁)) *
        ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩⁻¹ = ⟨yf a, hyX⟩ := by
      apply Subtype.ext
      show (a : LGL 2 V) * (xf a)⁻¹ = yf a
      calc (a : LGL 2 V) * (xf a)⁻¹ = (xf a * yf a) * (xf a)⁻¹ := by rw [← hxy a]
        _ = yf a := by rw [htwo.comm (xf a) (hxf a) (yf a) (hyf a)]; group
    have hker : alphaMk Y L₁ ((⟨(a : LGL 2 V), ⟨hA a.2, hAn₁ a.2⟩⟩ : ↥(alphaX Y L₁)) *
        ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩⁻¹) = 1 := by
      rw [hd]
      exact (QuotientGroup.eq_one_iff
        (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mpr
        (Subgroup.mem_subgroupOf.mpr hyA)
    have h2 := hker
    rw [map_mul, map_inv] at h2
    exact (mul_inv_eq_one.mp h2).symm
  have hyq₂ : ∀ a : ↥A,
      alphaMk Y L₂ ⟨yf a, ⟨htwo.le₂ (hyf a), L₂.le_normalizer (hyf a)⟩⟩ =
      alphaMk Y L₂ ⟨(a : LGL 2 V), ⟨hA a.2, hAn₂ a.2⟩⟩ := by
    intro a
    have hxC : xf a ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => (htwo.comm (xf a) (hxf a) l hl).symm
    have hxA : xf a ∈ alphaC Y L₂ := Subgroup.mem_inf.mpr ⟨htwo.le₁ (hxf a), hxC⟩
    have hxX : xf a ∈ alphaX Y L₂ :=
      ⟨htwo.le₁ (hxf a), Subgroup.centralizer_le_normalizer (L₂ : Set (LGL 2 V)) hxC⟩
    have hd : (⟨(a : LGL 2 V), ⟨hA a.2, hAn₂ a.2⟩⟩ : ↥(alphaX Y L₂)) *
        ⟨yf a, ⟨htwo.le₂ (hyf a), L₂.le_normalizer (hyf a)⟩⟩⁻¹ = ⟨xf a, hxX⟩ := by
      apply Subtype.ext
      show (a : LGL 2 V) * (yf a)⁻¹ = xf a
      calc (a : LGL 2 V) * (yf a)⁻¹ = (xf a * yf a) * (yf a)⁻¹ := by rw [← hxy a]
        _ = xf a := by group
    have hker : alphaMk Y L₂ ((⟨(a : LGL 2 V), ⟨hA a.2, hAn₂ a.2⟩⟩ : ↥(alphaX Y L₂)) *
        ⟨yf a, ⟨htwo.le₂ (hyf a), L₂.le_normalizer (hyf a)⟩⟩⁻¹) = 1 := by
      rw [hd]
      exact (QuotientGroup.eq_one_iff
        (N := (alphaC Y L₂).subgroupOf (alphaX Y L₂)) _).mpr
        (Subgroup.mem_subgroupOf.mpr hxA)
    have h2 := hker
    rw [map_mul, map_inv] at h2
    exact (mul_inv_eq_one.mp h2).symm
  have hcommx : ∀ a b : ↥A, xf a * xf b = xf b * xf a := fun a b =>
    w183k3_diag_comm_of_quot htwo.odd₁ htwo.le₁ hA hAn₁
      (isMulCommutative_iff.mp hel.1) (hxf a) (hxf b) (hxf2 a) (hxf2 b)
      (hxq₁ a) (hxq₁ b)
  have hcommy : ∀ a b : ↥A, yf a * yf b = yf b * yf a := fun a b =>
    w183k3_diag_comm_of_quot htwo.odd₂ htwo.le₂ hA hAn₂
      (isMulCommutative_iff.mp hel.1) (hyf a) (hyf b) (hyf2 a) (hyf2 b)
      (hyq₂ a) (hyq₂ b)
  have hsqx : ∀ a b : ↥A, (xf a * xf b) * (xf a * xf b) = 1 := by
    intro a b
    rw [show (xf a * xf b) * (xf a * xf b) = (xf a * xf a) * (xf b * xf b) by
      rw [show (xf a * xf b) * (xf a * xf b) = xf a * (xf b * xf a) * xf b by group,
        ← hcommx a b]
      group,
      hxf2 a, hxf2 b, one_mul]
  have hsqy : ∀ a b : ↥A, (yf a * yf b) * (yf a * yf b) = 1 := by
    intro a b
    rw [show (yf a * yf b) * (yf a * yf b) = (yf a * yf a) * (yf b * yf b) by
      rw [show (yf a * yf b) * (yf a * yf b) = yf a * (yf b * yf a) * yf b by group,
        ← hcommy a b]
      group,
      hyf2 a, hyf2 b, one_mul]
  have heq : ∀ a b : ↥A, xf (a * b) * yf (a * b) = (xf a * xf b) * (yf a * yf b) := by
    intro a b
    calc xf (a * b) * yf (a * b) = ((a * b : ↥A) : LGL 2 V) := (hxy (a * b)).symm
      _ = (a : LGL 2 V) * (b : LGL 2 V) := rfl
      _ = (xf a * yf a) * (xf b * yf b) := by rw [hxy a, hxy b]
      _ = (xf a * xf b) * (yf a * yf b) := by
        rw [show (xf a * yf a) * (xf b * yf b) = xf a * (yf a * xf b) * yf b by group,
          show yf a * xf b = xf b * yf a from (htwo.comm (xf b) (hxf b) (yf a) (hyf a)).symm]
        group
  let xhHom : ↥A →* LGL 2 V :=
    { toFun := xf
      map_one' := by
        have h1 : xf 1 * yf 1 = 1 := (hxy 1).symm
        exact (w183k3_diag_unique htwo (hxf 1) L₁.one_mem (hxf2 1) (by rw [mul_one])
          (hyf 1) L₂.one_mem (hyf2 1) (by rw [mul_one]) (by rw [h1, one_mul])).1
      map_mul' := fun a b =>
        (w183k3_diag_unique htwo (hxf (a * b)) (L₁.mul_mem (hxf a) (hxf b))
          (hxf2 (a * b)) (hsqx a b) (hyf (a * b)) (L₂.mul_mem (hyf a) (hyf b))
          (hyf2 (a * b)) (hsqy a b) (heq a b)).1 }
  let yhHom : ↥A →* LGL 2 V :=
    { toFun := yf
      map_one' := by
        have h1 : xf 1 * yf 1 = 1 := (hxy 1).symm
        exact (w183k3_diag_unique htwo (hxf 1) L₁.one_mem (hxf2 1) (by rw [mul_one])
          (hyf 1) L₂.one_mem (hyf2 1) (by rw [mul_one]) (by rw [h1, one_mul])).2
      map_mul' := fun a b =>
        (w183k3_diag_unique htwo (hxf (a * b)) (L₁.mul_mem (hxf a) (hxf b))
          (hxf2 (a * b)) (hsqx a b) (hyf (a * b)) (L₂.mul_mem (hyf a) (hyf b))
          (hyf2 (a * b)) (hsqy a b) (heq a b)).2 }
  have hxh_ker : ∀ a : ↥A, xhHom a = 1 → a = 1 := by
    intro a ha
    have hxa : xf a = 1 := ha
    apply Subtype.ext
    have h : (a : LGL 2 V) = yf a := by rw [hxy a, hxa, one_mul]
    have hcent : (a : LGL 2 V) ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
      rw [h]
      exact Subgroup.mem_centralizer_iff.mpr fun l hl => htwo.comm l hl (yf a) (hyf a)
    have hbot : (a : LGL 2 V) ∈ A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := ⟨a.2, hcent⟩
    rw [hC₁, Subgroup.mem_bot] at hbot
    exact hbot
  have hyh_ker : ∀ a : ↥A, yhHom a = 1 → a = 1 := by
    intro a ha
    have hya : yf a = 1 := ha
    apply Subtype.ext
    have h : (a : LGL 2 V) = xf a := by rw [hxy a, hya, mul_one]
    have hcent : (a : LGL 2 V) ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      rw [h]
      exact Subgroup.mem_centralizer_iff.mpr fun l hl => (htwo.comm (xf a) (hxf a) l hl).symm
    have hbot : (a : LGL 2 V) ∈ A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := ⟨a.2, hcent⟩
    rw [hC₂, Subgroup.mem_bot] at hbot
    exact hbot
  have hxh_inj : Function.Injective xhHom := by
    intro a b hab
    have hker : xhHom (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hxh_ker (a * b⁻¹) hker)
  have hyh_inj : Function.Injective yhHom := by
    intro a b hab
    have hker : yhHom (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hyh_ker (a * b⁻¹) hker)
  have hX₁le : xhHom.range ≤ L₁ := by
    rintro x ⟨a, rfl⟩
    exact hxf a
  have hX₂le : yhHom.range ≤ L₂ := by
    rintro x ⟨a, rfl⟩
    exact hyf a
  have hX₁sq : ∀ x ∈ xhHom.range, x * x = 1 := by
    rintro x ⟨a, rfl⟩
    exact hxf2 a
  have hcardX₁ : Nat.card ↥xhHom.range = 4 :=
    (Nat.card_congr (MonoidHom.ofInjective hxh_inj).toEquiv).symm.trans hcard
  let φ : ↥xhHom.range ≃* ↥yhHom.range :=
    (MonoidHom.ofInjective hxh_inj).symm.trans (MonoidHom.ofInjective hyh_inj)
  have hφ_apply : ∀ a : ↥A, φ (MonoidHom.ofInjective hxh_inj a) =
      MonoidHom.ofInjective hyh_inj a := by
    intro a
    simp [φ, MulEquiv.trans_apply]
  have hAdiag : ∀ d, d ∈ A ↔ ∃ x : ↥xhHom.range, d = (x : LGL 2 V) * (φ x : LGL 2 V) := by
    intro d
    constructor
    · intro hd
      refine ⟨MonoidHom.ofInjective hxh_inj ⟨d, hd⟩, ?_⟩
      rw [hφ_apply ⟨d, hd⟩, MonoidHom.ofInjective_apply hxh_inj,
        MonoidHom.ofInjective_apply hyh_inj]
      change d = xf ⟨d, hd⟩ * yf ⟨d, hd⟩
      exact hxy ⟨d, hd⟩
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      have hxeq : x = MonoidHom.ofInjective hxh_inj a :=
        Subtype.ext (by rw [MonoidHom.ofInjective_apply]; exact ha.symm)
      rw [hxeq, hφ_apply a, MonoidHom.ofInjective_apply hxh_inj,
        MonoidHom.ofInjective_apply hyh_inj] at hx
      rw [hx]
      change xf a * yf a ∈ A
      rw [← hxy a]
      exact a.2
  obtain ⟨nb, hnbL, hnbNorm, hnbFpf⟩ := hn
  obtain ⟨nsub, hnsub, hnbeq⟩ := Subgroup.mem_map.mp hnbL
  have hnL : nsub.1 ∈ L₁ := Subgroup.mem_subgroupOf.mp hnsub
  refine ⟨xhHom.range, yhHom.range, φ, hX₁le, hX₂le, hcardX₁, hX₁sq, hAdiag, nsub.1, hnL, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    have hmem_xf : alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ ∈
        alphaA Y L₁ A := by
      rw [hxq₁ a]
      exact Subgroup.mem_map_of_mem (alphaMk Y L₁)
        (Subgroup.mem_subgroupOf.mpr a.2)
    have hnbA : nb * alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ * nb⁻¹ ∈
        alphaA Y L₁ A := hnbNorm _ hmem_xf
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hnbA
    let x' : ↥xhHom.range :=
      ⟨xhHom ⟨b.1, hb⟩, MonoidHom.mem_range.mpr ⟨⟨b.1, hb⟩, rfl⟩⟩
    have hx'q : alphaMk Y L₁ ⟨x'.1, ⟨htwo.le₁ (hX₁le x'.2), L₁.le_normalizer (hX₁le x'.2)⟩⟩ =
        nb * alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ * nb⁻¹ := by
      have h1 : alphaMk Y L₁ ⟨x'.1, ⟨htwo.le₁ (hX₁le x'.2), L₁.le_normalizer (hX₁le x'.2)⟩⟩ =
          alphaMk Y L₁ ⟨(((⟨b.1, hb⟩ : ↥A) : LGL 2 V)), ⟨hA hb, hAn₁ hb⟩⟩ :=
        hxq₁ ⟨b.1, hb⟩
      have h2 : alphaMk Y L₁ b =
          alphaMk Y L₁ ⟨(((⟨b.1, hb⟩ : ↥A) : LGL 2 V)), ⟨hA hb, hAn₁ hb⟩⟩ :=
        congrArg (alphaMk Y L₁) (Subtype.ext rfl)
      rw [h1, ← h2, hbeq]
    have hker : alphaMk Y L₁ (nsub * ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
        nsub⁻¹ * ⟨x'.1, ⟨htwo.le₁ (hX₁le x'.2), L₁.le_normalizer (hX₁le x'.2)⟩⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hnbeq, hx'q]
      group
    have hvalC : (nsub * ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
        nsub⁻¹ * ⟨x'.1, ⟨htwo.le₁ (hX₁le x'.2), L₁.le_normalizer (hX₁le x'.2)⟩⟩⁻¹).1 ∈
        Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff
          (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mp hker))).2
    have hzL : (nsub * ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
        nsub⁻¹ * ⟨x'.1, ⟨htwo.le₁ (hX₁le x'.2), L₁.le_normalizer (hX₁le x'.2)⟩⟩⁻¹).1 ∈ L₁ :=
      L₁.mul_mem (L₁.mul_mem (L₁.mul_mem hnL (hxf a)) (L₁.inv_mem hnL))
        (L₁.inv_mem (hX₁le x'.2))
    have hzqc : (nsub * ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
        nsub⁻¹ * ⟨x'.1, ⟨htwo.le₁ (hX₁le x'.2), L₁.le_normalizer (hX₁le x'.2)⟩⟩⁻¹).1 ∈
        quasiCentre L₁ := by
      rw [mem_quasiCentre]
      exact ⟨hzL, fun l hl => (Subgroup.mem_centralizer_iff.mp hvalC l hl).symm⟩
    have hA2 : (nsub.1 * xf a * nsub.1⁻¹) * (nsub.1 * xf a * nsub.1⁻¹) = 1 := by
      rw [show (nsub.1 * xf a * nsub.1⁻¹) * (nsub.1 * xf a * nsub.1⁻¹) =
          nsub.1 * (xf a * xf a) * nsub.1⁻¹ by group, hxf2 a]
      group
    have hB2 : (x'.1)⁻¹ * (x'.1)⁻¹ = 1 := by
      rw [← mul_inv_rev, hX₁sq x'.1 x'.2, inv_one]
    have hcommAB : (x'.1)⁻¹ * (nsub.1 * xf a * nsub.1⁻¹) =
        (nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹ := by
      have hzA : (nsub.1 * xf a * nsub.1⁻¹) ∈ L₁ :=
        L₁.mul_mem (L₁.mul_mem hnL (hxf a)) (L₁.inv_mem hnL)
      have h1 := (mem_quasiCentre.mp hzqc).2 (nsub.1 * xf a * nsub.1⁻¹) hzA
      change ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) * (nsub.1 * xf a * nsub.1⁻¹) =
        (nsub.1 * xf a * nsub.1⁻¹) * ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) at h1
      have h2 : (nsub.1 * xf a * nsub.1⁻¹) * ((x'.1)⁻¹ * (nsub.1 * xf a * nsub.1⁻¹)) =
          (nsub.1 * xf a * nsub.1⁻¹) * ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) := by
        rw [← mul_assoc, h1]
      exact mul_left_cancel h2
    have hzsq : ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) *
        ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) = 1 := by
      rw [show ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) *
          ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) =
          ((nsub.1 * xf a * nsub.1⁻¹) * (nsub.1 * xf a * nsub.1⁻¹)) *
            ((x'.1)⁻¹ * (x'.1)⁻¹) by
        rw [show ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) *
            ((nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹) =
            (nsub.1 * xf a * nsub.1⁻¹) * ((x'.1)⁻¹ * (nsub.1 * xf a * nsub.1⁻¹)) *
              (x'.1)⁻¹ by group, hcommAB]
        group,
        hA2, hB2, one_mul]
    have hz1 : (nsub.1 * xf a * nsub.1⁻¹) * (x'.1)⁻¹ = 1 :=
      quasi_centre_two_pow_eq_one htwo.odd₁ hzqc (k := 1) (by
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
        exact hzsq)
    have hAeq : nsub.1 * xf a * nsub.1⁻¹ = x'.1 := mul_inv_eq_one.mp hz1
    change nsub.1 * xf a * nsub.1⁻¹ ∈ xhHom.range
    rw [hAeq]
    exact x'.2
  · intro x hx hxne hfix
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    have hmem_xf : alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ ∈
        alphaA Y L₁ A := by
      rw [hxq₁ a]
      exact Subgroup.mem_map_of_mem (alphaMk Y L₁)
        (Subgroup.mem_subgroupOf.mpr a.2)
    have hfixq : nb * alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ * nb⁻¹ =
        alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ := by
      have h1 : alphaMk Y L₁ (nsub * ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
          nsub⁻¹) = nb * alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
          nb⁻¹ := by
        simp only [map_mul, map_inv, hnbeq]
      have h2 : alphaMk Y L₁ (nsub * ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ *
          nsub⁻¹) =
          alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ := by
        congr 1
        apply Subtype.ext
        show nsub.1 * xf a * nsub.1⁻¹ = xf a
        exact hfix
      rw [← h1, h2]
    have hne1 : alphaMk Y L₁ ⟨xf a, ⟨htwo.le₁ (hxf a), L₁.le_normalizer (hxf a)⟩⟩ ≠ 1 := by
      intro h1
      have hpa : alphaMk Y L₁ ⟨(a : LGL 2 V), ⟨hA a.2, hAn₁ a.2⟩⟩ = 1 := by
        rw [← hxq₁ a, h1]
      have hbot : (a : LGL 2 V) ∈ A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
        refine ⟨a.2, ?_⟩
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp
          ((QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mp
            hpa))).2
      rw [hC₁, Subgroup.mem_bot] at hbot
      have ha1 : a = 1 := Subtype.ext hbot
      exact hxne (by rw [ha1]; exact map_one xhHom)
    exact (hnbFpf _ hmem_xf hne1) hfixq

end CFSG.LocalAnalysis.WeakClosure81

end
