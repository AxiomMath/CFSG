module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin

namespace H

namespace Pair

variable {V : Type*} [CommGroup V]

@[expose] def IsInv (L : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  ∀ l ∈ L, ∀ w ∈ W, l w ∈ W

@[expose] def IsIrr (L : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  W ≠ ⊥ ∧ ∀ U : Subgroup V, U ≤ W → IsInv L U → U = ⊥ ∨ U = W

@[expose] def IsoMod (L : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V) : Prop :=
  ∃ e : W₁ ≃* W₂, ∀ l ∈ L, ∀ (w : W₁) (h : l w ∈ W₁), (e ⟨l w, h⟩ : V) = l (e w)

theorem IsoMod.symm {L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V} (h₁ : IsInv L W₁)
    (h : IsoMod L W₁ W₂) : IsoMod L W₂ W₁ := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun l hl w hw => ?_⟩
  have hlu : l ((e.symm w : W₁) : V) ∈ W₁ := h₁ l hl _ (e.symm w).2
  have h1 := he l hl (e.symm w) hlu
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : e.symm ⟨l w, hw⟩ = ⟨l (e.symm w : V), hlu⟩ := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext h1.symm
  rw [h2]

theorem decomp_unique {V₁ V₂ : Subgroup V} (hinf : V₁ ⊓ V₂ = ⊥) {a b c d : V} (ha : a ∈ V₁)
    (hb : b ∈ V₂) (hc : c ∈ V₁) (hd : d ∈ V₂) (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : c⁻¹ * a = d * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : c⁻¹ * a ∈ V₁ ⊓ V₂ :=
    ⟨V₁.mul_mem (V₁.inv_mem hc) ha, h1 ▸ V₂.mul_mem hd (V₂.inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have h3 : a = c := (inv_mul_eq_one.mp h2).symm
  subst h3
  exact ⟨rfl, mul_left_cancel h⟩

theorem exists_decomp {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (v : V) :
    ∃ a ∈ V₁, ∃ b ∈ V₂, a * b = v :=
  Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top v)

@[expose] noncomputable def proj {V₁ V₂ : Subgroup V} (hinf : V₁ ⊓ V₂ = ⊥)
    (hsup : V₁ ⊔ V₂ = ⊤) : V →* V where
  toFun v := Classical.choose (exists_decomp hsup v)
  map_one' := by
    obtain ⟨ha, b, hb, hab⟩ := Classical.choose_spec (exists_decomp hsup (1 : V))
    exact (decomp_unique hinf ha hb V₁.one_mem V₂.one_mem (by rw [hab, one_mul])).1
  map_mul' v w := by
    obtain ⟨ha, b, hb, hab⟩ := Classical.choose_spec (exists_decomp hsup v)
    obtain ⟨hc, d, hd, hcd⟩ := Classical.choose_spec (exists_decomp hsup w)
    obtain ⟨he, f, hf, hef⟩ := Classical.choose_spec (exists_decomp hsup (v * w))
    refine (decomp_unique hinf he hf (V₁.mul_mem ha hc) (V₂.mul_mem hb hd) ?_).1
    rw [hef, mul_mul_mul_comm, hab, hcd]

section Proj

variable {V₁ V₂ : Subgroup V} (hinf : V₁ ⊓ V₂ = ⊥) (hsup : V₁ ⊔ V₂ = ⊤)

theorem proj_mem (v : V) : proj hinf hsup v ∈ V₁ :=
  (Classical.choose_spec (exists_decomp hsup v)).1

theorem proj_spec {v a b : V} (ha : a ∈ V₁) (hb : b ∈ V₂) (h : a * b = v) :
    proj hinf hsup v = a := by
  obtain ⟨ha', b', hb', hab'⟩ := Classical.choose_spec (exists_decomp hsup v)
  exact (decomp_unique hinf ha' hb' ha hb (hab'.trans h.symm)).1

theorem proj_eq_self {a : V} (ha : a ∈ V₁) : proj hinf hsup a = a :=
  proj_spec hinf hsup ha V₂.one_mem (mul_one a)

theorem proj_eq_one_iff {v : V} : proj hinf hsup v = 1 ↔ v ∈ V₂ := by
  obtain ⟨ha, b, hb, hab⟩ := Classical.choose_spec (exists_decomp hsup v)
  have hp : proj hinf hsup v = Classical.choose (exists_decomp hsup v) := rfl
  constructor
  · intro h
    rw [hp] at h
    rw [← hab, h, one_mul]
    exact hb
  · intro hv
    exact proj_spec hinf hsup V₁.one_mem hv (one_mul v)

theorem proj_equivariant {L : Subgroup (MulAut V)} (h₁ : IsInv L V₁) (h₂ : IsInv L V₂)
    {l : MulAut V} (hl : l ∈ L) (v : V) : proj hinf hsup (l v) = l (proj hinf hsup v) := by
  obtain ⟨ha, b, hb, hab⟩ := Classical.choose_spec (exists_decomp hsup v)
  have hp : proj hinf hsup v = Classical.choose (exists_decomp hsup v) := rfl
  refine proj_spec hinf hsup (h₁ l hl _ ha) (h₂ l hl _ hb) ?_
  rw [hp, ← map_mul, hab]

theorem exists_iso_of_proj {L : Subgroup (MulAut V)} (h₁ : IsInv L V₁) (h₂ : IsInv L V₂)
    (hI₁ : IsIrr L V₁) {W : Subgroup V} (hW : IsInv L W) (hW0 : W ≠ ⊥) (hW2 : W ⊓ V₂ = ⊥) :
    ∃ e : W ≃* V₁, (∀ w : W, (e w : V) = proj hinf hsup w) := by
  have hinj : Function.Injective ((proj hinf hsup).comp W.subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : V) ∈ V₂ := (proj_eq_one_iff hinf hsup).mp hw
    have : (w : V) ∈ W ⊓ V₂ := ⟨w.2, h1⟩
    rw [hW2, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have himg : W.map (proj hinf hsup) = V₁ := by
    have hle : W.map (proj hinf hsup) ≤ V₁ := by
      rintro _ ⟨w, -, rfl⟩
      exact proj_mem hinf hsup w
    have hinv : IsInv L (W.map (proj hinf hsup)) := by
      rintro l hl _ ⟨w, hw, rfl⟩
      exact ⟨l w, hW l hl w hw, proj_equivariant hinf hsup h₁ h₂ hl w⟩
    rcases hI₁.2 _ hle hinv with h | h
    · exfalso
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      have : proj hinf hsup w ∈ W.map (proj hinf hsup) := ⟨w, hw, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      have := hinj (a₁ := ⟨w, hw⟩) (a₂ := 1) (by simpa using this)
      simpa using congrArg Subtype.val this
    · exact h
  let f : W →* V₁ := ((proj hinf hsup).comp W.subtype).codRestrict V₁
    (fun w => proj_mem hinf hsup w)
  have hfinj : Function.Injective f := fun a b h => hinj (congrArg Subtype.val h)
  have hfsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rw [← himg] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨⟨w, hw⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, fun w => rfl⟩

end Proj

theorem eq_or_eq_of_isIrr {L : Subgroup (MulAut V)} {V₁ V₂ : Subgroup V} (hinf : V₁ ⊓ V₂ = ⊥)
    (hsup : V₁ ⊔ V₂ = ⊤) (h₁ : IsInv L V₁) (h₂ : IsInv L V₂) (hI₁ : IsIrr L V₁)
    (hI₂ : IsIrr L V₂) (hniso : ¬ IsoMod L V₁ V₂) {W : Subgroup V} (hW : IsInv L W)
    (hWI : IsIrr L W) : W = V₁ ∨ W = V₂ := by
  have hinv1 : IsInv L (W ⊓ V₁) := fun l hl w hw => ⟨hW l hl w hw.1, h₁ l hl w hw.2⟩
  have hinv2 : IsInv L (W ⊓ V₂) := fun l hl w hw => ⟨hW l hl w hw.1, h₂ l hl w hw.2⟩
  rcases hWI.2 _ inf_le_left hinv1 with h1 | h1
  · rcases hWI.2 _ inf_le_left hinv2 with h2 | h2
    · exfalso
      have hinf' : V₂ ⊓ V₁ = ⊥ := by rw [inf_comm]; exact hinf
      have hsup' : V₂ ⊔ V₁ = ⊤ := by rw [sup_comm]; exact hsup
      obtain ⟨e₁, he₁⟩ := exists_iso_of_proj hinf hsup h₁ h₂ hI₁ hW hWI.1 h2
      obtain ⟨e₂, he₂⟩ := exists_iso_of_proj hinf' hsup' h₂ h₁ hI₂ hW hWI.1 h1
      apply hniso
      refine ⟨e₁.symm.trans e₂, fun l hl v hv => ?_⟩
      set w := e₁.symm v with hw
      have hlw : l w ∈ W := hW l hl w w.2
      have h3 : e₁.symm ⟨l v, hv⟩ = ⟨l w, hlw⟩ := by
        apply e₁.injective
        rw [MulEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [he₁]
        change (l v : V) = proj hinf hsup (l (w : V))
        rw [proj_equivariant hinf hsup h₁ h₂ hl, ← he₁, hw, MulEquiv.apply_symm_apply]
      simp only [MulEquiv.trans_apply, h3]
      rw [he₂, he₂]
      exact proj_equivariant hinf' hsup' h₂ h₁ hl _
    · right
      have hWV : W ≤ V₂ := by
        calc W = W ⊓ V₂ := h2.symm
          _ ≤ V₂ := inf_le_right
      rcases hI₂.2 W hWV hW with h | h
      · exact absurd h hWI.1
      · exact h
  · left
    have hWV : W ≤ V₁ := by
      calc W = W ⊓ V₁ := h1.symm
        _ ≤ V₁ := inf_le_right
    rcases hI₁.2 W hWV hW with h | h
    · exact absurd h hWI.1
    · exact h

theorem isInv_map {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut V))) {W : Subgroup V} (hW : IsInv L W) :
    IsInv L (W.map g.toMonoidHom) := by
  rintro l hl _ ⟨w, hw, rfl⟩
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
    simpa using this
  refine ⟨(g⁻¹ * l * g) w, hW _ hl' w hw, ?_⟩
  simp [MulAut.mul_apply]

theorem isIrr_map {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut V))) {W : Subgroup V} (hW : IsIrr L W) :
    IsIrr L (W.map g.toMonoidHom) := by
  refine ⟨?_, fun U hU hUi => ?_⟩
  · intro h
    apply hW.1
    rw [eq_bot_iff]
    intro w hw
    have : g w ∈ W.map g.toMonoidHom := ⟨w, hw, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    simpa using this
  · have hginv : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := Subgroup.inv_mem _ hg
    have h1 : U.map g⁻¹.toMonoidHom ≤ W := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨w, hw, hwu⟩ := hU hu
      rw [← hwu]
      simpa [MulAut.mul_apply] using hw
    rcases hW.2 _ h1 (isInv_map hginv hUi) with h2 | h2
    · left
      rw [eq_bot_iff]
      intro u hu
      have : g⁻¹ u ∈ U.map g⁻¹.toMonoidHom := ⟨u, hu, rfl⟩
      rw [h2, Subgroup.mem_bot] at this
      simpa using this
    · right
      apply le_antisymm hU
      rintro _ ⟨w, hw, rfl⟩
      rw [← h2] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      simpa [MulAut.mul_apply] using hu

theorem map_eq_or_map_eq {L : Subgroup (MulAut V)} {V₁ V₂ : Subgroup V} (hinf : V₁ ⊓ V₂ = ⊥)
    (hsup : V₁ ⊔ V₂ = ⊤) (h₁ : IsInv L V₁) (h₂ : IsInv L V₂) (hI₁ : IsIrr L V₁)
    (hI₂ : IsIrr L V₂) (hniso : ¬ IsoMod L V₁ V₂) {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    V₁.map g.toMonoidHom = V₁ ∨ V₁.map g.toMonoidHom = V₂ :=
  eq_or_eq_of_isIrr hinf hsup h₁ h₂ hI₁ hI₂ hniso (isInv_map hg h₁) (isIrr_map hg hI₁)

end Pair

end H

end CFSG.Quasithin
