module

public import CFSG.Quasithin.Recognition.M12AscL1
public import Certificates.Certificate17036


public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

@[expose] def ax6 : Perm (Fin 6) := TA 4 * TA 3
@[expose] def ax16 : Perm (Fin 6) := TA 1 * TA 0

@[expose] def E6l : List (Perm (Fin 6)) :=
  [1, ax6, ax6 * ax6, ax16, ax16 * ax6, ax16 * (ax6 * ax6), ax16 * ax16, ax16 * ax16 * ax6,
    ax16 * ax16 * (ax6 * ax6)]

@[expose] def NormDb (σ : Perm (Fin 6)) : Bool :=
  D6l.all fun d => D6l.any fun d' => σ * d == d' * σ

@[expose] def NormEb (σ : Perm (Fin 6)) : Bool :=
  E6l.all fun e => D6l.any fun d' => σ * e == d' * σ

theorem D6l_nodup : D6l.Nodup :=
  Certificates.certificate17036.1
theorem D6l_mul : ∀ d ∈ D6l, ∀ d' ∈ D6l, d * d' ∈ D6l :=
  Certificates.certificate17036.2.1
theorem D6l_inv : ∀ d ∈ D6l, d⁻¹ ∈ D6l :=
  Certificates.certificate17036.2.2

@[expose] def D6 : Subgroup (Perm (Fin 6)) where
  carrier := {d | d ∈ D6l}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb => D6l_mul a ha b hb
  inv_mem' := fun {a} ha => D6l_inv a ha

theorem mem_D6 {d : Perm (Fin 6)} : d ∈ D6 ↔ d ∈ D6l := Iff.rfl

theorem alpha_D6l : D6l.map outerAlpha = E6l := by
  have h1 : outerAlpha x6 = ax6 := by
    unfold x6 ax6
    rw [map_mul]
    exact congrArg₂ (· * ·) (outerAlpha_gen 4) (outerAlpha_gen 3)
  have h2 : outerAlpha x16 = ax16 := by
    unfold x16 ax16
    rw [map_mul]
    exact congrArg₂ (· * ·) (outerAlpha_gen 1) (outerAlpha_gen 0)
  simp [D6l, E6l, map_mul, map_one, h1, h2]

theorem NormDb_iff (σ : Perm (Fin 6)) :
    NormDb σ = true ↔ ∀ d ∈ D6, σ * d * σ⁻¹ ∈ D6 := by
  simp only [NormDb, List.all_eq_true, List.any_eq_true, beq_iff_eq, mem_D6]
  refine forall₂_congr fun d _ => ?_
  constructor
  · rintro ⟨d', hd', h⟩
    have : σ * d * σ⁻¹ = d' := by rw [h]; group
    rw [this]
    exact hd'
  · intro h
    exact ⟨σ * d * σ⁻¹, h, by group⟩

theorem NormEb_iff
    (σ : Perm (Fin 6)) :
    NormEb σ = true ↔ ∀ d ∈ D6, σ * outerAlpha d * σ⁻¹ ∈ D6 := by
  have hE : ∀ e, e ∈ E6l ↔ ∃ d ∈ D6l, outerAlpha d = e := by
    intro e
    rw [← alpha_D6l, List.mem_map]
  simp only [NormEb, List.all_eq_true, List.any_eq_true, beq_iff_eq, mem_D6]
  constructor
  · intro h d hd
    obtain ⟨d', hd', hh⟩ := h (outerAlpha d) ((hE _).2 ⟨d, hd, rfl⟩)
    have : σ * outerAlpha d * σ⁻¹ = d' := by rw [hh]; group
    rw [this]
    exact hd'
  · intro h e he
    obtain ⟨d, hd, rfl⟩ := (hE e).1 he
    exact ⟨σ * outerAlpha d * σ⁻¹, h d hd, by group⟩

end CFSG.Quasithin
