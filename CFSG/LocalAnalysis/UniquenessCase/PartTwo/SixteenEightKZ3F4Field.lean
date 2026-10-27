module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

noncomputable section

abbrev S16kF4 : Type := GaloisField 2 2

def s16kEmb : ZMod 2 →+* S16kF4 := ZMod.castHom (dvd_refl 2) S16kF4

private theorem s16k_card_f4 : Nat.card S16kF4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem s16k_f4_exists_alpha : ∃ α : S16kF4, α ^ 2 + α + 1 = 0 := by
  have hcardU : Nat.card S16kF4ˣ = 3 := by
    rw [Nat.card_units, s16k_card_f4]
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := S16kF4ˣ)
  have horder : orderOf ζ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, hcardU]
  have hζ3 : (ζ : S16kF4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← horder, pow_orderOf_eq_one, Units.val_one]
  have hζne : (ζ : S16kF4) ≠ 1 := by
    intro h
    have h1 : ζ = 1 := Units.ext h
    rw [h1, orderOf_one] at horder
    norm_num at horder
  refine ⟨(ζ : S16kF4), ?_⟩
  have hfac : ((ζ : S16kF4) - 1) * ((ζ : S16kF4) ^ 2 + (ζ : S16kF4) + 1) = 0 := by
    have h3 : (ζ : S16kF4) ^ 3 - 1 = 0 := by rw [hζ3]; ring
    have : ((ζ : S16kF4) - 1) * ((ζ : S16kF4) ^ 2 + (ζ : S16kF4) + 1) =
        (ζ : S16kF4) ^ 3 - 1 := by ring
    rw [this, h3]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h (sub_ne_zero.mpr hζne)
  · exact h

def s16kAlpha : S16kF4 := s16k_f4_exists_alpha.choose

theorem s16kAlpha_spec : s16kAlpha ^ 2 + s16kAlpha + 1 = 0 :=
  s16k_f4_exists_alpha.choose_spec

private theorem s16k_one_add_one : (1 : S16kF4) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharP.cast_eq_zero S16kF4 2

private theorem s16kAlpha_ne_zero : s16kAlpha ≠ 0 := by
  intro h
  have hspec := s16kAlpha_spec
  rw [h] at hspec
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add] at hspec
  exact one_ne_zero hspec

private theorem s16kAlpha_ne_one : s16kAlpha ≠ 1 := by
  intro h
  have hspec := s16kAlpha_spec
  rw [h] at hspec
  have hsq : (1 : S16kF4) ^ 2 + 1 + 1 = (1 + 1) + 1 := by ring
  rw [hsq, s16k_one_add_one, zero_add] at hspec
  exact one_ne_zero hspec

private theorem s16kAlpha_cube : s16kAlpha ^ 3 = 1 := by
  apply sub_eq_zero.mp
  have hfac : s16kAlpha ^ 3 - 1 =
      (s16kAlpha - 1) * (s16kAlpha ^ 2 + s16kAlpha + 1) := by ring
  rw [hfac, s16kAlpha_spec, mul_zero]

theorem s16kAlpha_primitive : IsPrimitiveRoot s16kAlpha 3 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_eq_prime s16kAlpha_cube s16kAlpha_ne_one

private theorem s16k_zmod_two_eq_zero_or_eq_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hle : x.val ≤ 1 := by
    rw [← Nat.lt_succ_iff]
    exact ZMod.val_lt x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
  · left; rw [← ZMod.natCast_zmod_val x, h]; norm_num
  · right; rw [← ZMod.natCast_zmod_val x, h]; norm_num

theorem s16kF4_coeff (x : S16kF4) :
    ∃ a b : ZMod 2, x = s16kEmb a + s16kAlpha * s16kEmb b := by
  have hemb_inj : Function.Injective s16kEmb :=
    ZMod.castHom_injective (n := 2) (R := S16kF4)
  have hcard : Nat.card (ZMod 2 × ZMod 2) = Nat.card S16kF4 := by
    rw [Nat.card_prod, Nat.card_zmod, s16k_card_f4]
  have hinj : Function.Injective
      (fun p : ZMod 2 × ZMod 2 => s16kEmb p.1 + s16kAlpha * s16kEmb p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq]
    have h1 : s16kEmb (a - a') = s16kAlpha * s16kEmb (b' - b) := by
      rw [map_sub, map_sub]
      linear_combination h
    rcases s16k_zmod_two_eq_zero_or_eq_one (b' - b) with hd | hd
    · rw [hd, map_zero, mul_zero] at h1
      have haa : a - a' = 0 := hemb_inj (by simpa using h1)
      exact ⟨sub_eq_zero.mp haa, (sub_eq_zero.mp hd).symm⟩
    · rw [hd, map_one, mul_one] at h1
      rcases s16k_zmod_two_eq_zero_or_eq_one (a - a') with hc | hc
      · rw [hc, map_zero] at h1
        exact absurd h1.symm s16kAlpha_ne_zero
      · rw [hc, map_one] at h1
        exact absurd h1.symm s16kAlpha_ne_one
  have hbij : Function.Bijective
      (fun p : ZMod 2 × ZMod 2 => s16kEmb p.1 + s16kAlpha * s16kEmb p.2) :=
    hinj.bijective_of_nat_card_le (le_of_eq hcard.symm)
  obtain ⟨p, hp⟩ := hbij.2 x
  exact ⟨p.1, p.2, hp.symm⟩

theorem s16kF4_cube (μ : S16kF4) (h : μ ^ 3 = 1) :
    μ = 1 ∨ μ = s16kAlpha ∨ μ = s16kAlpha ^ 2 := by
  have hα3 : s16kAlpha ^ 3 = 1 := s16kAlpha_cube
  have hprod : (μ - 1) * (μ - s16kAlpha) * (μ - s16kAlpha ^ 2) = 0 := by
    have hfac : (μ - 1) * (μ - s16kAlpha) * (μ - s16kAlpha ^ 2) =
        μ ^ 3 - (1 + s16kAlpha + s16kAlpha ^ 2) * μ ^ 2 +
          (s16kAlpha + s16kAlpha ^ 2 + s16kAlpha ^ 3) * μ - s16kAlpha ^ 3 := by ring
    rw [hfac]
    have h1 : 1 + s16kAlpha + s16kAlpha ^ 2 = 0 := by
      rw [show 1 + s16kAlpha + s16kAlpha ^ 2 = s16kAlpha ^ 2 + s16kAlpha + 1 by ring,
        s16kAlpha_spec]
    have h2 : s16kAlpha + s16kAlpha ^ 2 + s16kAlpha ^ 3 = 0 := by
      rw [show s16kAlpha + s16kAlpha ^ 2 + s16kAlpha ^ 3 =
          (s16kAlpha ^ 2 + s16kAlpha + 1) + (s16kAlpha ^ 3 - 1) by ring,
        s16kAlpha_spec, hα3]
      ring
    rw [h1, h2, hα3, h]
    ring
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h1))

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
