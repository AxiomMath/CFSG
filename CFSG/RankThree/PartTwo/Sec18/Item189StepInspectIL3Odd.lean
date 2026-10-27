module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL3OddInvol

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.PGLModel (projSL)
open scoped MatrixGroups

theorem cube_root_eq_one189 {F : Type} [Field F] [Finite F] (hq : Nat.card F % 3 = 2)
    (a : Fˣ) (ha : a ^ 3 = 1) : a = 1 := by
  have h1 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf a ∣ Nat.card F - 1 := Nat.card_units F ▸ orderOf_dvd_natCard a
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h2
    omega

theorem nonempty_sl3_equiv_projSL189 {F : Type} [Field F] (h3 : ∀ a : Fˣ, a ^ 3 = 1 → a = 1) :
    Nonempty (SL(3, F) ≃* projSL 3 F) := by
  have hrange : projSL 3 F = (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) F →* _).range := by
    rw [projSL, CFSG.PGLModel.projImage, Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) F →* _) := by
    rw [← MonoidHom.ker_eq_bot_iff, Matrix.SpecialLinearGroup.toPGL_ker, eq_bot_iff]
    intro g hg
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
    have hr3 : r ^ 3 = 1 := by simpa using hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr3
    have hr1 : r = 1 := by
      simpa using congrArg Units.val (h3 (Units.mk0 r hr0) (Units.ext (by simpa using hr3)))
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrg, hr1, map_one]
    rfl
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)⟩

theorem eq_one_of_mem_normalizer_projSL3Odd189 {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 3 = 2)
    (e : Y ≃* projSL 3 (GaloisField p f)) (S : Sylow 2 Y) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y)) (hy3 : y ^ 3 = 1) : y = 1 := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hF : Odd (Nat.card (GaloisField p f)) :=
    hcard ▸ ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have h3 : ∀ a : (GaloisField p f)ˣ, a ^ 3 = 1 → a = 1 := cube_root_eq_one189 (hcard ▸ hq)
  obtain ⟨ε⟩ := nonempty_sl3_equiv_projSL189 h3
  let ι : Y ≃* SL(3, GaloisField p f) := e.trans ε.symm
  let S' : Sylow 2 SL(3, GaloisField p f) := S.mapSurjective (f := ι.toMonoidHom) ι.surjective
  have hy' : ι y ∈ Subgroup.normalizer ((S' : Subgroup SL(3, GaloisField p f)) :
      Set SL(3, GaloisField p f)) := by
    change ι.toMonoidHom y ∈ Subgroup.normalizer
      (((S : Subgroup Y).map ι.toMonoidHom : Subgroup SL(3, GaloisField p f)) :
        Set SL(3, GaloisField p f))
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hy
  have h1 := eq_one_of_mem_normalizer_sl3_189 hF h3 S' hy' (by rw [← map_pow, hy3, map_one])
  exact ι.injective (h1.trans (map_one ι).symm)

theorem inspect189L3Odd : Inspect189L3Odd := by
  intro Y _ _ X Q x p f _ hD hp hf hq ⟨e⟩
  exfalso
  obtain ⟨S, hS⟩ := hD.sylow.inf_of_le_normalizer (N := X) le_top
    (Subgroup.normalizer_eq_top_iff.2 hD.normal).ge
  have hmem : ∀ y : X, y ∈ (S : Subgroup X) ↔ (y : Y) ∈ Q := fun y => by
    have h1 := Subgroup.mem_map_iff_mem X.subtype_injective (K := (S : Subgroup X)) (x := y)
    rw [hS, Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.2 h).1, fun h => h1.1 ⟨h, y.2⟩⟩
  have hxS : (⟨x, hD.mem⟩ : X) ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    exact Subgroup.mem_normalizer_iff.1 hD.mem_normalizer y
  have hx : orderOf (⟨x, hD.mem⟩ : X) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hD.orderOf_eq
  have h1 := eq_one_of_mem_normalizer_projSL3Odd189 hp hf hq e S hxS
    (by rw [← hx]; exact pow_orderOf_eq_one _)
  rw [h1, orderOf_one] at hx
  exact absurd hx (by norm_num)

end CFSG.RankThree.PartTwo.Sec18
