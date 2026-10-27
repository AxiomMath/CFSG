module

public import CFSG.Quasithin.Background.BlueprintB2Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Quasithin.BlueprintB2

variable {Y : Type*} [Group Y]

theorem A7_central_Sylow_seed_reduced_module [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (T : Sylow p Y) {P : Subgroup Y} [hPn : P.Normal] (hP : IsPGroup p P)
    (hCP : centralizer (P : Set Y) ≤ P) {Z : Subgroup Y} (hZ : Z ≤ centerTorsion p T) :
    (normalClosure (Z : Set Y)).Normal ∧
      CFSG.Open.IsElemAbelian p (normalClosure (Z : Set Y)) ∧
      normalClosure (Z : Set Y) ≤ centerTorsion p P ∧
      ∀ D : Subgroup Y, D.Normal → centralizer (normalClosure (Z : Set Y) : Set Y) ≤ D →
        (∀ d ∈ D, ∃ k : ℕ, d ^ p ^ k ∈ centralizer (normalClosure (Z : Set Y) : Set Y)) →
        D = centralizer (normalClosure (Z : Set Y) : Set Y) := by
  classical
  set U := normalClosure (Z : Set Y) with hUdef
  have hPT : P ≤ T := hP.le_sylow_of_normal T
  have hZP : Z ≤ centerTorsion p P := by
    intro z hz
    obtain ⟨hzT, hzc, hzp⟩ := mem_centerTorsion_iff.1 (hZ hz)
    have hzC : z ∈ centralizer (P : Set Y) :=
      mem_centralizer_iff.2 fun k hk => hzc k (hPT hk)
    exact mem_centerTorsion_iff.2 ⟨hCP hzC, fun k hk => hzc k (hPT hk), hzp⟩
  have hΩn : (centerTorsion p P).Normal := ⟨fun x hx y => by
    obtain ⟨hxP, hxc, hxp⟩ := mem_centerTorsion_iff.1 hx
    refine mem_centerTorsion_iff.2 ⟨hPn.conj_mem x hxP y, fun k hk => ?_, ?_⟩
    · have hk' : y⁻¹ * k * y ∈ P := by
        have := hPn.conj_mem k hk y⁻¹
        rwa [inv_inv] at this
      have h1 := hxc _ hk'
      calc k * (y * x * y⁻¹) = y * ((y⁻¹ * k * y) * x) * y⁻¹ := by group
        _ = y * (x * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
        _ = y * x * y⁻¹ * k := by group
    · rw [conj_pow, hxp, mul_one, mul_inv_cancel]⟩
  have hUΩ : U ≤ centerTorsion p P := normalClosure_le_normal hZP
  have hUn : U.Normal := normalClosure_normal
  have hUel : CFSG.Open.IsElemAbelian p U := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => (mem_centerTorsion_iff.1 (hUΩ hx)).2.2⟩
    obtain ⟨hxP, -, -⟩ := mem_centerTorsion_iff.1 (hUΩ x.2)
    obtain ⟨-, hyc, -⟩ := mem_centerTorsion_iff.1 (hUΩ y.2)
    exact hyc x hxP
  refine ⟨hUn, hUel, hUΩ, fun D hDn hCD hDp => ?_⟩
  have hCn : (centralizer (U : Set Y)).Normal := inferInstance
  set C := centralizer (U : Set Y) with hCdef
  have hZC : ∀ c ∈ C, ∀ z ∈ Z, c * z = z * c := fun c hc z hz =>
    (mem_centralizer_iff.1 hc z (subset_normalClosure hz)).symm
  have hZT : ∀ t ∈ (T : Subgroup Y), ∀ z ∈ Z, t * z = z * t := fun t ht z hz =>
    (mem_centerTorsion_iff.1 (hZ hz)).2.1 t ht
  have hDTC : ∀ d ∈ D, ∃ t ∈ (T : Subgroup Y), t⁻¹ * d ∈ C := by
    intro d hd
    let f := QuotientGroup.mk' C
    have hf : Function.Surjective f := QuotientGroup.mk'_surjective C
    have hDbar : (D.map f).Normal := Subgroup.Normal.map hDn f hf
    have hDp' : IsPGroup p (D.map f) := by
      rintro ⟨_, x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hDp x hx
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, MonoidHom.mem_ker.1 (by rwa [QuotientGroup.ker_mk'])]
    have hle := hDp'.le_sylow_of_normal (T.mapSurjective hf)
    obtain ⟨t, ht, htd⟩ := hle ⟨d, hd, rfl⟩
    refine ⟨t, ht, ?_⟩
    have : f t = f d := htd
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
  have hDZ : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d := by
    intro d hd z hz
    obtain ⟨t, ht, htC⟩ := hDTC d hd
    have h1 := hZC _ htC z hz
    have h2 := hZT t ht z hz
    calc d * z = t * (t⁻¹ * d) * z := by group
      _ = t * (z * (t⁻¹ * d)) := by rw [mul_assoc, h1]
      _ = (t * z) * (t⁻¹ * d) := by group
      _ = z * t * (t⁻¹ * d) := by rw [h2]
      _ = z * d := by group
  have hZD : Z ≤ centralizer (D : Set Y) := fun z hz =>
    mem_centralizer_iff.2 fun x hx => hDZ x hx z hz
  have hUD : U ≤ centralizer (D : Set Y) := normalClosure_le_normal hZD
  refine le_antisymm (fun d hd => ?_) hCD
  rw [mem_centralizer_iff]
  intro u hu
  exact (mem_centralizer_iff.1 (hUD hu) d hd).symm

end CFSG.Quasithin.H13.A7
