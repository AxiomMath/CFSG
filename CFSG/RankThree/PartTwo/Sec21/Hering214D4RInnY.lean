module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RLine
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSL2
public import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec11

section InnY


variable {n : ℕ} {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem not_three_dvd_two_pow (n : ℕ) : ¬ 3 ∣ 2 ^ n := fun h3 => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem exists_four_shortSL2 (P : D4Par n F σ) (hev : Even n) {g : C0 σ} (hg : g ∈ Asub σ)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ W : Subgroup (C0 σ), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ W ≤ Asub σ ∧
      (∀ w ∈ W, g * w * g⁻¹ ∈ W) ∧ ∃ w ∈ W, g * w * g⁻¹ ≠ w := by
  have hσ3 := P.sigma_pow_three
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
  have hfin : Finite (CFSG.LieType.Chevalley.orbitField TwistTag.D4 F σ.toRingHom
      KS11Lie4Proof.d4Outer) := Subtype.finite
  have h3 : 3 ∣ Nat.card (CFSG.LieType.Chevalley.orbitField TwistTag.D4 F σ.toRingHom
      KS11Lie4Proof.d4Outer) - 1 := by
    rw [KS11Lie4Proof.natCard_orbitField_d4Outer hσ3, P.card]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 3 - 1 ^ 3 := Nat.sub_dvd_pow_sub_pow _ _ _
    rw [one_pow] at h1
    exact (three_dvd_two_pow_sub_one hev).trans h1
  haveI := P.charP
  haveI : CharP (CFSG.LieType.Chevalley.orbitField TwistTag.D4 F σ.toRingHom
      KS11Lie4Proof.d4Outer) 2 :=
    RingHom.charP (Subfield.subtype _) Subtype.val_injective 2
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  set s := e.symm ⟨g, hg⟩ with hs
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← map_pow]
    have : (⟨g, hg⟩ : ↥(Asub σ)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  have hs1 : s ≠ 1 := by
    intro h
    apply hg1
    have := congrArg e h
    rw [hs, MulEquiv.apply_symm_apply, map_one] at this
    exact congrArg Subtype.val this
  obtain ⟨W₀, hW₀, hW₀4, hW₀inv, w₀, hw₀, hmove⟩ := exists_four_sl2 hω hω1 s hs3 hs1
  refine ⟨(W₀.map e.toMonoidHom).map (Asub σ).subtype,
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map hW₀ _) _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Asub σ).subtype_injective,
      Subgroup.card_map_of_injective e.injective, hW₀4]
  · rintro _ ⟨_, _, rfl⟩
    exact Subtype.coe_prop _
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨e (s * w * s⁻¹), ⟨s * w * s⁻¹, hW₀inv w hw, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, map_mul, map_inv, hs,
      MulEquiv.apply_symm_apply]
  · refine ⟨((e w₀ : ↥(Asub σ)) : C0 σ), ⟨_, ⟨w₀, hw₀, rfl⟩, rfl⟩, fun hcon => hmove ?_⟩
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, hs, MulEquiv.apply_symm_apply]
    exact hcon

theorem inner_classY_four_aux (P : D4Par n F σ) (hev : Even n) {g₁ g₂ x : C0 σ}
    (hg₁ : g₁ ∈ Bsub σ) (hg₁3 : g₁ ^ 3 = 1) (hg₁1 : g₁ ≠ 1) (hg₂3 : g₂ ^ 3 = 1)
    (hg₂1 : g₂ ≠ 1) (h₁₂ : g₂ * g₁ = g₁ * g₂) (hx₁ : x * g₁ = g₁ * x)
    (hx₂ : x * g₂ * x⁻¹ = g₂⁻¹) : FourFixedMoved (MulAut.conj g₁) (MulAut.conj g₂) := by
  have hq3 := not_three_dvd_two_pow n
  have hBC := (KS11Lie6Proof.d4ThreeBCent_holds F (2 ^ n) σ P.card P.frob hq3 g₁ hg₁ hg₁3
    hg₁1).1
  have hxC : x ∈ Subgroup.centralizer ({g₁} : Set (C0 σ)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hx₁
  have hg₂C : g₂ ∈ Subgroup.centralizer ({g₁} : Set (C0 σ)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h₁₂
  have hcomm := hBC x hxC g₂ hg₂C
  rw [hx₂] at hcomm
  have hg₂A : g₂ ∈ Asub σ := by
    have h2 : g₂ * g₂ * g₂ = 1 := by rw [← pow_three']; exact hg₂3
    have : g₂⁻¹ * g₂⁻¹ = g₂ := by
      calc g₂⁻¹ * g₂⁻¹ = (g₂ * g₂ * g₂)⁻¹ * g₂ := by group
        _ = g₂ := by rw [h2]; group
    rw [← this]
    exact hcomm
  obtain ⟨W, hW, hW4, hWA, hWn, w₀, hw₀, hmove⟩ := exists_four_shortSL2 P hev hg₂A hg₂3 hg₂1
  refine ⟨W, hW, hW4, fun w hw => ?_, fun w hw => ?_, w₀, hw₀, ?_⟩
  · rw [MulAut.conj_apply]
    have hc := Subgroup.mem_centralizer_iff.mp hg₁ w (hWA hw)
    exact mul_inv_eq_iff_eq_mul.mpr hc.symm
  · rw [MulAut.conj_apply]
    exact hWn w hw
  · rw [MulAut.conj_apply]
    exact hmove

theorem inner_classY_four (P : D4Par n F σ) (hev : Even n) {g₁ g₂ x h : C0 σ}
    (hg₁ : h * g₁ * h⁻¹ ∈ Bsub σ) (hg₁3 : g₁ ^ 3 = 1) (hg₁1 : g₁ ≠ 1) (hg₂3 : g₂ ^ 3 = 1)
    (hg₂1 : g₂ ≠ 1) (h₁₂ : g₂ * g₁ = g₁ * g₂) (hx₁ : x * g₁ = g₁ * x)
    (hx₂ : x * g₂ * x⁻¹ = g₂⁻¹) : FourFixedMoved (MulAut.conj g₁) (MulAut.conj g₂) := by
  refine FourFixedMoved.of_autConj (MulAut.conj h) ?_
  have hφc : ∀ g : C0 σ, MulAut.conj h * MulAut.conj g * (MulAut.conj h)⁻¹ =
      MulAut.conj (MulAut.conj h g) := fun g => by
    rw [← map_inv, ← map_mul, ← map_mul, MulAut.conj_apply, mul_assoc]
  rw [hφc, hφc]
  have hinj := (MulAut.conj h).injective
  refine inner_classY_four_aux P hev (x := MulAut.conj h x) hg₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hg₁3, map_one]
  · intro hc
    exact hg₁1 (hinj (hc.trans (map_one _).symm))
  · rw [← map_pow, hg₂3, map_one]
  · intro hc
    exact hg₂1 (hinj (hc.trans (map_one _).symm))
  · rw [← map_mul, ← map_mul, h₁₂]
  · rw [← map_mul, ← map_mul, hx₁]
  · rw [← map_mul, ← map_inv, ← map_mul, hx₂, map_inv]

end InnY

end CFSG.RankThree.PartTwo.Sec21.Hering214
