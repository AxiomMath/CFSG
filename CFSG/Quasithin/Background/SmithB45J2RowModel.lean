module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.SmithB45J2Out
public import CFSG.Quasithin.Background.SmithB45J2Inner

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Quasithin.H
open scoped Matrix

section Ratio

variable {V : Type} [CommGroup V] [Finite V]

theorem two_le_rAV_iff (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    (2 : ℚ) ≤ rAV A ↔ Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ Nat.card V :=
  CFSG.Quasithin.RAV.two_le_rAV_iff hV hA

theorem two_lt_rAV_iff (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    (2 : ℚ) < rAV A ↔ Nat.card A ^ 2 * Nat.card ↥(fixV A) < Nat.card V :=
  CFSG.Quasithin.RAV.two_lt_rAV_iff hV hA

end Ratio

theorem eq_refl_of_apply_ω {σ : FieldFour ≃+* FieldFour} (h : σ ω = ω) :
    σ = RingEquiv.refl FieldFour := by
  refine RingEquiv.ext fun c => ?_
  have hc : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω₂ := by revert c; decide
  rcases hc with rfl | rfl | rfl | rfl
  · exact map_zero σ
  · exact map_one σ
  · exact h
  · rw [show ω₂ = 1 + ω by decide, map_add, map_one, h]
    rfl

theorem card_sq_le_of_semilinear {U : Submodule FieldFour V6} {t : MulAut W6}
    {σ : FieldFour ≃+* FieldFour} (ht : IsSemilinear t σ) (hσ : σ ω ≠ ω) :
    Nat.card {v : V6 // v ∈ U ∧ toAddMap t v = v} ^ 2 ≤ Nat.card ↥U := by
  set F := {v : V6 // v ∈ U ∧ toAddMap t v = v}
  let f : F × F → ↥U := fun p => ⟨p.1.1 + ω • p.2.1, U.add_mem p.1.2.1 (U.smul_mem ω p.2.2.1)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hxU, hx⟩, ⟨y, hyU, hy⟩⟩ ⟨⟨x', hx'U, hx'⟩, ⟨y', hy'U, hy'⟩⟩ h
    have h1 : x + ω • y = x' + ω • y' := congrArg Subtype.val h
    have h2 : x - x' = ω • (y' - y) := by
      rw [smul_sub]
      linear_combination h1
    have h3 : toAddMap t (x - x') = x - x' := by
      have e : x - x' = x + (-1 : FieldFour) • x' := by rw [neg_one_smul, sub_eq_add_neg]
      rw [e, toAddMap_add, ht, map_neg, map_one, hx, hx']
    have h4 : toAddMap t (ω • (y' - y)) = σ ω • (y' - y) := by
      have e : y' - y = y' + (-1 : FieldFour) • y := by rw [neg_one_smul, sub_eq_add_neg]
      rw [ht, e, toAddMap_add, ht, map_neg, map_one, hy, hy']
    rw [h2, h4] at h3
    have h5 : (σ ω - ω) • (y' - y) = 0 := by rw [sub_smul, h3, sub_self]
    have hyy : y' - y = 0 := (smul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr hσ)
    have hxx : x - x' = 0 := by rw [h2, hyy, smul_zero]
    have e1 : y = y' := (sub_eq_zero.mp hyy).symm
    have e2 : x = x' := sub_eq_zero.mp hxx
    subst e1 e2
    rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← sq] at this

theorem toAdd_mem_mFix {A : Subgroup (MulAut W6)} {v : W6} (hv : v ∈ fixV A) :
    Multiplicative.toAdd v ∈ mFix (A.comap matHom) := by
  intro b hb
  have h := hv _ hb
  have h1 := congrArg Multiplicative.toAdd h
  rw [matHom_apply] at h1
  exact h1

theorem card_fixV_le_mFix (A : Subgroup (MulAut W6)) :
    Nat.card ↥(fixV A) ≤ Nat.card ↥(mFix (A.comap matHom)) :=
  Nat.card_le_card_of_injective (fun v : ↥(fixV A) => (⟨_, toAdd_mem_mFix v.2⟩ :
    ↥(mFix (A.comap matHom)))) fun v w h => by
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      exact Multiplicative.toAdd.injective h1

theorem card_comap_matHom {A : Subgroup (MulAut W6)} (hA : A ≤ L6) :
    Nat.card ↥(A.comap matHom) = Nat.card A := by
  refine Nat.card_congr (Equiv.ofBijective (fun b : ↥(A.comap matHom) => (⟨matHom b.1, b.2⟩ : ↥A))
    ⟨fun b c h => Subtype.ext (matHom_injective (congrArg Subtype.val h)), fun a => ?_⟩)
  obtain ⟨γ, hγ⟩ := hA a.2
  have e : matHom (γ : GL6) = a := hγ
  exact ⟨⟨γ, by rw [Subgroup.mem_comap, e]; exact a.2⟩, Subtype.ext e⟩

theorem comap_matHom_le {A : Subgroup (MulAut W6)} (hA : A ≤ L6) : A.comap matHom ≤ Γ₆ := by
  intro b hb
  obtain ⟨γ, hγ⟩ := hA hb
  have : (γ : GL6) = b := matHom_injective (by rw [← hγ]; rfl)
  rw [← this]
  exact γ.2

theorem toAdd_matHom (g : GL6) (z : W6) :
    Multiplicative.toAdd (matHom g z) = (g : M6) *ᵥ Multiplicative.toAdd z := rfl

theorem eq_zero_of_mulVec {M : M6} (h : ∀ v : V6, M *ᵥ v = 0) : M = 0 := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem quad_of_commSeries {A : Subgroup (MulAut W6)} (hq : commSeries A 2 = ⊥) :
    ∀ x ∈ A.comap matHom, ∀ y ∈ A.comap matHom, ((y : M6) - 1) * ((x : M6) - 1) = 0 := by
  rw [← isQuadratic_iff_commSeries_two] at hq
  intro x hx y hy
  refine eq_zero_of_mulVec fun v => ?_
  have hmem : matHom x (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ ∈ commV A :=
    Subgroup.subset_closure ⟨_, hx, _, rfl⟩
  have h1 := congrArg Multiplicative.toAdd (hq hmem _ hy)
  rw [toAdd_matHom, toAdd_mul, toAdd_inv, toAdd_matHom, toAdd_ofAdd] at h1
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_add_neg ((x : M6) *ᵥ v), h1, sub_self]

theorem card_W6 : Nat.card W6 = 4096 := by
  rw [Nat.card_congr Multiplicative.toAdd, card_V6]

theorem le_of_sq_le {s m b : ℕ} (h : s ^ 2 ≤ m) (hm : m ≤ b ^ 2) : s ≤ b := by
  by_contra hlt
  push Not at hlt
  have := Nat.pow_lt_pow_left hlt (two_ne_zero)
  omega

section Row

variable (hcard : Nat.card Γ₆ = 604800) (hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6)
  (hZ : Subgroup.center ↥L6 = ⊥) {X : Subgroup (MulAut W6)} (hXN : X ≤ natNorm Γ₆)
  (hrank : ∀ A : Subgroup (MulAut W6), A ≤ X → IsElemAbelian2 A → Nat.card A ≤ 16)

include hcard hAut hZ hXN hrank in
theorem card_bound {A : Subgroup (MulAut W6)} (hA : IsA2 X A) :
    Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4096 ∧
      (commSeries A 2 = ⊥ → Nat.card A ^ 2 * Nat.card ↥(fixV A) < 4096) := by
  have hAX := hA.le
  have hAN : A ≤ natNorm Γ₆ := hAX.trans hXN
  have hel := hA.isElemAbelian2
  have hA16 := hrank A hAX hel
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hel.2 x hx
  have hA2 : 2 ≤ Nat.card A := by
    have := (Subgroup.one_lt_card_iff_ne_bot A).mpr hA.ne_bot
    omega
  set A₀ := A ⊓ L6 with hA₀
  have hlin : A ⊓ linSub ≤ A₀ := by
    rintro t ⟨htA, htl⟩
    exact ⟨htA, mem_natImage_of_linear hAut hZ (hAN htA) htl (hsq t htA)⟩
  have hcard2 : Nat.card A ≤ 2 * Nat.card A₀ := by
    have h1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ linSub) :=
      card_le_two_mul_card_inf_linSub hasScalarCommutant_Γ₆ (n := 2) (by norm_num)
        (by rw [FieldFour.natCard_eq]; norm_num) hAN fun x hx => hel.2 x hx
    exact h1.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hlin))
  set B₀ := A₀.comap matHom with hB₀
  have hA₀L : A₀ ≤ L6 := inf_le_right
  have hB₀Γ : B₀ ≤ Γ₆ := comap_matHom_le hA₀L
  have hB₀c : Nat.card B₀ = Nat.card A₀ := card_comap_matHom hA₀L
  have hB₀comm : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
    matHom_injective (by rw [map_mul, map_mul]; exact hel.1 _ hx.1 _ hy.1)
  have hB₀sq : ∀ x ∈ B₀, x * x = 1 := fun x hx =>
    matHom_injective (by rw [map_mul, map_one]; exact hsq _ hx.1)
  obtain ⟨b2, b3, b5⟩ := inner_bounds hcard hB₀Γ hB₀comm hB₀sq
  by_cases hAL : A ≤ L6
  · have hAA₀ : A₀ = A := inf_eq_left.mpr hAL
    have hC : Nat.card ↥(fixV A) ≤ Nat.card ↥(mFix B₀) := by
      rw [hB₀, hAA₀]
      exact card_fixV_le_mFix A
    rw [hAA₀] at hB₀c
    by_cases h5 : 5 ≤ Nat.card A
    · obtain ⟨h16, x, hx, y, hy, hxy⟩ := b5 (by rw [hB₀c]; exact h5)
      have hx' : x ∈ A.comap matHom := by rw [← hAA₀]; exact hx
      have hy' : y ∈ A.comap matHom := by rw [← hAA₀]; exact hy
      refine ⟨?_, fun hq => absurd (quad_of_commSeries hq x hx' y hy') hxy⟩
      calc Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 16 ^ 2 * 16 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hA16 2) (hC.trans h16)
        _ = 4096 := by norm_num
    · by_cases h3 : 3 ≤ Nat.card A
      · have h64 := hC.trans (b3 (by rw [hB₀c]; exact h3))
        have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4 ^ 2 * 64 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) h64
        exact ⟨by omega, fun _ => by omega⟩
      · have h256 := hC.trans (b2 (by rw [hB₀c]; exact hA2))
        have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 2 ^ 2 * 256 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) h256
        exact ⟨by omega, fun _ => by omega⟩
  · obtain ⟨t, htA, htL⟩ : ∃ t ∈ A, t ∉ L6 := by
      by_contra h
      push Not at h
      exact hAL h
    obtain ⟨σ, hσ⟩ := exists_semilinear hasScalarCommutant_Γ₆ (hAN htA)
    have hσω : σ ω ≠ ω := by
      intro h
      have e := eq_refl_of_apply_ω h
      subst e
      exact htL (mem_natImage_of_linear hAut hZ (hAN htA) hσ (hsq t htA))
    have hC : Nat.card ↥(fixV A) ≤ Nat.card {v : V6 // v ∈ mFix B₀ ∧ toAddMap t v = v} := by
      refine Nat.card_le_card_of_injective (fun v => ⟨Multiplicative.toAdd (v : W6),
        toAdd_mem_mFix (fun x hx => v.2 x hx.1),
        congrArg Multiplicative.toAdd (v.2 t htA)⟩) fun v w h => ?_
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      exact Multiplicative.toAdd.injective h1
    have hhalf := card_sq_le_of_semilinear (U := mFix B₀) hσ hσω
    set s := Nat.card {v : V6 // v ∈ mFix B₀ ∧ toAddMap t v = v} with hs
    have hn1 : 1 ≤ Nat.card A₀ := Nat.card_pos
    suffices h : Nat.card A ^ 2 * Nat.card ↥(fixV A) < 4096 from ⟨h.le, fun _ => h⟩
    by_cases h5 : 5 ≤ Nat.card A₀
    · have hs4 : s ≤ 4 := le_of_sq_le hhalf ((b5 (by rw [hB₀c]; exact h5)).1.trans (by norm_num))
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 16 ^ 2 * 4 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hA16 2) (hC.trans hs4)
      omega
    by_cases h3 : 3 ≤ Nat.card A₀
    · have hs8 : s ≤ 8 := le_of_sq_le hhalf ((b3 (by rw [hB₀c]; exact h3)).trans (by norm_num))
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 8 ^ 2 * 8 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (hC.trans hs8)
      omega
    by_cases h2 : 2 ≤ Nat.card A₀
    · have hs16 : s ≤ 16 := le_of_sq_le hhalf ((b2 (by rw [hB₀c]; exact h2)).trans (by norm_num))
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4 ^ 2 * 16 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (hC.trans hs16)
      omega
    · have hm : Nat.card ↥(mFix B₀) ≤ 64 ^ 2 :=
        (card_mono le_top).trans (by rw [card_top]; norm_num)
      have hs64 : s ≤ 64 := le_of_sq_le hhalf hm
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 2 ^ 2 * 64 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (hC.trans hs64)
      omega

end Row

end CFSG.Quasithin.J2Row
