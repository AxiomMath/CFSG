module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaCore

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Eichler

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_left_add {u u' w : V} (hu : Q u = 0) (hu' : Q u' = 0) (hw : Q w = 0)
    (huu' : polar Q u u' = 0) (huw : polar Q u w = 0) (hu'w : polar Q u' w = 0) :
    eichler Q (u + u') w = eichler Q u w * eichler Q u' w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsum : Q (u + u') = 0 := by
    rw [QuadraticMap.map_add Q u u', hu, hu', huu', add_zero, add_zero]
  have hsumw : polar Q (u + u') w = 0 := by rw [polar_add_left, huw, hu'w, add_zero]
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have hu'u : polar Q u' u = 0 := by rw [polar_comm, huu']
  have hww : polar Q w w = 0 := polar_self_eq_zero hw
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, eichler_ts_apply hu hw huw, eichler_ts_apply hu' hw hu'w,
    eichler_ts_apply hsum hw hsumw]
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, hwu, hu'u, hww, hu'w, mul_zero,
    add_zero]
  module
end Eichler


section FiniteField

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem subring_eq_top_of_card_prime {p : ℕ} (hp : p.Prime) (hK : Nat.card K = 2 ^ p)
    (S : Subring K) {a : K} (ha : a ∈ S) (ha0 : a ≠ 0) (ha1 : a ≠ 1) : S = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    · have h1 : x ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
      have hc : 2 ≤ Fintype.card K := by
        have := Fintype.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial K)
        omega
      have h2 : x⁻¹ = x ^ (Fintype.card K - 2) := by
        have h3 : x * x ^ (Fintype.card K - 2) = 1 := by
          rw [← pow_succ']
          have : Fintype.card K - 2 + 1 = Fintype.card K - 1 := by omega
          rw [this, h1]
        exact inv_eq_of_mul_eq_one_right h3
      rw [h2]
      exact S.pow_mem hx _
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let S' : Subalgebra (ZMod 2) K :=
    { S.toSubsemiring with
      algebraMap_mem' := fun z => by
        obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
        simp only [map_natCast]
        exact natCast_mem S n }
  let E : IntermediateField (ZMod 2) K := S'.toIntermediateField hinv
  have hfin : Module.finrank (ZMod 2) K = p := by
    have h1 : Fintype.card K = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) K :=
      Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hmul := Module.finrank_mul_finrank (ZMod 2) E K
  have hdvd : Module.finrank (ZMod 2) E ∣ p := ⟨Module.finrank E K, by rw [← hfin, hmul]⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exfalso
    have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
    have haE : a ∈ E := ha
    rw [hbot] at haE
    obtain ⟨z, rfl⟩ := IntermediateField.mem_bot.1 haE
    have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hz2 z with rfl | rfl
    · exact ha0 (map_zero _)
    · exact ha1 (map_one _)
  · have h2 : Module.finrank E K = 1 := by
      rw [h1, hfin] at hmul
      exact (Nat.mul_eq_left hp.ne_zero).1 hmul
    have htop : E = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.1 h2
    refine Subring.ext fun x => ⟨fun _ => trivial, fun _ => ?_⟩
    have hx : x ∈ E := by rw [htop]; trivial
    exact hx

end FiniteField

section Ring

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {b c : K} {F : OmegaFrame Q b c} {k : Subfield K}
  {Rat M : Subgroup (V ≃ₗ[K] V)}

theorem eichler_comm_root (F : OmegaFrame Q b c) (s t : K) :
    eichler Q (F.e 0) (s • F.f 2) * eichler Q (F.e 2) (t • F.e 1) *
        (eichler Q (F.e 0) (s • F.f 2))⁻¹ =
      eichler Q (F.e 2) (t • F.e 1) * eichler Q (F.e 0) ((s * t) • F.e 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hg := eichler_mem_orthogonalGroup Q (F.e 0) (s • F.f 2)
  rw [eichler_conj hg]
  have hw : polar Q (F.e 0) (s • F.f 2) = 0 := by
    rw [polar_smul_right_eq, F.polar_ef]
    simp
  have hQw : Q (s • F.f 2) = 0 := by rw [map_smul_eq_sq, F.Q_f, mul_zero]
  have e20 : polar Q (F.e 2) (F.e 0) = 0 := F.polar_ee 2 0
  have e10 : polar Q (F.e 1) (F.e 0) = 0 := F.polar_ee 1 0
  have e2f2 : polar Q (F.e 2) (s • F.f 2) = s := by
    rw [polar_smul_right_eq, F.polar_ef]
    simp
  have e1f2 : polar Q (F.e 1) (s • F.f 2) = 0 := by
    rw [polar_smul_right_eq, F.polar_ef]
    simp
  have ge2 : eichler Q (F.e 0) (s • F.f 2) (F.e 2) = F.e 2 + s • F.e 0 := by
    rw [eichler_apply (F.Q_e 0) hw, e20, e2f2, hQw]
    have hneg : -s = s := by linear_combination (-s) * h2
    simp only [zero_smul, add_zero, mul_zero]
    rw [sub_eq_add_neg, ← neg_smul, hneg]
  have ge1 : eichler Q (F.e 0) (s • F.f 2) (t • F.e 1) = t • F.e 1 := by
    rw [map_smul, eichler_apply (F.Q_e 0) hw, e10, e1f2, hQw]
    simp
  rw [ge2, ge1]
  have hsum : eichler Q (F.e 2 + s • F.e 0) (t • F.e 1) =
      eichler Q (F.e 2) (t • F.e 1) * eichler Q (s • F.e 0) (t • F.e 1) := by
    refine eichler_left_add (F.Q_e 2) ?_ ?_ ?_ ?_ ?_
    · rw [map_smul_eq_sq, F.Q_e, mul_zero]
    · rw [map_smul_eq_sq, F.Q_e, mul_zero]
    · rw [polar_smul_right_eq, F.polar_ee, mul_zero]
    · rw [polar_smul_right_eq, F.polar_ee, mul_zero]
    · rw [polar_smul_left_eq, polar_smul_right_eq, F.polar_ee]
      simp
  rw [hsum, eichler_smul_left, smul_smul]

omit [CharP K 2] in
theorem full_line_of_mem (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {t : K}
    (ht : eichler Q (F.e 0) (t • F.e 1) ∈ M) {x y : V} (hx : F.IsRat k x) (hy : F.IsRat k y)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hx0 : x ≠ 0)
    (hya : ∀ a : K, y ≠ a • x) : eichler Q x (t • y) ∈ M := by
  obtain ⟨r, hrR, hrx, a, hry⟩ := R.trans x y hx hy hQx hQy hxy hx0 hya
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hrR)
  have h := eichler_std_conj hrO hQx hrx hry t
  have h' : eichler Q x (t • y) = r⁻¹ * eichler Q (F.e 0) (t • F.e 1) * r := by
    calc eichler Q x (t • y) = r⁻¹ * (r * eichler Q x (t • y) * r⁻¹) * r := by group
      _ = r⁻¹ * eichler Q (F.e 0) (t • F.e 1) * r := by rw [← h]
  rw [h']
  exact M.mul_mem (M.mul_mem (M.inv_mem (hRM hrR)) ht) (hRM hrR)

omit [CharP K 2] in
theorem frame_e_ne_zero (F : OmegaFrame Q b c) (i : Fin 3) : F.e i ≠ 0 := fun h0 => by
  have := F.polar_ef i i
  rw [h0, polar_zero_left] at this
  simp at this

@[expose] def rootRing (R : RatGroupData F k Rat) (hRM : Rat ≤ M) : Subring K where
  carrier := {t | eichler Q (F.e 0) (t • F.e 1) ∈ M}
  zero_mem' := by
    show eichler Q (F.e 0) ((0 : K) • F.e 1) ∈ M
    rw [zero_smul, eichler_zero_right]
    exact M.one_mem
  one_mem' := by
    show eichler Q (F.e 0) ((1 : K) • F.e 1) ∈ M
    rw [one_smul]
    exact hRM (R.eichler_mem (F.e 0) (F.e 1) (F.isRat_e 0) (F.isRat_e 1) (F.Q_e 0)
      (F.polar_ee 0 1))
  add_mem' := by
    intro s t hs ht
    have hs' : eichler Q (F.e 0) (s • F.e 1) ∈ M := hs
    have ht' : eichler Q (F.e 0) (t • F.e 1) ∈ M := ht
    show eichler Q (F.e 0) ((s + t) • F.e 1) ∈ M
    have h1 : polar Q (F.e 0) (s • F.e 1) = 0 := by
      rw [polar_smul_right_eq, F.polar_ee, mul_zero]
    have h2 : polar Q (F.e 0) (t • F.e 1) = 0 := by
      rw [polar_smul_right_eq, F.polar_ee, mul_zero]
    rw [add_smul, ← eichler_mul h1 h2]
    exact M.mul_mem hs' ht'
  neg_mem' := by
    intro t ht
    have ht' : eichler Q (F.e 0) (t • F.e 1) ∈ M := ht
    show eichler Q (F.e 0) ((-t) • F.e 1) ∈ M
    rw [CharTwo.neg_eq]
    exact ht'
  mul_mem' := by
    intro s t hs ht
    have hs' : eichler Q (F.e 0) (s • F.e 1) ∈ M := hs
    have ht' : eichler Q (F.e 0) (t • F.e 1) ∈ M := ht
    show eichler Q (F.e 0) ((s * t) • F.e 1) ∈ M
    have hg : eichler Q (F.e 0) (s • F.f 2) ∈ M := by
      refine full_line_of_mem R hRM hs' (F.isRat_e 0) (F.isRat_f 2) (F.Q_e 0) (F.Q_f 2) ?_
        (frame_e_ne_zero F 0) ?_
      · rw [F.polar_ef]
        simp
      · intro a ha
        have := F.polar_ef 2 2
        have h0 : polar Q (F.e 2) (a • F.e 0) = 0 := by
          rw [polar_smul_right_eq, F.polar_ee, mul_zero]
        rw [← ha, F.polar_ef] at h0
        simp at h0
    have hh : eichler Q (F.e 2) (t • F.e 1) ∈ M := by
      refine full_line_of_mem R hRM ht' (F.isRat_e 2) (F.isRat_e 1) (F.Q_e 2) (F.Q_e 1)
        (F.polar_ee 2 1) (frame_e_ne_zero F 2) ?_
      intro a ha
      have h0 : polar Q (a • F.e 2) (F.f 1) = 0 := by
        rw [polar_smul_left_eq, F.polar_ef]
        simp
      rw [← ha, polar_comm, F.polar_fe] at h0
      simp at h0
    have hcomm := eichler_comm_root F s t
    have hE : eichler Q (F.e 0) ((s * t) • F.e 1) =
        (eichler Q (F.e 2) (t • F.e 1))⁻¹ *
          (eichler Q (F.e 0) (s • F.f 2) * eichler Q (F.e 2) (t • F.e 1) *
            (eichler Q (F.e 0) (s • F.f 2))⁻¹) := by
      rw [hcomm]
      group
    rw [hE]
    exact M.mul_mem (M.inv_mem hh) (M.mul_mem (M.mul_mem hg hh) (M.inv_mem hg))

theorem std_full_of_irrational [Finite K] {p : ℕ} (hp : p.Prime) (hK : Nat.card K = 2 ^ p)
    (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {x y : V} (hx : F.IsRat k x) (hy : F.IsRat k y)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hx0 : x ≠ 0)
    (hya : ∀ a : K, y ≠ a • x) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hM : eichler Q x (a • y) ∈ M) (t : K) :
    eichler Q (F.e 0) (t • F.e 1) ∈ M := by
  obtain ⟨r, hrR, hrx, a₀, hry⟩ := R.trans x y hx hy hQx hQy hxy hx0 hya
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hrR)
  have h := eichler_std_conj hrO hQx hrx hry a
  have haM : eichler Q (F.e 0) (a • F.e 1) ∈ M := by
    rw [h]
    exact M.mul_mem (M.mul_mem (hRM hrR) hM) (M.inv_mem (hRM hrR))
  have htop : rootRing R hRM = ⊤ := subring_eq_top_of_card_prime hp hK _ haM ha0 ha1
  have : t ∈ rootRing R hRM := by rw [htop]; trivial
  exact this

end Ring


end CFSG.RankThree.PartOne.SEITZ2
