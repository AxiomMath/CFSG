module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerImprimitiveField
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerProjectiveImage
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerOvergroupArithmetic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module MulAction

universe u

variable {F : Type u} [Field F]

theorem false_of_card_mul_eq [Finite F] [CharP F 2] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (heven : Even e) (hd : 0 < d) (hde : d ∣ e) :
    ∀ (m : ℕ) (k : Type u) [Field k] [Algebra k F] (s a : ℕ), finrank k F = m →
      Nat.card k = 2 ^ s → 1 ≤ a → a ≤ s → ∀ G : Subgroup (F ≃ₗ[k] F), scalars k F ≤ G →
        Nat.card G * a = 2 ^ e * (2 ^ e - 1) * d → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k _ _ s a hm hk ha has G hSG hcard
  have : FiniteDimensional k F := Module.Finite.of_finite
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  have hesm : e = s * m := by
    have h := Module.natCard_eq_pow_finrank (K := k) (V := F)
    rw [hF, hk, hm, ← pow_mul] at h
    exact Nat.pow_right_injective le_rfl h
  have hs1 : 1 ≤ s := by
    have h1 : 1 < Nat.card k := Finite.one_lt_card
    rw [hk] at h1
    by_contra h0
    have : s = 0 := by omega
    subst this
    simp at h1
  have hm1 : 1 ≤ m := by
    rw [← hm]
    exact Module.finrank_pos
  have he1 : 1 ≤ e := by
    rw [hesm]
    exact Nat.mul_pos hs1 hm1
  have hpos : 0 < 2 ^ e * (2 ^ e - 1) * d := by
    have := Nat.one_lt_two_pow (show e ≠ 0 by omega)
    exact Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) hd
  have hnormal : (∀ g ∈ G, ∀ c : Fˣ, ∃ c' : Fˣ, ∀ x, g (c * x) = c' * g x) → False := by
    intro hN
    have hle := card_le_of_normalizes G hN
    rw [hF, hm] at hle
    exact lt_of_card_eq hesm he1 hd has hcard hle
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    apply hnormal
    intro g _ c
    refine ⟨c, fun x => ?_⟩
    have htop : (⊤ : IntermediateField k F) = ⊥ :=
      IntermediateField.finrank_eq_one_iff.mp ((IntermediateField.finrank_top').trans (by omega))
    have hc : (c : F) ∈ (⊥ : IntermediateField k F) := htop ▸ IntermediateField.mem_top
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hc
    rw [← hr, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm2' : m = 2 := by omega
    have hdvd := Subgroup.card_subgroup_dvd_card G
    rw [card_linearEquiv_of_finrank_eq_two (hm.trans hm2'), hk] at hdvd
    refine not_two_pow_dvd_of_dvd_card_GL_two hs1 ha has hdvd ?_
    rw [hcard, hesm, hm2', mul_comm s 2]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
  by_cases hprim : IsPreprimitive G (ℙ k F)
  ·
    have := isPreprimitive_projectiveImage G
    have := isPretransitive_projectiveImage_scalars (k := k) (F := F)
    have hcardP : Nat.card (ℙ k F) = ∑ i ∈ Finset.range m, (2 ^ s) ^ i := by
      rw [card_of_finrank k F hm, hk]
    have hP2 : 2 ≤ Nat.card (ℙ k F) := by
      rw [hcardP]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm1
      rw [add_comm, sum_range_succ_pow]
      have hb : 2 ≤ 2 ^ s :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs1
      have h1 : 1 ≤ ∑ i ∈ Finset.range n, (2 ^ s) ^ i := by
        obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
        rw [add_comm, sum_range_succ_pow]
        omega
      nlinarith
    rcases CFSG.burnside_schur (projectiveImage G) (projectiveImage (scalars k F)) hP2
        (projectiveImage_mono hSG) stabilizer_projectiveImage_scalars with
      h2 | ⟨p, -, -, -, -, -, hN⟩
    ·
      have hdiv := mul_pred_dvd_card h2 hP2
      have hGcard := card_eq_card_projectiveImage_mul G hSG
      have hproj := Projectivization.card k F
      rw [hF, hk] at hproj
      rw [hk] at hGcard
      set v := Nat.card (ℙ k F)
      have hb1 : 0 < 2 ^ s - 1 := by
        have := Nat.one_lt_two_pow (show s ≠ 0 by omega)
        omega
      have hv0 : 0 < v := by omega
      have hGa : Nat.card (projectiveImage G) * a = 2 ^ e * v * d := by
        have h1 : Nat.card (projectiveImage G) * a * (2 ^ s - 1) =
            2 ^ e * v * d * (2 ^ s - 1) := by
          calc Nat.card (projectiveImage G) * a * (2 ^ s - 1)
              = Nat.card G * a := by rw [hGcard]; ring
            _ = 2 ^ e * (2 ^ e - 1) * d := hcard
            _ = 2 ^ e * v * d * (2 ^ s - 1) := by rw [hproj]; ring
        exact Nat.eq_of_mul_eq_mul_right hb1 h1
      have h3 : v * (v - 1) ∣ v * (2 ^ e * d) := by
        have := hdiv.trans (Dvd.intro a hGa)
        convert this using 1
        ring
      have h4 := Nat.dvd_of_mul_dvd_mul_left hv0 h3
      rw [hcardP, hesm] at h4
      exact not_sum_pow_sub_one_dvd hs1 hm3 (hesm ▸ heven) (hesm ▸ hde) h4
    ·
      exact hnormal fun g hg c => normalizes_of_normal hSG hN hg c
  ·
    obtain ⟨l, hl, -, hσ, -⟩ :=
      exists_intermediateField_normalized_of_not_isPreprimitive (by omega) G hSG hprim
    obtain ⟨G₁, hG₁G, hG₁lin, hG₁mem, h, hh, hcardG⟩ := exists_card_eq_mul_of_semilinear G l hσ
    have ht1 : finrank k l ≠ 1 := fun h1 => hl (IntermediateField.finrank_eq_one_iff.mp h1)
    have ht2 : 2 ≤ finrank k l := by
      have : 0 < finrank k l := Module.finrank_pos
      omega
    have htower : finrank k l * finrank l F = m := by
      rw [Module.finrank_mul_finrank, hm]
    have hlF : 0 < finrank l F := Module.finrank_pos
    have hlt : finrank l F < m := by
      rw [← htower]
      nlinarith
    have hcardl : Nat.card l = 2 ^ (s * finrank k l) := by
      rw [Module.natCard_eq_pow_finrank (K := k) (V := l), hk, ← pow_mul]
    set G' := G₁.comap (restrictScalarsHom k l)
    have hcardG' : Nat.card G' = Nat.card G₁ := by
      have hmap : G'.map (restrictScalarsHom k l) = G₁ := by
        rw [Subgroup.map_comap_eq, inf_eq_right]
        intro g hg
        obtain ⟨g', hg'⟩ := exists_restrictScalarsHom_eq (hG₁lin g hg)
        exact ⟨g', hg'⟩
      rw [← hmap, Subgroup.card_map_of_injective restrictScalarsHom_injective]
    have hSG' : scalars l F ≤ G' := by
      rintro _ ⟨c, rfl⟩
      change restrictScalarsHom k l (scalarHom l F c) ∈ G₁
      rw [restrictScalarsHom_scalarHom]
      exact hG₁mem _ (hSG (scalarHom_mem_scalars c)) fun b x => by
        rw [scalarHom_apply, scalarHom_apply, mul_left_comm]
    have hh1 : 1 ≤ h := by
      by_contra h0
      have : h = 0 := by omega
      rw [this, mul_zero] at hcardG
      rw [hcardG, zero_mul] at hcard
      omega
    exact ih (finrank l F) hlt l (s * finrank k l) (a * h) rfl hcardl
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
      (Nat.mul_le_mul has hh) G' hSG' (by rw [hcardG', ← hcard, hcardG]; ring)

theorem not_exists_singer_overgroup_card_eq [Algebra (ZMod 2) F] {e d : ℕ}
    (heven : Even e) (hF : Nat.card F = 2 ^ e) (hd : 0 < d) (hde : d ∣ e) :
    ¬ ∃ R : Subgroup (F ≃ₗ[ZMod 2] F), scalars (ZMod 2) F ≤ R ∧
      Nat.card R = 2 ^ e * (2 ^ e - 1) * d := by
  rintro ⟨R, hSR, hR⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  set k₀ := (⊥ : IntermediateField (ZMod 2) F)
  have hsurj : Function.Surjective (restrictScalarsHom (ZMod 2) k₀) := by
    intro g
    refine exists_restrictScalarsHom_eq fun a x => ?_
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp a.2
    rw [← hz, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  set R₀ := R.comap (restrictScalarsHom (ZMod 2) k₀)
  have hcard₀ : Nat.card R₀ = Nat.card R := by
    have hmap : R₀.map (restrictScalarsHom (ZMod 2) k₀) = R := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hsurj, top_inf_eq]
    rw [← hmap, Subgroup.card_map_of_injective restrictScalarsHom_injective]
  have hS₀ : scalars k₀ F ≤ R₀ := by
    rintro _ ⟨c, rfl⟩
    change restrictScalarsHom (ZMod 2) k₀ (scalarHom k₀ F c) ∈ R
    rw [restrictScalarsHom_scalarHom]
    exact hSR (scalarHom_mem_scalars c)
  have hk₀ : Nat.card k₀ = 2 ^ 1 := by
    rw [Nat.card_congr (IntermediateField.botEquiv (ZMod 2) F).toEquiv, Nat.card_zmod, pow_one]
  have hfin : finrank k₀ F = e := by
    rw [IntermediateField.finrank_bot']
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  exact false_of_card_mul_eq hF heven hd hde e k₀ 1 1 hfin hk₀ le_rfl le_rfl R₀ hS₀
    (by rw [mul_one, hcard₀, hR])

end CFSG.ShultStronglyClosedTI.Singer
