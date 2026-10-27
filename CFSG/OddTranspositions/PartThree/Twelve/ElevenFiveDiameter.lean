module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

private theorem zmod5_id1 (Qv Qw B : ZMod 5) :
    B * B * Qv + (-Qv) * (-Qv) * Qw + 2 * (B * (-Qv) * B) =
      B ^ 2 * Qv + 2 * (B * (-Qv) * B) + (-Qv) ^ 2 * Qw := by
  revert Qv Qw B; decide

private theorem zmod5_id2 (Qv Qw B : ZMod 5) :
    B ^ 2 * Qv + 2 * (B * (-Qv) * B) + (-Qv) ^ 2 * Qw =
      Qv * (Qv * Qw - B * B) := by
  revert Qv Qw B; decide

private theorem zmod5_id3 (Qv B : ZMod 5) : B * Qv + (-Qv) * B = 0 := by
  revert Qv B; decide

private theorem zmod5_id4 (Qv Qw B : ZMod 5) :
    B * B + (-Qv) * Qw = -(Qv * Qw - B * B) := by
  revert Qv Qw B; decide

theorem zmod5_sub_two_mul_self (a : ZMod 5) : a - 2 * a = -a := by
  revert a; decide

private theorem zmod5_mul_ne_zero : ∀ a b : ZMod 5, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  decide

private theorem zmod5_pow_ne_zero : ∀ a : ZMod 5, a ≠ 0 → a ^ 2 ≠ 0 := by
  decide

private theorem zmod5_neg_neg_mul (a b : ZMod 5) : -((-a) * b) = a * b := by
  revert a b; decide

private theorem zmod5_module_id (Qv B wi vi : ZMod 5) :
    Qv * wi = B * vi - (B * vi + (-Qv) * wi) := by
  revert Qv B wi vi; decide

theorem isFiveNondeg_span_range_of_det_ne_zero {n : ℕ} {ε : Bool}
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → Fin (n + 1) → ZMod 5)
    (hdet : Matrix.det (fun i j => fiveForm n ε (b i) (b j)) ≠ 0) :
    IsFiveNondeg n ε (Submodule.span (ZMod 5) (Set.range b)) := by
  rw [isFiveNondeg_iff]
  intro x hx horth
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  let G : Matrix ι ι (ZMod 5) := fun i j => fiveForm n ε (b i) (b j)
  have hdetG : G.det ≠ 0 := by simpa [G] using hdet
  have hsys : G *ᵥ c = 0 := by
    ext j
    have h := horth (b j) (Submodule.subset_span ⟨j, rfl⟩)
    rw [← hc] at h
    have h1 : fiveBilin n ε true (∑ i, c i • b i) (b j) = 0 := by
      rw [fiveBilin_apply, h, mul_zero]
    have h2 : fiveBilin n ε true (∑ i, c i • b i) (b j) =
        ∑ i, c i * fiveBilin n ε true (b i) (b j) := by
      rw [LinearMap.BilinForm.sum_left]
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.BilinForm.smul_left]
    rw [h2] at h1
    simp only [fiveBilin_apply] at h1
    have h1' : (fiveSignRep true)⁻¹ * ∑ i, c i * fiveForm n ε (b i) (b j) = 0 := by
      rw [Finset.mul_sum]
      rw [← h1]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsum0 : ∑ i, c i * fiveForm n ε (b i) (b j) = 0 :=
      (mul_eq_zero.mp h1').resolve_left (inv_ne_zero (fiveSignRep_ne_zero true))
    rw [Matrix.mulVec, dotProduct]
    rw [show (∑ i, G j i * c i) = ∑ i, c i * fiveForm n ε (b i) (b j) by
      apply Finset.sum_congr rfl
      intro i _
      simp only [G]
      rw [fiveForm_comm]
      ring]
    exact hsum0
  have hinj : Function.Injective G.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdetG
  have hc0 : c = 0 := hinj (by rw [hsys]; simp)
  rw [← hc, hc0]
  simp

theorem exists_common_perp_fiveForm {n : ℕ} (hn : 4 ≤ n) (ε π : Bool)
    {v w : Fin (n + 1) → ZMod 5}
    (hv : fiveForm n ε v v ≠ 0)
    (hlin : ∀ μ : ZMod 5, w ≠ μ • v) :
    ∃ x : Fin (n + 1) → ZMod 5, x ≠ 0 ∧ fiveForm n ε x x ≠ 0 ∧
      (IsSquare (fiveForm n ε x x) ↔ π = true) ∧
      fiveForm n ε x v = 0 ∧ fiveForm n ε x w = 0 := by
  by_cases hdet : fiveForm n ε v v * fiveForm n ε w w - fiveForm n ε v w * fiveForm n ε v w = 0
  ·
    let u : Fin (n + 1) → ZMod 5 :=
      fiveForm n ε v w • v + (-(fiveForm n ε v v)) • w
    have hu_ne : u ≠ 0 := by
      intro hu0
      have h1 : fiveForm n ε v w • v = fiveForm n ε v v • w := by
        have h' : fiveForm n ε v w • v + (-(fiveForm n ε v v)) • w = 0 := by
          simpa only [u] using hu0
        have h'' : fiveForm n ε v w • v = -((-(fiveForm n ε v v)) • w) :=
          add_eq_zero_iff_eq_neg.mp h'
        rw [h'']
        funext i
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        exact zmod5_neg_neg_mul _ _
      have hw_eq : w = ((fiveForm n ε v v)⁻¹ * fiveForm n ε v w) • v := by
        have h2 := congrArg (fun z => (fiveForm n ε v v)⁻¹ • z) h1
        simp only [smul_smul, inv_mul_cancel₀ hv, one_smul] at h2
        exact h2.symm
      exact hlin _ hw_eq
    have huQ : fiveForm n ε u u = 0 := by
      have hexp : fiveForm n ε u u =
          fiveForm n ε v w ^ 2 * fiveForm n ε v v
          + 2 * (fiveForm n ε v w * (-(fiveForm n ε v v)) * fiveForm n ε v w)
          + (-(fiveForm n ε v v)) ^ 2 * fiveForm n ε w w := by
        simp only [u]
        rw [fiveForm_self_add, fiveForm_smul_smul, fiveForm_smul_smul, fiveForm_smul_smul]
        exact zmod5_id1 _ _ _
      rw [hexp, zmod5_id2, hdet, mul_zero]
    have huv : fiveForm n ε u v = 0 := by
      simp only [u]
      rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, fiveForm_comm n ε w v]
      exact zmod5_id3 _ _
    have huw : fiveForm n ε u w = 0 := by
      simp only [u]
      rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left]
      rw [zmod5_id4, hdet]
      exact neg_zero
    obtain ⟨z, hzu⟩ : ∃ z, fiveForm n ε z u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu_ne (isFiveNondeg_iff.1 (isFiveNondeg_top n ε) u trivial (fun y _ => by
        rw [fiveForm_comm]; exact hcon y))
    have huz : fiveForm n ε u z ≠ 0 := by rwa [fiveForm_comm] at hzu
    let b3 : Fin 3 → Fin (n + 1) → ZMod 5 := ![v, u, z]
    let G3 : Matrix (Fin 3) (Fin 3) (ZMod 5) := fun i j => fiveForm n ε (b3 i) (b3 j)
    have hdet3 : G3.det = -(fiveForm n ε v v * (fiveForm n ε u z) ^ 2) := by
      rw [Matrix.det_fin_three]
      have h00 : G3 0 0 = fiveForm n ε v v := rfl
      have h01 : G3 0 1 = 0 := by
        change fiveForm n ε v u = 0
        rw [fiveForm_comm]; exact huv
      have h02 : G3 0 2 = fiveForm n ε v z := rfl
      have h10 : G3 1 0 = 0 := by
        change fiveForm n ε u v = 0
        exact huv
      have h11 : G3 1 1 = 0 := by
        change fiveForm n ε u u = 0
        exact huQ
      have h12 : G3 1 2 = fiveForm n ε u z := rfl
      have h20 : G3 2 0 = fiveForm n ε v z := by
        change fiveForm n ε z v = fiveForm n ε v z
        rw [fiveForm_comm]
      have h21 : G3 2 1 = fiveForm n ε u z := by
        change fiveForm n ε z u = fiveForm n ε u z
        rw [fiveForm_comm]
      have h22 : G3 2 2 = fiveForm n ε z z := rfl
      rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
      ring
    have hb3det : Matrix.det (fun i j => fiveForm n ε (b3 i) (b3 j)) ≠ 0 := by
      change G3.det ≠ 0
      rw [hdet3]
      exact neg_ne_zero.mpr (zmod5_mul_ne_zero _ _ hv (zmod5_pow_ne_zero _ huz))
    have hT : IsFiveNondeg n ε (Submodule.span (ZMod 5) (Set.range b3)) :=
      isFiveNondeg_span_range_of_det_ne_zero b3 hb3det
    have hN : IsFiveNondeg n ε (fiveOrth n ε (Submodule.span (ZMod 5) (Set.range b3))) := by
      simpa only [top_inf_eq] using
        isFiveNondeg_inf_fiveOrth (isFiveNondeg_top n ε) hT le_top
    have hdim : 2 ≤ Module.finrank (ZMod 5)
        (fiveOrth n ε (Submodule.span (ZMod 5) (Set.range b3))) := by
      have h := finrank_inf_fiveOrth_add (k := n) (ε := ε) (W := ⊤)
        (U := Submodule.span (ZMod 5) (Set.range b3)) (isFiveNondeg_top n ε) le_top
      rw [top_inf_eq] at h
      have hle : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (Set.range b3)) ≤ 3 := by
        have h := finrank_span_finset_le_card (R := ZMod 5) (s := Finset.univ.image b3)
        rw [show (↑(Finset.univ.image b3) : Set (Fin (n + 1) → ZMod 5)) = Set.range b3 by
          ext; simp] at h
        calc Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (Set.range b3))
            ≤ (Finset.univ.image b3).card := h
          _ ≤ Finset.univ.card := Finset.card_image_le
          _ = 3 := by simp
      have htop : Module.finrank (ZMod 5)
          (⊤ : Submodule (ZMod 5) (Fin (n + 1) → ZMod 5)) = n + 1 := by
        rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
      rw [htop] at h
      omega
    obtain ⟨x, hx, hxQ⟩ := exists_fiveForm_eq_of_nondeg hN hdim (c := fiveSignRep π)
    have hwT : w ∈ Submodule.span (ZMod 5) (Set.range b3) := by
      have h1 : fiveForm n ε v v • w = fiveForm n ε v w • v - u := by
        simp only [u]
        funext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact zmod5_module_id _ _ _ _
      have hw_eq : w = ((fiveForm n ε v v)⁻¹ * fiveForm n ε v w) • v
          - (fiveForm n ε v v)⁻¹ • u := by
        have h2 := congrArg (fun z => (fiveForm n ε v v)⁻¹ • z) h1
        simp only [smul_sub, smul_smul, inv_mul_cancel₀ hv, one_smul] at h2
        exact h2
      rw [hw_eq]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    refine ⟨x, ?_, ?_, ?_, ?_, ?_⟩
    · rintro rfl
      simp [fiveForm] at hxQ
      exact fiveSignRep_ne_zero π hxQ.symm
    · rw [hxQ]; exact fiveSignRep_ne_zero π
    · rw [hxQ]; exact isSquare_fiveSignRep_iff π
    · exact (mem_fiveOrth.mp hx) v (Submodule.subset_span ⟨0, rfl⟩)
    · exact (mem_fiveOrth.mp hx) w hwT
  ·
    let b2 : Fin 2 → Fin (n + 1) → ZMod 5 := ![v, w]
    let G2 : Matrix (Fin 2) (Fin 2) (ZMod 5) := fun i j => fiveForm n ε (b2 i) (b2 j)
    have hdet2 : G2.det = fiveForm n ε v v * fiveForm n ε w w
        - fiveForm n ε v w * fiveForm n ε v w := by
      rw [Matrix.det_fin_two]
      simp only [G2, b2, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [fiveForm_comm n ε w v]
    have hb2det : Matrix.det (fun i j => fiveForm n ε (b2 i) (b2 j)) ≠ 0 := by
      change G2.det ≠ 0
      rw [hdet2]
      exact hdet
    have hP : IsFiveNondeg n ε (Submodule.span (ZMod 5) (Set.range b2)) :=
      isFiveNondeg_span_range_of_det_ne_zero b2 hb2det
    have hN : IsFiveNondeg n ε (fiveOrth n ε (Submodule.span (ZMod 5) (Set.range b2))) := by
      simpa only [top_inf_eq] using
        isFiveNondeg_inf_fiveOrth (isFiveNondeg_top n ε) hP le_top
    have hdim : 2 ≤ Module.finrank (ZMod 5)
        (fiveOrth n ε (Submodule.span (ZMod 5) (Set.range b2))) := by
      have h := finrank_inf_fiveOrth_add (k := n) (ε := ε) (W := ⊤)
        (U := Submodule.span (ZMod 5) (Set.range b2)) (isFiveNondeg_top n ε) le_top
      rw [top_inf_eq] at h
      have hle : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (Set.range b2)) ≤ 2 := by
        have h := finrank_span_finset_le_card (R := ZMod 5) (s := Finset.univ.image b2)
        rw [show (↑(Finset.univ.image b2) : Set (Fin (n + 1) → ZMod 5)) = Set.range b2 by
          ext; simp] at h
        calc Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (Set.range b2))
            ≤ (Finset.univ.image b2).card := h
          _ ≤ Finset.univ.card := Finset.card_image_le
          _ = 2 := by simp
      have htop : Module.finrank (ZMod 5)
          (⊤ : Submodule (ZMod 5) (Fin (n + 1) → ZMod 5)) = n + 1 := by
        rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
      rw [htop] at h
      omega
    obtain ⟨x, hx, hxQ⟩ := exists_fiveForm_eq_of_nondeg hN hdim (c := fiveSignRep π)
    refine ⟨x, ?_, ?_, ?_, ?_, ?_⟩
    · rintro rfl
      simp [fiveForm] at hxQ
      exact fiveSignRep_ne_zero π hxQ.symm
    · rw [hxQ]; exact fiveSignRep_ne_zero π
    · rw [hxQ]; exact isSquare_fiveSignRep_iff π
    · exact (mem_fiveOrth.mp hx) v (Submodule.subset_span ⟨0, rfl⟩)
    · exact (mem_fiveOrth.mp hx) w (Submodule.subset_span ⟨1, rfl⟩)

end CFSG.OddTranspositions.PartThree

end
