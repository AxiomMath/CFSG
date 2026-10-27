module

public import CFSG.RankThree.PartTwo.Sec17.Item174StarU3Model

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host.U3

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem smul_eq (g : hypSU h 1 1) (v : HypIndex 1 1 → K) :
    g • v = ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ v := rfl

theorem smul_vec_smul (g : hypSU h 1 1) (a : K) (v : HypIndex 1 1 → K) :
    g • (a • v) = a • (g • v) := by
  rw [smul_eq, smul_eq, Matrix.mulVec_smul]

theorem smul_vec_add (g : hypSU h 1 1) (v u : HypIndex 1 1 → K) : g • (v + u) = g • v + g • u := by
  rw [smul_eq, smul_eq, smul_eq, Matrix.mulVec_add]

theorem smul_single_apply (g : hypSU h 1 1) (j a : HypIndex 1 1) :
    (g • (Pi.single j (1 : K) : HypIndex 1 1 → K)) a =
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a j := by
  rw [smul_eq]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

@[expose] def fixV (D : Subgroup (hypSU h 1 1)) : Set (HypIndex 1 1 → K) :=
  {v | ∀ d ∈ D, d • v = v}

variable {D : Subgroup (hypSU h 1 1)}

theorem fixV_add {v u : HypIndex 1 1 → K} (hv : v ∈ fixV D) (hu : u ∈ fixV D) :
    v + u ∈ fixV D := fun d hd => by rw [smul_vec_add, hv d hd, hu d hd]

theorem fixV_smul {v : HypIndex 1 1 → K} (a : K) (hv : v ∈ fixV D) : a • v ∈ fixV D :=
  fun d hd => by rw [smul_vec_smul, hv d hd]

theorem fixV_smul_of_mem_normalizer {n : hypSU h 1 1}
    (hn : n ∈ Subgroup.normalizer (D : Set (hypSU h 1 1))) {v : HypIndex 1 1 → K}
    (hv : v ∈ fixV D) : n • v ∈ fixV D := by
  intro d hd
  have hd' : n⁻¹ * d * n ∈ D := by
    rw [Subgroup.mem_normalizer_iff.mp hn]
    simpa [mul_assoc] using hd
  rw [← mul_smul, show d * n = n * (n⁻¹ * d * n) by group, mul_smul, hv _ hd']

theorem eq_one_of_fix_e_f (d : hypSU h 1 1) (he : d • (Pi.single ie (1 : K) : HypIndex 1 1 → K) = Pi.single ie 1)
    (hf : d • (Pi.single jf (1 : K) : HypIndex 1 1 → K) = Pi.single jf 1) : d = 1 := by
  set M := ((d : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hM
  have hcol : ∀ j a, M a j = (d • (Pi.single j (1 : K) : HypIndex 1 1 → K)) a := fun j a =>
    (smul_single_apply d j a).symm
  have hiso := hypForm_smul_smul h d
  have h1 : M jf iw = 0 := by
    have := hiso (Pi.single ie 1) (Pi.single iw 1)
    rw [he, hypForm_eq, hypForm_eq] at this
    simpa [← hcol] using this
  have h2 : M ie iw = 0 := by
    have := hiso (Pi.single jf 1) (Pi.single iw 1)
    rw [hf, hypForm_eq, hypForm_eq] at this
    simpa [← hcol] using this
  have hee : M ie ie = 1 := by rw [hcol, he]; simp
  have hwe : M iw ie = 0 := by rw [hcol, he]; simp
  have hfe : M jf ie = 0 := by rw [hcol, he]; simp
  have hef : M ie jf = 0 := by rw [hcol, hf]; simp
  have hwf : M iw jf = 0 := by rw [hcol, hf]; simp
  have hff : M jf jf = 1 := by rw [hcol, hf]; simp
  have hdet : M.det = 1 := d.2.2
  rw [det_hyp3, hee, hwe, hfe, hef, hwf, hff, h1, h2] at hdet
  have hww : M iw iw = 1 := by simpa using hdet
  refine Subtype.ext (Units.ext ?_)
  change M = 1
  refine mat_ext fun i j hi hj => ?_
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp [hee, hwe, hfe, hef, hwf, hff, h1, h2, hww]

theorem sSU_smul (v : HypIndex 1 1 → K) :
    (sSU h • v) ie = v jf ∧ (sSU h • v) jf = v ie := by
  rw [smul_eq, coe_sSU]
  constructor <;> simp [Matrix.mulVec, dotProduct, sum_hyp]

theorem sSU_smul_single_ie :
    sSU h • (Pi.single ie (1 : K) : HypIndex 1 1 → K) = Pi.single jf 1 := by
  rw [smul_eq, coe_sSU]
  refine vec_ext ?_ ?_ ?_ <;> simp [Matrix.mulVec, dotProduct, sum_hyp]

theorem two_dvd_card_vec (h : UnitaryFieldData 2 f K) :
    2 ∣ Nat.card (HypIndex 1 1 → K) := by
  have := h.finite
  rw [Nat.card_fun, h.card]
  have hf := h.one_le
  exact (dvd_pow_self 2 (by omega)).trans (dvd_pow_self _ (by simp))

@[expose] def wPerp (D : Subgroup (hypSU h 1 1)) (hw : Pi.single iw (1 : K) ∈ fixV D) :
    SubMulAction D (HypIndex 1 1 → K) where
  carrier := {u | u iw = 0}
  smul_mem' d u hu := by
    change ((d : hypSU h 1 1) • u) iw = 0
    have := hypForm_smul_smul h (d : hypSU h 1 1) (Pi.single iw 1) u
    rw [hw d d.2, hypForm_eq, hypForm_eq] at this
    have h' : ((d : hypSU h 1 1) • u) iw = u iw := by simpa using this
    rw [h']
    exact hu

theorem card_wPerp (h : UnitaryFieldData 2 f K) (hw : Pi.single iw (1 : K) ∈ fixV D) :
    2 ∣ Nat.card (wPerp D hw) := by
  have := h.finite
  have e : wPerp D hw ≃ K × K :=
    { toFun := fun u => ((u : HypIndex 1 1 → K) ie, (u : HypIndex 1 1 → K) jf)
      invFun := fun x => ⟨fun a => Sum.elim (fun _ => x.1) (Sum.elim (fun _ => 0) (fun _ => x.2)) a,
        show (0 : K) = 0 from rfl⟩
      left_inv := fun u => Subtype.ext (vec_ext rfl u.2.symm rfl)
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_prod, h.card]
  have hf := h.one_le
  exact (dvd_pow_self 2 (by omega)).mul_right _

theorem eq_bot_of_two (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : orderOf ω = 3)
    (hωb : h.bar (ω : K) = ω) {D : Subgroup (hypSU h 1 1)} (hD : IsPGroup 2 D)
    (hc : tau h ω ∈ Subgroup.normalizer (D : Set (hypSU h 1 1)))
    (hs : sSU h ∈ Subgroup.normalizer (D : Set (hypSU h 1 1))) : D = ⊥ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    exact one_ne_zero
  have h0 : (0 : HypIndex 1 1 → K) ∈ MulAction.fixedPoints D (HypIndex 1 1 → K) :=
    fun d => smul_zero _
  obtain ⟨b, hb, hb0⟩ := hD.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (HypIndex 1 1 → K) (two_dvd_card_vec h) h0
  have hbU : b ∈ fixV D := fun d hd => hb ⟨d, hd⟩
  by_cases hE : ∃ v ∈ fixV D, v ie ≠ 0 ∨ v jf ≠ 0
  ·
    have hE' : ∃ v ∈ fixV D, v ie ≠ 0 := by
      obtain ⟨v, hv, hv0 | hv0⟩ := hE
      · exact ⟨v, hv, hv0⟩
      · exact ⟨sSU h • v, fixV_smul_of_mem_normalizer hs hv, by rw [(sSU_smul v).1]; exact hv0⟩
    obtain ⟨v, hv, hv0⟩ := hE'
    have hcv := fixV_smul_of_mem_normalizer hc hv
    have hccv := fixV_smul_of_mem_normalizer hc hcv
    have h3e : (3 : K) • Pi.single ie (v ie) ∈ fixV D := by
      rw [three_smul_single_ie h hω hωb]
      exact fixV_add (fixV_add hv (fixV_smul _ hcv)) (fixV_smul _ hccv)
    have he : Pi.single ie (1 : K) ∈ fixV D := by
      have := fixV_smul ((v ie)⁻¹ * (3 : K)⁻¹) h3e
      rwa [smul_smul, mul_assoc, inv_mul_cancel₀ h3, mul_one, ← Pi.single_smul', smul_eq_mul,
        inv_mul_cancel₀ hv0] at this
    have hf : Pi.single jf (1 : K) ∈ fixV D := by
      rw [← sSU_smul_single_ie]
      exact fixV_smul_of_mem_normalizer hs he
    rw [eq_bot_iff]
    intro d hd
    exact eq_one_of_fix_e_f d (he d hd) (hf d hd)
  ·
    push Not at hE
    exfalso
    obtain ⟨hbe, hbf⟩ := hE b hbU
    have hbw : b iw ≠ 0 := by
      intro hbw
      exact hb0 (vec_ext (by simp [hbe]) (by simp [hbw]) (by simp [hbf])).symm
    have hw : Pi.single iw (1 : K) ∈ fixV D := by
      have := fixV_smul (b iw)⁻¹ hbU
      convert this using 1
      refine vec_ext ?_ ?_ ?_ <;> simp [hbe, hbf, inv_mul_cancel₀ hbw]
    set z : wPerp D hw := ⟨0, show (0 : HypIndex 1 1 → K) iw = 0 from rfl⟩
    have h0' : z ∈ MulAction.fixedPoints D (wPerp D hw) := fun d =>
      Subtype.ext (show (d : hypSU h 1 1) • (0 : HypIndex 1 1 → K) = 0 from smul_zero _)
    obtain ⟨u, hu, hu0⟩ := hD.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (wPerp D hw) (card_wPerp h hw) h0'
    have huU : (u : HypIndex 1 1 → K) ∈ fixV D := fun d hd =>
      congrArg Subtype.val (hu ⟨d, hd⟩)
    obtain ⟨hue, huf⟩ := hE _ huU
    apply hu0
    apply Subtype.ext
    show (0 : HypIndex 1 1 → K) = (u : HypIndex 1 1 → K)
    exact vec_ext hue.symm (show (u : HypIndex 1 1 → K) iw = 0 from u.2).symm huf.symm

end CFSG.RankThree.PartTwo.Sec17.Proof174Host.U3
