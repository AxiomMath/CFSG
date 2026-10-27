module

public import CFSG.Quasithin.Recognition.Stroth.Str83EightL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.B45L2 CFSG.Quasithin.G11.Harris.L2 CFSG.Timmesfeld.Bridge.Higman
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open scoped MatrixGroups

section Numerics

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem eightL_l_one_numerics (hF : Fintype.card F = 2 ^ 3)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (hW : Nat.card W = 2 ^ 8) :
    (∀ a : SL(2, F), a ≠ 1 → a * a = 1 →
      Nat.card W = 16 * Nat.card (fixedSub ρ (Subgroup.zpowers a))) ∧
    (∀ A : Subgroup SL(2, F), A ≠ ⊥ → (∀ a ∈ A, a * a = 1) → Nat.card A = 4 →
      64 * Nat.card (fixedSub ρ A) ≤ Nat.card W) ∧
    (∀ A : Subgroup SL(2, F), A ≠ ⊥ → (∀ a ∈ A, a * a = 1) → Nat.card A = 8 →
      128 * Nat.card (fixedSub ρ A) ≤ Nat.card W) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 3) (by norm_num) hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have hfinW : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨K, hKF, hKfin, hKchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    rw [hDcard, hdim, ← pow_mul] at h1
    exact h1
  have hexp : d * 2 ^ J.card = 8 := by
    have h := Nat.pow_right_injective (a := 2) (by norm_num) (by
      change 2 ^ (d * 2 ^ J.card) = 2 ^ 8
      rw [← hWcard, hW])
    exact h
  have hJle : J.card ≤ 3 := by
    have hsub : J ⊆ Finset.range 3 := by
      intro i hi
      rw [Finset.mem_range]
      exact hJn i hi
    calc J.card ≤ (Finset.range 3).card := Finset.card_le_card hsub
      _ = 3 := by simp
  have hJpos : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hJ3 : J.card = 3 := by
    rcases Nat.eq_or_lt_of_le hJpos with h | h
    ·
      exfalso
      have hd4 : d = 4 := by
        rw [← h] at hexp
        norm_num at hexp
        omega
      obtain ⟨j, hjJ⟩ := Finset.card_eq_one.mp h.symm
      have hj : j < 3 := hJn j (by rw [hjJ]; simp)
      have hjd : (j + d) % 3 = j := by
        have hmem : (j + d) % 3 ∈ J := by
          have himg : (j + d) % 3 ∈ J.image (fun i => (i + d) % 3) := by
            simp only [Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨j, by rw [hjJ]; simp, rfl⟩
          rwa [hshift] at himg
        simpa [hjJ] using hmem
      have h3d : 3 ∣ d := by
        have h1 : (j + d) % 3 = (j + 0) % 3 := by rw [hjd, add_zero, Nat.mod_eq_of_lt hj]
        exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)
      have : 3 ∣ 4 := by
        rw [← hd4]; exact h3d
      omega
    · rcases Nat.eq_or_lt_of_le h with h2 | h2
      ·
        exfalso
        have hd2 : d = 2 := by
          rw [← h2] at hexp
          norm_num at hexp
          omega
        have hkg := le_card_mul_gcd_of_shift (n := 3) (d := d) (J := J) (by norm_num)
          hJne hJn hshift
        rw [← h2, hd2] at hkg
        norm_num at hkg
      · omega
  have hd_eq : d = 1 := by
    rw [hJ3] at hexp
    norm_num at hexp
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro a ha1 ha2
    have hC := natCard_fixW_involution ρ b ιF ιD J hJne Φ a ha1 ha2
    have hC' : Nat.card {w : W // ρ a w = w} = 16 := by
      rw [hC, hDcard, hJ3]
      norm_num
      rw [← pow_mul, hd_eq]
      norm_num
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_fixedSub_zpowers ρ a w), hC', hW]
    norm_num
  · intro A hA1 hA2 hA4
    obtain ⟨x, hxU⟩ := exists_conj_le_rootGroup A hA2
    let A' : Subgroup SL(2, F) := A.map (MulAut.conj x⁻¹).toMonoidHom
    have hA'le : A' ≤ (upperUnipotent (F := F)).range := by
      rintro g ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hxU a ha
    have hA'2inv : ∀ g ∈ A', g * g = 1 := by
      intro g hg
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
      have h1 : ((MulAut.conj x⁻¹) a) ^ 2 = 1 := by
        rw [pow_two, ← map_mul, hA2 a ha, map_one]
      rw [← hae]
      simpa [pow_two] using h1
    have hmem : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ A' := by
      intro g
      constructor
      · intro hg
        simpa [A', MulAut.conj_apply] using
          Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hg
      · intro hg
        obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
        have : a = g := by
          simpa [MulAut.conj_apply] using congrArg (fun y => x * y * x⁻¹) hae
        simpa [this] using ha
    have hA'card : Nat.card A' = Nat.card A :=
      (Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv).symm
    have hC : Nat.card (fixedSub ρ A) =
        Nat.card {w : W // ∀ a ∈ A', ρ a w = w} := by
      simpa [fixedSub] using natCard_fixed_conj ρ A A' x hmem
    let E : Finset F := Finset.univ.filter (fun t : F => uElt t ∈ A')
    have hE_mem : ∀ t : F, t ∈ E ↔ uElt t ∈ A' := by
      intro t; simp [E]
    have hEcard : Nat.card A' = E.card := by
      have hinj : Function.Injective
          (fun t : E => (⟨uElt t, (hE_mem t).mp t.2⟩ : A')) := by
        intro t1 t2 h
        exact Subtype.ext (uElt_injective (congrArg Subtype.val h))
      have hsurj : Function.Surjective
          (fun t : E => (⟨uElt t, (hE_mem t).mp t.2⟩ : A')) := by
        intro a
        obtain ⟨t, ht⟩ := (mem_rootGroup_iff (a : SL(2, F))).mp (hA'le a.2)
        have htE : t ∈ E := (hE_mem t).mpr (by simpa [ht] using a.2)
        exact ⟨⟨t, htE⟩, Subtype.ext (by simpa using ht.symm)⟩
      have hEsub : Nat.card ↥E = E.card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      calc Nat.card A' = Nat.card ↥E :=
            (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm
        _ = E.card := hEsub
    have hEcard4 : E.card = 4 := by rw [← hEcard, hA'card, hA4]
    have hnotLine : ¬ ∃ v : F, v ≠ 0 ∧ ∀ t ∈ E, ∃ c : F,
        c ^ (2 ^ 1) = c ∧ t = c * v := by
      rintro ⟨v, hv0, hline⟩
      have hmap : E.image (fun t => t / v) ⊆
          Finset.univ.filter (fun c : F => c ^ (2 ^ 1) = c) := by
        intro c hc
        obtain ⟨t, htE, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨c, hcfix, hceq⟩ := hline t htE
        have hdiv : t / v = c := by
          rw [hceq, mul_div_cancel_right₀ c hv0]
        rw [hdiv]
        simpa using hcfix
      have hcard_image : (E.image (fun t => t / v)).card = E.card := by
        apply Finset.card_image_of_injective
        intro t1' t2' h
        exact mul_right_cancel₀ hv0 (by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h)
      have hS : (Finset.univ.filter (fun c : F => c ^ (2 ^ 1) = c)).card ≤ 2 ^ 1 :=
        card_le_of_frob_fixed (by norm_num) _ (fun c hc => (Finset.mem_filter.mp hc).2)
      have hEc2 : E.card ≤ 2 := by
        calc E.card = (E.image (fun t => t / v)).card := hcard_image.symm
          _ ≤ (Finset.univ.filter (fun c : F => c ^ (2 ^ 1) = c)).card :=
              Finset.card_le_card hmap
          _ ≤ 2 ^ 1 := hS
          _ = 2 := by norm_num
      omega
    have hE1 : 1 < E.card := by omega
    obtain ⟨v, hvE, hv0⟩ := Finset.exists_mem_ne hE1 0
    have hex : ∃ t ∈ E, (t / v) ^ (2 ^ 1) ≠ t / v := by
      by_contra hall
      push Not at hall
      exact hnotLine ⟨v, hv0, fun t htE => ⟨t / v, hall t htE,
        by rw [div_mul_cancel₀ t hv0]⟩⟩
    obtain ⟨t, htE, htne⟩ := hex
    have hvA' : uElt v ∈ A' := (hE_mem v).mp hvE
    have htA' : uElt t ∈ A' := (hE_mem t).mp htE
    obtain ⟨a, ha2l, hJeq⟩ := exists_sorted_orbit (l := 1) (by norm_num) (by norm_num)
      hJ3 hJne hJn (by simpa [hd_eq] using hshift)
    have ha0 : a = 0 := by omega
    have hJ02 : J = {0, 1, 2} := by simpa [ha0] using hJeq
    have h0J : (0 : ℕ) ∈ J := by rw [hJ02]; simp
    have h1J : (1 : ℕ) ∈ J := by rw [hJ02]; simp
    have ht_eq : t = (t / v) * v := (div_mul_cancel₀ t hv0).symm
    have hdet : (ιF v) ^ (2 ^ 0) * (ιF t) ^ (2 ^ (0 + 1)) ≠
        (ιF t) ^ (2 ^ 0) * (ιF v) ^ (2 ^ (0 + 1)) := by
      intro h
      rw [ht_eq, map_mul, mul_pow] at h
      have h' : (ιF v) ^ 3 * (ιF (t / v)) ^ 2 = (ιF v) ^ 3 * ιF (t / v) := by
        linear_combination h
      have hv3 : (ιF v) ^ 3 ≠ 0 :=
        pow_ne_zero _ ((map_ne_zero ιF).mpr hv0)
      have hu : (ιF (t / v)) ^ 2 = ιF (t / v) :=
        mul_left_cancel₀ hv3 h'
      have hu' : (t / v) ^ 2 = t / v := by
        apply ιF.injective
        simpa [map_pow] using hu
      exact htne hu'
    have hpair := natCard_fixW_pair_le ρ b ιF ιD J hJ3 Φ (a := 0) (b' := 1)
      h0J h1J (by norm_num) hv0 (by simpa using hdet)
    have hC_le : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} ≤
        Nat.card {w : W // ρ (uElt v) w = w ∧ ρ (uElt t) w = w} := by
      refine Nat.card_le_card_of_injective
        (fun w => ⟨w.1, w.2 _ hvA', w.2 _ htA'⟩) ?_
      intro w1 w2 h
      apply Subtype.ext
      exact congrArg (fun z : {w : W // ρ (uElt v) w = w ∧ ρ (uElt t) w = w} =>
        (z : W)) h
    have hCbound : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} ≤ 4 := by
      refine hC_le.trans (hpair.trans ?_)
      rw [hDcard, ← pow_mul, hd_eq]
      norm_num
    rw [hC]
    calc 64 * Nat.card {w : W // ∀ g ∈ A', ρ g w = w}
        ≤ 64 * 4 := Nat.mul_le_mul_left 64 hCbound
      _ = Nat.card W := by rw [hW]; norm_num

  · intro A hA1 hA2 hA8
    obtain ⟨x, hxU⟩ := exists_conj_le_rootGroup A hA2
    let A' : Subgroup SL(2, F) := A.map (MulAut.conj x⁻¹).toMonoidHom
    have hA'le : A' ≤ (upperUnipotent (F := F)).range := by
      rintro g ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hxU a ha
    have hA'2inv : ∀ g ∈ A', g * g = 1 := by
      intro g hg
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
      have h1 : ((MulAut.conj x⁻¹) a) ^ 2 = 1 := by
        rw [pow_two, ← map_mul, hA2 a ha, map_one]
      rw [← hae]
      simpa [pow_two] using h1
    have hmem : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ A' := by
      intro g
      constructor
      · intro hg
        simpa [A', MulAut.conj_apply] using
          Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hg
      · intro hg
        obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
        have : a = g := by
          simpa [MulAut.conj_apply] using congrArg (fun y => x * y * x⁻¹) hae
        simpa [this] using ha
    have hA'card : Nat.card A' = Nat.card A :=
      (Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv).symm
    have hC : Nat.card (fixedSub ρ A) =
        Nat.card {w : W // ∀ a ∈ A', ρ a w = w} := by
      simpa [fixedSub] using natCard_fixed_conj ρ A A' x hmem
    have hA'8 : Nat.card A' = 8 := by rw [hA'card, hA8]
    have hAleF : Nat.card A' ≤ Nat.card F := card_le_of_involutions A' hA'2inv
    have hF8 : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
    have hAeq : Nat.card A' = 2 ^ 3 := by omega
    have hCroot : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} = Nat.card (EndRing ρ) :=
      card_fixed_eq_of_card (n := 3) ρ hF b ιF ιD J hJn Φ A' hA'2inv hAeq
    have hC2 : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} = 2 := by
      rw [hCroot, hDcard, hd_eq]; norm_num
    rw [hC, hC2, hW]
    norm_num



end Numerics

end CFSG.Quasithin.Stroth
