module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LinA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}

private lemma w135c2_mem_fixV_zpowers {w : W} :
    w ∈ fixV (Subgroup.zpowers t) ↔ t w = w := by
  refine ⟨fun h => h t (Subgroup.mem_zpowers t), fun h x hx => ?_⟩
  have hle : Subgroup.zpowers t ≤ MulAction.stabilizer (MulAut W) w :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
  exact MulAction.mem_stabilizer_iff.mp (hle hx)

private lemma w135c2_char_two (hW : ∀ w : W, w ^ 2 = 1) :
    ∀ x : ↥(LEnd L), x + x = 0 := by
  have h2W : ∀ y : Additive W, y + y = 0 := by
    intro y
    apply Additive.toMul.injective
    simpa [pow_two] using hW (Additive.toMul y)
  intro x
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  change (x : AddMonoid.End (Additive W)) a + (x : AddMonoid.End (Additive W)) a = 0
  exact h2W _

private def w135c2_smul (e : ↥(LEnd L)) (v : W) : W :=
  Additive.toMul ((e : AddMonoid.End (Additive W)) (Additive.ofMul v))

private lemma w135c2_smul_add (e₁ e₂ : ↥(LEnd L)) (v : W) :
    w135c2_smul (e₁ + e₂) v = w135c2_smul e₁ v * w135c2_smul e₂ v := rfl

private lemma w135c2_smul_one (v : W) : w135c2_smul (1 : ↥(LEnd L)) v = v := rfl

private lemma w135c2_smul_neg (e : ↥(LEnd L)) (v : W) :
    w135c2_smul (-e) v = (w135c2_smul e v)⁻¹ := rfl

private lemma w135c2_smul_semilinear (σ : ↥(LEnd L) ≃+* ↥(LEnd L)) (hσ : SemilinearBy t σ)
    (e : ↥(LEnd L)) (v : W) :
    w135c2_smul (σ e) (t v) = t (w135c2_smul e v) := by
  have h := congrArg Additive.toMul (hσ e (Additive.ofMul v))
  simpa [w135c2_smul] using h

private lemma w135c2_exists_add_sigma_eq_one (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥)
    (σ : ↥(LEnd L) ≃+* ↥(LEnd L)) (hσ2 : ∀ φ, σ (σ φ) = φ) (hne : ∃ φ, σ φ ≠ φ) :
    ∃ e0 : ↥(LEnd L), e0 + σ e0 = 1 := by
  classical
  letI : Field ↥(LEnd L) := (w135c2_lend_isField hW hirr).toField
  have h2 := w135c2_char_two (L := L) hW
  obtain ⟨φ, hφ⟩ := hne
  have hc_ne : φ + σ φ ≠ 0 := by
    intro h
    apply hφ
    have h1 : σ φ = -φ := (eq_neg_iff_add_eq_zero).mpr (by rw [add_comm]; exact h)
    have h2' : -φ = φ := (neg_eq_iff_add_eq_zero).mpr (h2 φ)
    rw [h1, h2']
  refine ⟨(φ + σ φ)⁻¹ * φ, ?_⟩
  have hfix : σ (φ + σ φ) = φ + σ φ := by
    rw [map_add, hσ2 φ, add_comm]
  rw [map_mul, map_inv₀, hfix, ← mul_add, inv_mul_cancel₀ hc_ne]

private def w135c2_speiserHom (t : MulAut W) : W →* W where
  toFun w := w * (t w)⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private lemma w135c2_speiserHom_ker (t : MulAut W) :
    (w135c2_speiserHom t).ker = fixV (Subgroup.zpowers t) := by
  ext w
  rw [MonoidHom.mem_ker, w135c2_mem_fixV_zpowers]
  change w * (t w)⁻¹ = 1 ↔ t w = w
  rw [mul_inv_eq_one]
  exact eq_comm

private lemma w135c2_speiserHom_range_le (hW : ∀ w : W, w ^ 2 = 1) (ht2 : orderOf t = 2) :
    (w135c2_speiserHom t).range ≤ fixV (Subgroup.zpowers t) := by
  rintro x ⟨w, rfl⟩
  rw [w135c2_mem_fixV_zpowers]
  have hinv : ∀ z : W, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hW z)
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have httw : ∀ z : W, t (t z) = z := fun z => by
    have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) htt) z
    simpa using h
  change t (w * (t w)⁻¹) = w * (t w)⁻¹
  calc t (w * (t w)⁻¹) = t w * (t (t w))⁻¹ := by rw [map_mul, map_inv]
    _ = t w * w⁻¹ := by rw [httw]
    _ = t w * w := by rw [hinv w]
    _ = w * t w := by rw [mul_comm]
    _ = w * (t w)⁻¹ := by rw [hinv (t w)]

private lemma w135c2_speiserHom_range_ge (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W)
    (σ : ↥(LEnd L) ≃+* ↥(LEnd L)) (hσ : SemilinearBy t σ)
    {e0 : ↥(LEnd L)} (he0 : e0 + σ e0 = 1) :
    fixV (Subgroup.zpowers t) ≤ (w135c2_speiserHom t).range := by
  intro v hv
  rw [w135c2_mem_fixV_zpowers] at hv
  have h2 := w135c2_char_two (L := L) hW
  refine ⟨w135c2_smul e0 v, ?_⟩
  change w135c2_smul e0 v * (t (w135c2_smul e0 v))⁻¹ = v
  rw [← w135c2_smul_semilinear σ hσ e0 v, hv]
  rw [← w135c2_smul_neg (L := L) (σ e0) v, ← w135c2_smul_add (L := L)]
  have hneg : -(σ e0) = σ e0 := (neg_eq_iff_add_eq_zero).mpr (h2 (σ e0))
  rw [hneg, he0, w135c2_smul_one]

theorem w135c2_semilinear (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) (ht2 : orderOf t = 2)
    {k : ℕ} (hk : Nat.card ↥(LEnd L) = 2 ^ k) (σ : ↥(LEnd L) ≃+* ↥(LEnd L))
    (hσ : SemilinearBy t σ) (hσ2 : ∀ φ, σ (σ φ) = φ) (hne : ∃ φ, σ φ ≠ φ) :
    Even k ∧ rk W = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  letI : Field ↥(LEnd L) := (w135c2_lend_isField hW hirr).toField
  haveI : Finite (AddMonoid.End (Additive W)) := DFunLike.finite _
  haveI : Finite ↥(LEnd L) := inferInstance
  have hσsq : σ * σ = 1 := by
    apply RingEquiv.ext
    intro φ
    simpa using hσ2 φ
  have hσne : σ ≠ 1 := by
    intro h
    obtain ⟨φ, hφ⟩ := hne
    exact hφ (by simpa using congrArg (fun f : ↥(LEnd L) ≃+* ↥(LEnd L) => f φ) h)
  have hEven : Even k := by
    haveI : Finite (↥(LEnd L) ≃+* ↥(LEnd L)) := by
      refine Finite.of_injective
        (fun f : ↥(LEnd L) ≃+* ↥(LEnd L) => (f : ↥(LEnd L) → ↥(LEnd L))) ?_
      intro a b h
      exact RingEquiv.ext (congrFun h)
    haveI : Fintype ↥(Subgroup.zpowers σ) := Fintype.ofFinite _
    have hcardσ : Fintype.card ↥(Subgroup.zpowers σ) = 2 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
      exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hσne
    have hfinrank : Module.finrank (FixedPoints.subfield (Subgroup.zpowers σ) ↥(LEnd L))
        ↥(LEnd L) = 2 := by
      rw [FixedPoints.finrank_eq_card, hcardσ]
    have hcardE : Nat.card ↥(LEnd L) =
        Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) ↥(LEnd L)) ^ 2 := by
      rw [Module.natCard_eq_pow_finrank
        (K := FixedPoints.subfield (Subgroup.zpowers σ) ↥(LEnd L)) (V := ↥(LEnd L)), hfinrank]
    have hdvd : Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) ↥(LEnd L)) ∣ 2 ^ k := by
      rw [← hk, hcardE, pow_two]
      exact dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hk2 : 2 ^ k = 2 ^ (2 * j) := by
      rw [← hk, hcardE, hj, pow_two, ← pow_add, ← two_mul]
    have hk_eq : k = 2 * j := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hk2
    exact ⟨j, by omega⟩
  refine ⟨hEven, ?_⟩
  set C : Subgroup W := fixV (Subgroup.zpowers t) with hC
  have hker : (w135c2_speiserHom t).ker = C := by
    rw [hC]; exact w135c2_speiserHom_ker t
  have hrange : (w135c2_speiserHom t).range = C := by
    rw [hC]
    apply le_antisymm
    · exact w135c2_speiserHom_range_le hW ht2
    · obtain ⟨e0, he0⟩ := w135c2_exists_add_sigma_eq_one (L := L) hW hirr σ hσ2 hne
      exact w135c2_speiserHom_range_ge (L := L) hW t σ hσ he0
  have hcardW : Nat.card W = Nat.card ↥C * Nat.card ↥C := by
    have h := Subgroup.card_ker_mul_card_range (w135c2_speiserHom t)
    rw [hker, hrange] at h
    exact h.symm
  have hcardWpow := w135_card_eq_two_pow_rk hW
  have hcardCpow := card_eq_two_pow (V := W) hW C
  have hrk : rk W = 2 * rk ↥C := by
    have hpow : 2 ^ rk W = 2 ^ (2 * rk ↥C) := by
      rw [← hcardWpow, hcardW, hcardCpow, ← pow_add, ← two_mul]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hmQuot : E3.mQuot ⊤ C = rkIdx C := by
    unfold E3.mQuot rkIdx
    rw [Subgroup.relIndex_top_right]
  have hrkIdx : rkIdx C = rk ↥C := by
    have h := rk_add_rkIdx (G := W) C
    omega
  rw [hrk, hmQuot, hrkIdx]

end CFSG.LocalAnalysis.WeakClosure81
