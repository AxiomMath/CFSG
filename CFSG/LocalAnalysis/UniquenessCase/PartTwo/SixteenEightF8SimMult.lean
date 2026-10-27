module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.RankThree.GF2n.Stroth80 CFSG.Open

theorem s16g_hom_eq_one_of_coprime {G C : Type*} [Group G] [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hG : IsPGroup p G) (hpC : ¬ p ∣ Nat.card C) (φ : G →* C) : φ = 1 := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨k, hk⟩ := hG x
  have h1 : orderOf (φ x) ∣ p ^ k := (orderOf_map_dvd φ x).trans (orderOf_dvd_of_pow_eq_one hk)
  have h2 : orderOf (φ x) ∣ Nat.card C := orderOf_dvd_natCard _
  have hc : Nat.Coprime (p ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpC)
  rw [MonoidHom.one_apply]
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hc h1 h2)

theorem s16g_card_le_mul_card_ker {G C : Type*} [Group G] [Group C] [Finite C] (φ : G →* C) :
    Nat.card G ≤ Nat.card C * Nat.card φ.ker := by
  have h2 : Nat.card φ.range ≤ Nat.card C := Nat.card_le_card_of_injective _ Subtype.val_injective
  calc Nat.card G = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card φ.ker * Nat.card C := Nat.mul_le_mul_left _ h2
    _ = Nat.card C * Nat.card φ.ker := mul_comm _ _

private theorem s16g_smul_left_injective {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] {B : Matrix ι ι K} (hB : IsUnit B.det) :
    Function.Injective fun c : K => c • B := by
  intro c c' h
  by_contra hne
  have h0 : (c - c') • B = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.2 h
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact hne (sub_eq_zero.1 h1)
  · rw [h1, Matrix.det_zero] at hB
    exact not_isUnit_zero hB

private theorem s16g_mult_exists {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (GL ι K)} (hΓ : AddCommutantScalar Γ) {B : Matrix ι ι K} (hB : IsUnit B.det)
    (hΓB : ∀ A ∈ Γ, (A : Matrix ι ι K)ᵀ * B * (A : Matrix ι ι K) = B) {g : GL ι K}
    (hg : g ∈ Subgroup.normalizer (Γ : Set (GL ι K))) :
    ∃ c : K, (g : Matrix ι ι K)ᵀ * B * (g : Matrix ι ι K) = c • B := by
  set G : Matrix ι ι K := (g : Matrix ι ι K)ᵀ * B * (g : Matrix ι ι K) with hG
  have hGA : ∀ A ∈ Γ, (A : Matrix ι ι K)ᵀ * G * (A : Matrix ι ι K) = G := by
    intro A hA
    have hA' : g * A * g⁻¹ ∈ Γ := (Subgroup.mem_normalizer_iff.1 hg A).1 hA
    have e : ((g * A * g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) =
        (g : Matrix ι ι K) * (A : Matrix ι ι K) := by
      rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    have h := hΓB _ hA'
    calc (A : Matrix ι ι K)ᵀ * G * (A : Matrix ι ι K)
        = ((g : Matrix ι ι K) * (A : Matrix ι ι K))ᵀ * B *
          ((g : Matrix ι ι K) * (A : Matrix ι ι K)) := by
          simp only [hG, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (((g * A * g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K))ᵀ * B *
          (((g * A * g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K)) := by rw [e]
      _ = (g : Matrix ι ι K)ᵀ * (((g * A * g⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * B *
          ((g * A * g⁻¹ : GL ι K) : Matrix ι ι K)) * (g : Matrix ι ι K) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = G := by rw [h]
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  set T : Matrix ι ι K := B⁻¹ * G with hT
  have hTA : ∀ A ∈ Γ, (A : Matrix ι ι K) * T = T * (A : Matrix ι ι K) := by
    intro A hA
    have hAAi : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : (A : Matrix ι ι K)ᵀ * B = B * ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
      calc (A : Matrix ι ι K)ᵀ * B
          = (A : Matrix ι ι K)ᵀ * B * ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
            rw [hAAi, Matrix.mul_one]
        _ = ((A : Matrix ι ι K)ᵀ * B * (A : Matrix ι ι K)) * ((A⁻¹ : GL ι K) : Matrix ι ι K) :=
            (Matrix.mul_assoc _ _ _).symm
        _ = B * ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hΓB A hA]
    have h2 : B⁻¹ * (A : Matrix ι ι K)ᵀ = ((A⁻¹ : GL ι K) : Matrix ι ι K) * B⁻¹ := by
      calc B⁻¹ * (A : Matrix ι ι K)ᵀ = B⁻¹ * (A : Matrix ι ι K)ᵀ * (B * B⁻¹) := by
            rw [hBi', Matrix.mul_one]
        _ = B⁻¹ * ((A : Matrix ι ι K)ᵀ * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * (B * ((A⁻¹ : GL ι K) : Matrix ι ι K)) * B⁻¹ := by rw [h1]
        _ = ((A⁻¹ : GL ι K) : Matrix ι ι K) * B⁻¹ := by
            rw [← Matrix.mul_assoc B⁻¹ B, hBi, Matrix.one_mul]
    calc (A : Matrix ι ι K) * T = (A : Matrix ι ι K) * (B⁻¹ * ((A : Matrix ι ι K)ᵀ * G *
          (A : Matrix ι ι K))) := by rw [hGA A hA]
      _ = (A : Matrix ι ι K) * ((B⁻¹ * (A : Matrix ι ι K)ᵀ) * G * (A : Matrix ι ι K)) := by
          simp only [Matrix.mul_assoc]
      _ = (A : Matrix ι ι K) * ((((A⁻¹ : GL ι K) : Matrix ι ι K) * B⁻¹) * G *
          (A : Matrix ι ι K)) := by rw [h2]
      _ = ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) * (B⁻¹ * G) *
          (A : Matrix ι ι K) := by simp only [Matrix.mul_assoc]
      _ = T * (A : Matrix ι ι K) := by rw [hAAi, Matrix.one_mul]
  obtain ⟨c, hc⟩ := hΓ (Matrix.mulVecLin T).toAddMonoidHom (fun A hA v => by
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [hTA A hA])
  have hTc : T = c • (1 : Matrix ι ι K) :=
    Matrix.ext_iff_mulVec.2 fun v => by rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact hc v
  refine ⟨c, ?_⟩
  calc G = B * T := (Matrix.mul_nonsing_inv_cancel_left B G hB).symm
    _ = B * (c • (1 : Matrix ι ι K)) := by rw [hTc]
    _ = c • B := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem s16g_exists_mult {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type} [Field K]
    {Γ : Subgroup (GL ι K)} (hΓ : AddCommutantScalar Γ) {B : Matrix ι ι K} (hB : IsUnit B.det)
    (hΓB : ∀ A ∈ Γ, (A : Matrix ι ι K)ᵀ * B * (A : Matrix ι ι K) = B) :
    ∃ μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ,
      (∀ g : ↥(Subgroup.normalizer (Γ : Set (GL ι K))),
        ((g : GL ι K) : Matrix ι ι K)ᵀ * B * ((g : GL ι K) : Matrix ι ι K) = (μ g : K) • B) ∧
      ∀ g : ↥(Subgroup.normalizer (Γ : Set (GL ι K))),
        μ g = 1 ↔ ((g : GL ι K) : Matrix ι ι K)ᵀ * B * ((g : GL ι K) : Matrix ι ι K) = B := by
  have hex : ∀ g : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), ∃ c : K,
      ((g : GL ι K) : Matrix ι ι K)ᵀ * B * ((g : GL ι K) : Matrix ι ι K) = c • B :=
    fun g => s16g_mult_exists hΓ hB hΓB g.2
  choose c hc using hex
  have hinj := s16g_smul_left_injective hB
  have hcne : ∀ g, c g ≠ 0 := by
    intro g h0
    have h1 := hc g
    rw [h0, zero_smul] at h1
    have hg : IsUnit ((g : GL ι K) : Matrix ι ι K).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (g : GL ι K).isUnit
    have hdet : IsUnit
        (((g : GL ι K) : Matrix ι ι K)ᵀ * B * ((g : GL ι K) : Matrix ι ι K)).det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      exact (hg.mul hB).mul hg
    rw [h1, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet
  refine ⟨{ toFun := fun g => Units.mk0 (c g) (hcne g), map_one' := ?_, map_mul' := ?_ },
    fun g => hc g, fun g => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · refine Units.ext (hinj ?_)
    show c 1 • B = (1 : K) • B
    rw [← hc 1]
    simp
  · intro g h
    refine Units.ext (hinj ?_)
    show c (g * h) • B = (c g * c h) • B
    rw [← hc (g * h)]
    calc (((g * h : ↥(Subgroup.normalizer (Γ : Set (GL ι K)))) : GL ι K) : Matrix ι ι K)ᵀ * B *
          (((g * h : ↥(Subgroup.normalizer (Γ : Set (GL ι K)))) : GL ι K) : Matrix ι ι K)
        = ((h : GL ι K) : Matrix ι ι K)ᵀ * (((g : GL ι K) : Matrix ι ι K)ᵀ * B *
          ((g : GL ι K) : Matrix ι ι K)) * ((h : GL ι K) : Matrix ι ι K) := by
          simp only [Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((h : GL ι K) : Matrix ι ι K)ᵀ * (c g • B) * ((h : GL ι K) : Matrix ι ι K) := by
          rw [hc g]
      _ = (c g * c h) • B := by
          rw [Matrix.mul_smul, Matrix.smul_mul, hc h, smul_smul]
  · have h2 : c g = 1 := congrArg Units.val h1
    rw [hc g, h2, one_smul]
  · exact Units.ext (hinj (by show c g • B = (1 : K) • B; rw [← hc g, h1, one_smul]))

theorem s16g_exists_mult_statedSp {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] :
    ∃ μ : ↥(Subgroup.normalizer (StatedSp m K : Set (GL (Fin m ⊕ Fin m) K))) →* Kˣ,
      (∀ g : ↥(Subgroup.normalizer (StatedSp m K : Set (GL (Fin m ⊕ Fin m) K))),
        ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ *
          fromBlocks 0 1 (-1) 0 * ((g : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = (μ g : K) • fromBlocks 0 1 (-1) 0) ∧
      ∀ g : ↥(Subgroup.normalizer (StatedSp m K : Set (GL (Fin m ⊕ Fin m) K))),
        μ g = 1 ↔ (g : GL (Fin m ⊕ Fin m) K) ∈ StatedSp m K := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, hm⟩⟩
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      fromBlocks 0 (-1) 1 0 = 1 := by
    simp [fromBlocks_multiply]
  have hdet : IsUnit (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).det :=
    Matrix.isUnit_det_of_right_inverse hJ
  obtain ⟨μ, h1, h2⟩ := s16g_exists_mult (ι := Fin m ⊕ Fin m) (K := K)
    (addCommutantScalar_statedSp (m := m) (K := K)) (B := fromBlocks 0 1 (-1) 0) hdet
    fun A hA => StatedAPI.mem_statedSp_iff.1 hA
  exact ⟨μ, h1, fun g => (h2 g).trans StatedAPI.mem_statedSp_iff.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
