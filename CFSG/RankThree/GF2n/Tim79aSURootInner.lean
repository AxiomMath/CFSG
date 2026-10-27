module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.Open

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem radVec_conj_uTrans {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (Θ : SUThetaFacts σ a d T) {v : Fin m → F} (hvP : v ∈ perpPair σ a d)
    (hvv : uForm σ v v = 0) {c : F} {t : SU σ m} (ht : suMat σ m t = uTrans σ v c)
    {x : SU σ m} (hx : x ∈ uRad σ a) :
    radVec σ a d (t * x * t⁻¹) = radVec σ a d x + (c * uForm σ v (radVec σ a d x)) • v := by
  have hta : suMat σ m t *ᵥ a = (1 : F) • a := by rw [Θ.transv_a hvP ht, one_smul]
  rw [Θ.conj hta hx, map_one, one_smul, Θ.levAct_transv hvP hvv ht (Θ.mem_perp x)]

theorem rootInnerModel_su_of_s2 [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {K : Type} [Group K]
    {Φ : SU σ m →* K} (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {a d : Fin m → F}
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) (haa : uForm σ a a = 0)
    (had : uForm σ a d = 1) (Θ : SUThetaFacts σ a d T) (G : SUGeomFacts σ a d)
    (hcore : pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (uRad σ a).map Φ) (hS2 : RootS2Model K (T.map Φ)) : RootInnerModel K (T.map Φ) := by
  intro α hfix hN
  obtain ⟨s, hs, rfl⟩ :=
    hS2 α hfix fun b hb => hN b (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hb)
  refine ⟨s, ?_, rfl⟩
  rw [hcore] at hs
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hs
  refine Subgroup.mem_map_of_mem Φ ((Θ.eq_zero_iff hz).1 ?_)
  by_contra hw0
  have hwP : radVec σ a d z ∈ perpPair σ a d := Θ.mem_perp z
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  obtain ⟨v, hvP, hvv, hvw⟩ := G.nonorth hwP hw0
  obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hvv h1
  have htL : t ∈ uLine σ a := ⟨1, one_ne_zero, by rw [Θ.transv_a hvP ht, one_smul]⟩
  have htN : t ∈ Subgroup.normalizer (T : Set (SU σ m)) := by
    rw [normalizer_eq_uLine hσ ha0 hT]
    exact htL
  have hΦt : Φ t ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) :=
    Subgroup.le_normalizer_map Φ (Subgroup.mem_map_of_mem Φ htN)
  have hy := hN (Φ t) hΦt
  rw [MulAut.conj_apply] at hy
  have hy' : Φ (t⁻¹ * z * t * z⁻¹) ∈ T.map Φ := by
    rw [show Φ (t⁻¹ * z * t * z⁻¹) = (Φ t)⁻¹ * (Φ z * Φ t * (Φ z)⁻¹) by
      simp only [map_mul, map_inv, mul_assoc]]
    exact hy
  obtain ⟨τ, hτ, hτy⟩ := Subgroup.mem_map.1 hy'
  have hkc : τ⁻¹ * (t⁻¹ * z * t * z⁻¹) ∈ Subgroup.center (SU σ m) :=
    hker (MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hτy, inv_mul_cancel]))
  have hτR : τ ∈ uRad σ a := le_uRad_of_isUTransGroup haa hT hτ
  have hzt : t⁻¹ * z * t ∈ uRad σ a := by
    have := conj_mem_uRad (inv_mem htL) hz
    rwa [inv_inv] at this
  have hyR : t⁻¹ * z * t * z⁻¹ ∈ uRad σ a := mul_mem hzt (inv_mem hz)
  have hkR : τ⁻¹ * (t⁻¹ * z * t * z⁻¹) ∈ uRad σ a := mul_mem (inv_mem hτR) hyR
  have hθ1 : radVec σ a d (t⁻¹ * z * t) =
      radVec σ a d z + (-1 * uForm σ v (radVec σ a d z)) • v := by
    have := radVec_conj_uTrans Θ hvP hvv (suMat_inv_of_eq hvv ht) hz
    rwa [inv_inv] at this
  have hθy : radVec σ a d (t⁻¹ * z * t * z⁻¹) = (-1 * uForm σ v (radVec σ a d z)) • v := by
    rw [Θ.mul hzt (inv_mem hz), hθ1, Θ.inv hz]
    abel
  have hθk : radVec σ a d (τ⁻¹ * (t⁻¹ * z * t * z⁻¹)) =
      (-1 * uForm σ v (radVec σ a d z)) • v := by
    rw [Θ.mul (inv_mem hτR) hyR, Θ.inv hτR, (Θ.eq_zero_iff hτR).2 hτ, neg_zero, zero_add, hθy]
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at hvw
  obtain ⟨v', hv'P, hv'v', hvv'⟩ := G.partner hvP hv0 hvv
  obtain ⟨t', ht'⟩ := exists_suMat_eq_uTrans hσ hv'v' h1
  have h3 := radVec_conj_uTrans Θ hv'P hv'v' ht' hkR
  rw [Subgroup.mem_center_iff.1 hkc t', mul_inv_cancel_right] at h3
  have hv'0 : v' ≠ 0 := by
    rintro rfl
    rw [uForm_zero_right] at hvv'
    exact zero_ne_one hvv'
  have h5 := (smul_eq_zero.1 (left_eq_add.1 h3)).resolve_right hv'0
  have hv'v : uForm σ v' v = 1 := by rw [← uForm_conj σ hσ v v', hvv', map_one]
  rw [hθk, uForm_smul_right, hv'v] at h5
  exact hvw (by linear_combination -h5)

end CFSG.RankThree.GF2n.Tim79a
