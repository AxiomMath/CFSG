module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

@[expose] def IsLin625 (m : Subgroup.normalizer (V : Set G)) : Prop :=
  ∀ (c : h.data.K) (w : Fin 2 → h.data.K), h.data.conj m (c • w) = c • h.data.conj m w

@[expose] noncomputable def det625 (m : Subgroup.normalizer (V : Set G)) : h.data.K :=
  det2 (h.data.conj m ![1, 0]) (h.data.conj m ![0, 1])

theorem conj_one_ch625 (w : Fin 2 → h.data.K) : h.data.conj 1 w = w :=
  h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _) w

theorem conj_inv_conj_ch625 (m : Subgroup.normalizer (V : Set G)) (w : Fin 2 → h.data.K) :
    h.data.conj m⁻¹ (h.data.conj m w) = w := by
  rw [← h.data.conj_mul, inv_mul_cancel, h.conj_one_ch625]

theorem conj_conj_inv_ch625 (m : Subgroup.normalizer (V : Set G)) (w : Fin 2 → h.data.K) :
    h.data.conj m (h.data.conj m⁻¹ w) = w := by
  rw [← h.data.conj_mul, mul_inv_cancel, h.conj_one_ch625]

theorem semilinear_cases_ch625 (m : Subgroup.normalizer (V : Set G))
    (hmL : (m : G) ∈ Subgroup.normalizer (L : Set G)) :
    h.IsLin625 m ∨ ∀ (c : h.data.K) w, h.data.conj m (c • w) = c ^ 2 • h.data.conj m w := by
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear m hmL
  rcases ringAut_ch625 h.card_K_ch625 σ with h1 | h1
  · left
    intro c w
    rw [hσ, h1]
  · right
    intro c w
    rw [hσ, h1]

theorem det2_conj_lin_ch625 {m : Subgroup.normalizer (V : Set G)} (hm : h.IsLin625 m)
    (x y : Fin 2 → h.data.K) :
    det2 (h.data.conj m x) (h.data.conj m y) = det2 x y * h.det625 m :=
  det2_semilinear (σ := RingHom.id _) (fun v w => map_add _ v w) hm x y

theorem det2_conj_frob_ch625 {m : Subgroup.normalizer (V : Set G)}
    (hm : ∀ (c : h.data.K) w, h.data.conj m (c • w) = c ^ 2 • h.data.conj m w)
    (x y : Fin 2 → h.data.K) :
    det2 (h.data.conj m x) (h.data.conj m y) = det2 x y ^ 2 * h.det625 m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP h.data.K 2 := by
    rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
    exact_mod_cast two_eq_zero_ch625 h.card_K_ch625
  exact det2_semilinear (σ := frobenius h.data.K 2) (fun v w => map_add _ v w)
    (fun c v => by rw [hm, frobenius_def]) x y

theorem det625_ne_zero (m : Subgroup.normalizer (V : Set G))
    (hmL : (m : G) ∈ Subgroup.normalizer (L : Set G)) : h.det625 m ≠ 0 := by
  intro h0
  have hne : h.data.conj m ![1, 0] ≠ 0 := by
    intro h1
    have := (h.data.conj m).injective (h1.trans (map_zero _).symm)
    have := congrFun this 0
    simp at this
  obtain ⟨c, hc⟩ := exists_eq_smul_of_det2_eq_zero hne h0
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear m hmL
  have h1 : h.data.conj m ![0, 1] = h.data.conj m (σ.symm c • ![1, 0]) := by
    rw [hσ, RingEquiv.apply_symm_apply]
    exact hc
  have h2 := congrFun ((h.data.conj m).injective h1) 1
  simp at h2

theorem isLin625_and_det_of_mem_L (m : Subgroup.normalizer (V : Set G)) (hmL : (m : G) ∈ L) :
    h.IsLin625 m ∧ h.det625 m = 1 := by
  obtain ⟨A, hA⟩ := h.data.exists_matrix_of_mem m hmL
  refine ⟨fun c w => by rw [hA, hA, Matrix.mulVec_smul], ?_⟩
  have h1 := det2_semilinear (σ := RingHom.id h.data.K)
    (f := fun v => (A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec v)
    (fun v w => Matrix.mulVec_add _ v w) (fun c v => Matrix.mulVec_smul _ c v) ![1, 0] ![0, 1]
  have hdet : det2 ((A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![1, 0])
      ((A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![0, 1]) = 1 := by
    have := det_basisMat ((A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![1, 0])
      ((A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![0, 1])
    rw [← this]
    have e : basisMat ((A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![1, 0])
        ((A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![0, 1]) =
          (A : Matrix (Fin 2) (Fin 2) h.data.K) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [basisMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e, A.2]
  unfold det625
  rw [hA, hA]
  exact hdet

theorem exists_eq_smul_conj_ch625 (m : Subgroup.normalizer (V : Set G))
    (hmL : (m : G) ∈ Subgroup.normalizer (L : Set G)) (hm : h.IsLin625 m) :
    ∃ y : Subgroup.normalizer (V : Set G), (y : G) ∈ L ∧ ∃ μ : h.data.K, μ ≠ 0 ∧
      μ ^ 2 = h.det625 m ∧ ∀ w, h.data.conj m w = μ • h.data.conj y w := by
  have hK := h.card_K_ch625
  set a := h.data.conj m ![1, 0] with ha
  set b := h.data.conj m ![0, 1] with hb
  have hdab : det2 a b ≠ 0 := h.det625_ne_zero m hmL
  set μ := (det2 a b) ^ 2 with hμ
  have hμ0 : μ ≠ 0 := pow_ne_zero _ hdab
  have hμ2 : μ ^ 2 = det2 a b := sq_sq_ch625 hK _
  have hdet : det2 (μ⁻¹ • a) (μ⁻¹ • b) = det2 (![1, 0] : Fin 2 → h.data.K) ![0, 1] := by
    rw [det2_smul_left_ch625, det2_smul_right_ch625, det2_e_ch625, ← hμ2]
    field_simp
  obtain ⟨B, hB1, hB2⟩ := exists_sl2_basis (by rw [det2_e_ch625]; exact one_ne_zero) hdet
  obtain ⟨y, hyL, hy⟩ := h.data.exists_mem_of_matrix B
  refine ⟨y, hyL, μ, hμ0, hμ2, fun w => ?_⟩
  have hmw : h.data.conj m w = w 0 • a + w 1 • b := by
    conv_lhs => rw [eq_basis_ch625 w]
    rw [map_add, hm, hm]
  have hyw : h.data.conj y w = w 0 • (μ⁻¹ • a) + w 1 • (μ⁻¹ • b) := by
    conv_lhs => rw [eq_basis_ch625 w]
    rw [hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hB1, hB2]
  have e1 : ∀ (c : h.data.K) (u : Fin 2 → h.data.K), μ • (c • (μ⁻¹ • u)) = c • u := by
    intro c u
    rw [smul_smul, smul_smul, mul_comm μ c, mul_assoc, mul_inv_cancel₀ hμ0, mul_one]
  rw [hmw, hyw, smul_add, e1, e1]

theorem mem_pCoreOf_of_mem_centralizer_ch625 {z : G} (hzL : z ∈ L)
    (hzC : z ∈ Subgroup.centralizer (V : Set G)) : z ∈ pCoreOf 2 L :=
  h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨z, hzL⟩) ((h.data.mem_ker_rho_iff _).mpr hzC)

theorem comm_mem_centralizer_of_smul_ch625 (n : Subgroup.normalizer (V : Set G)) {μ : h.data.K}
    (hμ : μ ≠ 0) (hn : ∀ w, h.data.conj n w = μ • w) {z : G} (hz : z ∈ L) :
    (n : G) * z * (n : G)⁻¹ * z⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  set zz : Subgroup.normalizer (V : Set G) := ⟨z, h.toHyp611.L_le_normalizer hz⟩ with hzz
  have hlin := (h.isLin625_and_det_of_mem_L zz hz).1
  have hninv : ∀ w, h.data.conj n⁻¹ w = μ⁻¹ • w := by
    intro w
    apply (h.data.conj n).injective
    rw [h.conj_conj_inv_ch625, hn, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  have e : ((n * zz * n⁻¹ * zz⁻¹ : Subgroup.normalizer (V : Set G)) : G) =
      (n : G) * z * (n : G)⁻¹ * z⁻¹ := rfl
  rw [← e]
  apply h.data.mem_centralizer_of_conj_eq
  intro w
  rw [h.data.conj_mul, h.data.conj_mul, h.data.conj_mul, hninv, hlin, hn, smul_smul,
    mul_inv_cancel₀ hμ, one_smul, h.conj_conj_inv_ch625]

theorem not_isLin625_of_fieldAut {t : G} (htN : t ∈ Subgroup.normalizer (V : Set G))
    (ht : IsInvolutoryFieldAut L t) : ¬ h.IsLin625 ⟨t, htN⟩ := by
  intro hlin
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, htN⟩ with htt
  obtain ⟨y, hyL, μ, hμ0, -, hty⟩ := h.exists_eq_smul_conj_ch625 tt ht.1 hlin
  have hylin := (h.isLin625_and_det_of_mem_L y hyL).1
  set n : Subgroup.normalizer (V : Set G) := y⁻¹ * tt with hndef
  have hnG : (n : G) = (y : G)⁻¹ * t := rfl
  have hn : ∀ w, h.data.conj n w = μ • w := by
    intro w
    have h1 : h.data.conj y (h.data.conj n w) = h.data.conj y (μ • w) := by
      rw [← h.data.conj_mul, hndef, mul_inv_cancel_left, hty, hylin]
    exact (h.data.conj y).injective h1
  apply ht.2.2
  refine ⟨y, hyL, fun x hx => ?_⟩
  have hc := h.comm_mem_centralizer_of_smul_ch625 n hμ0 hn hx
  rw [hnG] at hc
  have hyV : (y : G) ∈ Subgroup.normalizer (V : Set G) := y.2
  have hc' := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62 hyV) _).mp hc
  have e : (y : G) * ((y : G)⁻¹ * t * x * ((y : G)⁻¹ * t)⁻¹ * x⁻¹) * (y : G)⁻¹ =
      t * x * t⁻¹ * ((y : G) * x * (y : G)⁻¹)⁻¹ := by group
  rw [e] at hc'
  have hL : t * x * t⁻¹ * ((y : G) * x * (y : G)⁻¹)⁻¹ ∈ L := by
    have h1 : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht.1 x).mp hx
    have h2 : (y : G) * x * (y : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL hx) (L.inv_mem hyL)
    exact L.mul_mem h1 (L.inv_mem h2)
  exact h.mem_pCoreOf_of_mem_centralizer_ch625 hL hc'

theorem isInvolutoryFieldAut_of_not_lin {t : G} (htM : t ∈ ch6MV M V)
    {x y : Fin 2 → h.data.K} (hxy : det2 x y ≠ 0)
    (hx : h.data.conj ⟨t, htM.2⟩ x = x) (hy : h.data.conj ⟨t, htM.2⟩ y = y)
    (hlin : ¬ h.IsLin625 ⟨t, htM.2⟩) : IsInvolutoryFieldAut L t := by
  have hK := h.card_K_ch625
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, htM.2⟩ with htt
  have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal htM.1
  have hfrob := (h.semilinear_cases_ch625 tt htL).resolve_left hlin
  have ht2 : (t ^ 2 : G) ∈ Subgroup.centralizer (V : Set G) := by
    have e : ((tt * tt : Subgroup.normalizer (V : Set G)) : G) = t ^ 2 := by
      simp [htt, pow_two]
    rw [← e]
    apply h.data.mem_centralizer_of_conj_eq
    intro w
    rw [h.data.conj_mul]
    conv_lhs => rw [eq_add_of_det2_ne_zero hxy w]
    rw [map_add, map_add, hfrob, hfrob, hfrob, hfrob]
    simp only [hx, hy]
    rw [sq_sq_ch625 hK, sq_sq_ch625 hK, ← eq_add_of_det2_ne_zero hxy w]
  refine ⟨htL, fun z hz => ?_, ?_⟩
  · have hsN : t ^ 2 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ htL 2
    exact h.toHyp611Nat.commutator_mem_pCoreOf hsN ht2 hz
  · rintro ⟨y', hy'L, hy'⟩
    set yy : Subgroup.normalizer (V : Set G) := ⟨y', h.toHyp611.L_le_normalizer hy'L⟩ with hyy
    have hn : ∀ z ∈ L, ((yy⁻¹ * tt : Subgroup.normalizer (V : Set G)) : G) * z *
        ((yy⁻¹ * tt : Subgroup.normalizer (V : Set G)) : G)⁻¹ * z⁻¹ ∈
          Subgroup.centralizer (V : Set G) := by
      intro z hz
      have h1 := h.toHyp611.pCoreOf_le_centralizer (hy' z hz)
      have hyV : (y'⁻¹ : G) ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.inv_mem _ (h.toHyp611.L_le_normalizer hy'L)
      have h2 := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62 hyV) _).mp h1
      have e : y'⁻¹ * (t * z * t⁻¹ * (y' * z * y'⁻¹)⁻¹) * y'⁻¹⁻¹ =
          ((yy⁻¹ * tt : Subgroup.normalizer (V : Set G)) : G) * z *
            ((yy⁻¹ * tt : Subgroup.normalizer (V : Set G)) : G)⁻¹ * z⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, htt, hyy]
        group
      rwa [e] at h2
    obtain ⟨c, hc⟩ := h.data.exists_conj_eq_smul (yy⁻¹ * tt) hn
    apply hlin
    have hylin := (h.isLin625_and_det_of_mem_L yy hy'L).1
    intro d w
    have ht' : ∀ v, h.data.conj tt v = h.data.conj yy (c • v) := by
      intro v
      rw [← hc, h.data.conj_mul, h.conj_conj_inv_ch625]
    rw [ht', ht', smul_comm, hylin]

theorem isFieldType_iff_ch625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4) :
    IsFieldType M L V F 1 ↔ ∃ t ∈ ch6MV M V, t ∈ Subgroup.centralizer (F : Set G) ∧
      ∃ htN : t ∈ Subgroup.normalizer (V : Set G), ¬ h.IsLin625 ⟨t, htN⟩ := by
  have hK := h.card_K_ch625
  constructor
  · rintro ⟨-, -, t, htM, ht, htF⟩
    rw [conjSubgroup_one] at htM ht
    exact ⟨t, htM, htF, htM.2, h.not_isLin625_of_fieldAut htM.2 ht⟩
  · rintro ⟨t, htM, htF, htN, hlin⟩
    set tt : Subgroup.normalizer (V : Set G) := ⟨t, htN⟩ with htt
    have hfix : ∀ w, h.vec625 w ∈ F → h.data.conj tt w = w := by
      intro w hw
      apply h.vec625_injective
      rw [← h.conj_vec625]
      have := Subgroup.mem_centralizer_iff.mp htF _ hw
      calc t * h.vec625 w * t⁻¹ = h.vec625 w * t * t⁻¹ := by rw [← this]
        _ = h.vec625 w := by group
    have hfrob := (h.semilinear_cases_ch625 tt (h.normal htM.1)).resolve_left hlin
    rcases h.four_cases_ch625 hFV hF4 with ⟨v, hv0, hv⟩ | ⟨x, y, hxy, hP⟩
    ·
      exfalso
      obtain ⟨ω, hω⟩ : ∃ ω : h.data.K, ω ^ 2 ≠ ω := by
        by_contra hcon
        push Not at hcon
        have hsub : ∀ c : h.data.K, c = 0 ∨ c = 1 := fun c => by
          rcases sq_add_self_ch625 hK c with h0 | h0
          · exact eq_zero_or_one_ch625 hK h0
          · exfalso
            rw [hcon c, add_self_ch625 hK] at h0
            exact zero_ne_one h0
        have := Fintype.ofFinite h.data.K
        have hcard : Fintype.card h.data.K ≤ 2 := by
          classical
          calc Fintype.card h.data.K = (Finset.univ : Finset h.data.K).card := rfl
            _ ≤ ({0, 1} : Finset h.data.K).card := Finset.card_le_card fun c _ => by
                rcases hsub c with rfl | rfl <;> simp
            _ ≤ 2 := Finset.card_le_two
        rw [← Nat.card_eq_fintype_card, hK] at hcard
        omega
      have h1 := hfix (ω • v) ((hv (ω • v)).mpr ⟨ω, rfl⟩)
      rw [hfrob, hfix v ((hv v).mpr ⟨1, (one_smul _ v).symm⟩)] at h1
      apply hω
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
      exact mul_right_cancel₀ hi this
    · have hinv := h.isInvolutoryFieldAut_of_not_lin htM hxy
        (hfix x ((hP x).mpr (Or.inr (Or.inl rfl))))
        (hfix y ((hP y).mpr (Or.inr (Or.inr (Or.inl rfl))))) hlin
      refine ⟨?_, hF4, t, ?_, ?_, htF⟩
      · rw [conjSubgroup_one]; exact hFV
      · rw [conjSubgroup_one]; exact htM
      · rw [conjSubgroup_one]; exact hinv

end Hyp6Sec2

end CFSG.Quasithin.H13
