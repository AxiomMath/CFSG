module

public import CFSG.Quasithin.Vol2.Ch6Offender
public import CFSG.Quasithin.Background.A4Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

section Torus

variable {F : Type} [Field F] [Finite F]

theorem exists_torus (hF : 2 ∣ Nat.card F) {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ u : Fin 2 → F, det2 v u ≠ 0 ∧ ∀ μ : F, μ ≠ 0 →
      ∃ D : Matrix.SpecialLinearGroup (Fin 2) F, Odd (orderOf D) ∧
        (D : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v ∧
        (D : Matrix (Fin 2) (Fin 2) F).mulVec u = μ⁻¹ • u := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  refine ⟨(B : Matrix (Fin 2) (Fin 2) F).mulVec ![0, 1], ?_, fun μ hμ => ?_⟩
  · have hdet := Matrix.SpecialLinearGroup.det_coe B
    rw [Matrix.det_fin_two] at hdet
    rw [← hB]
    simp only [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add]
    intro h0
    apply one_ne_zero (α := F)
    rw [← hdet]
    linear_combination h0
  · let X : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Matrix.diagonal ![μ, μ⁻¹], by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp [hμ]⟩
    have hXv : ∀ w : Fin 2 → F,
        (X : Matrix (Fin 2) (Fin 2) F).mulVec w = ![μ * w 0, μ⁻¹ * w 1] := by
      intro w
      change (Matrix.diagonal ![μ, μ⁻¹]).mulVec w = _
      funext i
      rw [Matrix.mulVec_diagonal]
      fin_cases i <;> simp
    refine ⟨B * X * B⁻¹, ?_, ?_, ?_⟩
    · have hX1 : X ^ (Fintype.card F - 1) = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
        change (Matrix.diagonal ![μ, μ⁻¹]) ^ (Fintype.card F - 1) = 1
        rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
        congr 1
        funext i
        fin_cases i
        · simp [FiniteField.pow_card_sub_one_eq_one μ hμ]
        · simp [FiniteField.pow_card_sub_one_eq_one μ⁻¹ (inv_ne_zero hμ)]
      have hpow : (B * X * B⁻¹) ^ (Fintype.card F - 1) = 1 := by
        rw [conj_pow, hX1, mul_one, mul_inv_cancel]
      have hodd : Odd (Fintype.card F - 1) := by
        have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
        rw [← Nat.card_eq_fintype_card] at hpos ⊢
        obtain ⟨m, hm⟩ := hF
        rw [hm]
        have : 1 ≤ 2 * m := hm ▸ hpos
        exact ⟨m - 1, by omega⟩
      exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hB, inv_mulVec_mulVec, hXv,
        ← Matrix.mulVec_smul]
      congr 1
      funext i
      fin_cases i <;> simp
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_mulVec_mulVec, hXv,
        ← Matrix.mulVec_smul]
      congr 1
      funext i
      fin_cases i <;> simp

end Torus

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem Hyp611.eq_oTwoUpper (h : Hyp611 G T M L V n) : L = oTwoUpper L :=
  (eq_oTwoUpper_iff_forall_normal L).mpr h.faithful.2.1

namespace Hyp611Nat

theorem mem_normalizer_ZS_of_rho (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K}
    (hv : v ≠ 0) (hle : h.rhoTL ≤ sl2Stab v) (g : ↥L) {μ : h.data.K} (hμ : μ ≠ 0)
    (hg : ((h.data.rho g : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
      Matrix (Fin 2) (Fin 2) h.data.K).mulVec v = μ • v) :
    (g : G) ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := h.data.le_normalizer g.2
  set m : Subgroup.normalizer (V : Set G) := ⟨g, hgN⟩ with hm
  have hconj : ∀ x : ↥V, Multiplicative.toAdd (h.data.E (conjAct V m x)) =
      ((h.data.rho g : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec (Multiplicative.toAdd (h.data.E x)) := by
    intro x
    rw [← h.data.conj_apply]
    exact h.data.conj_eq_rho g _
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have hzV : z ∈ V := hz.1
    obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hzV⟩).mp hz
    have hmem := (h.mem_ZS_iff_line hv hle (conjAct V m ⟨z, hzV⟩)).mpr
      ⟨c * μ, by rw [hconj, hc, Matrix.mulVec_smul, hg, smul_smul]⟩
    rw [conjAct_apply_coe] at hmem
    exact hmem
  · intro hz
    have hzV : z ∈ V := (Subgroup.mem_normalizer_iff.mp hgN z).mpr hz.1
    have hz' : ((conjAct V m ⟨z, hzV⟩ : ↥V) : G) ∈ ch6ZS T L V := by
      rw [conjAct_apply_coe]
      exact hz
    obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle _).mp hz'
    rw [hconj] at hc
    refine (h.mem_ZS_iff_line hv hle ⟨z, hzV⟩).mpr ⟨c / μ, ?_⟩
    set R := ((h.data.rho g : Matrix.SpecialLinearGroup (Fin 2) h.data.K))
    have h1 : (R : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ((c / μ) • v) = c • v := by
      rw [Matrix.mulVec_smul, hg, smul_smul, div_mul_cancel₀ _ hμ]
    rw [← inv_mulVec_mulVec R (Multiplicative.toAdd (h.data.E ⟨z, hzV⟩)), hc, ← h1,
      inv_mulVec_mulVec]

theorem exists_mem_lOne (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K}
    (hv : v ≠ 0) (hle : h.rhoTL ≤ sl2Stab v) {D : Matrix.SpecialLinearGroup (Fin 2) h.data.K}
    (hD : Odd (orderOf D)) {μ : h.data.K} (hμ : μ ≠ 0)
    (hDv : (D : Matrix (Fin 2) (Fin 2) h.data.K).mulVec v = μ • v) :
    ∃ ℓ : ↥L, (ℓ : G) ∈ lOne L (ch6ZS T L V) ∧ h.data.rho ℓ = D := by
  obtain ⟨g, hg⟩ := h.data.rho_surjective D
  have hgN : (g : G) ∈ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    h.mem_normalizer_ZS_of_rho hv hle g hμ (by rw [hg]; exact hDv)
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G))
    (show (g : G) ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) from ⟨g.2, hgN⟩)
  have hcop : Nat.Coprime (2 ^ k) (orderOf D) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hD)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (A4.mem_zpowers_pow_of_coprime hcop)
  refine ⟨(g ^ 2 ^ k) ^ j, ?_, ?_⟩
  · have : (((g ^ 2 ^ k) ^ j : ↥L) : G) = ((g : G) ^ 2 ^ k) ^ j := by
      rw [Subgroup.coe_zpow, Subgroup.coe_pow]
    rw [this]
    exact Subgroup.zpow_mem _ hk j
  · rw [map_zpow, map_pow, hg, hj]

theorem irred (h : Hyp611Nat G T M L V n) :
    IsIrredOnSection (lOne L (ch6ZS T L V) ⊔ T) V (ch6ZS T L V) := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨u, hdet, htor⟩ := exists_torus h.two_dvd_card_K hv
  have hlOne : lOne L (ch6ZS T L V) ≤ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    oTwoUpper_le _
  have hXV : lOne L (ch6ZS T L V) ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hlOne.trans (inf_le_left.trans h.data.le_normalizer)) h.toHyp611.T_le_normalizer
  have hXZ : lOne L (ch6ZS T L V) ⊔ T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    sup_le (hlOne.trans inf_le_right) h.T_le_normalizer_ZS
  let P : Subgroup G → (Fin 2 → h.data.K) → Prop := fun W y =>
    ((h.data.E.symm (Multiplicative.ofAdd y) : ↥V) : G) ∈ W
  have hPE : ∀ (W : Subgroup G) (x : ↥V), (x : G) ∈ W ↔ P W (Multiplicative.toAdd (h.data.E x)) :=
    fun W x => by simp only [P, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hPadd : ∀ (W : Subgroup G) {y y' : Fin 2 → h.data.K}, P W y → P W y' → P W (y + y') := by
    intro W y y' hy hy'
    simp only [P, ofAdd_add, map_mul, Subgroup.coe_mul]
    exact W.mul_mem hy hy'
  have hPneg : ∀ (W : Subgroup G) {y : Fin 2 → h.data.K}, P W y → P W (-y) := by
    intro W y hy
    simp only [P, ofAdd_neg, map_inv, Subgroup.coe_inv]
    exact W.inv_mem hy
  have hPZ : ∀ c : h.data.K, P (ch6ZS T L V) (c • v) := by
    intro c
    refine (h.mem_ZS_iff_line hv hle _).mpr ⟨c, ?_⟩
    simp
  have hu : ¬ P (ch6ZS T L V) u := by
    intro hz
    obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle _).mp hz
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hc
    apply hdet
    rw [hc]
    simp only [det2, Pi.smul_apply, smul_eq_mul]
    ring
  have hZV : ch6ZS T L V ≠ V := by
    intro heq
    apply hu
    show ((h.data.E.symm (Multiplicative.ofAdd u) : ↥V) : G) ∈ ch6ZS T L V
    rw [heq]
    exact (h.data.E.symm _).2
  refine ⟨lt_of_le_of_ne h.ZS_le hZV, hXV, hXZ, fun W hZW hWV hXW => ?_⟩
  by_cases hW : W ≤ ch6ZS T L V
  · exact Or.inl (le_antisymm hW hZW)
  · right
    obtain ⟨w, hwW, hwZ⟩ := Set.not_subset.mp hW
    have hwV : w ∈ V := hWV hwW
    have hPD : ∀ μ : h.data.K, μ ≠ 0 → ∀ D : Matrix.SpecialLinearGroup (Fin 2) h.data.K,
        Odd (orderOf D) → (D : Matrix (Fin 2) (Fin 2) h.data.K).mulVec v = μ • v →
        ∀ y, P W y → P W ((D : Matrix (Fin 2) (Fin 2) h.data.K).mulVec y) := by
      intro μ hμ D hD hDv y hy
      obtain ⟨ℓ, hℓ, hρℓ⟩ := h.exists_mem_lOne hv hle hD hμ hDv
      have hℓX : (ℓ : G) ∈ lOne L (ch6ZS T L V) ⊔ T := Subgroup.mem_sup_left hℓ
      set x : ↥V := h.data.E.symm (Multiplicative.ofAdd y) with hx
      have hxW : (x : G) ∈ W := hy
      have h1 : ((conjAct V ⟨ℓ, h.data.le_normalizer ℓ.2⟩ x : ↥V) : G) ∈ W := by
        rw [conjAct_apply_coe]
        exact (Subgroup.mem_normalizer_iff.mp (hXW hℓX) x).mp hxW
      rw [hPE] at h1
      rw [h.data.toAdd_E_conj, h.data.conj_eq_rho, hρℓ, hx] at h1
      simpa using h1
    obtain ⟨a, b, hab⟩ : ∃ a b : h.data.K,
        Multiplicative.toAdd (h.data.E ⟨w, hwV⟩) = a • v + b • u :=
      ⟨_, _, eq_add_of_det2_ne_zero hdet _⟩
    have hb : b ≠ 0 := by
      rintro rfl
      apply hwZ
      refine (h.mem_ZS_iff_line hv hle ⟨w, hwV⟩).mpr ⟨a, ?_⟩
      rw [hab, zero_smul, add_zero]
    have hPw : P W (a • v + b • u) := by rw [← hab, ← hPE]; exact hwW
    have hPu : ∀ b' : h.data.K, P W (b' • u) := by
      intro b'
      by_cases hb' : b' = 0
      · rw [hb', zero_smul]
        have := hPZ 0
        rw [zero_smul] at this
        exact hZW this
      · obtain ⟨D, hD, hDv, hDu⟩ := htor (b / b') (div_ne_zero hb hb')
        have h1 := hPD (b / b') (div_ne_zero hb hb') D hD hDv _ hPw
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hDv, hDu, smul_smul,
          smul_smul, inv_div, show b * (b' / b) = b' by field_simp] at h1
        have h2 := hPadd W h1 (hPneg W (hZW (hPZ (a * (b / b')))))
        rwa [add_neg_cancel_comm] at h2
    refine le_antisymm hWV fun y hy => ?_
    obtain ⟨a', b', hab'⟩ : ∃ a' b' : h.data.K,
        Multiplicative.toAdd (h.data.E ⟨y, hy⟩) = a' • v + b' • u :=
      ⟨_, _, eq_add_of_det2_ne_zero hdet _⟩
    have := (hPE W ⟨y, hy⟩).mpr (by rw [hab']; exact hPadd W (hZW (hPZ a')) (hPu b'))
    exact this

theorem almostSpecialHyp (h : Hyp611Nat G T M L V n) :
    AlmostSpecialHyp V (ch6ZS T L V) L T (Subgroup.normalizer (ch6ZS T L V : Set G)) where
  elemAbelian := h.toHyp611.isElemAbelian
  ne_bot := h.ZS_ne_bot
  le_V := h.ZS_le
  oTwo_eq := h.toHyp611.eq_oTwoUpper
  V_le_T := h.toHyp611.le_T
  T_le_normV₁ := h.T_le_normalizer_ZS
  T_le_normV := h.toHyp611.T_le_normalizer
  T_le_normL := h.T_le_normalizer_L
  sylow_LT := h.toHyp611.isSylowIn_T
  H_le := le_rfl
  lOne_sup_le := sup_le ((oTwoUpper_le _).trans inf_le_right) h.T_le_normalizer_ZS
  sylow_H := E6.isSylowIn_of_le
    ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
    h.T_le_normalizer_ZS le_top
  charTwo := h.charTwo_normalizer_ZS
  irred := h.irred

theorem V_le_pCoreOf_normalizer (h : Hyp611Nat G T M L V n) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (ch6ZS T L V : Set G)) := by
  have hA := h.almostSpecialHyp
  intro x hx
  have hcc := hA.conjClosure_le_N
  have hxU : x ∈ conjClosure V (Subgroup.normalizer (ch6ZS T L V : Set G)) :=
    le_conjClosure _ _ hx
  have hQ := omegaOneCenterOf_le _ ((secImg_le_iff.1 hA.G22_one.2) ⟨x, hcc hxU⟩ hxU)
  exact (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 hQ

theorem V_le_pCoreOf_centralizer (h : Hyp611Nat G T M L V n) :
    V ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := h.V_le_pCoreOf_normalizer
  have hVC : V ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian (h.ZS_le hz) hx
  have hX : pCoreOf 2 (Subgroup.normalizer (ch6ZS T L V : Set G)) ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G) ≤
        pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (ch6ZS T L V : Set G) :=
      Subgroup.centralizer_le_normalizer _ hc
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hcN)
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hc)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨(h1 x).mp a, (h2 x).mp b⟩, fun ⟨a, b⟩ => ⟨(h1 x).mpr a, (h2 x).mpr b⟩⟩
  exact fun x hx => hX ⟨hN hx, hVC hx⟩

end Hyp611Nat

theorem stmt6_1_9 (h432 : Stmt4_3_2) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
      (ch6S T L V = (T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T) ∧
        IsSylowIn 2 (ch6S T L V) (Subgroup.centralizer (ch6ZS T L V : Set G))) ∧
      Subgroup.normalizer (ch6S T L V : Set G) ≤ M ∧
      QuasithinUnique.CharTwo (Subgroup.normalizer (ch6ZS T L V : Set G)) ∧
      (V ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) ∧ V ≤ ch6S T L V ∧
        ⁅V, ch6S T L V⁆ ≤ ch6ZS T L V) ∧
      (Subgroup.normalizer (ch6ZS T L V : Set G) =
          Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
            (M ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) ∧
        Subgroup.normalizer (ch6ZS T L V : Set G) =
          Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
            (ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G))) ∧
      (thompsonJ T = thompsonJ (ch6S T L V) ∧ baum T = baum (ch6S T L V)) := by
  intro G _ _ T M L V n h
  exact ⟨⟨h.S_eq_pCore h.toHyp611.centralizer_eq, h.isSylowIn_S⟩,
    h.normalizer_S_le h432, h.charTwo_normalizer_ZS,
    ⟨h.V_le_pCoreOf_centralizer, h.V_le_S, h.commutator_V_S_le⟩, h.normalizer_ZS_eq h432,
    h.thompsonJ_eq, h.baum_eq⟩

end CFSG.Quasithin.H13
