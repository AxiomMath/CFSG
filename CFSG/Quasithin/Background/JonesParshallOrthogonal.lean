module

public import CFSG.Quasithin.Background.JonesParshallHermitian
public import CFSG.Quasithin.Background.JonesParshallAverage

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix

section Stab

variable {F : Type} [Field F]

theorem eq_uMat_of_mem_stab {g : SL2 F}
    (hg : g ∈ MulAction.stabilizer (SL2 F) (![1, 0] : Fin 2 → F)) :
    g = uMat ((g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hg' : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![1, 0] := hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrFun hg' 0
    rw [mulVec_two_zero] at this
    simpa using this
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrFun hg' 1
    rw [mulVec_two_one] at this
    simpa using this
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := g.2
    rw [det_fin_two, h00, h10] at this
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat_coe, h00, h10, h11]

theorem odd_index_stab_e1 [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) (hn : 0 < n) :
    Odd (MulAction.stabilizer (SL2 F) (![1, 0] : Fin 2 → F)).index := by
  classical
  set e₁ : Fin 2 → F := ![1, 0]
  have horbit : MulAction.orbit (SL2 F) e₁ = {0}ᶜ := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩ h0
      have : e₁ = g⁻¹ • (g • e₁) := (inv_smul_smul g e₁).symm
      rw [h0, smul_zero] at this
      exact absurd (congrFun this 0) (by simp [e₁])
    · intro hv
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
        refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, funext fun i => ?_⟩
        fin_cases i
        · change (!![0, -(v 1)⁻¹; v 1, 0] *ᵥ e₁) 0 = v 0
          rw [mulVec_two_zero]
          simp [e₁, h0]
        · change (!![0, -(v 1)⁻¹; v 1, 0] *ᵥ e₁) 1 = v 1
          rw [mulVec_two_one]
          simp [e₁]
      · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h0]⟩, funext fun i => ?_⟩
        fin_cases i
        · change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ e₁) 0 = v 0
          rw [mulVec_two_zero]
          simp [e₁]
        · change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ e₁) 1 = v 1
          rw [mulVec_two_one]
          simp [e₁]
  rw [MulAction.index_stabilizer, horbit, Set.ncard_compl, Set.ncard_singleton,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hF, ← pow_mul]
  obtain ⟨k, hk⟩ : ∃ k, n * 2 = k + 1 := ⟨n * 2 - 1, by omega⟩
  rw [hk, pow_succ]
  exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩

end Stab

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

omit [CharP F 2] in
theorem exists_pow_ne_one {n : ℕ} (hn : 0 < n) (hcard : n + 1 < Fintype.card F) :
    ∃ t : F, t ≠ 0 ∧ t ^ n ≠ 1 := by
  classical
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert 0 (Polynomial.nthRoots n (1 : F)).toFinset) (t := Finset.univ) (by
      rw [Finset.card_univ]
      calc (insert 0 (Polynomial.nthRoots n (1 : F)).toFinset).card
          ≤ (Polynomial.nthRoots n (1 : F)).toFinset.card + 1 := Finset.card_insert_le _ _
        _ ≤ n + 1 := by
            have h1 := Multiset.toFinset_card_le (Polynomial.nthRoots n (1 : F))
            have h2 := Polynomial.card_nthRoots n (1 : F)
            omega
        _ < Fintype.card F := hcard)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn] at ht
  exact ⟨t, ht.1, ht.2⟩

theorem exists_sig_ne {a : ℕ} (hF : Fintype.card F = 2 ^ (2 * a)) (ha : 0 < a) :
    ∃ t : F, sig a t ≠ t := by
  have h1 : 0 < 2 ^ a - 1 := by
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have h2 : 2 ^ a - 1 + 1 < Fintype.card F := by
    rw [hF, Nat.sub_add_cancel Nat.one_le_two_pow]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨t, ht0, ht⟩ := exists_pow_ne_one h1 h2
  refine ⟨t, fun h => ht ?_⟩
  rw [sig_apply] at h
  have h3 : t ^ (2 ^ a - 1) * t = 1 * t := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h, one_mul]
  exact mul_right_cancel₀ ht0 h3

theorem not_injective_of_sig {a : ℕ} {t₀ : F} (ht₀ : sig a t₀ ≠ t₀) {φ : F → F}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hK : ∀ x, sig a (φ x) = φ x)
    (hnz : ∀ x, φ x = 0 → x = 0) : False := by
  have hinj : Function.Injective φ := fun x y hxy => by
    have h := hadd (x - y) y
    rw [sub_add_cancel] at h
    have h0 : φ (x - y) = 0 := by linear_combination hxy - h
    exact sub_eq_zero.mp (hnz _ h0)
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hinj) t₀
  exact ht₀ (hs ▸ hK s)

theorem sqrtF_ne_zero {x : F} (hx : x ≠ 0) : sqrtF x ≠ 0 := fun h => by
  have := sqrtF_sq x
  rw [h, zero_pow two_ne_zero] at this
  exact hx this.symm

omit [Fintype F] in
theorem sig_ne_zero (a : ℕ) {x : F} (hx : x ≠ 0) : sig a x ≠ 0 :=
  (map_ne_zero (sig a)).mpr hx

@[expose] def torusHom : Fˣ →* SL2 F where
  toFun c := tMat (c : F) c.ne_zero
  map_one' := by
    ext i j
    rw [tMat_coe]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' c d := by
    ext i j
    change !![((c * d : Fˣ) : F), 0; 0, ((c * d : Fˣ) : F)⁻¹] i j =
      (!![(c : F), 0; 0, (c : F)⁻¹] * !![(d : F), 0; 0, (d : F)⁻¹]) i j
    rw [mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

omit [Fintype F] [CharP F 2] in
theorem torusHom_mk0 (c : F) (hc : c ≠ 0) : torusHom (Units.mk0 c hc) = tMat c hc := rfl

theorem mem_B1A_herm {a : ℕ} (hF : Fintype.card F = 2 ^ (2 * a)) (ha : 0 < a)
    {f : SL2 F → ↥(hermA a F)} (hf : f ∈ Z1A (hermAct a (sig_sig hF))) :
    f ∈ B1A (hermAct a (sig_sig hF)) := by
  classical
  set hσ := sig_sig hF
  set μ := hermAct a hσ
  have h2 : ∀ m : ↥(hermA a F), m + m = 0 := hermA_add_self
  have hodd : Odd (Fintype.card Fˣ) := by
    rw [Fintype.card_units, hF]
    obtain ⟨k, hk⟩ : ∃ k, 2 * a = k + 1 := ⟨2 * a - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩
  obtain ⟨ψ, hψ, hfψ, heq⟩ := exists_equivariant torusHom hodd h2 hf
  suffices hψB : ψ ∈ B1A μ by
    have := add_mem hfψ hψB
    rwa [sub_add_cancel] at this
  obtain ⟨t₀, ht₀⟩ := exists_sig_ne hF ha
  have hψ1 : ψ 1 = 0 := Z1A_one hψ
  set α : F → F := fun t => (ψ (uMat t) : Matrix (Fin 2) (Fin 2) F) 0 0 with hα
  set β : F → F := fun t => (ψ (uMat t) : Matrix (Fin 2) (Fin 2) F) 0 1 with hβ
  set γ : F → F := fun t => (ψ (uMat t) : Matrix (Fin 2) (Fin 2) F) 1 1 with hγ
  have hcoc : ∀ s t, ψ (uMat (s + t)) = ψ (uMat s) + μ (uMat s) (ψ (uMat t)) := fun s t => by
    rw [← uMat_mul]
    exact hψ _ _
  have hα_add : ∀ s t, α (s + t) = α s + (α t + sig a s * β t + s * sig a (β t) +
      s * sig a s * γ t) := fun s t => by
    have h := congrArg (fun X : ↥(hermA a F) => (X : Matrix (Fin 2) (Fin 2) F) 0 0) (hcoc s t)
    simp only [AddSubgroup.coe_add, Matrix.add_apply] at h
    simp only [hα, hβ, hγ]
    rw [h, hermAct_uMat_00, hermA_10]
  have hβ_add : ∀ s t, β (s + t) = β s + (β t + s * γ t) := fun s t => by
    have h := congrArg (fun X : ↥(hermA a F) => (X : Matrix (Fin 2) (Fin 2) F) 0 1) (hcoc s t)
    simp only [AddSubgroup.coe_add, Matrix.add_apply] at h
    simp only [hβ, hγ]
    rw [h, hermAct_uMat_01]
  have hγ_add : ∀ s t, γ (s + t) = γ s + γ t := fun s t => by
    have h := congrArg (fun X : ↥(hermA a F) => (X : Matrix (Fin 2) (Fin 2) F) 1 1) (hcoc s t)
    simp only [AddSubgroup.coe_add, Matrix.add_apply] at h
    simp only [hγ]
    rw [h, hermAct_uMat_11]
  have htor : ∀ (c : F) (hc : c ≠ 0) (t : F),
      ψ (uMat (c ^ 2 * t)) = μ (tMat c hc) (ψ (uMat t)) := fun c hc t => by
    rw [← tMat_conj c hc t, ← torusHom_mk0 c hc]
    exact heq _ _
  have hα_tor : ∀ (c : F) (hc : c ≠ 0) (t : F), α (c ^ 2 * t) = c * sig a c * α t :=
    fun c hc t => by
      change (ψ (uMat (c ^ 2 * t)) : Matrix (Fin 2) (Fin 2) F) 0 0 = _
      rw [htor c hc t, hermAct_tMat_00]
  have hβ_tor : ∀ (c : F) (hc : c ≠ 0) (t : F), β (c ^ 2 * t) = c * sig a c⁻¹ * β t :=
    fun c hc t => by
      change (ψ (uMat (c ^ 2 * t)) : Matrix (Fin 2) (Fin 2) F) 0 1 = _
      rw [htor c hc t, hermAct_tMat_01]
  have hγ_tor : ∀ (c : F) (hc : c ≠ 0) (t : F), γ (c ^ 2 * t) = c⁻¹ * sig a c⁻¹ * γ t :=
    fun c hc t => by
      change (ψ (uMat (c ^ 2 * t)) : Matrix (Fin 2) (Fin 2) F) 1 1 = _
      rw [htor c hc t, hermAct_tMat_11]
  have hzero : ψ (uMat 0) = 0 := by rw [uMat_zero, hψ1]
  have hα0 : α 0 = 0 := by
    change (ψ (uMat 0) : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
    rw [hzero]
    rfl
  have hγ0' : γ 0 = 0 := by
    change (ψ (uMat 0) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
    rw [hzero]
    rfl
  have hαK : ∀ t, sig a (α t) = α t := fun t => hermA_00 _
  have hγK : ∀ t, sig a (γ t) = γ t := fun t => hermA_11 _
  have hsq : ∀ x : F, x ≠ 0 → (sqrtF x) ^ 2 * 1 = x := fun x _ => by rw [sqrtF_sq, mul_one]
  have hγ0 : ∀ t, γ t = 0 := by
    have hγ1 : γ 1 = 0 := by
      by_contra hne
      refine not_injective_of_sig ht₀ hγ_add hγK fun x hx => ?_
      by_contra hx0
      have hs := sqrtF_ne_zero hx0
      have h := hγ_tor (sqrtF x) hs 1
      rw [hsq x hx0, hx] at h
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hs) (sig_ne_zero a (inv_ne_zero hs))) hne
        h.symm
    intro t
    by_cases ht : t = 0
    · rw [ht, hγ0']
    · have h := hγ_tor (sqrtF t) (sqrtF_ne_zero ht) 1
      rw [hsq t ht, hγ1, mul_zero] at h
      exact h
  have hβ_add' : ∀ s t, β (s + t) = β s + β t := fun s t => by
    rw [hβ_add, hγ0, mul_zero, add_zero]
  obtain ⟨B, hBK, hBN, hBt⟩ : ∃ B : F, sig a B = B ∧ (∀ c : F, c ≠ 0 → c * sig a c * B = B) ∧
      ∀ t, β t = t * B := by
    rcases Nat.lt_or_ge 1 a with h1 | h1
    ·
      refine ⟨0, map_zero _, fun c _ => mul_zero _, fun t => ?_⟩
      have hq : 2 ^ a + 1 + 1 < Fintype.card F := by
        rw [hF, two_mul, pow_add]
        have h4 : 4 ≤ 2 ^ a := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h1
        nlinarith
      obtain ⟨s, hs0, hs⟩ := exists_pow_ne_one (n := 2 ^ a + 1) (Nat.succ_pos _) hq
      set c₀ := s ^ (2 ^ a + 1)
      have hc₀K : sig a c₀ = c₀ := by
        rw [sig_apply, ← pow_mul, add_mul, one_mul, ← pow_add, ← two_mul, ← hF, pow_add,
          FiniteField.pow_card, ← pow_succ']
      have hc₀0 : c₀ ≠ 0 := pow_ne_zero _ hs0
      have hc₁0 : c₀ + 1 ≠ 0 := fun h => hs (by
        have : c₀ = -1 := eq_neg_of_add_eq_zero_left h
        rw [this, CharTwo.neg_eq])
      have hc₁K : sig a (c₀ + 1) = c₀ + 1 := by rw [map_add, map_one, hc₀K]
      have hfix : ∀ (c : F) (hc : c ≠ 0), sig a c = c → ∀ t, β (c ^ 2 * t) = β t :=
        fun c hc hcK t => by
          rw [hβ_tor c hc t, map_inv₀, hcK, mul_inv_cancel₀ hc, one_mul]
      have e1 := hfix _ hc₁0 hc₁K t
      have e2 := hfix _ hc₀0 hc₀K t
      have e3 : (c₀ + 1) ^ 2 * t = c₀ ^ 2 * t + t := by
        rw [CharTwo.add_sq, one_pow, add_mul, one_mul]
      rw [e3, hβ_add', e2] at e1
      rw [mul_zero]
      linear_combination e1
    ·
      have ha1 : a = 1 := le_antisymm h1 ha
      subst ha1
      have hcube : ∀ c : F, c ≠ 0 → c ^ 3 = 1 := fun c hc => by
        have := FiniteField.pow_card_sub_one_eq_one c hc
        rwa [hF] at this
      have hsig : ∀ c : F, sig 1 c = c ^ 2 := fun c => by rw [sig_apply, pow_one]
      have hlin : ∀ t, β t = t * β 1 := fun t => by
        by_cases ht : t = 0
        · rw [ht, zero_mul]
          change (ψ (uMat 0) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
          rw [hzero]
          rfl
        · have hc := sqrtF_ne_zero ht
          have h := hβ_tor (sqrtF t) hc 1
          rw [hsq t ht, map_inv₀, hsig] at h
          have hinv : (sqrtF t ^ 2)⁻¹ = sqrtF t :=
            inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hcube _ hc)
          rw [h, hinv]
          calc sqrtF t * sqrtF t * β 1 = sqrtF t ^ 2 * β 1 := by ring
            _ = t * β 1 := by rw [sqrtF_sq]
      refine ⟨β 1, ?_, fun c hc => ?_, hlin⟩
      · have e := hα_add 1 t₀
        rw [show (1 : F) + t₀ = t₀ + 1 from add_comm _ _, hα_add t₀ 1, hlin t₀, hγ0, hγ0] at e
        simp only [map_one, one_mul, mul_zero, add_zero, map_mul] at e
        have e' : (sig 1 t₀ - t₀) * (β 1 - sig 1 (β 1)) = 0 := by linear_combination e
        rcases mul_eq_zero.mp e' with h | h
        · exact absurd (sub_eq_zero.mp h) ht₀
        · exact (sub_eq_zero.mp h).symm
      · rw [hsig, ← pow_succ', hcube c hc, one_mul]
  have hXB : (!![0, 0; 0, B] : Matrix (Fin 2) (Fin 2) F) ∈ hermA a F :=
    mem_hermA_of fun i j => by fin_cases i <;> fin_cases j <;> simp [hBK]
  set XB : ↥(hermA a F) := ⟨!![0, 0; 0, B], hXB⟩
  set f₁ := ψ - coboundaryA μ XB with hf₁
  have hf₁Z : f₁ ∈ Z1A μ := sub_mem hψ (B1A_le_Z1A _ ⟨_, rfl⟩)
  have hXB00 : (XB : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := rfl
  have hXB01 : (XB : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := rfl
  have hXB10 : (XB : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl
  have hXB11 : (XB : Matrix (Fin 2) (Fin 2) F) 1 1 = B := rfl
  have hf₁_00 : ∀ t, (f₁ (uMat t) : Matrix (Fin 2) (Fin 2) F) 0 0 = α t - t * sig a t * B :=
    fun t => by
      rw [hf₁, Pi.sub_apply, coboundaryA_apply, AddSubgroup.coe_sub, AddSubgroup.coe_sub,
        Matrix.sub_apply, Matrix.sub_apply, hermAct_uMat_00, hXB00, hXB01, hXB10, hXB11]
      ring
  have hf₁_01 : ∀ t, (f₁ (uMat t) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := fun t => by
    rw [hf₁, Pi.sub_apply, coboundaryA_apply, AddSubgroup.coe_sub, AddSubgroup.coe_sub,
      Matrix.sub_apply, Matrix.sub_apply, hermAct_uMat_01, hXB01, hXB11]
    change β t - _ = 0
    rw [hBt]
    ring
  have hf₁_11 : ∀ t, (f₁ (uMat t) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := fun t => by
    rw [hf₁, Pi.sub_apply, coboundaryA_apply, AddSubgroup.coe_sub, AddSubgroup.coe_sub,
      Matrix.sub_apply, Matrix.sub_apply, hermAct_uMat_11]
    change γ t - _ = 0
    rw [hγ0]
    ring
  set α₁ : F → F := fun t => α t - t * sig a t * B with hα₁
  have hα₁_add : ∀ s t, α₁ (s + t) = α₁ s + α₁ t := fun s t => by
    simp only [hα₁]
    rw [hα_add, hBt, hγ0, map_add, map_mul, hBK]
    ring
  have hα₁K : ∀ t, sig a (α₁ t) = α₁ t := fun t => by
    simp only [hα₁]
    rw [map_sub, map_mul, map_mul, hαK, hσ, hBK]
    ring
  have hα₁_tor : ∀ (c : F) (hc : c ≠ 0) (t : F), α₁ (c ^ 2 * t) = c * sig a c * α₁ t :=
    fun c hc t => by
      simp only [hα₁]
      rw [hα_tor c hc t, map_mul, map_pow]
      have := hBN c hc
      linear_combination (-(c * sig a c * t * sig a t)) * this
  have hα₁0 : ∀ t, α₁ t = 0 := by
    have h1 : α₁ 1 = 0 := by
      by_contra hne
      refine not_injective_of_sig ht₀ hα₁_add hα₁K fun x hx => ?_
      by_contra hx0
      have hs := sqrtF_ne_zero hx0
      have h := hα₁_tor (sqrtF x) hs 1
      rw [hsq x hx0, hx] at h
      exact mul_ne_zero (mul_ne_zero hs (sig_ne_zero a hs)) hne h.symm
    intro t
    by_cases ht : t = 0
    · simp only [hα₁]
      rw [ht, hα0, zero_mul, zero_mul, sub_zero]
    · have h := hα₁_tor (sqrtF t) (sqrtF_ne_zero ht) 1
      rw [hsq t ht, h1, mul_zero] at h
      exact h
  have hvan : ∀ t, f₁ (uMat t) = 0 := fun t => by
    refine hermA_ext ?_ ?_ ?_
    · rw [hf₁_00]
      exact hα₁0 t
    · rw [hf₁_01]
      rfl
    · rw [hf₁_11]
      rfl
  have hB₁ : f₁ ∈ B1A μ := by
    have hn : 0 < 2 * a := by omega
    refine mem_B1A_of_vanish h2 (odd_index_stab_e1 hF hn) hf₁Z fun g hg => ?_
    rw [eq_uMat_of_mem_stab hg]
    exact hvan _
  have := add_mem hB₁ (⟨XB, rfl⟩ : coboundaryA μ XB ∈ B1A μ)
  rwa [hf₁, sub_add_cancel] at this

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_orthogonalFour {ρ : Representation (ZMod 2) Γ W} {a : ℕ}
    (hF : Fintype.card F = 2 ^ (2 * a)) (ha : 0 < a) (h : Explicit.BinaryOrthogonalFour ρ F a) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  obtain ⟨θ, β, hβ⟩ := BinaryOrthogonalFour.intertwiner (sig_sig hF) h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hZ : Z1A (hermAct a (sig_sig hF)) = B1A (hermAct a (sig_sig hF)) :=
    le_antisymm (fun f hf => mem_B1A_herm hF ha hf) (B1A_le_Z1A _)
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ (k := 1) (by rw [hZ, one_mul]), pow_zero]

end CFSG.Quasithin.JonesParshall
