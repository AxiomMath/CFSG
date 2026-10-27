module

public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma
open scoped MatrixGroups

@[expose] def sl12 (a : F4) : SL(2, F4) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl21 (a : F4) : SL(2, F4) := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

theorem omega_smul_eq : ∀ w : Fin 2 → F4,
    ((sl12 F4.ω * sl21 1 : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec w +
      ((sl21 1 * sl12 F4.ω : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec w = F4.ω • w := by
  decide +kernel

theorem eq_smul_one_of_comm : ∀ N : Matrix (Fin 2) (Fin 2) F4,
    N * ((sl12 1 : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) =
      ((sl12 1 : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) * N →
    N * ((sl21 1 : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) =
      ((sl21 1 : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) * N →
    N = N 0 0 • (1 : Matrix (Fin 2) (Fin 2) F4) := by
  decide +kernel

theorem F4_cases' : ∀ c : F4, c ≠ 0 → c ≠ 1 → c = F4.ω ∨ c = 1 + F4.ω := by decide

theorem omega_smul_e0_ne_zero : F4.ω • (![1, 0] : Fin 2 → F4) ≠ 0 := by decide

theorem omega_smul_e0_ne : F4.ω • (![1, 0] : Fin 2 → F4) ≠ ![1, 0] := by decide

theorem e0_ne_zero : (![1, 0] : Fin 2 → F4) ≠ 0 := by decide

theorem det_rescale : ∀ d : F4, d ≠ 0 → ((d ^ 2)⁻¹) ^ 2 * d = 1 := by decide

theorem mul_frob_inv : ∀ c : F4, c ≠ 0 → c * frobF4 c⁻¹ = c⁻¹ := by decide

theorem frob_omega : frobF4 F4.ω = 1 + F4.ω := by decide

theorem frob_one_add_omega : frobF4 (1 + F4.ω) = F4.ω := by decide

theorem sq_ne_zero' : ∀ d : F4, d ≠ 0 → d ^ 2 ≠ 0 := by decide

@[expose] def matOf (f : (Fin 2 → F4) → Fin 2 → F4) : Matrix (Fin 2) (Fin 2) F4 :=
  Matrix.of fun i j => f (Pi.single j 1) i

theorem matOf_mulVec {f : (Fin 2 → F4) → Fin 2 → F4} (hadd : ∀ v w, f (v + w) = f v + f w)
    (hsmul : ∀ (a : F4) v, f (a • v) = a • f v) (w : Fin 2 → F4) :
    (matOf f).mulVec w = f w := by
  have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  conv_rhs => rw [hw, hadd, hsmul, hsmul]
  funext i
  simp [matOf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

variable {G : Type} [Group G]

structure NatSL24 (H K Q U Z : Subgroup G) where
  π : ↥K →* SL(2, F4)
  β : ↥U →* Multiplicative (Fin 2 → F4)
  K_le : K ≤ H
  conj_K : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K
  conj_U : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U
  conj_Z : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z
  π_surj : Function.Surjective π
  π_ker : π.ker = Q.subgroupOf K
  β_surj : Function.Surjective β
  β_ker : β.ker = Z.subgroupOf U
  β_conj : ∀ (k : ↥K) (u u' : ↥U), (u' : G) = k * u * (k : G)⁻¹ →
    β u' = Multiplicative.ofAdd ((π k : Matrix (Fin 2) (Fin 2) F4).mulVec
      (Multiplicative.toAdd (β u)))

namespace NatSL24

variable {H K Q U Z : Subgroup G} (D : NatSL24 H K Q U Z)

@[expose] noncomputable def pre (w : Fin 2 → F4) : ↥U :=
  Function.surjInv D.β_surj (Multiplicative.ofAdd w)

theorem β_pre (w : Fin 2 → F4) : D.β (D.pre w) = Multiplicative.ofAdd w :=
  Function.surjInv_eq D.β_surj _

@[expose] def conjU (h : ↥H) (u : ↥U) : ↥U := ⟨h * u * (h : G)⁻¹, D.conj_U h h.2 u u.2⟩

theorem conjU_mul (h : ↥H) (u u' : ↥U) : D.conjU h (u * u') = D.conjU h u * D.conjU h u' := by
  apply Subtype.ext
  simp only [conjU, Subgroup.coe_mul]
  group

theorem conjU_mul_left (h h' : ↥H) (u : ↥U) : D.conjU (h * h') u = D.conjU h (D.conjU h' u) := by
  apply Subtype.ext
  simp only [conjU, Subgroup.coe_mul]
  group

theorem conjU_one (u : ↥U) : D.conjU 1 u = u := by
  apply Subtype.ext
  simp [conjU]

@[expose] noncomputable def act (h : ↥H) (w : Fin 2 → F4) : Fin 2 → F4 :=
  Multiplicative.toAdd (D.β (D.conjU h (D.pre w)))

theorem act_β (h : ↥H) (u : ↥U) :
    D.act h (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β (D.conjU h u)) := by
  set u₀ := D.pre (Multiplicative.toAdd (D.β u)) with hu₀
  have h1 : D.β u₀ = D.β u := by rw [hu₀, D.β_pre]; rfl
  have h2 : u₀⁻¹ * u ∈ D.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [D.β_ker, Subgroup.mem_subgroupOf] at h2
  have h5 : (D.conjU h u₀)⁻¹ * D.conjU h u ∈ D.β.ker := by
    rw [D.β_ker, Subgroup.mem_subgroupOf]
    have e : (((D.conjU h u₀)⁻¹ * D.conjU h u : ↥U) : G) =
        (h : G) * ((u₀⁻¹ * u : ↥U) : G) * (h : G)⁻¹ := by
      simp only [conjU, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact D.conj_Z h h.2 _ h2
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h5
  show Multiplicative.toAdd (D.β (D.conjU h u₀)) = _
  rw [h5]

theorem act_add (h : ↥H) (v w : Fin 2 → F4) : D.act h (v + w) = D.act h v + D.act h w := by
  have hvw : v + w = Multiplicative.toAdd (D.β (D.pre v * D.pre w)) := by
    rw [map_mul, toAdd_mul, D.β_pre, D.β_pre]
    rfl
  rw [hvw, D.act_β, D.conjU_mul, map_mul, toAdd_mul]
  rfl

theorem act_mul (h h' : ↥H) (w : Fin 2 → F4) : D.act (h * h') w = D.act h (D.act h' w) := by
  have e : D.act h' w = Multiplicative.toAdd (D.β (D.conjU h' (D.pre w))) := rfl
  rw [e, D.act_β, ← D.conjU_mul_left]
  rfl

theorem act_one (w : Fin 2 → F4) : D.act 1 w = w := by
  show Multiplicative.toAdd (D.β (D.conjU 1 (D.pre w))) = w
  rw [D.conjU_one, D.β_pre]
  rfl

theorem act_zero (h : ↥H) : D.act h 0 = 0 := by
  have := D.act_add h 0 0
  rw [add_zero] at this
  exact (add_eq_left.mp this.symm)

theorem act_inv_act (h : ↥H) (w : Fin 2 → F4) : D.act h⁻¹ (D.act h w) = w := by
  rw [← D.act_mul, inv_mul_cancel, D.act_one]

theorem act_act_inv (h : ↥H) (w : Fin 2 → F4) : D.act h (D.act h⁻¹ w) = w := by
  rw [← D.act_mul, mul_inv_cancel, D.act_one]

theorem act_injective (h : ↥H) : Function.Injective (D.act h) := fun v w hvw => by
  rw [← D.act_inv_act h v, hvw, D.act_inv_act]

@[expose] def kH (k : ↥K) : ↥H := ⟨k, D.K_le k.2⟩

@[expose] def conjK (h : ↥H) (k : ↥K) : ↥K := ⟨h * k * (h : G)⁻¹, D.conj_K h h.2 k k.2⟩

theorem act_K (k : ↥K) (w : Fin 2 → F4) :
    D.act (D.kH k) w = (D.π k : Matrix (Fin 2) (Fin 2) F4).mulVec w := by
  have := D.β_conj k (D.pre w) (D.conjU (D.kH k) (D.pre w)) rfl
  show Multiplicative.toAdd (D.β (D.conjU (D.kH k) (D.pre w))) = _
  rw [this, D.β_pre]
  rfl

theorem mul_kH (h : ↥H) (k : ↥K) : h * D.kH k = D.kH (D.conjK h k) * h := by
  apply Subtype.ext
  simp only [kH, conjK, Subgroup.coe_mul]
  group

theorem act_conjK (h : ↥H) (k : ↥K) (w : Fin 2 → F4) :
    D.act h ((D.π k : Matrix (Fin 2) (Fin 2) F4).mulVec w) =
      (D.π (D.conjK h k) : Matrix (Fin 2) (Fin 2) F4).mulVec (D.act h w) := by
  rw [← D.act_K, ← D.act_mul, D.mul_kH, D.act_mul, D.act_K]

theorem conjK_conjK_inv (h : ↥H) (k : ↥K) : D.conjK h (D.conjK h⁻¹ k) = k := by
  apply Subtype.ext
  simp only [conjK, Subgroup.coe_inv, inv_inv]
  group

theorem π_eq_of_mulVec {k k' : ↥K}
    (h : ∀ w, (D.π k : Matrix (Fin 2) (Fin 2) F4).mulVec w =
      (D.π k' : Matrix (Fin 2) (Fin 2) F4).mulVec w) : D.π k = D.π k' :=
  Subtype.ext (Matrix.ext_iff_mulVec.mpr h)

theorem exists_omega (h : ↥H) : ∃ c : F4, ∀ w, D.act h (F4.ω • w) = c • D.act h w := by
  obtain ⟨k₁, hk₁⟩ := D.π_surj (sl12 F4.ω * sl21 1)
  obtain ⟨k₂, hk₂⟩ := D.π_surj (sl21 1 * sl12 F4.ω)
  obtain ⟨k₃, hk₃⟩ := D.π_surj (sl12 1)
  obtain ⟨k₄, hk₄⟩ := D.π_surj (sl21 1)
  set N : Matrix (Fin 2) (Fin 2) F4 := (D.π (D.conjK h k₁) : Matrix (Fin 2) (Fin 2) F4) +
    (D.π (D.conjK h k₂) : Matrix (Fin 2) (Fin 2) F4) with hN
  have hom : ∀ w, D.act h (F4.ω • w) = N.mulVec (D.act h w) := by
    intro w
    rw [← omega_smul_eq w, ← hk₁, ← hk₂, D.act_add, D.act_conjK, D.act_conjK, hN,
      Matrix.add_mulVec]
  have hcomm : ∀ k : ↥K, N * (D.π k : Matrix (Fin 2) (Fin 2) F4) =
      (D.π k : Matrix (Fin 2) (Fin 2) F4) * N := by
    intro k
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    obtain ⟨y, rfl⟩ : ∃ y, D.act h y = x := ⟨D.act h⁻¹ x, D.act_act_inv h x⟩
    have e1 : (D.π k : Matrix (Fin 2) (Fin 2) F4).mulVec (D.act h y) =
        D.act h ((D.π (D.conjK h⁻¹ k) : Matrix (Fin 2) (Fin 2) F4).mulVec y) := by
      rw [D.act_conjK, D.conjK_conjK_inv]
    rw [e1, ← hom, ← Matrix.mulVec_smul, D.act_conjK, D.conjK_conjK_inv, hom]
  have hN' := eq_smul_one_of_comm N (by rw [← hk₃]; exact hcomm k₃)
    (by rw [← hk₄]; exact hcomm k₄)
  set c := N 0 0 with hc
  refine ⟨c, fun w => ?_⟩
  rw [hom, hN', Matrix.smul_mulVec, Matrix.one_mulVec]

theorem omega_cases {h : ↥H} {c : F4} (hc : ∀ w, D.act h (F4.ω • w) = c • D.act h w) :
    c = F4.ω ∨ c = 1 + F4.ω := by
  have h0 : D.act h ![1, 0] ≠ 0 := by
    intro h0
    rw [← D.act_zero h] at h0
    exact e0_ne_zero (D.act_injective h h0)
  refine F4_cases' c (fun hc0 => ?_) (fun hc1 => ?_)
  · have := hc ![1, 0]
    rw [hc0, zero_smul, ← D.act_zero h] at this
    exact omega_smul_e0_ne_zero (D.act_injective h this)
  · have := hc ![1, 0]
    rw [hc1, one_smul] at this
    exact omega_smul_e0_ne (D.act_injective h this)

theorem act_smul_of_omega {h : ↥H} (hc : ∀ w, D.act h (F4.ω • w) = F4.ω • D.act h w)
    (a : F4) (w : Fin 2 → F4) : D.act h (a • w) = a • D.act h w := by
  rcases F4_cases a with rfl | rfl | rfl | rfl
  · rw [zero_smul, zero_smul, D.act_zero]
  · rw [one_smul, one_smul]
  · exact hc w
  · rw [add_smul, add_smul, one_smul, one_smul, D.act_add, hc]

theorem act_smul_of_omega_sq {h : ↥H}
    (hc : ∀ w, D.act h (F4.ω • w) = (1 + F4.ω) • D.act h w)
    (a : F4) (w : Fin 2 → F4) : D.act h (a • w) = frobF4 a • D.act h w := by
  rcases F4_cases a with rfl | rfl | rfl | rfl
  · rw [map_zero, zero_smul, zero_smul, D.act_zero]
  · rw [map_one, one_smul, one_smul]
  · rw [frob_omega]
    exact hc w
  · rw [frob_one_add_omega, add_smul, one_smul, D.act_add, hc, add_smul, one_smul,
      ← add_assoc, ← two_smul F4, F4.two_eq_zero, zero_smul, zero_add]


theorem not_linear_of_not_mem (hQK : Q ≤ K)
    (hidx : ∀ h ∈ H, ∀ h' ∈ H, h ∉ K → h' ∉ K → h * h'⁻¹ ∈ K)
    (hZ : ∀ h ∈ H, (∀ h' ∈ H, h * h' * h⁻¹ * h'⁻¹ ∈ Q) → h ∈ Q)
    {t : ↥H} (htK : (t : G) ∉ K) : ¬ ∀ w, D.act t (F4.ω • w) = F4.ω • D.act t w := by
  intro hlin
  have hsm := D.act_smul_of_omega hlin
  set M := matOf (D.act t) with hM
  have hMv : ∀ w, M.mulVec w = D.act t w := matOf_mulVec (D.act_add t) hsm
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hMv, ← D.act_zero t] at hMv0
    exact hv (D.act_injective t hMv0)
  set μ := M.det ^ 2 with hμ
  have hμ0 : μ ≠ 0 := sq_ne_zero' _ hdet
  have hgdet : (μ⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hμ]
    exact det_rescale _ hdet
  obtain ⟨k₀, hk₀⟩ := D.π_surj ⟨μ⁻¹ • M, hgdet⟩
  set t' : ↥H := (D.kH k₀)⁻¹ * t with ht'
  have ht'K : (t' : G) ∉ K := by
    intro h'
    apply htK
    have e : (t : G) = (k₀ : G) * t' := by
      rw [ht']
      simp [kH]
    rw [e]
    exact mul_mem k₀.2 h'
  have hact' : ∀ w, D.act t' w = μ • w := by
    intro w
    apply D.act_injective (D.kH k₀)
    rw [← D.act_mul, ht', mul_inv_cancel_left, D.act_K, Matrix.mulVec_smul, hk₀, ← hMv]
    show M.mulVec w = μ • (μ⁻¹ • M).mulVec w
    rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hcK : ∀ k : ↥K, (t' : G) * k * (t' : G)⁻¹ * (k : G)⁻¹ ∈ Q := by
    intro k
    have he : D.π (D.conjK t' k) = D.π k := by
      apply D.π_eq_of_mulVec
      intro y
      have h1 := D.act_conjK t' k y
      rw [hact', hact', Matrix.mulVec_smul] at h1
      exact (smul_right_injective _ hμ0 h1).symm
    have hmem : D.conjK t' k * k⁻¹ ∈ D.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [D.π_ker, Subgroup.mem_subgroupOf] at hmem
    simpa [conjK] using hmem
  apply ht'K
  apply hQK
  apply hZ t' t'.2
  intro h hh
  by_cases hhK : h ∈ K
  · exact hcK ⟨h, hhK⟩
  · have hk : h * (t' : G)⁻¹ ∈ K := hidx h hh t' t'.2 hhK ht'K
    have e : (t' : G) * h * (t' : G)⁻¹ * h⁻¹ =
        (t' : G) * (h * (t' : G)⁻¹) * (t' : G)⁻¹ * (h * (t' : G)⁻¹)⁻¹ := by group
    rw [e]
    exact hcK ⟨h * (t' : G)⁻¹, hk⟩

theorem act_smul_of_not_mem (hQK : Q ≤ K)
    (hidx : ∀ h ∈ H, ∀ h' ∈ H, h ∉ K → h' ∉ K → h * h'⁻¹ ∈ K)
    (hZ : ∀ h ∈ H, (∀ h' ∈ H, h * h' * h⁻¹ * h'⁻¹ ∈ Q) → h ∈ Q)
    {t : ↥H} (htK : (t : G) ∉ K) (a : F4) (w : Fin 2 → F4) :
    D.act t (a • w) = frobF4 a • D.act t w := by
  obtain ⟨c, hc⟩ := D.exists_omega t
  rcases D.omega_cases hc with rfl | rfl
  · exact absurd hc (D.not_linear_of_not_mem hQK hidx hZ htK)
  · exact D.act_smul_of_omega_sq hc a w

abbrev σ : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem frobVec_σ (w : Fin 2 → F4) : frobVec σ w = fun i => frobF4 (w i) :=
  frobVec_of_eq_one rfl w

theorem frobVec_σ_σ (w : Fin 2 → F4) : frobVec σ (frobVec σ w) = w := by
  rw [frobVec_σ, frobVec_σ]
  funext i
  exact frobF4_frobF4 _

include D in
theorem exists_sigma (hQK : Q ≤ K) (ht : ∃ t ∈ H, t ∉ K)
    (hidx : ∀ h ∈ H, ∀ h' ∈ H, h ∉ K → h' ∉ K → h * h'⁻¹ ∈ K)
    (hZ : ∀ h ∈ H, (∀ h' ∈ H, h * h' * h⁻¹ * h'⁻¹ ∈ Q) → h ∈ Q) :
    ∃ (φ : ↥H →* SigmaL2F4) (ψ : ↥U →* Multiplicative (Fin 2 → F4)),
      Function.Surjective φ ∧ φ.ker = Q.subgroupOf H ∧ Function.Surjective ψ ∧
      ψ.ker = Z.subgroupOf U ∧
      ∀ (h : ↥H) (u u' : ↥U), (u' : G) = h * u * (h : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (sigmaAct (φ h) (Multiplicative.toAdd (ψ u))) := by
  obtain ⟨t₀, ht₀H, ht₀K⟩ := ht
  set t : ↥H := ⟨t₀, ht₀H⟩ with htdef
  have htK : (t : G) ∉ K := ht₀K
  have hsemi := D.act_smul_of_not_mem hQK hidx hZ htK
  set Lt : (Fin 2 → F4) → Fin 2 → F4 := fun w => D.act t (frobVec σ w) with hLt
  have hLadd : ∀ v w, Lt (v + w) = Lt v + Lt w := fun v w => by
    simp only [hLt, frobVec_add, D.act_add]
  have hLsmul : ∀ (a : F4) v, Lt (a • v) = a • Lt v := fun a v => by
    have e : frobVec σ (a • v) = frobF4 a • frobVec σ v := by
      rw [frobVec_σ, frobVec_σ]
      funext i
      simp [map_mul]
    simp only [hLt, e, hsemi, frobF4_frobF4]
  set M := matOf Lt with hM
  have hMv : ∀ w, M.mulVec w = Lt w := matOf_mulVec hLadd hLsmul
  have hactt : ∀ w, D.act t w = M.mulVec (frobVec σ w) := fun w => by
    rw [hMv]
    simp only [hLt, frobVec_σ_σ]
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hMv] at hMv0
    simp only [hLt] at hMv0
    rw [← D.act_zero t] at hMv0
    have h1 := D.act_injective t hMv0
    apply hv
    rw [← frobVec_σ_σ v, h1, frobVec_σ]
    funext i
    simp
  set c₀ := M.det ^ 2 with hc₀
  have hc₀0 : c₀ ≠ 0 := sq_ne_zero' _ hdet
  have hM'det : (c₀⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hc₀]
    exact det_rescale _ hdet
  set M' : SL(2, F4) := ⟨c₀⁻¹ • M, hM'det⟩ with hM'
  set xt : SigmaL2F4 := ⟨M', σ⟩ with hxt
  set act' : ↥H → (Fin 2 → F4) → Fin 2 → F4 := fun h w => c₀ • D.act h (c₀⁻¹ • w)
    with hact'
  have act'_mul : ∀ h h' w, act' (h * h') w = act' h (act' h' w) := by
    intro h h' w
    simp only [hact', D.act_mul, smul_smul, inv_mul_cancel₀ hc₀0, one_smul]
  have act'_K : ∀ (k : ↥K) w,
      act' (D.kH k) w = sigmaAct (SemidirectProduct.inl (D.π k)) w := by
    intro k w
    rw [sigmaAct_inl]
    simp only [hact', D.act_K, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc₀0, one_smul]
  have act'_t : ∀ w, act' t w = sigmaAct xt w := by
    intro w
    show c₀ • D.act t (c₀⁻¹ • w) = (c₀⁻¹ • M).mulVec (frobVec σ w)
    rw [hsemi, hactt, smul_smul, mul_frob_inv _ hc₀0, Matrix.smul_mulVec]
  have hkey : ∀ h : ↥H, ∃ x : SigmaL2F4, ∀ w, act' h w = sigmaAct x w := by
    intro h
    by_cases hhK : (h : G) ∈ K
    · exact ⟨SemidirectProduct.inl (D.π ⟨h, hhK⟩), fun w => act'_K ⟨h, hhK⟩ w⟩
    · have hk : (h : G) * (t : G)⁻¹ ∈ K := hidx h h.2 t t.2 hhK htK
      have e : h = D.kH ⟨_, hk⟩ * t := by
        apply Subtype.ext
        simp [kH]
      refine ⟨SemidirectProduct.inl (D.π ⟨_, hk⟩) * xt, fun w => ?_⟩
      rw [show act' h w = act' (D.kH ⟨_, hk⟩ * t) w from congrArg (fun x => act' x w) e,
        act'_mul, act'_t, act'_K, sigmaAct_mul]
  have huniq : ∀ x y : SigmaL2F4, (∀ w, sigmaAct x w = sigmaAct y w) → x = y := by
    intro x y hxy
    have : x⁻¹ * y = 1 := eq_one_of_sigmaAct_eq fun v => by
      rw [sigmaAct_mul, ← hxy, ← sigmaAct_mul, inv_mul_cancel, sigmaAct_one]
    exact inv_mul_eq_one.mp this
  choose φf hφf using hkey
  have φ_mul : ∀ h h', φf (h * h') = φf h * φf h' := fun h h' => huniq _ _ fun w => by
    rw [← hφf, sigmaAct_mul, ← hφf, ← hφf, act'_mul]
  have φ_one : φf 1 = 1 := huniq _ _ fun w => by
    rw [← hφf, sigmaAct_one]
    simp only [hact', D.act_one, smul_smul, mul_inv_cancel₀ hc₀0, one_smul]
  let φ : ↥H →* SigmaL2F4 := { toFun := φf, map_one' := φ_one, map_mul' := φ_mul }
  have hφapp : ∀ h, φ h = φf h := fun _ => rfl
  have hφK : ∀ k : ↥K, φf (D.kH k) = SemidirectProduct.inl (D.π k) := fun k =>
    huniq _ _ fun w => by rw [← hφf, act'_K]
  have hφt : φf t = xt := huniq _ _ fun w => by rw [← hφf, act'_t]
  let ψ : ↥U →* Multiplicative (Fin 2 → F4) :=
    { toFun := fun u => Multiplicative.ofAdd (c₀ • Multiplicative.toAdd (D.β u))
      map_one' := by simp
      map_mul' := fun u u' => by simp [smul_add] }
  have hψapp : ∀ u, ψ u = Multiplicative.ofAdd (c₀ • Multiplicative.toAdd (D.β u)) :=
    fun _ => rfl
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨A, e⟩
    rcases zmod2_cases (Multiplicative.toAdd e) with he | he
    · obtain ⟨k, hk⟩ := D.π_surj A
      refine ⟨D.kH k, ?_⟩
      have he' : e = 1 := by rw [← ofAdd_toAdd e, he]; rfl
      subst he'
      rw [hφapp, hφK, hk]
      rfl
    · obtain ⟨k, hk⟩ := D.π_surj (A * M'⁻¹)
      refine ⟨D.kH k * t, ?_⟩
      have he' : e = σ := by rw [← ofAdd_toAdd e, he]
      subst he'
      rw [map_mul, hφapp, hφapp, hφK, hφt, hk, hxt]
      apply SemidirectProduct.ext
      · simp
      · simp
  ·
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      by_cases hhK : (h : G) ∈ K
      · have h2 : φf (D.kH ⟨h, hhK⟩) = 1 := h1
        rw [hφK] at h2
        have hπ1 : D.π ⟨h, hhK⟩ = 1 :=
          SemidirectProduct.inl_injective (h2.trans (map_one _).symm)
        have hmem : (⟨h, hhK⟩ : ↥K) ∈ D.π.ker := hπ1
        rw [D.π_ker, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      · exfalso
        have hk : (h : G) * (t : G)⁻¹ ∈ K := hidx h h.2 t t.2 hhK htK
        have e : h = D.kH ⟨_, hk⟩ * t := by
          apply Subtype.ext
          simp [kH]
        have h2 : φ (D.kH ⟨_, hk⟩ * t) = 1 := (congrArg φ e).symm.trans h1
        rw [map_mul, hφapp, hφapp, hφK, hφt] at h2
        have h3 := congrArg SemidirectProduct.right h2
        simp [hxt] at h3
    · intro hQ
      have hK : (h : G) ∈ K := hQK hQ
      have hπ1 : D.π ⟨h, hK⟩ = 1 := by
        have hmem : (⟨h, hK⟩ : ↥K) ∈ D.π.ker := by
          rw [D.π_ker, Subgroup.mem_subgroupOf]
          exact hQ
        exact hmem
      show φf (D.kH ⟨h, hK⟩) = 1
      rw [hφK, hπ1, map_one]
  ·
    intro y
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd (c₀⁻¹ • Multiplicative.toAdd y))
    refine ⟨u, ?_⟩
    rw [hψapp, hu, toAdd_ofAdd, smul_smul, mul_inv_cancel₀ hc₀0, one_smul, ofAdd_toAdd]
  ·
    ext u
    rw [MonoidHom.mem_ker, ← D.β_ker, MonoidHom.mem_ker, hψapp]
    constructor
    · intro h1
      have h2 : c₀ • Multiplicative.toAdd (D.β u) = 0 := by
        have := congrArg Multiplicative.toAdd h1
        simpa using this
      rcases smul_eq_zero.mp h2 with h2 | h2
      · exact absurd h2 hc₀0
      · rw [← ofAdd_toAdd (D.β u), h2]
        rfl
    · intro h1
      rw [h1]
      simp
  ·
    intro h u u' hu'
    have hc : D.conjU h u = u' := Subtype.ext hu'.symm
    rw [hψapp, hψapp, hφapp, toAdd_ofAdd, ← hφf]
    simp only [hact', smul_smul, inv_mul_cancel₀ hc₀0, one_smul]
    rw [D.act_β, hc]

end NatSL24

end CFSG.Quasithin.H13.L32A
