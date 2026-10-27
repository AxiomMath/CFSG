module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualCoord
public import CFSG.RankThree.GF2n.Stroth80.Sec12TransvGL
public import CFSG.ClassicalGroups.SpecialLinear.InvolutionTransvection

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG.ClassicalGroups.SpecialLinear

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F}

theorem exists_transvection_of_normal (C : NatDualCoord ρ ρ') (Q : QuadDatum K E) [CharP F 2]
    (hn : 3 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (b : E) (hb : Q.Qf b = 0) (N : Subgroup Γ)
    (hN2 : ∀ a ∈ N, ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1)
    (hNs : ∀ s : Γ, ρ s b = b → ∀ a ∈ N, s * a * s⁻¹ ∈ N)
    {a₀ : Γ} (ha₀ : a₀ ∈ N) (ha₀1 : ρ' a₀ ≠ 1) :
    ∃ a ∈ N, ∃ c γ : Fin n → F, c ≠ 0 ∧ γ ≠ 0 ∧ γ ⬝ᵥ c = 0 ∧
      ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨⟨v, α⟩, hbv⟩ : ∃ p : (Fin n → F) × (Fin n → F), C.Ψ b = p := ⟨_, rfl⟩
  have hb_eq : b = C.inl v + C.inr α := by
    have h := C.eq_inl_add_inr b
    rw [hbv] at h
    exact h
  have hb' : Q.Qf (C.inl v + C.inr α) = 0 := by
    rw [← hb_eq]
    exact hb
  have hαv : α ⬝ᵥ v = 0 := (C.Qf_inl_add_inr_eq_zero_iff Q hn2 hrange hQρ hK v α).mp hb'
  have hMM : ∀ M : Matrix (Fin n) (Fin n) F, M + M = 0 := by
    intro M
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hsub : ∀ M : Matrix (Fin n) (Fin n) F,
      (1 : Matrix (Fin n) (Fin n) F) - M = 1 + M := by
    intro M
    rw [sub_eq_add_neg, neg_eq_iff_add_eq_zero.mpr (hMM M)]
  have ht2 : ((ρ' a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((ρ' a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
    hN2 a₀ ha₀
  have ht1 : ((ρ' a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ 1 := by
    intro h
    exact ha₀1 (Units.ext (by rw [Units.val_one]; exact h))
  have hGL2 : ρ' a₀ * ρ' a₀ = 1 :=
    Units.ext (by rw [Units.val_mul, Units.val_one]; exact ht2)
  have hinvt : (ρ' a₀)⁻¹ = ρ' a₀ := inv_eq_of_mul_eq_one_right hGL2
  rcases CFSG.ClassicalGroups.SpecialLinear.exists_transvection_comm_of_involution
      ((ρ' a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ht2 ht1 v α hαv with
    ⟨c, γ, hc, hγ, hγc, ht_eq⟩ | ⟨c, γ, hc, hγc, hγv, hαc, hγ'0, hγ'c, hcomm⟩
  · exact ⟨a₀, ha₀, c, γ, hc, hγ, hγc, ht_eq⟩
  · obtain ⟨τ, hτM, hτinvM, hτS⟩ := exists_gl_transv c γ hγc
    have hτinv : ((τ⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        1 + Matrix.vecMulVec c γ := by
      rw [hτinvM]
      exact hsub _
    obtain ⟨s, hs⟩ := exists_eq_of_mem_statedSL hrange hτS
    have hsb : ρ s b = b := by
      apply C.Ψ.injective
      rw [C.act, hs, hbv, transvGL_mulVec τ c γ hτM, transvGL_tinv_mulVec τ c γ hγc hτM]
      simp [hγv, dotProduct_comm c α, hαc]
    have hsa : s * a₀⁻¹ * s⁻¹ ∈ N := hNs s hsb a₀⁻¹ (N.inv_mem ha₀)
    refine ⟨a₀ * (s * a₀⁻¹ * s⁻¹), N.mul_mem ha₀ hsa, c,
      γ ᵥ* ((ρ' a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + γ, hc, hγ'0, hγ'c, ?_⟩
    have hGa : ρ' (a₀ * (s * a₀⁻¹ * s⁻¹)) = ρ' a₀ * (τ * ρ' a₀ * τ⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hinvt, hs]
    rw [hGa]
    simp only [Units.val_mul]
    rw [hτM, hτinv, ← hcomm]
    simp only [mul_assoc]

end NatDualCoord

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')
  (Q : QuadDatum K E)

theorem Ψ_ρ_sub_one (a : Γ) (c γ : Fin n → F) (hγc : γ ⬝ᵥ c = 0)
    (ha : ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ)
    (e : E) :
    C.Ψ (ρ a e - e) = ((γ ⬝ᵥ (C.Ψ e).1) • c, (-(c ⬝ᵥ (C.Ψ e).2)) • γ) := by
  rw [map_sub, C.act, transvGL_mulVec (ρ' a) c γ ha, transvGL_tinv_mulVec (ρ' a) c γ hγc ha]
  refine Prod.ext ?_ ?_
  · simp
  · simp [neg_smul]

theorem sub_one_apply_eq (a : Γ) (e : E) :
    (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1) e = ρ a e - e := by
  simp

theorem mem_range_sub_one_iff (a : Γ) (c γ : Fin n → F) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (hγc : γ ⬝ᵥ c = 0)
    (ha : ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ)
    (v : E) :
    v ∈ LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1) ↔
      ∃ r s : F, C.Ψ v = (r • c, s • γ) := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨e, he⟩
    rw [sub_one_apply_eq] at he
    subst he
    exact ⟨γ ⬝ᵥ (C.Ψ e).1, -(c ⬝ᵥ (C.Ψ e).2), C.Ψ_ρ_sub_one a c γ hγc ha e⟩
  · rintro ⟨r, s, hv⟩
    obtain ⟨x, hx⟩ := exists_dotProduct_eq_of_ne_zero γ hγ r
    obtain ⟨y, hy⟩ := exists_dotProduct_eq_of_ne_zero c hc (-s)
    refine ⟨C.Ψ.symm (x, y), ?_⟩
    rw [sub_one_apply_eq]
    apply C.Ψ.injective
    rw [C.Ψ_ρ_sub_one a c γ hγc ha, hv]
    simp [hx, hy]

include C in
theorem ne_one_of_transv (a : Γ) (c γ : Fin n → F) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (hγc : γ ⬝ᵥ c = 0)
    (ha : ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ) :
    ρ a ≠ 1 := by
  intro h
  have hv : C.inl c ∈ LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1) := by
    rw [C.mem_range_sub_one_iff a c γ hc hγ hγc ha]
    exact ⟨1, 0, by rw [C.Ψ_inl]; simp⟩
  rw [LinearMap.mem_range] at hv
  obtain ⟨e, he⟩ := hv
  rw [sub_one_apply_eq, h] at he
  have hz : C.inl c = 0 := by
    rw [← he]
    simp
  have h0 := congrArg C.Ψ hz
  rw [C.Ψ_inl, map_zero] at h0
  exact hc (by simpa using congrArg Prod.fst h0)

include C in
theorem Qf_eq_zero_of_mem_range (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (a : Γ) (c γ : Fin n → F) (hc : c ≠ 0) (hγ : γ ≠ 0) (hγc : γ ⬝ᵥ c = 0)
    (ha : ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ)
    {v : E} (hv : v ∈ LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1)) :
    Q.Qf v = 0 := by
  obtain ⟨r, s, hrs⟩ := (C.mem_range_sub_one_iff a c γ hc hγ hγc ha v).mp hv
  have hv' : v = C.inl (r • c) + C.inr (s • γ) := by
    apply C.Ψ.injective
    rw [hrs, map_add, C.Ψ_inl, C.Ψ_inr]
    simp
  rw [hv', C.Qf_inl_add_inr_eq_zero_iff Q hn hrange hQρ hK]
  simp [smul_dotProduct, dotProduct_smul, hγc]

theorem finrank_eq_two_of_equiv [Finite K] (θ : K ≃+* F) (R : Submodule K E)
    (e : F × F ≃ R) : Module.finrank K R = 2 := by
  haveI : Finite F := Finite.of_equiv K θ.toEquiv
  haveI : Finite R := Finite.of_equiv (F × F) e
  haveI : Module.Finite K R := Module.finite_iff_finite.mpr inferInstance
  have hFK : Nat.card F = Nat.card K := (Nat.card_congr θ.toEquiv).symm
  have hcard : Nat.card R = Nat.card K ^ 2 := by
    rw [← Nat.card_congr e, Nat.card_prod, hFK, sq]
  have hpow : Nat.card K ^ Module.finrank K R = Nat.card K ^ 2 := by
    rw [← Module.natCard_eq_pow_finrank, hcard]
  have h1K : 1 < Nat.card K := Finite.one_lt_card
  have h2K : 2 ≤ Nat.card K := by omega
  exact Nat.pow_right_injective h2K hpow

include C in
theorem finrank_range_of_transv [Finite K] (a : Γ) (c γ : Fin n → F) (hc : c ≠ 0)
    (hγ : γ ≠ 0) (hγc : γ ⬝ᵥ c = 0)
    (ha : ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ) :
    Module.finrank K (LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1)) = 2 := by
  have hmem : ∀ r s : F, C.Ψ.symm (r • c, s • γ) ∈
      LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1) := fun r s =>
    (C.mem_range_sub_one_iff a c γ hc hγ hγc ha (C.Ψ.symm (r • c, s • γ))).mpr
      ⟨r, s, by simp⟩
  have hbij : Function.Bijective (fun p : F × F =>
      (⟨C.Ψ.symm (p.1 • c, p.2 • γ), hmem p.1 p.2⟩ :
        LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1))) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨r, s⟩ ⟨r', s'⟩ hpq
      have h1 : C.Ψ.symm (r • c, s • γ) = C.Ψ.symm (r' • c, s' • γ) :=
        congrArg Subtype.val hpq
      have h2 := congrArg C.Ψ h1
      simp only [AddEquiv.apply_symm_apply] at h2
      obtain ⟨h3, h4⟩ := Prod.mk.inj h2
      have h5 : (r - r') • c = 0 := by rw [sub_smul, h3, sub_self]
      have h6 : (s - s') • γ = 0 := by rw [sub_smul, h4, sub_self]
      have hr : r = r' := sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hc)
      have hs : s = s' := sub_eq_zero.mp ((smul_eq_zero.mp h6).resolve_right hγ)
      rw [hr, hs]
    · rintro ⟨v, hv⟩
      obtain ⟨r, s, hrs⟩ := (C.mem_range_sub_one_iff a c γ hc hγ hγc ha v).mp hv
      refine ⟨(r, s), Subtype.ext ?_⟩
      show C.Ψ.symm (r • c, s • γ) = v
      apply C.Ψ.injective
      rw [AddEquiv.apply_symm_apply, hrs]
  exact finrank_eq_two_of_equiv C.θ₁ (LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1))
    (Equiv.ofBijective _ hbij)

include C in
theorem transvection_range [Finite K] (hn : 3 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (a : Γ) (c γ : Fin n → F) (hc : c ≠ 0) (hγ : γ ≠ 0) (hγc : γ ⬝ᵥ c = 0)
    (ha : ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ) :
    ρ a ≠ 1 ∧ (∀ v ∈ LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1), Q.Qf v = 0) ∧
      Module.finrank K (LinearMap.range (((ρ a : E ≃ₗ[K] E) : E →ₗ[K] E) - 1)) = 2 :=
  ⟨C.ne_one_of_transv a c γ hc hγ hγc ha,
    fun v hv => C.Qf_eq_zero_of_mem_range Q (by omega) hrange hQρ hK a c γ hc hγ hγc ha hv,
    C.finrank_range_of_transv a c γ hc hγ hγc ha⟩

end NatDualCoord

end CFSG.RankThree.GF2n.Stroth80
