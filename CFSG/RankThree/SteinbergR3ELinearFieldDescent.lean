module

public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public noncomputable section

namespace CFSG.RankThree.LinearDescent

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.UnitaryDescent
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {K : Type} [Field K] {n : ℕ}

theorem map_eq_glAut (σ : K ≃+* K) (A : GL (Fin n) K) :
    GeneralLinearGroup.map (σ : K →+* K) A = glAut σ A := by
  ext i j
  rw [coe_glAut, Matrix.map_apply]
  rfl

theorem conjAut_mul_fieldAut_pow (σ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    (conjAut n K A * fieldAut n K σ) ^ k =
      conjAut n K (twistedNorm σ A k) * fieldAut n K (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero, twistedNorm_zero, map_one, pow_zero, map_one, mul_one]
  | succ k ih =>
    rw [pow_succ, ih, conjAut_mul_fieldAut_mul, map_eq_glAut, twistedNorm_succ, pow_succ]

private theorem linear_prime_semilinear_field_descent_core {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hn : 3 ≤ n) [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (a : MulAut (projectiveSL n K)) (haE : a ∈ semilinearAutGroup n K)
    (haD : a ∉ linearAutGroup n K) (hap : orderOf a = p) :
    p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧
      (∃ h ∈ linearAutGroup n K, a = h * fieldAut n K σ * h⁻¹) ∧
      Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp haE
  have h1 : (conjAut n K A * fieldAut n K σ) ^ p = 1 := hap ▸ pow_orderOf_eq_one _
  rw [conjAut_mul_fieldAut_pow] at h1
  obtain ⟨hσp, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at haD
    exact haD (conjAut_mem_linearAutGroup A)
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hcL : twistedNorm σ A p = GeneralLinearGroup.scalar (Fin n) c := hc.symm
  have hσc : σ (c : K) = c := by
    have e1 := twistedNorm_succ σ A p
    have e2 := twistedNorm_succ' σ A p
    rw [hσp, map_one, MulAut.one_apply, hcL] at e1
    rw [hcL, glAut_scalar] at e2
    have e3 : GeneralLinearGroup.scalar (Fin n) c * A =
        GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) c) * A := by
      rw [← e1, e2, scalar_mul_comm]
    have e4 := mul_right_cancel e3
    have e5 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) e4
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.coe_map] at e5
    exact e5.symm
  obtain ⟨b, hb⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := (c : K)⁻¹)
    (by rw [map_inv₀, hσc])
  rw [hσ] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (map_zero (σ ^ 0))] at hb
    exact inv_ne_zero c.ne_zero hb.symm
  set A' : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A with hA'
  have hcA' : conjAut n K A' = conjAut n K A := by rw [hA', map_mul, conjAut_scalar, one_mul]
  have hL' : twistedNorm σ A' p = 1 := by
    rw [hA', twistedNorm_scalar_mul, hcL, ← map_mul]
    rw [← map_one (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K)]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.coe_prod]
    simp only [Units.coe_map, Units.val_mk0, Units.val_one]
    change (∏ i ∈ Finset.range p, (σ ^ i) b) * c = 1
    rw [hb, inv_mul_cancel₀ c.ne_zero]
  set γ := semilin σ A' with hγ
  have hγp : ∀ v, (⇑γ)^[p] v = v := fun v => by
    rw [hγ, iterate_semilin, hL', Units.val_one, Matrix.one_mulVec, hσp]
    rfl
  obtain ⟨hpf, k₀, hk₀, hk₀card, bb, hbb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hℓ hf hK σ hσ (Module.finrank_fin_fun K) γ
      (semilin_smul σ _) hγp
  set Bm : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => bb j i with hBm
  have hBmT : Bm = (Pi.basisFun K (Fin n)).toMatrix bb := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  have hBm1 : Bm * bb.toMatrix (Pi.basisFun K (Fin n)) = 1 := by
    rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
  have hBm2 : bb.toMatrix (Pi.basisFun K (Fin n)) * Bm = 1 := by
    rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
  set Mg : GL (Fin n) K := ⟨Bm, bb.toMatrix (Pi.basisFun K (Fin n)), hBm1, hBm2⟩ with hMg
  have hfixM : A' * glAut σ Mg = Mg := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut]
    ext i j
    have := congrFun (hbb j) i
    rw [hγ, semilin_apply] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hMg, hBm] using this
  have hK₀ : semilinearFixedSubfield σ = k₀ := by
    apply SetLike.ext'
    rw [hk₀]
    ext x
    exact Iff.rfl
  refine ⟨hpf, σ, hσ, ⟨conjAut n K Mg, conjAut_mem_linearAutGroup Mg, ?_⟩, by rw [hK₀, hk₀card]⟩
  have e1 : fieldAut n K σ * conjAut n K (Mg⁻¹) * (fieldAut n K σ)⁻¹ =
      conjAut n K (glAut σ (Mg⁻¹)) := by
    rw [htrans.2.2.1, map_eq_glAut]
  have e2 : Mg * glAut σ (Mg⁻¹) = A' := by
    rw [map_inv, mul_inv_eq_iff_eq_mul]
    exact hfixM.symm
  calc conjAut n K A * fieldAut n K σ = conjAut n K A' * fieldAut n K σ := by rw [hcA']
    _ = conjAut n K (Mg * glAut σ (Mg⁻¹)) * fieldAut n K σ := by rw [e2]
    _ = conjAut n K Mg * (fieldAut n K σ * conjAut n K (Mg⁻¹) * (fieldAut n K σ)⁻¹) *
          fieldAut n K σ := by rw [e1, map_mul]
    _ = conjAut n K Mg * fieldAut n K σ * (conjAut n K Mg)⁻¹ := by rw [map_inv]; group

theorem higher_linear_prime_semilinear_field_descent {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hn : 3 ≤ n) [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) :
    (conjAut n K).ker = (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range ∧
    Function.Injective (fieldAut n K) ∧
    ((linearAutGroup n K).subgroupOf (semilinearAutGroup n K)).Normal ∧
    linearAutGroup n K ⊓ (fieldAut n K).range = ⊥ ∧
    linearAutGroup n K ⊔ (fieldAut n K).range = semilinearAutGroup n K ∧
    (linearAutGroup n K).Normal ∧
    (∀ a b : MulAut (projectiveSL n K), a * b * a⁻¹ * b⁻¹ ∈ linearAutGroup n K) ∧
    ∀ p : ℕ, p.Prime → p ≠ ℓ → ∀ a ∈ semilinearAutGroup n K, a ∉ linearAutGroup n K →
      orderOf a = p →
      p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧
        (∃ h ∈ linearAutGroup n K, a = h * fieldAut n K σ * h⁻¹) ∧
        Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hker : (conjAut n K).ker =
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro h1
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by rw [map_one, mul_one, h1])).2
    · rintro ⟨c, rfl⟩
      exact conjAut_scalar c
  have hinj : Function.Injective (fieldAut n K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    exact Subgroup.mem_bot.mpr
      (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 σ (by rw [map_one, one_mul, hσ])).1
  have hDE : ((linearAutGroup n K).subgroupOf (semilinearAutGroup n K)).Normal := by
    constructor
    intro d hd e
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    obtain ⟨A, σ, he⟩ := mem_semilinearAutGroup_iff.mp e.2
    obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.mp hd
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [he, ← hB]
    have h : conjAut n K A * fieldAut n K σ * conjAut n K B *
        (conjAut n K A * fieldAut n K σ)⁻¹ =
        conjAut n K A * (fieldAut n K σ * conjAut n K B * (fieldAut n K σ)⁻¹) *
          (conjAut n K A)⁻¹ := by group
    rw [h, htrans.2.2.1, ← map_inv, ← map_mul, ← map_mul]
    exact conjAut_mem_linearAutGroup _
  have hDF : linearAutGroup n K ⊓ (fieldAut n K).range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, σ, rfl⟩
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hxD
    have h1 : conjAut n K A⁻¹ * fieldAut n K σ = 1 := by rw [map_inv, hA, inv_mul_cancel]
    rw [(eq_one_of_conjAut_mul_fieldAut_eq_one hn _ σ h1).1, map_one]
    exact Subgroup.one_mem _
  have hDFE : linearAutGroup n K ⊔ (fieldAut n K).range = semilinearAutGroup n K := by
    rw [semilinearAutGroup, Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range,
      Subgroup.closure_eq]
  obtain ⟨hR, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDR, -⟩ := standard_outer_quotients (K := K) (n := n)
  have hDn : (linearAutGroup n K).Normal := by
    constructor
    intro d hd x
    have := hDR.conj_mem ⟨d, by rw [hR]; trivial⟩ (Subgroup.mem_subgroupOf.2 hd)
      ⟨x, by rw [hR]; trivial⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hcommAut : ∀ φ ψ : K ≃+* K, φ * ψ = ψ * φ := by
    obtain ⟨F, -, -, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    intro φ ψ
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp
      (htop ▸ Subgroup.mem_top φ : φ ∈ Subgroup.zpowers F)
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp
      (htop ▸ Subgroup.mem_top ψ : ψ ∈ Subgroup.zpowers F)
    exact zpow_mul_comm F a b
  have hδf : ∀ ρ : K ≃+* K, Commute (dualAut n K) (fieldAut n K ρ) := fun ρ => by
    change dualAut n K * fieldAut n K ρ = fieldAut n K ρ * dualAut n K
    calc dualAut n K * fieldAut n K ρ =
          dualAut n K * fieldAut n K ρ * (dualAut n K * dualAut n K) := by
            rw [htrans.2.2.2.1, mul_one]
      _ = fieldAut n K ρ * dualAut n K := by rw [← mul_assoc, htrans.2.2.2.2.2.1 ρ]
  have hab : ∀ a b : MulAut (projectiveSL n K), a * b * a⁻¹ * b⁻¹ ∈ linearAutGroup n K := by
    intro a b
    set π := QuotientGroup.mk' (linearAutGroup n K) with hπ
    have hπker : π.ker = linearAutGroup n K := by rw [hπ, QuotientGroup.ker_mk']
    have hπa : ∀ (C : GL (Fin n) K) (x : MulAut (projectiveSL n K)),
        π (conjAut n K C * x) = π x := fun C x => by
      have h1 : π (conjAut n K C) = 1 := by
        rw [← MonoidHom.mem_ker, hπker]
        exact conjAut_mem_linearAutGroup C
      rw [map_mul, h1, one_mul]
    obtain ⟨A, σ, ε, -, rfl⟩ := hform a
    obtain ⟨B, τ, η, -, rfl⟩ := hform b
    have hff : Commute (fieldAut n K σ) (fieldAut n K τ) := by
      change fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ
      rw [htrans.2.1, htrans.2.1, hcommAut σ τ]
    have hx : Commute (fieldAut n K σ * dualAut n K ^ ε) (fieldAut n K τ * dualAut n K ^ η) := by
      refine Commute.mul_left (Commute.mul_right hff ?_) (Commute.mul_right ?_ ?_)
      · exact ((hδf σ).pow_left η).symm
      · exact (hδf τ).pow_left ε
      · exact Commute.pow_pow_self _ ε η
    have key : π (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε *
        (conjAut n K B * fieldAut n K τ * dualAut n K ^ η) *
        (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε)⁻¹ *
        (conjAut n K B * fieldAut n K τ * dualAut n K ^ η)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc (conjAut n K A),
        mul_assoc (conjAut n K B), hπa, hπa, ← map_mul, hx.eq, map_mul, mul_inv_cancel_right,
        mul_inv_cancel]
    rw [← hπker]
    exact key
  refine ⟨hker, hinj, hDE, hDF, hDFE, hDn, hab, ?_⟩
  intro p hp _ a haE haD hap
  exact linear_prime_semilinear_field_descent_core hℓ hf hn hK hp a haE haD hap

end CFSG.RankThree.LinearDescent
