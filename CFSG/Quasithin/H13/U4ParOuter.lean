module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.H13.U4ParCoord
public import CFSG.Quasithin.H13.U4ParModel

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] noncomputable def barEquiv : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEquiv_apply (c : K) : barEquiv h c = h.bar c := rfl

theorem inr_bar_mem :
    (SemidirectProduct.inr (barEquiv h) : SemiGL (HypIndex 2 0) K) ∈
      semilinearSimilitudes h 2 0 :=
  ⟨1, one_ne_zero, map_one _, by
    rw [SemidirectProduct.left_inr]
    simp⟩

@[expose] noncomputable def frobElt (g : hypSU h 2 0) : hypSU h 2 0 :=
  ⟨glAut (barEquiv h) (g : GL (HypIndex 2 0) K), by
    have := conj_mem_hypSU (inr_bar_mem h) g
    simpa using this⟩

theorem coe_frobElt (g : hypSU h 2 0) :
    (((frobElt h g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar :=
  coe_glAut _ _

theorem frobElt_frobElt (g : hypSU h 2 0) : frobElt h (frobElt h g) = g := by
  apply hypSU_ext h
  rw [coe_frobElt, coe_frobElt]
  ext i j
  simp [h.bar_bar]

@[expose] noncomputable def frob : hypSU h 2 0 ≃* hypSU h 2 0 where
  toFun := frobElt h
  invFun := frobElt h
  left_inv := frobElt_frobElt h
  right_inv := frobElt_frobElt h
  map_mul' g g' := by
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_frobElt, coe_frobElt, coe_frobElt, coe_mul_hypSU, Matrix.map_mul]

theorem frob_apply (g : hypSU h 2 0) : frob h g = frobElt h g := rfl

theorem hypProj_injective : Function.Injective (hypProj h 2 0) := by
  rw [← MonoidHom.ker_eq_bot_iff, hypProj, QuotientGroup.ker_mk', hypScalars_eq_bot h]

theorem det_mul_bar_det_of_mem_hypUnitary {A : GL (HypIndex 2 0) K}
    (hA : A ∈ hypUnitary h 2 0) :
    h.bar (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = 1 := by
  have e := congrArg Matrix.det (mem_hypUnitary.mp hA)
  rw [det_mul, det_mul, det_transpose,
    show ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar).det =
      h.bar (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det from
      (RingHom.map_det h.bar _).symm] at e
  have hJ : (hypGram 2 0 K).det ≠ 0 := by
    intro h0
    have h1 : hypGram 2 0 K * hypGram 2 0 K = 1 := by
      ext a b
      rw [hypGram_mul_apply, hypGram_apply, one_apply, hypPartner_hypPartner]
      simp [eq_comm]
    have := congrArg Matrix.det h1
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have e' : (h.bar (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det - 1) * (hypGram 2 0 K).det = 0 := by
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hJ)

theorem exists_su_rep {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) :
    ∃ (g : hypSU h 2 0) (ε : Kˣ),
      (A : GL (HypIndex 2 0) K) = GeneralLinearGroup.scalar (HypIndex 2 0) ε * g := by
  have := h.finite
  have := Fintype.ofFinite K
  have := h.charP
  set δ := (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det with hδ
  have hN := det_mul_bar_det_of_mem_hypUnitary h hA
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [← hδ, h0, mul_zero] at hN
    exact zero_ne_one hN
  have hm := h.one_le
  set k := 4 ^ (m - 1) with hk
  have hcard : Fintype.card K = 4 ^ m := by
    rw [← Nat.card_eq_fintype_card, h.card, pow_mul]
    norm_num
  have h4k : 4 * k = Fintype.card K := by
    rw [hcard, hk, ← pow_succ']
    congr 1
    omega
  set ε : K := δ ^ k with hε
  have hε0 : ε ≠ 0 := pow_ne_zero _ hδ0
  have hε4 : ε ^ 4 = δ := by
    rw [hε, ← pow_mul, mul_comm, h4k, FiniteField.pow_card]
  have hεN : h.bar ε * ε = 1 := by
    rw [hε, map_pow, ← mul_pow, hδ, hN, one_pow]
  let εu : Kˣ := Units.mk0 ε hε0
  let B : GL (HypIndex 2 0) K := GeneralLinearGroup.scalar (HypIndex 2 0) εu⁻¹ * A
  have hB : B ∈ hypSU h 2 0 := by
    rw [mem_gramSU]
    have hεi : ((εu⁻¹ : Kˣ) : K) = ε⁻¹ := by simp [εu]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, conjTranspose_mul_mul, GeneralLinearGroup.coe_scalar, scalar_gram,
        Matrix.mul_smul, Matrix.smul_mul, mem_hypUnitary.mp hA, hεi, UnitaryFieldData.norm,
        map_inv₀, ← mul_inv, mul_comm, hεN, inv_one, one_smul]
    · rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        det_diagonal, Finset.prod_const, Finset.card_univ, ← hδ, hεi]
      have hc : Fintype.card (HypIndex 2 0) = 4 := by decide
      rw [hc, inv_pow, ← hε4, inv_mul_cancel₀ (pow_ne_zero _ hε0)]
  refine ⟨⟨B, hB⟩, εu, ?_⟩
  change A = GeneralLinearGroup.scalar (HypIndex 2 0) εu *
    (GeneralLinearGroup.scalar (HypIndex 2 0) εu⁻¹ * A)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem exists_frob_elt {Ŷ : Type} [Group Ŷ] (ψ : hypSU h 2 0 →* Ŷ) (hψ : Function.Injective ψ)
    (hidx : ψ.range.index = 2) (hC : Subgroup.centralizer (ψ.range : Set Ŷ) = ⊥) :
    ∃ y₀ : Ŷ, y₀ ∉ ψ.range ∧ y₀ * y₀ = 1 ∧ ∀ g : hypSU h 2 0, y₀ * ψ g * y₀⁻¹ = ψ (frob h g) := by
  have hn : ψ.range.Normal := Subgroup.normal_of_index_eq_two hidx
  have hne : ψ.range ≠ ⊤ := fun ht => by
    rw [ht, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  let e : hypSU h 2 0 ≃* ψ.range := MonoidHom.ofInjective hψ
  let θ : MulAut (hypSU h 2 0) := (e.trans (MulAut.conjNormal x)).trans e.symm
  have hθ : ∀ g, ψ (θ g) = x * ψ g * x⁻¹ := by
    intro g
    have h1 : (e (θ g) : Ŷ) = ψ (θ g) := MonoidHom.ofInjective_apply hψ
    rw [← h1]
    change ((e (e.symm (MulAut.conjNormal x (e g))) : ψ.range) : Ŷ) = _
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]
  let π := hypProj h 2 0
  let θ' : MulAut (hypPSU h 2 0) :=
    ((hypSUEquivPSU h).symm.trans θ).trans (hypSUEquivPSU h)
  have hπ : ∀ g, hypSUEquivPSU h g = π g := fun g => rfl
  have hθ' : ∀ g, θ' (π g) = π (θ g) := by
    intro g
    change hypSUEquivPSU h (θ ((hypSUEquivPSU h).symm (π g))) = π (θ g)
    rw [← hπ g, MulEquiv.symm_apply_apply, hπ]
  have hr : 1 ≤ 2 := by norm_num
  have hε : 0 ≤ 1 := by norm_num
  have hn4 : 3 ≤ 2 * 2 + 0 := by norm_num
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn4
    (fun h' => by omega) θ'
  obtain ⟨x₁, hx₁, -, hU⟩ := exists_unitary_rep h hr hε hn4 x₀
  rw [hx₀] at hx₁
  set A := (x₁ : SemiGL (HypIndex 2 0) K).left with hA
  set σ := (x₁ : SemiGL (HypIndex 2 0) K).right with hσ
  have hθA : ∀ g : hypSU h 2 0, ((θ g : hypSU h 2 0) : GL (HypIndex 2 0) K) =
      A * glAut σ (g : GL (HypIndex 2 0) K) * A⁻¹ := by
    intro g
    have h1 := semilinearAutHom_apply h hr hε x₁ g
    rw [hx₁, hθ'] at h1
    have h2 := hypProj_injective h h1
    exact congrArg Subtype.val h2
  obtain ⟨g₁, hg₁⟩ : x * x ∈ ψ.range := Subgroup.mul_self_mem_of_index_two hidx x
  have hθθ : ∀ g, θ (θ g) = g₁ * g * g₁⁻¹ := by
    intro g
    apply hψ
    rw [hθ, hθ, map_mul, map_mul, map_inv, hg₁]
    group
  let y₁ : semilinearSimilitudes h 2 0 :=
    ⟨SemidirectProduct.inl (g₁ : GL (HypIndex 2 0) K),
      ⟨1, one_ne_zero, map_one _, by
        rw [SemidirectProduct.left_inl, one_smul]
        exact (mem_gramSU.mp g₁.2).1⟩⟩
  have hΦ1 : semilinearAutHom h hr hε (x₁ * x₁ * y₁⁻¹) = 1 := by
    have hy₁ : semilinearAutHom h hr hε y₁ = θ' * θ' := by
      refine MulEquiv.ext fun z => ?_
      obtain ⟨g, rfl⟩ := hypProj_surjective h 2 0 z
      rw [semilinearAutHom_apply, MulAut.mul_apply, hθ', hθ', hθθ]
      congr 1
    rw [map_mul, map_mul, map_inv, hx₁, hy₁, mul_inv_cancel]
  have hσ2 : σ * σ = 1 := by
    have h1 := ((semilinearAutHom_eq_one_iff h hr hε hn4 _).mp hΦ1).1
    have e1 : ((x₁ * x₁ * y₁⁻¹ : semilinearSimilitudes h 2 0) :
        SemiGL (HypIndex 2 0) K).right = σ * σ := by
      simp [σ, y₁, SemidirectProduct.mul_right]
    rw [e1] at h1
    exact h1
  obtain ⟨a, εu, hAa⟩ := exists_su_rep h hU
  have hc : ∀ X : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) εu * X =
      X * GeneralLinearGroup.scalar (HypIndex 2 0) εu := fun X => by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, mul_comm]
  have hθa : ∀ g : hypSU h 2 0, ((θ g : hypSU h 2 0) : GL (HypIndex 2 0) K) =
      (a : GL (HypIndex 2 0) K) * glAut σ (g : GL (HypIndex 2 0) K) *
        (a : GL (HypIndex 2 0) K)⁻¹ := by
    intro g
    rw [hθA g, hAa]
    have hcen : ∀ Y : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) εu * Y *
        (GeneralLinearGroup.scalar (HypIndex 2 0) εu)⁻¹ = Y := fun Y => by
      rw [hc Y, mul_assoc, mul_inv_cancel, mul_one]
    calc GeneralLinearGroup.scalar (HypIndex 2 0) εu * (a : GL (HypIndex 2 0) K) *
          glAut σ (g : GL (HypIndex 2 0) K) *
          (GeneralLinearGroup.scalar (HypIndex 2 0) εu * (a : GL (HypIndex 2 0) K))⁻¹ =
        GeneralLinearGroup.scalar (HypIndex 2 0) εu * ((a : GL (HypIndex 2 0) K) *
          glAut σ (g : GL (HypIndex 2 0) K) * (a : GL (HypIndex 2 0) K)⁻¹) *
          (GeneralLinearGroup.scalar (HypIndex 2 0) εu)⁻¹ := by group
      _ = _ := hcen _
  rcases ringEquiv_eq_refl_or_bar h hσ2 with hσ1 | hσb
  ·
    exfalso
    have hθg : ∀ g, θ g = a * g * a⁻¹ := by
      intro g
      apply Subtype.ext
      rw [hθa g, hσ1]
      change (a : GL (HypIndex 2 0) K) * glAut 1 (g : GL (HypIndex 2 0) K) *
        (a : GL (HypIndex 2 0) K)⁻¹ = _
      rw [map_one, MulAut.one_apply]
      rfl
    have hy : ψ a⁻¹ * x ∈ Subgroup.centralizer (ψ.range : Set Ŷ) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, rfl⟩
      have h1 : ψ a⁻¹ * x * ψ g * (ψ a⁻¹ * x)⁻¹ = ψ g := by
        have h2 : x * ψ g * x⁻¹ = ψ (a * g * a⁻¹) := by rw [← hθ, hθg]
        calc ψ a⁻¹ * x * ψ g * (ψ a⁻¹ * x)⁻¹ = ψ a⁻¹ * (x * ψ g * x⁻¹) * (ψ a⁻¹)⁻¹ := by group
          _ = ψ g := by rw [h2, ← map_inv, ← map_mul, ← map_mul]; congr 1; group
      calc ψ g * (ψ a⁻¹ * x) = (ψ a⁻¹ * x * ψ g * (ψ a⁻¹ * x)⁻¹) * (ψ a⁻¹ * x) := by rw [h1]
        _ = ψ a⁻¹ * x * ψ g := by group
    rw [hC, Subgroup.mem_bot] at hy
    apply hx
    have : x = ψ a := by
      calc x = ψ a * (ψ a⁻¹ * x) := by rw [map_inv]; group
        _ = ψ a := by rw [hy, mul_one]
    rw [this]
    exact ⟨a, rfl⟩
  ·
    have hθg : ∀ g, θ g = a * frob h g * a⁻¹ := by
      intro g
      apply Subtype.ext
      rw [hθa g]
      have e1 : glAut σ (g : GL (HypIndex 2 0) K) = ((frob h g : hypSU h 2 0) :
          GL (HypIndex 2 0) K) := by
        apply Units.ext
        rw [coe_glAut, frob_apply, coe_frobElt]
        ext i j
        exact hσb _
      rw [e1]
      rfl
    have hact : ∀ g, ψ a⁻¹ * x * ψ g * (ψ a⁻¹ * x)⁻¹ = ψ (frob h g) := by
      intro g
      have h2 : x * ψ g * x⁻¹ = ψ (a * frob h g * a⁻¹) := by rw [← hθ, hθg]
      calc ψ a⁻¹ * x * ψ g * (ψ a⁻¹ * x)⁻¹ = ψ a⁻¹ * (x * ψ g * x⁻¹) * (ψ a⁻¹)⁻¹ := by group
        _ = ψ (frob h g) := by rw [h2, ← map_inv, ← map_mul, ← map_mul]; congr 1; group
    refine ⟨ψ a⁻¹ * x, fun hmem => hx ?_, ?_, hact⟩
    · have : x = ψ a * (ψ a⁻¹ * x) := by rw [map_inv]; group
      rw [this]
      exact ψ.range.mul_mem ⟨a, rfl⟩ hmem
    · have hy : (ψ a⁻¹ * x) * (ψ a⁻¹ * x) ∈ Subgroup.centralizer (ψ.range : Set Ŷ) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨g, rfl⟩
        have h1 : (ψ a⁻¹ * x) * (ψ a⁻¹ * x) * ψ g * ((ψ a⁻¹ * x) * (ψ a⁻¹ * x))⁻¹ = ψ g := by
          calc (ψ a⁻¹ * x) * (ψ a⁻¹ * x) * ψ g * ((ψ a⁻¹ * x) * (ψ a⁻¹ * x))⁻¹ =
              (ψ a⁻¹ * x) * ((ψ a⁻¹ * x) * ψ g * (ψ a⁻¹ * x)⁻¹) * (ψ a⁻¹ * x)⁻¹ := by group
            _ = ψ g := by rw [hact, hact, frob_apply, frob_apply, frobElt_frobElt]
        calc ψ g * ((ψ a⁻¹ * x) * (ψ a⁻¹ * x)) =
            ((ψ a⁻¹ * x) * (ψ a⁻¹ * x) * ψ g * ((ψ a⁻¹ * x) * (ψ a⁻¹ * x))⁻¹) *
              ((ψ a⁻¹ * x) * (ψ a⁻¹ * x)) := by rw [h1]
          _ = (ψ a⁻¹ * x) * (ψ a⁻¹ * x) * ψ g := by group
      rw [hC, Subgroup.mem_bot] at hy
      exact hy

end CFSG.Quasithin.H13.U4Par
