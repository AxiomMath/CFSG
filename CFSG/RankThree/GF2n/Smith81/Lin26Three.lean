module

public import CFSG.RankThree.GF2n.Smith81.Lin26Scalar
public import CFSG.RankThree.GF2n.Smith81.Lin26NatDual
public import CFSG.RankThree.GF2n.Smith81.Lin26Normal
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section SL

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem RestModel.injective_of_qf (R : RestModel M Q Z n V₁ V₂) (U : R.M₀.E →ₗ[R.K] R.M₀.E)
    (hU : ∀ e, R.M₀.Qf (U e) = R.M₀.Qf e) : Function.Injective U := by
  have hB := R.B_of_qf U 1 (fun e => by rw [hU e, one_mul])
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro e he
  refine R.M₀.nondeg e fun e' => ?_
  rw [← one_mul (R.M₀.B e e'), ← hB, he, map_zero, LinearMap.zero_apply]

theorem RestModel.slProp_of_three (R : RestModel M Q Z n V₁ V₂) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) : R.SLProp := by
  classical
  intro U hUQ h₁ h₂ hdet
  obtain ⟨F₀, hF₀field, hF₀fin, hF₀card, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φc, hΦc, hΦ₁, hΦ₂⟩ := exists_equivariant_coord R.M₀
    (R.φ.comp (Subgroup.inclusion hSH)) (fun s x hx => R.φπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂
    hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (R.φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [R.gm.card, hF₀card]) Φc hΦc
  have hW₁ : ∀ e, e ∈ R.W₁ ↔ e ∈ C.W₁ := fun e => by
    rw [R.memW₁, C.mem_W₁, hCΦ, hΦ₁]
  have hW₂ : ∀ e, e ∈ R.W₂ ↔ e ∈ C.W₂ := fun e => by
    rw [R.memW₂, C.mem_W₂, hCΦ, hΦ₂]
  have hinj := R.injective_of_qf U hUQ
  let T : R.M₀.E ≃ₗ[R.K] R.M₀.E := LinearEquiv.ofInjectiveEndo U hinj
  have hTU : ∀ e, T e = U e := fun e => rfl
  have hTQ : ∀ e, R.M₀.Qf (T e) = R.M₀.Qf e := fun e => by rw [hTU, hUQ]
  have hP : C.Preserves T := by
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rw [hTU]
      exact (hW₁ _).mp (h₁ _ ((hW₁ _).mpr (C.inl_mem_W₁ x)))
    · rw [hTU]
      exact (hW₂ _).mp (h₂ _ ((hW₂ _).mpr (C.inr_mem_W₂ y)))
  let ψ : ↥R.W₁ ≃+ (Fin n → F₀) :=
    { toFun := fun w => (C.Ψ (w : R.M₀.E)).1
      invFun := fun x => ⟨C.inl x, (hW₁ _).mpr (C.inl_mem_W₁ x)⟩
      left_inv := fun w => by
        apply Subtype.ext
        show C.inl (C.Ψ (w : R.M₀.E)).1 = w
        exact ((C.eq_inl_of_mem_W₁ ((hW₁ _).mp w.2)).symm)
      right_inv := fun x => by
        show (C.Ψ (C.inl x)).1 = x
        rw [NatDualCoord.Ψ_inl]
      map_add' := fun a b => by
        show (C.Ψ ((a : R.M₀.E) + b)).1 = (C.Ψ a).1 + (C.Ψ b).1
        rw [map_add]; rfl }
  have hψ : ∀ (c : R.K) (w : ↥R.W₁), ψ (c • w) = C.θ₁ c • ψ w := fun c w => by
    show (C.Ψ (c • (w : R.M₀.E))).1 = C.θ₁ c • (C.Ψ (w : R.M₀.E)).1
    rw [C.smul]
  obtain ⟨A', hA'v, hA'd⟩ := exists_matrix_det_eq C.θ₁ ψ hψ (U.restrict h₁)
  have hdetF : ∀ A : Matrix (Fin n) (Fin n) F₀,
      (∀ x, (C.Ψ (T (C.inl x))).1 = A *ᵥ x) → A.det = 1 := by
    intro A hA
    have hAA : A = A' := by
      refine Matrix.ext_iff_mulVec.mpr fun x => ?_
      have h1 := hA'v ⟨C.inl x, (hW₁ _).mpr (C.inl_mem_W₁ x)⟩
      have h2 : ψ ((U.restrict h₁) ⟨C.inl x, (hW₁ _).mpr (C.inl_mem_W₁ x)⟩) =
          (C.Ψ (T (C.inl x))).1 := rfl
      have h3 : ψ ⟨C.inl x, (hW₁ _).mpr (C.inl_mem_W₁ x)⟩ = x := by
        show (C.Ψ (C.inl x)).1 = x
        rw [NatDualCoord.Ψ_inl]
      rw [h2, h3] at h1
      rw [← hA x, h1]
    rw [hAA, hA'd, hdet, map_one]
  have hK : ∃ c : R.K, c ≠ 0 ∧ c ^ 2 ≠ 1 :=
    exists_ne_zero_sq_ne_one_of_two_lt_card R.K (by
      rw [R.gm.card]; have := hc.hyp.q4; omega)
  obtain ⟨g, hg⟩ := C.exists_eq_of_preserves_det (quadDatumOfModel R.M₀) hn hrange
    (fun g e => R.φQf _ e) hK T hTQ hP hdetF
  refine ⟨(g : G), (hSH g.2).1, fun x hx => ?_⟩
  have h4 := R.φπ ⟨(g : G), hSH g.2⟩ x hx
  rw [h4, ← hTU]
  exact (LinearEquiv.congr_fun hg _).symm ▸ rfl

end SL

section Main


theorem lin26Scalar_of_three (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ)
    (V₁ V₂ : Subgroup G) (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ c ∈ M, ∃ ν : Kˣ, ν ≠ 1 ∧ ∀ x ∈ Q, M₀.π (c * x * c⁻¹) = (ν : K) • M₀.π x := by
  obtain ⟨V₁', V₂', hS', -, h31⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS (by omega)
  obtain ⟨R⟩ := exists_restModel hc hS' hn
  have hsl := R.slProp_of_three hc hS' hn
  obtain ⟨Y₂, hY₂, hY₂V⟩ := R.exists_root (by omega) fun v hv hv1 =>
    (h31 v (R.V₂Q hv) hv1).mpr (Or.inr hv)
  obtain ⟨Y₁, hY₁, hY₁V⟩ := R.symm.exists_root (by omega) fun v hv hv1 =>
    (h31 v (R.V₁Q hv) hv1).mpr (Or.inl hv)
  have hmod := linModuleStatement_holds G M Q Z B n V₁' V₂' hb hc hS' hn
  obtain ⟨c, hcM, ν, hν, hcπ⟩ := R.exists_scalar (by omega) hsl h31
    ⟨Y₁, hY₁, hY₁V, (hmod Y₁ hY₁.conj hY₁.ne).1 hY₁V⟩
    ⟨Y₂, hY₂, hY₂V, (hmod Y₂ hY₂.conj hY₂.ne).2 hY₂V⟩
  exact ⟨R.K, R.instField, R.instFinite, R.instChar, R.γ, R.M₀, R.gm, c, hcM, ν, hν, hcπ⟩

end Main

section Normal

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.exists_scalar_normal (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ A : Subgroup G, Q ≤ A ∧ A ≤ M ∧
      M ≤ Subgroup.normalizer (A : Set G) ∧ (∀ a ∈ A, ∃ k : ℕ, a ^ p ^ k ∈ Q) ∧
      (∀ a ∈ A, ∀ s ∈ Lgen M (LB M Q B), a * s * a⁻¹ * s⁻¹ ∈ Q) ∧
      ∃ c ∈ A, ∀ u ∈ Q, ∀ y ∈ Q, y * (c * u) = c * u * y → y = 1 := by
  obtain ⟨K, _, _, _, γ, M₀, gm, c, hcM, ν, hν, hcπ⟩ :=
    lin26Scalar_of_three G M Q Z B n V₁ V₂ hb hc hS hn
  exact exists_scalar_normal_of_scalar hc.hyp gm (Lgen_le_H0 hc) hcM hν hcπ

end Normal

end CFSG.RankThree.GF2n.Smith81
