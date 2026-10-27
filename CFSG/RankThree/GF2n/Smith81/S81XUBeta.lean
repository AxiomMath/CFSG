module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Form
public import CFSG.RankThree.GF2n.Smith81.S81UModel

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

section Beta

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]
  (e : K ≃+* Fσ σ)

theorem betaU_e3uVal_wact (g : SUid σ 6) (w : E3UWspace σ e) :
    e3uVal (e3uWact σ e g w) = rho F (g : GL (Fin 6) F) (e3uVal w) := rfl

theorem betaU_det_SUid (g : SUid σ 6) :
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
  ((CFSG.ClassicalGroups.Unitary.mem_SUid_iff σ).mp g.2).1

@[expose] noncomputable def betaUFs (hσ : ∀ c, σ (σ c) = c) (x y : E3UWspace σ e) : Fσ σ :=
  ⟨beta F (e3uVal x) (e3uVal y),
    U6Cube.mem_Fσ_iff.mpr (U6Cube.beta_mem_fixed hσ
      (U6Cube.mem_Wform_iff.mp (show U6Cube.Wform σ from x).2)
      (U6Cube.mem_Wform_iff.mp (show U6Cube.Wform σ from y).2))⟩

theorem betaUFs_val (hσ : ∀ c, σ (σ c) = c) (x y : E3UWspace σ e) :
    ((betaUFs e hσ x y : Fσ σ) : F) = beta F (e3uVal x) (e3uVal y) := rfl

theorem betaUFs_add_left (hσ : ∀ c, σ (σ c) = c) (x y z : E3UWspace σ e) :
    betaUFs e hσ (x + y) z = betaUFs e hσ x z + betaUFs e hσ y z := by
  apply Subtype.ext
  show beta F (e3uVal x + e3uVal y) (e3uVal z) =
    beta F (e3uVal x) (e3uVal z) + beta F (e3uVal y) (e3uVal z)
  rw [map_add, LinearMap.add_apply]

theorem betaUFs_add_right (hσ : ∀ c, σ (σ c) = c) (x y z : E3UWspace σ e) :
    betaUFs e hσ x (y + z) = betaUFs e hσ x y + betaUFs e hσ x z := by
  apply Subtype.ext
  show beta F (e3uVal x) (e3uVal y + e3uVal z) =
    beta F (e3uVal x) (e3uVal y) + beta F (e3uVal x) (e3uVal z)
  rw [map_add]

theorem betaUFs_smul_left (hσ : ∀ c, σ (σ c) = c) (c : K) (x z : E3UWspace σ e) :
    betaUFs e hσ (c • x) z = e c * betaUFs e hσ x z := by
  apply Subtype.ext
  show beta F (((e c : Fσ σ) : F) • e3uVal x) (e3uVal z) =
    ((e c : Fσ σ) : F) * beta F (e3uVal x) (e3uVal z)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem betaUFs_smul_right (hσ : ∀ c, σ (σ c) = c) (c : K) (x z : E3UWspace σ e) :
    betaUFs e hσ x (c • z) = e c * betaUFs e hσ x z := by
  apply Subtype.ext
  show beta F (e3uVal x) (((e c : Fσ σ) : F) • e3uVal z) =
    ((e c : Fσ σ) : F) * beta F (e3uVal x) (e3uVal z)
  rw [map_smul, smul_eq_mul]

theorem betaUFs_wact (hσ : ∀ c, σ (σ c) = c) (g : SUid σ 6) (x y : E3UWspace σ e) :
    betaUFs e hσ (e3uWact σ e g x) (e3uWact σ e g y) = betaUFs e hσ x y := by
  apply Subtype.ext
  show beta F (e3uVal (e3uWact σ e g x)) (e3uVal (e3uWact σ e g y)) =
    beta F (e3uVal x) (e3uVal y)
  rw [betaU_e3uVal_wact, betaU_e3uVal_wact, A5Cube.beta_rho, betaU_det_SUid g, one_mul]

theorem betaUFs_skew (hσ : ∀ c, σ (σ c) = c) (x y : E3UWspace σ e) :
    betaUFs e hσ x y = -betaUFs e hσ y x := by
  apply Subtype.ext
  show beta F (e3uVal x) (e3uVal y) = -beta F (e3uVal y) (e3uVal x)
  exact A5Cube.beta_skew (e3uVal x) (e3uVal y)

theorem betaU_add_left (hσ : ∀ c, σ (σ c) = c) (m₁ m₂ n : E3UWspace σ e) :
    e.symm (betaUFs e hσ (m₁ + m₂) n) = e.symm (betaUFs e hσ m₁ n) + e.symm (betaUFs e hσ m₂ n) := by
  rw [betaUFs_add_left e hσ m₁ m₂ n, map_add]

theorem betaU_smul_left (hσ : ∀ c, σ (σ c) = c) (c : K) (m n : E3UWspace σ e) :
    e.symm (betaUFs e hσ (c • m) n) = c • e.symm (betaUFs e hσ m n) := by
  rw [betaUFs_smul_left e hσ c m n, map_mul, RingEquiv.symm_apply_apply, smul_eq_mul]

theorem betaU_add_right (hσ : ∀ c, σ (σ c) = c) (m n₁ n₂ : E3UWspace σ e) :
    e.symm (betaUFs e hσ m (n₁ + n₂)) = e.symm (betaUFs e hσ m n₁) + e.symm (betaUFs e hσ m n₂) := by
  rw [betaUFs_add_right e hσ m n₁ n₂, map_add]

theorem betaU_smul_right (hσ : ∀ c, σ (σ c) = c) (c : K) (m n : E3UWspace σ e) :
    e.symm (betaUFs e hσ m (c • n)) = c • e.symm (betaUFs e hσ m n) := by
  rw [betaUFs_smul_right e hσ c m n, map_mul, RingEquiv.symm_apply_apply, smul_eq_mul]

@[expose] noncomputable def betaU (hσ : ∀ c, σ (σ c) = c) :
    E3UWspace σ e →ₗ[K] E3UWspace σ e →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => e.symm (betaUFs e hσ x y)) (betaU_add_left e hσ)
    (betaU_smul_left e hσ) (betaU_add_right e hσ) (betaU_smul_right e hσ)

theorem betaU_eq (hσ : ∀ c, σ (σ c) = c) (x y : E3UWspace σ e) :
    betaU e hσ x y = e.symm (betaUFs e hσ x y) := rfl

theorem betaU_apply (hσ : ∀ c, σ (σ c) = c) (x y : E3UWspace σ e) :
    ((e (betaU e hσ x y) : Fσ σ) : F) = beta F (e3uVal x) (e3uVal y) := by
  rw [betaU_eq e hσ x y, RingEquiv.apply_symm_apply]
  exact betaUFs_val e hσ x y

theorem betaU_wact (hσ : ∀ c, σ (σ c) = c) (g : SUid σ 6) (x y : E3UWspace σ e) :
    betaU e hσ (e3uWact σ e g x) (e3uWact σ e g y) = betaU e hσ x y := by
  rw [betaU_eq e hσ (e3uWact σ e g x) (e3uWact σ e g y), betaU_eq e hσ x y,
    betaUFs_wact e hσ g x y]

theorem betaU_skew (hσ : ∀ c, σ (σ c) = c) (x y : E3UWspace σ e) :
    betaU e hσ x y = - betaU e hσ y x := by
  rw [betaU_eq e hσ x y, betaU_eq e hσ y x, betaUFs_skew e hσ x y, map_neg]

theorem hformU_K (hσ : IsUnitaryInvolution σ) {G : Type} [Group G] {Q Z : Subgroup G} {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] E3UWspace σ e}
    (hform : ∃ lam : F, lam ≠ 0 ∧ ∀ e' f' : M₀.E,
      ((e (M₀.B e' f') : Fσ σ) : F) = lam * beta F (e3uVal (ψ e')) (e3uVal (ψ f'))) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ e' f' : M₀.E, M₀.B e' f' = lam * betaU e hσ.invol (ψ e') (ψ f') := by
  obtain ⟨lam, hlam0, hlam⟩ := hform
  have hpW : pt0 F ∈ Wsub σ := mem_Wsub_iff.mpr theta_pt0
  obtain ⟨η, hηW, hηne⟩ : ∃ η ∈ Wsub σ, beta F (pt0 F) η ≠ 0 := by
    by_contra hcon
    exact pt0_ne_zero (K := F) (beta_nondeg_Wsub hσ hpW fun η hη => by
      by_contra h
      exact hcon ⟨η, hη, h⟩)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E3UWspace σ e, e3uVal x₀ = pt0 F := ⟨e3uP0 σ e, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : E3UWspace σ e, e3uVal y = η :=
    ⟨show E3UWspace σ e from (show Wform σ from ⟨η, mem_Wform_iff.mpr hηW⟩), rfl⟩
  have hB : beta F (e3uVal x₀) (e3uVal y) ≠ 0 := by
    rw [hx₀, hy]
    exact hηne
  obtain ⟨c₁, hc₁⟩ : ∃ c : Fσ σ, (c : F) = beta F (e3uVal x₀) (e3uVal y) :=
    ⟨_, betaU_apply e hσ.invol x₀ y⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : Fσ σ, (c : F) = lam * beta F (e3uVal x₀) (e3uVal y) := by
    refine ⟨e (M₀.B (ψ.symm x₀) (ψ.symm y)), ?_⟩
    have h := hlam (ψ.symm x₀) (ψ.symm y)
    rwa [ψ.apply_symm_apply, ψ.apply_symm_apply] at h
  have hc₁ne : (c₁ : F) ≠ 0 := by
    rw [hc₁]
    exact hB
  have hc₂' : (c₂ : F) = lam * (c₁ : F) := by
    rw [hc₂, hc₁]
  have h1 : σ (c₂ : F) = (c₂ : F) := mem_Fσ_iff.mp c₂.2
  have h2 : σ (c₁ : F) = (c₁ : F) := mem_Fσ_iff.mp c₁.2
  have key : σ lam * (c₁ : F) = lam * (c₁ : F) := by
    calc σ lam * (c₁ : F) = σ lam * σ (c₁ : F) := by rw [h2]
      _ = σ (lam * (c₁ : F)) := (map_mul σ _ _).symm
      _ = σ (c₂ : F) := by rw [hc₂']
      _ = (c₂ : F) := h1
      _ = lam * (c₁ : F) := hc₂'
  have hmem : lam ∈ Fσ σ := mem_Fσ_iff.mpr (mul_right_cancel₀ hc₁ne key)
  refine ⟨e.symm ⟨lam, hmem⟩, ?_, ?_⟩
  · intro h0
    apply hlam0
    have h3 := congrArg e h0
    rw [RingEquiv.apply_symm_apply, map_zero] at h3
    exact congrArg Subtype.val h3
  · intro e' f'
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply]
    apply Subtype.ext
    show ((e (M₀.B e' f') : Fσ σ) : F) = lam * ((e (betaU e hσ.invol (ψ e') (ψ f')) : Fσ σ) : F)
    rw [hlam e' f', betaU_apply e hσ.invol (ψ e') (ψ f')]

end Beta

end CFSG.RankThree.GF2n.Smith81
