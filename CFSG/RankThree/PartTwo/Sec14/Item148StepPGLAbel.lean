module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepPGL

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial

theorem exists_detPow_projImage {K : Type} [Field K] (H : Subgroup (GL (Fin 3) K)) (m : ℕ)
    (hker : ∀ A ∈ H, A ∈ Subgroup.center (GL (Fin 3) K) → GeneralLinearGroup.det A ^ m = 1) :
    ∃ δ : ↥(projImage H) →* Kˣ, ∀ (A : GL (Fin 3) K) (hA : A ∈ H),
      δ ⟨ProjGenLinGroup.mk A, Subgroup.mem_map.mpr ⟨A, hA, rfl⟩⟩ =
        GeneralLinearGroup.det A ^ m := by
  set F : H →* ProjGenLinGroup (Fin 3) K := ProjGenLinGroup.mk.comp H.subtype with hF
  set D : H →* Kˣ := (powMonoidHom m).comp (GeneralLinearGroup.det.comp H.subtype) with hD
  have hk : F.ker ≤ D.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    have hc : (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [← ProjGenLinGroup.mk_eq_one]
      exact hA
    exact hker A A.2 hc
  have hr : F.range = projImage H := by
    rw [hF, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  refine ⟨(QuotientGroup.lift F.ker D hk).comp
    ((QuotientGroup.quotientKerEquivRange F).symm.toMonoidHom.comp
      (MulEquiv.subgroupCongr hr.symm).toMonoidHom), fun A hA => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivRange F).symm
      ((MulEquiv.subgroupCongr hr.symm) ⟨ProjGenLinGroup.mk A,
        Subgroup.mem_map.mpr ⟨A, hA, rfl⟩⟩) = ((⟨A, hA⟩ : H) : H ⧸ F.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1,
    QuotientGroup.lift_mk, hD]
  rfl

noncomputable def diagGL148 {K : Type} [Field K] (t : Kˣ) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal ![(t : K), 1, 1]) (by
    rw [det_diagonal, Fin.prod_univ_three]
    simp)

theorem det_diagGL148 {K : Type} [Field K] (t : Kˣ) : GeneralLinearGroup.det (diagGL148 t) = t := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  change (diagonal ![(t : K), 1, 1]).det = t
  rw [det_diagonal, Fin.prod_univ_three]
  simp

theorem det_scalar148 {K : Type} [Field K] (u : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
    det_diagonal, Fin.prod_univ_three, Units.val_pow_eq_pow_val]
  ring

theorem exists_detPow_data_glPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : Sec4.PiField π p f K) (hmod : Sec4.ModThree π (p ^ f)) :
    ∃ m : ℕ, (∀ A ∈ Sec4.glPi π 3 (p ^ f) K, A ∈ Subgroup.center (GL (Fin 3) K) →
        GeneralLinearGroup.det A ^ m = 1) ∧
      (∀ A ∈ Sec4.glPi π 3 (p ^ f) K, GeneralLinearGroup.det A ^ (3 * m) = 1) ∧
      ∃ A₀ ∈ Sec4.glPi π 3 (p ^ f) K, GeneralLinearGroup.det A₀ ^ m ≠ 1 := by
  have := hK.finite
  have hcyc : IsCyclic Kˣ := inferInstance
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hog : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hKu : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by have := hK.one_le; omega) hK.prime.one_lt
  cases π with
  | true =>
    have hcard : Nat.card K = p ^ f := hK.card
    have h3 : p ^ f % 3 = 1 := hmod
    refine ⟨(p ^ f - 1) / 3, ?_, ?_, ?_⟩
    · intro A _ hA
      rw [GeneralLinearGroup.center_eq_range_scalar] at hA
      obtain ⟨u, rfl⟩ := hA
      rw [det_scalar148, ← pow_mul, show 3 * ((p ^ f - 1) / 3) = Nat.card Kˣ by omega]
      exact pow_card_eq_one'
    · intro A _
      rw [show 3 * ((p ^ f - 1) / 3) = Nat.card Kˣ by omega]
      exact pow_card_eq_one'
    · refine ⟨diagGL148 g, Sec4.mem_glPi_true _ _, ?_⟩
      rw [det_diagGL148]
      intro h1
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rw [hog, hKu, hcard] at hdvd
      have hpos : 0 < (p ^ f - 1) / 3 := by omega
      have := Nat.le_of_dvd hpos hdvd
      omega
  | false =>
    have hU : UnitaryFieldData p f K := hK.unitary
    have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
    have h3 : p ^ f % 3 = 2 := hmod
    have hbar : ∀ c : K, hU.bar c = c ^ p ^ f := fun c => rfl
    have hGU : ∀ A ∈ Sec4.glPi false 3 (p ^ f) K, GeneralLinearGroup.det A ^ (p ^ f + 1) = 1 := by
      intro A hA
      rw [Sec4.mem_glPi_false hU] at hA
      have hd := congrArg Matrix.det hA
      rw [det_mul, det_transpose,
        show (A : Matrix (Fin 3) (Fin 3) K).map hU.bar = hU.bar.mapMatrix (A : Matrix _ _ K)
          from rfl, ← RingHom.map_det, det_one, hbar] at hd
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one, pow_succ]
      exact hd
    refine ⟨(p ^ f + 1) / 3, ?_, ?_, ?_⟩
    · intro A hA hAc
      rw [GeneralLinearGroup.center_eq_range_scalar] at hAc
      obtain ⟨u, rfl⟩ := hAc
      rw [Sec4.mem_glPi_false hU, GeneralLinearGroup.coe_scalar, scalar_apply,
        diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one] at hA
      have hu : hU.bar (u : K) * u = 1 := congrFun (diagonal_injective hA) 0
      rw [hbar, ← pow_succ] at hu
      rw [det_scalar148, ← pow_mul, show 3 * ((p ^ f + 1) / 3) = p ^ f + 1 by omega]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hu
    · intro A hA
      rw [show 3 * ((p ^ f + 1) / 3) = p ^ f + 1 by omega]
      exact hGU A hA
    ·
      set h := g ^ (p ^ f - 1) with hh
      have hoh : orderOf h = p ^ f + 1 := by
        have hdvd : p ^ f - 1 ∣ orderOf g := by
          rw [hog, hKu, hcard]
          exact ⟨p ^ f + 1, by
            have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
              have h1 : 1 ≤ p ^ f := by omega
              zify [h1, Nat.one_le_pow 2 (p ^ f) (by omega)]
              ring
            exact this⟩
        rw [hh, orderOf_pow_of_dvd (by omega) hdvd, hog, hKu, hcard]
        have h1 : 1 ≤ p ^ f := by omega
        have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
          zify [h1, Nat.one_le_pow 2 (p ^ f) (by omega)]
          ring
        rw [this, Nat.mul_div_cancel_left _ (by omega)]
      have hhq : (h : K) ^ (p ^ f + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← hoh, pow_orderOf_eq_one, Units.val_one]
      refine ⟨diagGL148 h, ?_, ?_⟩
      · rw [Sec4.mem_glPi_false hU]
        change ((diagonal ![(h : K), 1, 1]).map hU.bar)ᵀ * diagonal ![(h : K), 1, 1] = 1
        rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          rw [hbar, ← pow_succ]
          exact hhq
        · simp
        · simp
      · rw [det_diagGL148]
        intro h1
        have hdvd := orderOf_dvd_of_pow_eq_one h1
        rw [hoh] at hdvd
        have hpos : 0 < (p ^ f + 1) / 3 := by omega
        have := Nat.le_of_dvd hpos hdvd
        omega

theorem kf148PGLAbel : KF148PGLAbel := by
  intro Γ _ _ p f hΓ x htop
  obtain ⟨π, K, _, hK, hmod, ⟨e⟩⟩ := hΓ
  have : Finite K := hK.finite
  set H := Sec4.glPi π 3 (p ^ f) K with hH
  obtain ⟨m, hker, h3m, A₀, hA₀, hζ⟩ := exists_detPow_data_glPi hK hmod
  obtain ⟨δ, hδ⟩ := exists_detPow_projImage H m hker
  set ψ : Γ →* Multiplicative (ZMod 3) × Kˣ :=
    (MonoidHom.prodMap (MonoidHom.id _) δ).comp e.toMonoidHom with hψ
  have hδ3 : ∀ y : ↥(projImage H), δ y ^ 3 = 1 := by
    rintro ⟨y, hy⟩
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hδ A hA, ← pow_mul, mul_comm]
    exact h3m A hA
  have hz3 : ∀ z : Multiplicative (ZMod 3), z ^ 3 = 1 := by decide
  have hle : ∀ g : Γ, ψ g ∈ Subgroup.zpowers (ψ x) := by
    intro g
    have hg : g ∈ commutator Γ ⊔ Subgroup.zpowers x := htop ▸ Subgroup.mem_top g
    have hmap : ψ g ∈ (commutator Γ ⊔ Subgroup.zpowers x).map ψ := ⟨g, hg, rfl⟩
    have hc : (commutator Γ).map ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact Abelianization.commutator_subset_ker ψ
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hc, bot_sup_eq] at hmap
  have hx3 : ψ x ^ 3 = 1 := by
    rw [hψ, MonoidHom.coe_comp, Function.comp_apply, Prod.ext_iff]
    exact ⟨hz3 _, hδ3 _⟩
  have hcard : Nat.card (Subgroup.zpowers (ψ x)) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hx3
  set y₀ : ↥(projImage H) := ⟨ProjGenLinGroup.mk A₀, Subgroup.mem_map.mpr ⟨A₀, hA₀, rfl⟩⟩
  have hζ1 : δ y₀ ≠ 1 := by rw [hδ A₀ hA₀]; exact hζ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoζ : orderOf (δ y₀) = 3 := orderOf_eq_prime (hδ3 y₀) hζ1
  have hψv : ∀ (z : Multiplicative (ZMod 3)) (y : ↥(projImage H)),
      ψ (e.symm (z, y)) = (z, δ y) := by
    intro z y
    change (MonoidHom.prodMap (MonoidHom.id _) δ) (e (e.symm (z, y))) = (z, δ y)
    rw [MulEquiv.apply_symm_apply]
    rfl
  let F : Multiplicative (ZMod 3) × Fin 3 → Subgroup.zpowers (ψ x) :=
    fun zi => ⟨ψ (e.symm (zi.1, y₀ ^ (zi.2 : ℕ))), hle _⟩
  have hF : Function.Injective F := by
    rintro ⟨z, i⟩ ⟨z', i'⟩ hzi
    have h1 := congrArg Subtype.val hzi
    change ψ (e.symm (z, y₀ ^ (i : ℕ))) = ψ (e.symm (z', y₀ ^ (i' : ℕ))) at h1
    rw [hψv, hψv, Prod.mk.injEq, map_pow, map_pow] at h1
    obtain ⟨rfl, h2⟩ := h1
    have h3 : (i : ℕ) = (i' : ℕ) := pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hoζ]; exact i.2)
      (by rw [Set.mem_Iio, hoζ]; exact i'.2) h2
    rw [Fin.ext h3]
  have hle9 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 3)),
    Fintype.card_multiplicative, ZMod.card, Nat.card_eq_fintype_card (α := Fin 3),
    Fintype.card_fin] at hle9
  omega

end CFSG.RankThree.PartTwo.Sec14
