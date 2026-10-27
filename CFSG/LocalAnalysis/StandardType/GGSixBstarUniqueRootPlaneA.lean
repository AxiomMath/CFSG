module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizer
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

open scoped commutatorElement

namespace RootPlaneA

section Elementary

variable {m : ℕ} {F : Type} [Field F]

theorem isDiag_of_commute_diagonal {ι : Type*} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {δ : ι → Fin (m + 1) → F} (hsep : ∀ i j, i ≠ j → ∃ k, δ k i ≠ δ k j)
    (hM : ∀ k, M * diagonal (δ k) = diagonal (δ k) * M) : M.IsDiag := by
  intro i j hij
  obtain ⟨k, hk⟩ := hsep i j hij
  have h := congrFun (congrFun (hM k) i) j
  rw [mul_diagonal, diagonal_mul] at h
  have h2 : M i j * (δ k j - δ k i) = 0 := by rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hk

theorem isDiag_commute {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : M.IsDiag)
    (hN : N.IsDiag) : M * N = N * M := by
  obtain ⟨a, rfl⟩ : ∃ a, M = diagonal a := ⟨_, hM.diagonal_diag.symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, N = diagonal b := ⟨_, hN.diagonal_diag.symm⟩
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem commute_of_isDiag {X Y : GL (Fin (m + 1)) F}
    (hX : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    (hY : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) : Commute X Y :=
  Units.ext (isDiag_commute hX hY)

theorem diagonal_commute_transvection {e : Fin (m + 1) → F} {i j : Fin (m + 1)} (hij : i ≠ j)
    (he : e i = e j) (t : F) :
    diagonal e * ((SpecialLinearGroup.transvection hij t : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    ((SpecialLinearGroup.transvection hij t : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) * diagonal e := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul]
  congr 1
  ext a b
  rw [diagonal_mul, mul_diagonal, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [he, mul_comm]
  · rw [mul_zero, zero_mul]

theorem commutatorElement_mul_central {H : Type*} [Group H] {z₁ z₂ : H}
    (h₁ : z₁ ∈ Subgroup.center H) (h₂ : z₂ ∈ Subgroup.center H) (y₁ y₂ : H) :
    ⁅z₁ * y₁, z₂ * y₂⁆ = ⁅y₁, y₂⁆ := by
  have c1 := Subgroup.mem_center_iff.mp h₁
  have c2 := Subgroup.mem_center_iff.mp h₂
  have hw : z₁ * z₂ ∈ Subgroup.center H := Subgroup.mul_mem _ h₁ h₂
  have cw := Subgroup.mem_center_iff.mp hw
  have e1 : z₁ * y₁ * (z₂ * y₂) = z₁ * z₂ * (y₁ * y₂) := by
    calc z₁ * y₁ * (z₂ * y₂) = z₁ * (y₁ * z₂) * y₂ := by group
      _ = z₁ * (z₂ * y₁) * y₂ := by rw [c2 y₁]
      _ = z₁ * z₂ * (y₁ * y₂) := by group
  have e2 : z₂ * y₂ * (z₁ * y₁) = z₁ * z₂ * (y₂ * y₁) := by
    calc z₂ * y₂ * (z₁ * y₁) = z₂ * (y₂ * z₁) * y₁ := by group
      _ = z₂ * (z₁ * y₂) * y₁ := by rw [c1 y₂]
      _ = (z₂ * z₁) * (y₂ * y₁) := by group
      _ = z₁ * z₂ * (y₂ * y₁) := by rw [c1 z₂]
  rw [commutatorElement_def, commutatorElement_def]
  calc z₁ * y₁ * (z₂ * y₂) * (z₁ * y₁)⁻¹ * (z₂ * y₂)⁻¹ =
      (z₁ * y₁ * (z₂ * y₂)) * (z₂ * y₂ * (z₁ * y₁))⁻¹ := by group
    _ = (z₁ * z₂ * (y₁ * y₂)) * (z₁ * z₂ * (y₂ * y₁))⁻¹ := by rw [e1, e2]
    _ = (z₁ * z₂) * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (z₁ * z₂)⁻¹ := by group
    _ = (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (z₁ * z₂) * (z₁ * z₂)⁻¹ := by
        rw [cw (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)]
    _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by group

theorem false_of_isQuasisimple_of_comm {G : Type*} [Group G] {J : Subgroup G}
    (hJ : CFSG.Assembly.IsQuasisimple J) (hc : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) : False := by
  obtain ⟨-, hs⟩ := hJ
  have htop : Subgroup.center ↥J = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc _ g.2 _ z.2)
  have := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥J ⧸ Subgroup.center ↥J)
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _

theorem commutator_eq_of_isQuasisimple {G : Type*} [Group G] {J : Subgroup G}
    (hJ : CFSG.Assembly.IsQuasisimple J) : ⁅J, J⁆ = J := by
  have h := congrArg (Subgroup.map J.subtype) hJ.1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

end Elementary

section Core

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem toGL_conjSL (A : GL (Fin (m + 1)) F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    SpecialLinearGroup.toGL (InnerDiagA.conjSL A u) = A * SpecialLinearGroup.toGL u * A⁻¹ := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, InnerDiagA.coe_conjSL, Units.val_mul, Units.val_mul,
    SpecialLinearGroup.coe_GL_coe_matrix]

theorem exists_gl_of_psiInnerDiag (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {c : G}
    (hc : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c) :
    ∃ A : GL (Fin (m + 1)) F, ∀ u, c⁻¹ * ψ u * c = ψ (InnerDiagA.conjSL A u) := by
  obtain ⟨g, ⟨s, rfl⟩, χ, hχ⟩ := InnerDiagA.exists_chi_of_ggPsiInnerDiag ψ hc
  obtain ⟨D, hD⟩ := InnerDiagA.exists_conj_eq_conjSL hm ψ hker hχ
  refine ⟨SpecialLinearGroup.toGL s * D, fun u => ?_⟩
  have h2 : c⁻¹ * ψ u * c = ψ (s * InnerDiagA.conjSL D u * s⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← hD u]
    group
  rw [h2]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, toGL_conjSL, toGL_conjSL]
  group

theorem exists_rootSub_of_toral
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {D J : Subgroup G} (hJψ : J ≤ ψ.range) (hJD : D ≤ Subgroup.centralizer (J : Set G))
    (hJ : CFSG.Assembly.IsQuasisimple J) (Ad : G → GL (Fin (m + 1)) F)
    (hAd : ∀ d ∈ D, ∀ u, d⁻¹ * ψ u * d = ψ (InnerDiagA.conjSL (Ad d) u))
    (A₀ : GL (Fin (m + 1)) F)
    (hA₀ : ∀ d ∈ D, ((A₀ * Ad d * A₀⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) :
    ∃ (i j : Fin (m + 1)) (hij : i ≠ j) (s : SpecialLinearGroup (Fin (m + 1)) F),
      ∀ d ∈ D, ∀ t : F, ψ (s * SpecialLinearGroup.transvection hij t * s⁻¹) * d =
        d * ψ (s * SpecialLinearGroup.transvection hij t * s⁻¹) := by
  set δ : ↥D → Fin (m + 1) → F := fun d k =>
    ((A₀ * Ad d * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k with hδ
  by_cases hsep : ∀ i j : Fin (m + 1), i ≠ j → ∃ d : ↥D, δ d i ≠ δ d j
  · exfalso
    set S : Set G := {g | ∃ w : SpecialLinearGroup (Fin (m + 1)) F,
      ((A₀ * SpecialLinearGroup.toGL w * A₀⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag ∧ ψ w = g} with hS
    have hcommS : S.Pairwise Commute := by
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ -
      have h1 := (commute_of_isDiag hw hw').eq
      have e : ∀ a b : GL (Fin (m + 1)) F,
          (A₀ * a * A₀⁻¹) * (A₀ * b * A₀⁻¹) = A₀ * (a * b) * A₀⁻¹ := fun a b => by group
      rw [e, e] at h1
      have h3 : w * w' = w' * w := by
        apply SpecialLinearGroup.toGL_injective
        rw [map_mul, map_mul]
        exact mul_left_cancel (mul_right_cancel h1)
      change ψ w * ψ w' = ψ w' * ψ w
      rw [← map_mul, ← map_mul, h3]
    have hcent : ∀ d ∈ D, ∀ y : SpecialLinearGroup (Fin (m + 1)) F, ψ y ∈ J →
        InnerDiagA.conjSL (Ad d) y * y⁻¹ ∈ Subgroup.center _ := by
      intro d hd y hy
      apply hker
      have hc := Subgroup.mem_centralizer_iff.mp (hJD hd) (ψ y) hy
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hAd d hd y, mul_assoc d⁻¹ (ψ y) d, hc]
      group
    have hcomm : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ S := by
      intro a ha b hb
      obtain ⟨y₁, rfl⟩ := hJψ ha
      obtain ⟨y₂, rfl⟩ := hJψ hb
      refine ⟨⁅y₁, y₂⁆, ?_, map_commutatorElement ψ y₁ y₂⟩
      apply isDiag_of_commute_diagonal hsep
      rintro ⟨d, hd⟩
      have hfix : InnerDiagA.conjSL (Ad d) ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆ := by
        have h := commutatorElement_mul_central (hcent d hd y₁ ha) (hcent d hd y₂ hb) y₁ y₂
        simp only [inv_mul_cancel_right] at h
        rw [map_commutatorElement]
        exact h
      have hGL := congrArg SpecialLinearGroup.toGL hfix
      rw [toGL_conjSL] at hGL
      have hdg : diagonal (δ ⟨d, hd⟩) = ((A₀ * Ad d * A₀⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) := (hA₀ d hd).diagonal_diag
      rw [hdg, ← Units.val_mul, ← Units.val_mul]
      congr 1
      have hWc : Ad d * SpecialLinearGroup.toGL ⁅y₁, y₂⁆ =
          SpecialLinearGroup.toGL ⁅y₁, y₂⁆ * Ad d := by
        calc Ad d * SpecialLinearGroup.toGL ⁅y₁, y₂⁆ =
            (Ad d * SpecialLinearGroup.toGL ⁅y₁, y₂⁆ * (Ad d)⁻¹) * Ad d := by group
          _ = SpecialLinearGroup.toGL ⁅y₁, y₂⁆ * Ad d := by rw [hGL]
      calc A₀ * SpecialLinearGroup.toGL ⁅y₁, y₂⁆ * A₀⁻¹ * (A₀ * Ad d * A₀⁻¹) =
          A₀ * (SpecialLinearGroup.toGL ⁅y₁, y₂⁆ * Ad d) * A₀⁻¹ := by group
        _ = A₀ * (Ad d * SpecialLinearGroup.toGL ⁅y₁, y₂⁆) * A₀⁻¹ := by rw [hWc]
        _ = A₀ * Ad d * A₀⁻¹ * (A₀ * SpecialLinearGroup.toGL ⁅y₁, y₂⁆ * A₀⁻¹) := by group
    have hle : J ≤ Subgroup.closure S := by
      calc J = ⁅J, J⁆ := (commutator_eq_of_isQuasisimple hJ).symm
        _ ≤ Subgroup.closure S := Subgroup.commutator_le.mpr fun a ha b hb =>
            Subgroup.subset_closure (hcomm a ha b hb)
    have hab := Subgroup.isMulCommutative_closure hcommS
    exact false_of_isQuasisimple_of_comm hJ fun a ha b hb =>
      congrArg Subtype.val (hab.is_comm.comm ⟨a, hle ha⟩ ⟨b, hle hb⟩)
  · push Not at hsep
    obtain ⟨i, j, hij, hδij⟩ := hsep
    set a : F := (A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det with ha
    have ha0 : a ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A₀
    set e : Fin (m + 1) → F := fun l => if l = 0 then a else 1 with he
    have hdetE : (diagonal e).det = a := by
      rw [det_diagonal]
      simp [e]
    set Δ₀ : GL (Fin (m + 1)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal e)
      (by rw [hdetE]; exact ha0) with hΔ₀
    have hΔval : (Δ₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal e := rfl
    have hdet1 : Matrix.GeneralLinearGroup.det (A₀⁻¹ * Δ₀) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hΔval,
        hdetE]
    obtain ⟨s, hs⟩ : A₀⁻¹ * Δ₀ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →*
        GL (Fin (m + 1)) F).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hdet1
    refine ⟨i, j, hij, s, fun d hd t => ?_⟩
    obtain ⟨N, hN⟩ : ∃ N : GL (Fin (m + 1)) F, N = A₀ * Ad d * A₀⁻¹ := ⟨_, rfl⟩
    have hNdiag : (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := hN ▸ hA₀ d hd
    have hNe : (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i =
        (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F) j j := by
      rw [hN]
      exact hδij ⟨d, hd⟩
    have hNΔ : Commute N Δ₀ :=
      commute_of_isDiag hNdiag (by rw [hΔval]; exact isDiag_diagonal e)
    have hNT : Commute N (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
        ← hNdiag.diagonal_diag]
      exact diagonal_commute_transvection hij hNe t
    have hX := (hNΔ.mul_right hNT).mul_right hNΔ.inv_right
    have hfix : InnerDiagA.conjSL (Ad d) (s * SpecialLinearGroup.transvection hij t * s⁻¹) =
        s * SpecialLinearGroup.transvection hij t * s⁻¹ := by
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_conjSL, map_mul, map_mul, map_inv, hs]
      have hAd' : Ad d = A₀⁻¹ * N * A₀ := by rw [hN]; group
      have hXe : N * (Δ₀ * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) *
          Δ₀⁻¹) * N⁻¹ =
          Δ₀ * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) * Δ₀⁻¹ := by
        rw [hX.eq, mul_inv_cancel_right]
      rw [hAd']
      calc A₀⁻¹ * N * A₀ * (A₀⁻¹ * Δ₀ *
            SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) * (A₀⁻¹ * Δ₀)⁻¹) *
            (A₀⁻¹ * N * A₀)⁻¹ =
          A₀⁻¹ * (N * (Δ₀ * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) *
            Δ₀⁻¹) * N⁻¹) * A₀ := by group
        _ = A₀⁻¹ * (Δ₀ * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) *
            Δ₀⁻¹) * A₀ := by rw [hXe]
        _ = A₀⁻¹ * Δ₀ * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) *
            (A₀⁻¹ * Δ₀)⁻¹ := by group
    have h1 := hAd d hd (s * SpecialLinearGroup.transvection hij t * s⁻¹)
    rw [hfix] at h1
    calc ψ (s * SpecialLinearGroup.transvection hij t * s⁻¹) * d =
        d * (d⁻¹ * ψ (s * SpecialLinearGroup.transvection hij t * s⁻¹) * d) := by group
      _ = d * ψ (s * SpecialLinearGroup.transvection hij t * s⁻¹) := by rw [h1]

@[expose] def GGBstarToralA {G : Type*} [Group G] (m : ℕ) (F : Type) [Field F]
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G) (Bs : Subgroup G) : Prop :=
  ∃ A₀ : GL (Fin (m + 1)) F, ∀ b ∈ Bs, ∀ A : GL (Fin (m + 1)) F,
    (∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u)) →
      ((A₀ * A * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag

theorem orderOf_psi_conj_transvection [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {i j : Fin (m + 1)}
    (hij : i ≠ j) (s : SpecialLinearGroup (Fin (m + 1)) F) :
    orderOf (ψ (s * SpecialLinearGroup.transvection hij 1 * s⁻¹)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← map_pow, pow_two]
    have h : SpecialLinearGroup.transvection hij (1 : F) * SpecialLinearGroup.transvection hij 1 =
        1 := by
      rw [← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
        SpecialLinearGroup.transvection_coeff_zero]
    calc ψ (s * SpecialLinearGroup.transvection hij 1 * s⁻¹ *
          (s * SpecialLinearGroup.transvection hij 1 * s⁻¹)) =
        ψ (s * (SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hij 1) *
          s⁻¹) := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel, map_one]
  · intro h1
    have hc : s * SpecialLinearGroup.transvection hij 1 * s⁻¹ ∈ Subgroup.center _ := hker h1
    have hT : SpecialLinearGroup.transvection hij (1 : F) ∈
        Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
      have e : SpecialLinearGroup.transvection hij (1 : F) =
          s⁻¹ * (s * SpecialLinearGroup.transvection hij 1 * s⁻¹) * s := by group
      rw [e, mul_assoc, ← Subgroup.mem_center_iff.mp hc s, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hc
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center hij hT)

end Core

end RootPlaneA

section Family

theorem ggRootPlane_psl_of_toral {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {m f : ℕ} {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (htor : RootPlaneA.GGBstarToralA m (GaloisField 2 f) ψ Bs) :
    ∃ (E : Subgroup G) (γ : Fin (ggU .PSL (m + 1) f).D.rank → ℤ) (u : (ggU .PSL (m + 1) f).K)
      (r : G),
        E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        GGRootClass (ggU .PSL (m + 1) f).D .PSL γ ∧
        E ≤ Subgroup.centralizer (ggRootSub (ggU .PSL (m + 1) f).D ψ γ u : Set G) ∧
        r ∈ ggRootSub (ggU .PSL (m + 1) f).D ψ γ u ∧ orderOf r = 2 ∧
        ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
          IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hinn := hctx.2.2.2.2.2.2.1.2
  have hDBs := hctx.d_le_bstar
  have hJψ : J ≤ ψ.range := hctx.range_eq ▸ hctx.le_ggG0
  choose! Ad hAd using fun d (hd : d ∈ D) =>
    RootPlaneA.exists_gl_of_psiInnerDiag (F := GaloisField 2 f) hm hker (hinn d (hDBs hd))
  obtain ⟨A₀, hA₀⟩ := htor
  obtain ⟨i, j, hij, s, hcomm⟩ := RootPlaneA.exists_rootSub_of_toral hker hJψ
    hctx.le_centralizer_J hctx.stdSub.1.2.2.2.2.2.1.2.2 Ad hAd A₀
    fun d hd => hA₀ d (hDBs hd) (Ad d) (hAd d hd)
  refine ⟨D, InnerDiagA.typeARoot i j, s,
    ψ (s * SpecialLinearGroup.transvection hij 1 * s⁻¹), hDBs, hctx.d_elem,
    hctx.stdSub.1.2.2.1, ⟨InnerDiagA.typeARoot_mem_roots _ hij, fun h => ?_⟩, ?_, ?_,
    RootPlaneA.orderOf_psi_conj_transvection hker hij s, fun e he _ => Or.inl he⟩
  · rcases h with h | h | h <;> cases h
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    change z ∈ SpecialLinear.rootGroup m (GaloisField 2 f) (InnerDiagA.typeARoot i j) at hz
    rw [InnerDiagA.rootGroup_typeARoot hij] at hz
    obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij z).mp hz
    exact hcomm d hd t
  · refine ⟨_, ⟨SpecialLinearGroup.transvection hij 1, ?_, rfl⟩, rfl⟩
    change _ ∈ SpecialLinear.rootGroup m (GaloisField 2 f) (InnerDiagA.typeARoot i j)
    rw [InnerDiagA.rootGroup_typeARoot hij]
    exact SpecialLinear.transvection_mem_rootSubgroup hij 1

@[expose] def GGRootPlaneInputOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∃ (E : Subgroup G) (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K) (r : G),
        E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ GGRootClass (ggU t n f).D t γ ∧
        E ≤ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G) ∧
        r ∈ ggRootSub (ggU t n f).D ψ γ u ∧ orderOf r = 2 ∧
        ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
          IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2

theorem ggRootPlaneInput_of_on {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h₁ : GGRootPlaneInputOn P) (h₂ : GGRootPlaneInputOn fun t n f p => ¬ P t n f p) :
    GGRootPlaneInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1
  by_cases hP : P t n f p
  · exact h₁ G p B Bs x L D J t n f ψ hP hctx s1
  · exact h₂ G p B Bs x L D J t n f ψ hP hctx s1

@[expose] def GGPSLSplit (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .PSL ∧ p ∣ 2 ^ f - 1

@[expose] def GGBstarToralPSLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → p ∣ 2 ^ f - 1 →
      RootPlaneA.GGBstarToralA m (GaloisField 2 f) ψ Bs

theorem ggRootPlaneInputOn_pslSplit (h : GGBstarToralPSLInput) :
    GGRootPlaneInputOn GGPSLSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  obtain ⟨rfl, hpq⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  exact ggRootPlane_psl_of_toral hctx (h G p B Bs x L D J m f ψ hctx s1.1 hpq)

theorem ggRootPlaneInput_of_pslSplit (h : GGBstarToralPSLInput)
    (hrest : GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p) : GGRootPlaneInput :=
  ggRootPlaneInput_of_on (ggRootPlaneInputOn_pslSplit h) hrest

end Family

end CFSG.StandardType
