module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalAut

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.GroupTheory.WeirSylow

section Induced

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def InducedBySemilinear (Q : QuadraticForm K V) (α : MulAut (ProjOrthDerived Q)) :
    Prop :=
  ∃ (σ : K ≃+* K) (F : V ≃+ V) (_ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K), μ ≠ 0 ∧
    (∀ v, Q (F v) = μ * σ (Q v)) ∧
    ∀ g g' : orthDerived Q, (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      α (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] noncomputable def simEquiv {V' : Type} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (S : V ≃ₗ[K] V') (ν : Kˣ)
    (hS : ∀ v, Q' (S v) = ν * Q v) : ProjOrthDerived Q ≃* ProjOrthDerived Q' :=
  quotientSubgroupOfEquiv (linConj S) (map_orthDerived S ν hS) (map_scalars S)

theorem simEquiv_mk {V' : Type} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (S : V ≃ₗ[K] V') (ν : Kˣ)
    (hS : ∀ v, Q' (S v) = ν * Q v) (g : orthDerived Q) (g' : orthDerived Q')
    (hg : (g' : V' ≃ₗ[K] V') = linConj S g) :
    simEquiv S ν hS (QuotientGroup.mk g) = QuotientGroup.mk g' :=
  quotientSubgroupOfEquiv_mk _ _ _ g g' hg

theorem inducedBySemilinear_of_similarity {V' : Type} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (S : V ≃ₗ[K] V') (ν : Kˣ)
    (hS : ∀ v, Q' (S v) = ν * Q v) (h : ∀ α' : MulAut (ProjOrthDerived Q'),
      InducedBySemilinear Q' α') (α : MulAut (ProjOrthDerived Q)) : InducedBySemilinear Q α := by
  set e := simEquiv S ν hS with he
  obtain ⟨σ, F', hF', μ', hμ', hQ', hind'⟩ := h (MulAut.congr e α)
  let F : V ≃+ V := S.toAddEquiv.trans (F'.trans S.symm.toAddEquiv)
  have hFapp : ∀ v, F v = S.symm (F' (S v)) := fun v => rfl
  have hFS : ∀ v, S (F v) = F' (S v) := fun v => by rw [hFapp, LinearEquiv.apply_symm_apply]
  have hFsymm : ∀ w, F.symm w = S.symm (F'.symm (S w)) := fun w => by
    apply F.injective
    rw [AddEquiv.apply_symm_apply, hFapp, LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
  refine ⟨σ, F, fun c v => ?_, (ν : K)⁻¹ * μ' * σ (ν : K), ?_, fun v => ?_, fun g g' hgg' => ?_⟩
  · rw [hFapp, hFapp, map_smul, hF', map_smul]
  · exact mul_ne_zero (mul_ne_zero (inv_ne_zero ν.ne_zero) hμ') ((map_ne_zero _).mpr ν.ne_zero)
  · have h1 := hQ' (S v)
    have h2 : Q' (S (F v)) = ν * Q (F v) := hS _
    rw [hFS, h1, hS, map_mul] at h2
    have h3 : (ν : K) * Q (F v) = (ν : K) * ((ν : K)⁻¹ * μ' * σ (ν : K) * σ (Q v)) := by
      rw [← h2]
      field_simp
    exact mul_left_cancel₀ ν.ne_zero h3
  · have hmemg : linConj S g ∈ orthDerived Q' := by
      rw [← map_orthDerived S ν hS]
      exact Subgroup.mem_map_of_mem _ g.2
    have hmemg' : linConj S g' ∈ orthDerived Q' := by
      rw [← map_orthDerived S ν hS]
      exact Subgroup.mem_map_of_mem _ g'.2
    have h1 := hind' ⟨_, hmemg⟩ ⟨_, hmemg'⟩ (fun w => by
      change S (((g' : orthDerived Q) : V ≃ₗ[K] V) (S.symm w)) =
        F' (S (((g : orthDerived Q) : V ≃ₗ[K] V) (S.symm (F'.symm w))))
      rw [hgg', hFapp, LinearEquiv.apply_symm_apply, hFsymm, LinearEquiv.apply_symm_apply])
    have h2 : e (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hmemg⟩ :=
      simEquiv_mk S ν hS g _ rfl
    have h3 : e (QuotientGroup.mk g') = QuotientGroup.mk ⟨_, hmemg'⟩ :=
      simEquiv_mk S ν hS g' _ rfl
    have h4 : (MulAut.congr e α) (QuotientGroup.mk ⟨_, hmemg⟩) = e (α (QuotientGroup.mk g)) := by
      rw [← h2]
      simp [MulAut.congr_apply]
    rw [h4, ← h3] at h1
    exact e.injective h1

end Induced

section Main

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem inducedBySemilinear_of_image_eq_top {d : ℕ} (hd : 0 < d) (Q' : QuadraticForm K (Fin d → K))
    (h : matrixProjectiveImage Q' = ⊤) (α' : MulAut (ProjOrthDerived Q')) :
    InducedBySemilinear Q' α' := by
  obtain ⟨σ, F, hF, μ, hμ, hQ, hind⟩ := exists_semilin_of_mem_matrixProjectiveImage Q' hd α'
    (by rw [h]; exact Subgroup.mem_top _)
  exact ⟨σ, F, hF, μ, hμ, hQ, hind⟩

omit [Finite K] in
theorem exists_totally_singular_of_isometry_quadPlus {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (e : Q.IsometryEquiv (quadPlus n K)) :
    ∃ U : Submodule K V, finrank K U = n ∧ ∀ u ∈ U, Q u = 0 := by
  let ι : (Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := fun x y => by
        ext i
        cases i <;> simp
      map_smul' := fun c x => by
        ext i
        cases i <;> simp }
  have hι : Function.Injective ι := fun x y hxy => by
    ext i
    exact congrFun hxy (Sum.inl i)
  refine ⟨Submodule.map e.toLinearEquiv.symm.toLinearMap (LinearMap.range ι), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hι, Module.finrank_fin_fun]
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    have h1 := e.map_app (e.toLinearEquiv.symm (ι y))
    have h2 : e (e.toLinearEquiv.symm (ι y)) = ι y := e.toLinearEquiv.apply_symm_apply (ι y)
    rw [h2] at h1
    show Q (e.toLinearEquiv.symm (ι y)) = 0
    rw [← h1, quadPlus_apply]
    simp [ι]

theorem orthogonal_aut_semilinear_of_seven_le {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ finrank K V)
    (hD4 : finrank K V = 8 → ¬ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (α : MulAut (ProjOrthDerived Q)) : InducedBySemilinear Q α := by
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' (finrank K V)
  · have hn4 : 4 ≤ n := by omega
    rcases exists_isometry_quadPlus_or_quadMinus Q hQ (by omega) hn with
      ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · have hn5 : 5 ≤ n := by
        by_contra hlt
        have h4 : n = 4 := by omega
        subst h4
        exact hD4 (by omega) (exists_totally_singular_of_isometry_quadPlus e)
      let S : V ≃ₗ[K] (Fin (2 * n) → K) :=
        e.toLinearEquiv.trans (coordinatePlusIsometry n K).toLinearEquiv
      refine inducedBySemilinear_of_similarity S 1 (fun v => ?_)
        (inducedBySemilinear_of_image_eq_top (by omega) _
          (matrixProjectiveImage_eq_top_plus K n hn5)) α
      change coordinateQuadPlus n K ((coordinatePlusIsometry n K) (e v)) = ((1 : Kˣ) : K) * Q v
      rw [(coordinatePlusIsometry n K).map_app, e.map_app, Units.val_one, one_mul]
    · let S : V ≃ₗ[K] (Fin (2 * n) → K) :=
        e.toLinearEquiv.trans (coordinateMinusIsometry n K (by omega) b c).toLinearEquiv
      refine inducedBySemilinear_of_similarity S 1 (fun v => ?_)
        (inducedBySemilinear_of_image_eq_top (by omega) _
          (matrixProjectiveImage_eq_top_minus K n hn4 b c hirr)) α
      change coordinateQuadMinus n K (by omega) b c
        ((coordinateMinusIsometry n K (by omega) b c) (e v)) = ((1 : Kˣ) : K) * Q v
      rw [(coordinateMinusIsometry n K (by omega) b c).map_app, e.map_app, Units.val_one, one_mul]
  · have hn3 : 3 ≤ n := by omega
    have h2 : ringChar K ≠ 2 := by
      intro h2
      have : CharP K 2 := ringChar.of_eq h2
      have hB : (polarBilin Q).IsAlt := fun x => by
        change polar Q x x = 0
        rw [polar_self, two_nsmul]
        exact CharTwo.add_self_eq_zero _
      obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank hB hQ
      omega
    obtain ⟨c, hc, ⟨e⟩⟩ := exists_smul_isometry_quadOdd h2 Q hQ hn
    let S : V ≃ₗ[K] (Fin (2 * n + 1) → K) :=
      e.toLinearEquiv.trans (coordinateOddIsometry n K).toLinearEquiv
    refine inducedBySemilinear_of_similarity S (Units.mk0 c hc) (fun v => ?_)
      (inducedBySemilinear_of_image_eq_top (by omega) _
        (matrixProjectiveImage_eq_top_odd K n (by omega) h2)) α
    change coordinateQuadOdd n K ((coordinateOddIsometry n K) (e v)) = c * Q v
    rw [(coordinateOddIsometry n K).map_app, e.map_app]
    simp

theorem orthogonal_aut_semilinear {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) (hdim : 8 ≤ finrank K V)
    (hD4 : finrank K V = 8 → ¬ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (α : MulAut (ProjOrthDerived Q)) : InducedBySemilinear Q α :=
  orthogonal_aut_semilinear_of_seven_le Q hQ (by omega) hD4 α

end Main

end CFSG.RankThree.PartOne.KCOrthogonalAut
