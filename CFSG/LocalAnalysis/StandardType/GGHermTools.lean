module

public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TraceTransfer
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LieType.Universal.Unitary

theorem exists_hermTransfer {K F V : Type} [Field K] [Finite K] [Field F] [Finite F]
    [Algebra K F] [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower K F V]
    (σ : K →+* K) (τ : F ≃+* F)
    (hσσ : ∀ c, σ (σ c) = c) (hττ : ∀ x, τ (τ x) = x)
    (hτσ : ∀ c : K, τ (algebraMap K F c) = algebraMap K F (σ c))
    (hK : V → V → K)
    (hKaddL : ∀ x y z, hK (x + y) z = hK x z + hK y z)
    (hKaddR : ∀ x y z, hK x (y + z) = hK x y + hK x z)
    (hKsmulR : ∀ (c : K) x y, hK x (c • y) = c * hK x y)
    (hKherm : ∀ x y, hK x y = σ (hK y x))
    (hKnd : ∀ x, (∀ y, hK x y = 0) → x = 0)
    (hKF : ∀ (a : F) x y, hK (a • x) y = hK x (τ a • y)) :
    ∃ H : V → V → F,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧ (∀ x y z, H x (y + z) = H x y + H x z) ∧
      (∀ (a : F) x y, H (a • x) y = τ a * H x y) ∧ (∀ (a : F) x y, H x (a • y) = a * H x y) ∧
      (∀ x y, H x y = τ (H y x)) ∧ (∀ x, (∀ y, H x y = 0) → x = 0) ∧
      (∀ x y, hK x y = Algebra.trace K F (H x y)) := by
  classical
  let σe : K ≃+* K := RingEquiv.ofBijective σ ⟨fun a b h => by
    have := congrArg σ h
    rwa [hσσ, hσσ] at this, fun b => ⟨σ b, hσσ b⟩⟩
  have hσe_apply : ∀ c, σe c = σ c := fun c => rfl
  let B : V → V →ₗ[K] K := fun x =>
    { toFun := hK x
      map_add' := hKaddR x
      map_smul' := fun c y => by
        change hK x (c • y) = c • hK x y
        rw [hKsmulR, smul_eq_mul] }
  have B_apply : ∀ x y, B x y = hK x y := fun x y => rfl
  have B_addL : ∀ x y z, B (x + y) z = B x z + B y z := fun x y z => hKaddL x y z
  let H : V → V →ₗ[F] F := fun x => (existsUnique_traceTransfer B x).choose
  have H_spec : ∀ x y c, B x (c • y) = Algebra.trace K F (c * H x y) :=
    fun x => (existsUnique_traceTransfer B x).choose_spec.1
  have H_uniq : ∀ x (g : V →ₗ[F] F),
      (∀ y c, B x (c • y) = Algebra.trace K F (c * g y)) → g = H x :=
    fun x => (existsUnique_traceTransfer B x).choose_spec.2
  have H_trace : ∀ x y, hK x y = Algebra.trace K F (H x y) := by
    intro x y
    have h := H_spec x y (1 : F)
    rw [one_smul, one_mul, B_apply] at h
    exact h
  have hBh : ∀ x y, B y x = σe (B x y) := by
    intro x y
    have h1 : σ (hK x y) = hK y x := by
      have := congrArg σ (hKherm x y)
      rwa [hσσ] at this
    rw [B_apply, hσe_apply, ← h1, B_apply]
  have hτσe : ∀ c : K, τ (algebraMap K F c) = algebraMap K F (σe c) := by
    intro c
    rw [hσe_apply]
    exact hτσ c
  have hτ' : ∀ (a : F) x y, B (a • x) y = B x (τ a • y) := hKF
  obtain ⟨hHsmulL, hHherm⟩ := traceTransfer_herm σe B H H_spec hBh τ hτσe hττ hτ'
  have H_addL : ∀ x y z, H (x + y) z = H x z + H y z := by
    intro x y z
    let g : V →ₗ[F] F :=
      { toFun := fun w => H x w + H y w
        map_add' := by
          intro a b
          change H x (a + b) + H y (a + b) = (H x a + H y a) + (H x b + H y b)
          rw [map_add, map_add]
          abel
        map_smul' := by
          intro c a
          simp only [map_smul, smul_add, RingHom.id_apply] }
    have hg : ∀ w c, B (x + y) (c • w) = Algebra.trace K F (c * g w) := by
      intro w c
      rw [B_addL, H_spec x w c, H_spec y w c, ← map_add]
      congr 1
      change c * H x w + c * H y w = c * (H x w + H y w)
      ring
    have h := H_uniq (x + y) g hg
    have hz := congrArg (fun l : V →ₗ[F] F => l z) h
    simpa [g] using hz.symm
  refine ⟨fun x y => H x y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    exact H_addL x y z
  · intro x y z
    exact (H x).map_add y z
  · intro a x y
    exact hHsmulL a x y
  · intro a x y
    show H x (a • y) = a * H x y
    rw [(H x).map_smul, smul_eq_mul]
  · intro x y
    show H x y = τ (H y x)
    have h := congrArg τ (hHherm x y)
    rw [hττ] at h
    exact h.symm
  · intro x hx
    change (∀ y, H x y = 0) at hx
    apply hKnd x
    intro y
    rw [H_trace x y, hx y, map_zero]
  · intro x y
    exact H_trace x y

private lemma hermTools_form_sumL {E V ι : Type} [Field E] [AddCommGroup V] [Module E V]
    (σ : E ≃+* E) (H : V → V → E)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : E) x y, H (c • x) y = σ c * H x y)
    (s : Finset ι) (f : ι → E) (v : ι → V) (y : V) :
    H (∑ i ∈ s, f i • v i) y = ∑ i ∈ s, σ (f i) * H (v i) y := by
  classical
  refine Finset.induction_on s ?base ?step
  · have h0 : H 0 y = 0 := by
      have h := hsmulL 0 (0 : V) y
      simpa using h
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, hsmulL, ih]

private lemma hermTools_form_sumR {E V ι : Type} [Field E] [AddCommGroup V] [Module E V]
    (H : V → V → E)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : E) x y, H x (c • y) = c * H x y)
    (x : V) (s : Finset ι) (f : ι → E) (v : ι → V) :
    H x (∑ i ∈ s, f i • v i) = ∑ i ∈ s, f i * H x (v i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · have h0 : H x 0 = 0 := by
      have h := hsmulR 0 x (0 : V)
      simpa using h
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, haddR, hsmulR, ih]

private lemma hermTools_form_transport {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    (σ : E ≃+* E) (H : V → V → E) {k : ℕ} (v : Module.Basis (Fin k) E V)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : E) x y, H (c • x) y = σ c * H x y)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : E) x y, H x (c • y) = c * H x y)
    (c d : Fin k → E) :
    H (∑ p, c p • v p) (∑ q, d q • v q)
      = ∑ p, σ (c p) * ∑ q, H (v p) (v q) * d q := by
  classical
  rw [hermTools_form_sumL σ H haddL hsmulL Finset.univ c v (∑ q, d q • v q)]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [hermTools_form_sumR H haddR hsmulR (v p) Finset.univ d v]
  apply Finset.sum_congr rfl
  intro q _
  ring

private lemma hermTools_form_eq_sum {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    (σ : E ≃+* E) (H : V → V → E) {k : ℕ} (v : Module.Basis (Fin k) E V)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : E) x y, H (c • x) y = σ c * H x y)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : E) x y, H x (c • y) = c * H x y)
    (x y : V) :
    H x y = ∑ p, σ (v.equivFun x p) * ∑ q, H (v p) (v q) * v.equivFun y q := by
  have hx : x = ∑ p, v.equivFun x p • v p :=
    (v.equivFun.symm_apply_apply x).symm.trans
      (Module.Basis.equivFun_symm_apply v (v.equivFun x))
  have hy : y = ∑ q, v.equivFun y q • v q :=
    (v.equivFun.symm_apply_apply y).symm.trans
      (Module.Basis.equivFun_symm_apply v (v.equivFun y))
  conv_lhs => rw [hx, hy]
  rw [hermTools_form_transport σ H v haddL hsmulL haddR hsmulR (v.equivFun x) (v.equivFun y)]

private lemma hermTools_gram_det {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    (σ : E ≃+* E) (hσ : ∀ c, σ (σ c) = c) (H : V → V → E) {k : ℕ}
    (v : Module.Basis (Fin k) E V)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : E) x y, H (c • x) y = σ c * H x y)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : E) x y, H x (c • y) = c * H x y)
    (hnondeg : ∀ x, (∀ y, H x y = 0) → x = 0) :
    Matrix.det (fun i j => H (v i) (v j)) ≠ 0 := by
  classical
  let G : Matrix (Fin k) (Fin k) E := fun i j => H (v i) (v j)
  have hrow : LinearIndependent E Gᵀ.col := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    let x : V := v.equivFun.symm (fun p => σ (a p))
    have hvx : v.equivFun x = fun p => σ (a p) := by
      dsimp only [x]
      rw [LinearEquiv.apply_symm_apply]
    have ha' : ∀ q, ∑ p, a p * G p q = 0 := by
      intro q
      have h := congrFun ha q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
        Matrix.transpose_apply, Pi.zero_apply] at h
      exact h
    have hxH : ∀ y, H x y = 0 := by
      intro y
      rw [hermTools_form_eq_sum σ H v haddL hsmulL haddR hsmulR x y, hvx]
      have h1 : (∑ p, σ (σ (a p)) * ∑ q, H (v p) (v q) * v.equivFun y q)
          = ∑ q, (∑ p, a p * G p q) * v.equivFun y q := by
        simp only [hσ, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [h1]
      simp [ha']
    have hx0 : x = 0 := hnondeg x hxH
    intro i
    have hσai : σ (a i) = 0 := by
      have h := congrFun hvx i
      rw [hx0, map_zero] at h
      simpa using h.symm
    exact σ.injective (by rw [hσai, map_zero])
  have hu : IsUnit Gᵀ := Matrix.linearIndependent_cols_iff_isUnit.mp hrow
  have hud : IsUnit Gᵀ.det := (Matrix.isUnit_iff_isUnit_det Gᵀ).mp hu
  rw [Matrix.det_transpose] at hud
  exact hud.ne_zero

theorem exists_hermOrthonormalBasis {E : Type} [Field E]
    (σ : E ≃+* E) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : V → V → E) (k : ℕ) (hk : Module.finrank E V = k)
    (hherm : ∀ x y, H x y = σ (H y x))
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : E) x y, H (c • x) y = σ c * H x y)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : E) x y, H x (c • y) = c * H x y)
    (hnondeg : ∀ x, (∀ y, H x y = 0) → x = 0) :
    ∃ b : Module.Basis (Fin k) E V, ∀ i j, H (b i) (b j) = if i = j then 1 else 0 := by
  classical
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨(Module.finBasis E V).reindex (finCongr hk), ?_⟩
    intro i
    exact i.elim0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hkpos
    let v : Module.Basis (Fin k) E V := (Module.finBasis E V).reindex (finCongr hk)
    let G : Matrix (Fin k) (Fin k) E := fun i j => H (v i) (v j)
    have hGherm : conjTr σ G = G := by
      ext i j
      change σ (H (v j) (v i)) = H (v i) (v j)
      exact (hherm (v i) (v j)).symm
    have hGdet : G.det ≠ 0 :=
      hermTools_gram_det σ hσ.invol H v haddL hsmulL haddR hsmulR hnondeg
    obtain ⟨b, hbli, hb⟩ := CFSG.LieType.Steinberg.exists_herm_orthonormal hσ hGherm hGdet
    let e : (Fin k → E) ≃ₗ[E] V := v.equivFun.symm
    have hwli : LinearIndependent E (fun i => e (b i)) :=
      hbli.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    have hspanw : ⊤ ≤ Submodule.span E (Set.range (fun i => e (b i))) :=
      (LinearIndependent.span_eq_top_of_card_eq_finrank hwli (by
        rw [Fintype.card_fin]
        exact hk.symm)).ge
    refine ⟨Module.Basis.mk hwli hspanw, ?_⟩
    intro i j
    rw [Module.Basis.mk_apply, Module.Basis.mk_apply]
    change H (e (b i)) (e (b j)) = if i = j then 1 else 0
    rw [hermTools_form_eq_sum σ H v haddL hsmulL haddR hsmulR (e (b i)) (e (b j))]
    have hvx : v.equivFun (e (b i)) = b i := by
      dsimp only [e]
      rw [LinearEquiv.apply_symm_apply]
    have hvy : v.equivFun (e (b j)) = b j := by
      dsimp only [e]
      rw [LinearEquiv.apply_symm_apply]
    rw [hvx, hvy]
    have hsum : (∑ p, σ ((b i) p) * ∑ q, H (v p) (v q) * (b j) q)
        = CFSG.ClassicalGroups.Unitary.herm σ (b i) (G *ᵥ b j) := by
      rw [CFSG.ClassicalGroups.Unitary.herm_def]
      rfl
    rw [hsum, hb i j]

end CFSG.StandardType
