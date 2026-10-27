module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkSwap

public section

namespace CFSG.StandardType

namespace WitOmBlk

open QuadraticMap Module OrdPNsOm CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem fvec_map {m : ℕ} (g : V →ₗ[K] V) (e f : Fin m → V) (a b : V) (x : FrIdx m) :
    fvec (fun i => g (e i)) (fun i => g (f i)) (g a) (g b) x = g (fvec e f a b x) := by
  rcases x with i | i | j
  · rfl
  · rfl
  · fin_cases j <;> rfl

theorem isFrame_map {c₀ : K} {τ : Bool} {m : ℕ} {e f : Fin m → V} {a b : V}
    (hF : IsFrame Q c₀ τ e f a b) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    IsFrame Q c₀ τ (fun i => g (e i)) (fun i => g (f i)) (g a) (g b) := by
  have hQg : ∀ x, Q (g x) = Q x := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
  have hpg : ∀ x y, polar Q (g x) (g y) = polar Q x y :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg
  exact ⟨⟨fun k => by rw [hQg]; exact hF.hyp.map_e k, fun k => by rw [hQg]; exact hF.hyp.map_f k,
    fun i j => by rw [hpg]; exact hF.hyp.polar_ee i j,
    fun i j => by rw [hpg]; exact hF.hyp.polar_ff i j,
    fun i j => by rw [hpg]; exact hF.hyp.polar_ef i j⟩,
    fun i => by rw [hpg]; exact hF.pea i, fun i => by rw [hpg]; exact hF.peb i,
    fun i => by rw [hpg]; exact hF.pfa i, fun i => by rw [hpg]; exact hF.pfb i,
    by rw [hpg]; exact hF.pab, by rw [hQg]; exact hF.qa, by rw [hQg]; exact hF.qb⟩

variable [CharP K 2]

theorem exists_orthDerived_of_orth [Finite K] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {w : V} (hw : Q w ≠ 0) :
    ∃ g' ∈ CFSG.RankThree.Classical2.orthDerived Q, ∀ y, polar Q w (g y) = 0 → g' y = g y := by
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  have hrO := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q w
  have hr1 : finrank K (commSpace (TauCeti.QuadraticMap.reflection Q w)) = 1 :=
    finrank_commSpace_reflection hQ w
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  by_cases hev : Even (finrank K (commSpace g))
  · exact ⟨g, hΩ ⟨hg, hev⟩, fun _ _ => rfl⟩
  · refine ⟨TauCeti.QuadraticMap.reflection Q w * g, hΩ ⟨mul_mem hrO hg, ?_⟩, fun y hy => ?_⟩
    · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hev
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hrO hg, hr1, hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
      rfl
    · rw [LinearEquiv.mul_apply, TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ _ hy]

theorem exists_orthDerived_frame [Finite K] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {c₀ : K} {τ : Bool} {m : ℕ}
    {e f e' f' : Fin m → V} {a b a' b' : V} (hF : IsFrame Q c₀ τ e f a b)
    (hF' : IsFrame Q c₀ τ e' f' a' b') {w : V} (hw : Q w ≠ 0)
    (hw' : ∀ x, polar Q w (fvec e' f' a' b' x) = 0) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, ∀ x,
      g (fvec e f a b x) = fvec e' f' a' b' x := by
  obtain ⟨g, hg, hgF⟩ := exists_orth_frames (Q := Q) hQ (k := 1) (e := fun _ => e)
    (f := fun _ => f) (a := fun _ => a) (b := fun _ => b) (e' := fun _ => e') (f' := fun _ => f')
    (a' := fun _ => a') (b' := fun _ => b') (fun _ => hF) (fun _ => hF')
    (fun j j' h => absurd (Subsingleton.elim j j') h)
    (fun j j' h => absurd (Subsingleton.elim j j') h)
  obtain ⟨g', hg', hg'g⟩ := exists_orthDerived_of_orth hQ hT hg hw
  exact ⟨g', hg', fun x => by rw [hg'g _ (by rw [hgF 0 x]; exact hw' x), hgF 0 x]⟩

theorem exists_orthDerived_frame_swap [Finite K] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {c₀ : K} {τ : Bool} {m : ℕ}
    {v : V ≃ₗ[K] V} (hv : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {e f e₀ f₀ e₁ f₁ : Fin m → V} {a b a₀ b₀ a₁ b₁ : V} (hF : IsFrame Q c₀ τ e f a b)
    (hsw : ∀ x y, polar Q (fvec e f a b x) (v (fvec e f a b y)) = 0)
    (hF₀ : IsFrame Q c₀ τ e₀ f₀ a₀ b₀) (hF₁ : IsFrame Q c₀ τ e₁ f₁ a₁ b₁)
    (h01 : ∀ x y, polar Q (fvec e₀ f₀ a₀ b₀ x) (fvec e₁ f₁ a₁ b₁ y) = 0) {w : V} (hw : Q w ≠ 0)
    (hw₀ : ∀ x, polar Q w (fvec e₀ f₀ a₀ b₀ x) = 0)
    (hw₁ : ∀ x, polar Q w (fvec e₁ f₁ a₁ b₁ x) = 0) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, ∀ x,
      g (fvec e f a b x) = fvec e₀ f₀ a₀ b₀ x ∧ g (v (fvec e f a b x)) = fvec e₁ f₁ a₁ b₁ x := by
  have hFv := isFrame_map hF hv
  have hvF : ∀ x, fvec (fun i => v (e i)) (fun i => v (f i)) (v a) (v b) x =
      v (fvec e f a b x) := fun x => fvec_map (v : V →ₗ[K] V) e f a b x
  obtain ⟨g, hg, hgF⟩ := exists_orth_frames (Q := Q) hQ (k := 2)
    (e := ![e, fun i => v (e i)]) (f := ![f, fun i => v (f i)]) (a := ![a, v a])
    (b := ![b, v b]) (e' := ![e₀, e₁]) (f' := ![f₀, f₁]) (a' := ![a₀, a₁]) (b' := ![b₀, b₁])
    (fun j => by fin_cases j; exacts [hF, hFv]) (fun j => by fin_cases j; exacts [hF₀, hF₁])
    (fun j j' hjj x y => by
      fin_cases j <;> fin_cases j'
      · exact absurd rfl hjj
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
        rw [hvF]
        exact hsw x y
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
        rw [hvF, polar_comm]
        exact hsw y x
      · exact absurd rfl hjj)
    (fun j j' hjj x y => by
      fin_cases j <;> fin_cases j'
      · exact absurd rfl hjj
      · simpa using h01 x y
      · simpa [polar_comm] using h01 y x
      · exact absurd rfl hjj)
  obtain ⟨g', hg', hg'g⟩ := exists_orthDerived_of_orth hQ hT hg hw
  have h0 : ∀ x, g (fvec e f a b x) = fvec e₀ f₀ a₀ b₀ x := fun x => by
    simpa using hgF 0 x
  have h1 : ∀ x, g (v (fvec e f a b x)) = fvec e₁ f₁ a₁ b₁ x := fun x => by
    have := hgF 1 x
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rwa [hvF] at this
  refine ⟨g', hg', fun x => ⟨?_, ?_⟩⟩
  · rw [hg'g _ (by rw [h0 x]; exact hw₀ x), h0 x]
  · rw [hg'g _ (by rw [h1 x]; exact hw₁ x), h1 x]

end WitOmBlk

end CFSG.StandardType
