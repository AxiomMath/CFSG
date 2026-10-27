module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddMain
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentAssemble

public section

namespace CFSG.StandardType

namespace LIDTwDF

open Module QuadraticMap OrthBstarOdd

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem subset_perp {Q : QuadraticForm K V} {Y : Submodule K V}
    (hY : ∀ y ∈ Y, ∀ y' ∈ Y, polar Q y y' = 0) {y : V} (hy : y ∈ Y) : y ∈ perp Q Y :=
  mem_perp.mpr fun w hw => hY w hw y hy

abbrev RadCond (Q : QuadraticForm K V) (Y : Submodule K V) (h : V ≃ₗ[K] V) : Prop :=
  (∀ y ∈ Y, h y = y) ∧ (∀ v ∈ perp Q Y, h v - v ∈ Y) ∧ ∀ v, h v - v ∈ perp Q Y

@[expose] def radSub (Q : QuadraticForm K V) (Y : Submodule K V)
    (hY : ∀ y ∈ Y, ∀ y' ∈ Y, polar Q y y' = 0) (H : Subgroup (V ≃ₗ[K] V)) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {h | h ∈ H ∧ RadCond Q Y h}
  mul_mem' := by
    rintro a b ⟨haH, ha1, ha2, ha3⟩ ⟨hbH, hb1, hb2, hb3⟩
    refine ⟨mul_mem haH hbH, fun y hy => ?_, fun v hv => ?_, fun v => ?_⟩
    · rw [LinearEquiv.mul_apply, hb1 y hy, ha1 y hy]
    · have hbv : b v ∈ perp Q Y := by
        have h1 := (perp Q Y).add_mem (subset_perp hY (hb2 v hv)) hv
        rwa [sub_add_cancel] at h1
      have h1 := Y.add_mem (ha2 (b v) hbv) (hb2 v hv)
      rw [LinearEquiv.mul_apply]
      convert h1 using 1
      abel
    · have h1 := (perp Q Y).add_mem (ha3 (b v)) (hb3 v)
      rw [LinearEquiv.mul_apply]
      convert h1 using 1
      abel
  one_mem' := ⟨one_mem H, fun y _ => rfl, fun v _ => by
      rw [leq_one_apply, sub_self]
      exact Y.zero_mem, fun v => by
      rw [leq_one_apply, sub_self]
      exact (perp Q Y).zero_mem⟩
  inv_mem' := by
    rintro a ⟨haH, ha1, ha2, ha3⟩
    have hinv : ∀ v, a (a⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply a a⁻¹, mul_inv_cancel, leq_one_apply]
    refine ⟨inv_mem haH, fun y hy => ?_, fun v hv => ?_, fun v => ?_⟩
    · have h1 := congrArg (⇑(a⁻¹)) (ha1 y hy)
      rw [← LinearEquiv.mul_apply a⁻¹ a, inv_mul_cancel, leq_one_apply] at h1
      exact h1.symm
    · have hu3 := ha3 (a⁻¹ v)
      rw [hinv] at hu3
      have hu : a⁻¹ v ∈ perp Q Y := by
        have h1 := (perp Q Y).sub_mem hv hu3
        rwa [sub_sub_cancel] at h1
      have h1 := Y.neg_mem (ha2 _ hu)
      rw [hinv, neg_sub] at h1
      exact h1
    · have h1 := (perp Q Y).neg_mem (ha3 (a⁻¹ v))
      rw [hinv, neg_sub] at h1
      exact h1

variable {Q : QuadraticForm K V} {Y : Submodule K V}
  {hY : ∀ y ∈ Y, ∀ y' ∈ Y, polar Q y y' = 0} {H : Subgroup (V ≃ₗ[K] V)}

theorem radSub_pow_four [CharP K 2] {h : V ≃ₗ[K] V} (hh : h ∈ radSub Q Y hY H) : h ^ 4 = 1 := by
  obtain ⟨-, h1, h2, h3⟩ := hh
  have hc2 : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  refine LinearEquiv.ext fun v => ?_
  set a := h v - v with ha
  have hap : a ∈ perp Q Y := h3 v
  set b := h a - a with hb
  have hbY : b ∈ Y := h2 a hap
  have hhb : h b = b := h1 b hbY
  have hhv : h v = v + a := by rw [ha]; abel
  have hha : h a = a + b := by rw [hb]; abel
  have hhh : h (h v) = v + b := by
    rw [hhv, map_add, hha, hhv, show v + a + (a + b) = v + (a + a) + b by abel, hc2 a, add_zero]
  have hh4 : h (h (v + b)) = v := by
    rw [map_add, map_add, hhh, hhb, hhb, add_assoc, hc2 b, add_zero]
  show (h ^ 4) v = v
  rw [show h ^ 4 = h * h * (h * h) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, _root_.sq]]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhh]
  exact hh4

theorem isPGroup_radSub [CharP K 2] : IsPGroup 2 (radSub Q Y hY H) := fun h =>
  ⟨2, by
    rw [show 2 ^ 2 = 4 from rfl]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact radSub_pow_four h.2)⟩

theorem conj_mem_radSub {g : V ≃ₗ[K] V} (hgQ : ∀ v, Q (g v) = Q v) (hgY : ∀ y ∈ Y, g y ∈ Y)
    (hgYi : ∀ y ∈ Y, g⁻¹ y ∈ Y) (hgH : ∀ h ∈ H, g * h * g⁻¹ ∈ H) {h : V ≃ₗ[K] V}
    (hh : h ∈ radSub Q Y hY H) : g * h * g⁻¹ ∈ radSub Q Y hY H := by
  obtain ⟨hH, h1, h2, h3⟩ := hh
  have hgg : ∀ v, g (g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply g g⁻¹, mul_inv_cancel, leq_one_apply]
  have hgiQ : ∀ v, Q (g⁻¹ v) = Q v := fun v => by rw [← hgQ (g⁻¹ v), hgg]
  have hgP : ∀ v ∈ perp Q Y, g v ∈ perp Q Y := fun v hv => map_mem_perp hgQ hgYi hv
  have hgiP : ∀ v ∈ perp Q Y, g⁻¹ v ∈ perp Q Y := fun v hv =>
    map_mem_perp hgiQ (fun w hw => by rw [inv_inv]; exact hgY w hw) hv
  refine ⟨hgH h hH, fun y hy => ?_, fun v hv => ?_, fun v => ?_⟩
  · simp only [LinearEquiv.mul_apply]
    rw [h1 _ (hgYi y hy), hgg]
  · have e : (g * h * g⁻¹) v - v = g (h (g⁻¹ v) - g⁻¹ v) := by
      simp only [LinearEquiv.mul_apply, map_sub, hgg]
    rw [e]
    exact hgY _ (h2 _ (hgiP v hv))
  · have e : (g * h * g⁻¹) v - v = g (h (g⁻¹ v) - g⁻¹ v) := by
      simp only [LinearEquiv.mul_apply, map_sub, hgg]
    rw [e]
    exact hgP _ (h3 _)

theorem radCond_semiConj {G : V ≃+ V} {σ : K ≃+* K} {μ : K} (hμ : μ ≠ 0)
    (hGQ : ∀ v, Q (G v) = μ * σ (Q v)) (hGY : ∀ y ∈ Y, G y ∈ Y)
    (hGYi : ∀ y ∈ Y, G.symm y ∈ Y) {h h' : V ≃ₗ[K] V} (hh : RadCond Q Y h)
    (hconj : ∀ w, h' w = G (h (G.symm w))) : RadCond Q Y h' := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hGP : ∀ v ∈ perp Q Y, G v ∈ perp Q Y := by
    intro v hv
    rw [mem_perp] at hv ⊢
    intro y hy
    have h1 := hv _ (hGYi y hy)
    have h2 := polar_semi hGQ (G.symm y) v
    rw [AddEquiv.apply_symm_apply] at h2
    rw [h2, h1, map_zero, mul_zero]
  have hGiP : ∀ w ∈ perp Q Y, G.symm w ∈ perp Q Y := by
    intro w hw
    rw [mem_perp] at hw ⊢
    intro y hy
    have h1 := hw (G y) (hGY y hy)
    rw [← G.apply_symm_apply w, polar_semi hGQ] at h1
    exact (map_eq_zero_iff σ σ.injective).mp ((mul_eq_zero.mp h1).resolve_left hμ)
  refine ⟨fun y hy => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [hconj, h1 _ (hGYi y hy), AddEquiv.apply_symm_apply]
  · have e : h' v - v = G (h (G.symm v) - G.symm v) := by
      rw [hconj, map_sub, AddEquiv.apply_symm_apply]
    rw [e]
    exact hGY _ (h2 _ (hGiP v hv))
  · have e : h' v - v = G (h (G.symm v) - G.symm v) := by
      rw [hconj, map_sub, AddEquiv.apply_symm_apply]
    rw [e]
    exact hGP _ (h3 _)

theorem siegEquiv_mem_radSub [CharP K 2] {x w : V} (hsing : ∀ c d : K, Q (c • x + d • w) = 0)
    (hxY : x ∈ Y) (hwP : w ∈ perp Q Y) (hH : siegEquiv hsing ∈ H) :
    siegEquiv hsing ∈ radSub Q Y hY H := by
  have hxP : x ∈ perp Q Y := subset_perp hY hxY
  refine ⟨hH, fun y hy => ?_, fun v hv => ?_, fun v => ?_⟩
  · have e1 : polar Q y w = 0 := mem_perp.mp hwP y hy
    have e2 : polar Q y x = 0 := hY y hy x hxY
    rw [siegEquiv_apply, e1, e2, zero_smul, zero_smul, add_zero, add_zero]
  · have e2 : polar Q v x = 0 := by
      rw [polar_comm]
      exact mem_perp.mp hv x hxY
    rw [siegEquiv_sub, e2, zero_smul, add_zero]
    exact Y.smul_mem _ hxY
  · rw [siegEquiv_sub]
    exact (perp Q Y).add_mem ((perp Q Y).smul_mem _ hxP) ((perp Q Y).smul_mem _ hwP)

section Singular

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

omit [CharP K 2] in
theorem exists_singular_vector {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate) (h3 : 3 ≤ finrank K W) :
    ∃ w : W, w ≠ 0 ∧ R w = 0 := by
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_regular_split R hR
  have hdim := H.finrank_eq
  have hm : 1 ≤ m := by omega
  exact ⟨H.b (.inl ⟨0, hm⟩), H.b.ne_zero _, H.Q_inl _⟩

theorem exists_singular_perp (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank K V) {x : V}
    (hx : x ≠ 0) : ∃ w ∈ perp Q (K ∙ x), Q w = 0 ∧ ∀ c : K, w ≠ c • x := by
  classical
  have hself : ∀ u : V, polar Q u u = 0 := fun u => OrthRestOdd.polar_self_eq_zero Q u
  obtain ⟨x'', hx''⟩ : ∃ x'', polar Q x x'' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hQ.1 x fun v => by
      rw [polarBilin_apply_apply]
      exact hcon v)
  set x' := (polar Q x x'')⁻¹ • x'' with hx'
  have hxx' : polar Q x x' = 1 := by
    rw [hx', polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hx'']
  have hx'x : polar Q x' x = 1 := by rw [polar_comm]; exact hxx'
  set Z : Submodule K V := Submodule.span K {x, x'} with hZ
  set M : Submodule K V := perp Q Z with hM
  have hMx : ∀ u ∈ M, polar Q x u = 0 := fun u hu =>
    mem_perp.mp hu x (Submodule.subset_span (Set.mem_insert _ _))
  have hMx' : ∀ u ∈ M, polar Q x' u = 0 := fun u hu =>
    mem_perp.mp hu x' (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hdec : ∀ v : V, v - (polar Q v x' • x + polar Q v x • x') ∈ M := by
    intro v
    rw [hM, mem_perp]
    intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    have e1 : polar Q x v = polar Q v x := polar_comm Q x v
    have e2 : polar Q x' v = polar Q v x' := polar_comm Q x' v
    simp only [polar_add_left, polar_smul_left, polar_sub_right, polar_add_right,
      polar_smul_right, smul_eq_mul, hself, hxx', hx'x, e1, e2]
    ring
  have hnd : ∀ u ∈ M, (∀ u' ∈ M, polar Q u u' = 0) → u = 0 := by
    intro u hu hu'
    refine hQ.1 u fun v => ?_
    rw [polarBilin_apply_apply]
    have a1 : polar Q u x = 0 := by rw [polar_comm]; exact hMx u hu
    have a2 : polar Q u x' = 0 := by rw [polar_comm]; exact hMx' u hu
    have h1 : polar Q u (v - (polar Q v x' • x + polar Q v x • x')) = 0 := hu' _ (hdec v)
    have h2 : polar Q u (polar Q v x' • x + polar Q v x • x') = 0 := by
      simp only [polar_add_right, polar_smul_right, smul_eq_mul, a1, a2, mul_zero, add_zero]
    rw [polar_sub_right, h2, sub_zero] at h1
    exact h1
  have hZdim : finrank K Z ≤ 2 := by
    have h := finrank_span_finset_le_card (R := K) ({x, x'} : Finset V)
    rw [Finset.coe_pair] at h
    exact h.trans Finset.card_le_two
  have hMdim : 3 ≤ finrank K M := by
    have : finrank K M = finrank K V - finrank K Z :=
      LinearMap.BilinForm.finrank_orthogonal hQ Z
    omega
  obtain ⟨w, hw0, hwQ⟩ := exists_singular_vector (Q.comp M.subtype) (nondeg_comp hnd) hMdim
  refine ⟨(w : V), ?_, hwQ, fun c hc => ?_⟩
  · rw [mem_perp]
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [polar_smul_left, hMx _ w.2, smul_zero]
  · have h1 : polar Q x' (w : V) = 0 := hMx' _ w.2
    have h2 : polar Q (w : V) x' = 0 := by rw [polar_comm]; exact h1
    rw [hc, polar_smul_left, hxx', smul_eq_mul, mul_one] at h2
    apply hw0
    apply Subtype.ext
    rw [hc, h2, zero_smul]
    rfl

theorem exists_siegel_pair (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank K V)
    {Y : Submodule K V} (hY0 : Y ≠ ⊥) (hY : ∀ y ∈ Y, Q y = 0) :
    ∃ x ∈ Y, ∃ w ∈ perp Q Y, (∀ c d : K, Q (c • x + d • w) = 0) ∧
      ∀ c d : K, c • x + d • w = 0 → c = 0 ∧ d = 0 := by
  have hYp : ∀ y ∈ Y, ∀ y' ∈ Y, polar Q y y' = 0 := fun y hy y' hy' => by
    have := hY (y + y') (Y.add_mem hy hy')
    rw [polar, hY y hy, hY y' hy'] at *
    simpa [polar] using this
  obtain ⟨x, hxY, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hind : ∀ {w : V}, (∀ c : K, w ≠ c • x) → ∀ c d : K, c • x + d • w = 0 → c = 0 ∧ d = 0 := by
    intro w hw c d hcd
    by_cases hd : d = 0
    · subst hd
      rw [zero_smul, add_zero] at hcd
      exact ⟨(smul_eq_zero.mp hcd).resolve_right hx0, rfl⟩
    · exfalso
      refine hw (-(c * d⁻¹)) ?_
      have h1 : d • w = -(c • x) := eq_neg_of_add_eq_zero_right hcd
      calc w = d⁻¹ • (d • w) := by rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
        _ = -(c * d⁻¹) • x := by rw [h1, smul_neg, smul_smul, neg_smul, mul_comm]
  by_cases h : ∃ w ∈ Y, ∀ c : K, w ≠ c • x
  · obtain ⟨w, hwY, hw⟩ := h
    refine ⟨x, hxY, w, subset_perp hYp hwY, fun c d => hY _ (Y.add_mem (Y.smul_mem c hxY)
      (Y.smul_mem d hwY)), hind hw⟩
  · push Not at h
    obtain ⟨w, hw, hwQ, hwx⟩ := exists_singular_perp hQ h5 hx0
    have hYle : Y ≤ K ∙ x := fun y hy => by
      obtain ⟨c, hc⟩ := h y hy
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    have hwY : w ∈ perp Q Y := by
      rw [mem_perp] at hw ⊢
      exact fun y hy => hw y (hYle hy)
    refine ⟨x, hxY, w, hwY, fun c d => ?_, hind hwx⟩
    have hxw : polar Q x w = 0 := mem_perp.mp hw x (Submodule.mem_span_singleton_self x)
    rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul, hY x hxY, hwQ,
      polar_smul_left, polar_smul_right, hxw]
    simp

end Singular

end LIDTwDF

end CFSG.StandardType
