module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusFix

public section

open Module Multiplicative QuadraticMap
open scoped commutatorElement

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

section Normal

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem conj_mem_orthDerived {g x : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx : x ∈ orthDerived Q) : g * x * g⁻¹ ∈ orthDerived Q := by
  have hxO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup hx
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (Subgroup.commutator_mem_commutator hg hxO) hx

end Normal

section Frames

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isFrame_elim0 {c₀ : K} {τ : Bool} {m : ℕ} {e f : Fin m → V} {a b : V}
    (hF : OrdPNsOm.IsFrame Q c₀ τ e f a b) :
    OrdPNsOm.IsFrame Q c₀ τ (Fin.elim0 : Fin 0 → V) Fin.elim0 a b :=
  ⟨⟨finZeroElim, finZeroElim, finZeroElim, finZeroElim, finZeroElim⟩, finZeroElim, finZeroElim,
    finZeroElim, finZeroElim, hF.pab, hF.qa, hF.qb⟩

theorem tailSum_not (K : Type) [Field K] (τ : Bool) :
    OrdPNsOm.tailSum K (!τ) = -OrdPNsOm.tailSum K τ := by
  cases τ <;> simp [OrdPNsOm.tailSum]

theorem even_finrank_of_nondegOn [CharP K 2] {W : Submodule K V} [FiniteDimensional K W]
    (hW : SUTB.NondegOn (polarBilin Q) W) : Even (finrank K W) := by
  refine LinearMap.BilinForm.IsAlt.even_finrank
    (B := LinearMap.BilinForm.restrict (polarBilin Q) W) (fun x => ?_)
    ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change polar Q (x : V) x = 0
    exact OrdPNsOm.polar_self_charTwo _
  · refine Subtype.ext (hW x x.2 fun n hn => ?_)
    have h1 := hx ⟨n, hn⟩
    change polar Q (x : V) n = 0 at h1
    rw [polarBilin_apply_apply, polar_comm]
    exact h1
  · exact Subtype.ext (hW x x.2 fun n hn => hx ⟨n, hn⟩)

end Frames

section ActSub

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] [AddCommGroup V] [Module K V] {s r : ℕ} {κ : Type}
  (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V) (a : Fin r → Fin s)

theorem finrank_actSub (ha : Function.Injective a) :
    finrank K (actSub Φ a) = r * finrank K D := by
  classical
  let g : (Fin r → D) →ₗ[K] (Fin s → D) :=
    ∑ j : Fin r, (LinearMap.single K (fun _ : Fin s => D) (a j)).comp (LinearMap.proj j)
  let f : (Fin r → D) →ₗ[K] V :=
    Φ.toLinearMap.comp ((LinearMap.inl K (Fin s → D) (κ → K)).comp g)
  have hg_apply : ∀ (d : Fin r → D) (i : Fin s),
      g d i = ∑ j : Fin r, if i = a j then d j else 0 := by
    intro d i
    simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.single_apply, Pi.single_apply, Finset.sum_apply]
  have hg_self : ∀ (d : Fin r → D) (j : Fin r), g d (a j) = d j := by
    intro d j
    rw [hg_apply, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [if_neg (fun h => hk (ha h).symm)]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hg_zero : ∀ (d : Fin r → D) {i : Fin s}, (∀ j, a j ≠ i) → g d i = 0 := by
    intro d i hi
    rw [hg_apply, Finset.sum_eq_zero]
    intro j _
    rw [if_neg (fun h => hi j h.symm)]
  have hf : Function.Injective f := by
    intro d d' h
    have h0 : Φ ((g d, 0) : (Fin s → D) × (κ → K)) =
        Φ ((g d', 0) : (Fin s → D) × (κ → K)) := h
    have h1 : g d = g d' := congrArg Prod.fst (Φ.injective h0)
    funext j
    rw [← hg_self d j, ← hg_self d' j, h1]
  have hrange : LinearMap.range f = actSub Φ a := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, rfl⟩
      exact (frame_mem_actSub Φ a).mpr ⟨rfl, fun i hi => hg_zero d hi⟩
    · intro v hv
      obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
      obtain ⟨hw, hd⟩ := (frame_mem_actSub Φ a).mp hv
      refine ⟨fun j => d (a j), ?_⟩
      have hgd : g (fun j => d (a j)) = d := by
        funext i
        by_cases hi : ∃ j, a j = i
        · obtain ⟨j, rfl⟩ := hi
          rw [hg_self]
        · push Not at hi
          rw [hg_zero _ hi, hd i hi]
      change Φ (g (fun j => d (a j)), 0) = Φ (d, w)
      rw [hgd, hw]
  have hdom : finrank K (Fin r → D) = r * finrank K D := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  rw [← hrange, LinearMap.finrank_range_of_inj hf, hdom]

end ActSub

section Witt

variable {K : Type} [Field K] [Finite K] [CharP K 2] {D V : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {s r p : ℕ} [Fact p.Prime] {κ : Type} (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V)
  {cE : D ≃ₗ[K] D} (hcp : cE ^ p = 1) {a : Fin r → Fin s}
  {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D} {A : Subgroup (V ≃ₗ[K] V)}

omit [Finite K] in
theorem false_of_plane (hQ : (polarBilin Q).Nondegenerate) (hfix : ∀ x, cE x = x → x = 0)
    (ha : Function.Injective a)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (hdim : finrank K D = 2) (hA : (coordTorus Φ hcp a).range = A)
    (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {c₀ : K} {τ₀ : Bool} (j₀ : Fin r) {a₁ b₁ : V} (ha₁ : a₁ ∈ pieceSub Φ a j₀)
    (hb₁ : b₁ ∈ pieceSub Φ a j₀)
    (hF₁ : OrdPNsOm.IsFrame Q c₀ τ₀ (Fin.elim0 : Fin 0 → V) Fin.elim0 a₁ b₁) {a' b' : V}
    (ha' : a' ∈ fixSub Φ a) (hb' : b' ∈ fixSub Φ a)
    (hF' : OrdPNsOm.IsFrame Q c₀ τ₀ (Fin.elim0 : Fin 0 → V) Fin.elim0 a' b') : False := by
  classical
  obtain ⟨g, hgO, hg⟩ := OrdPNsOm.exists_orth_frames (k := 1) (m := 0) hQ
    (e := fun _ => Fin.elim0) (f := fun _ => Fin.elim0) (a := fun _ => a₁) (b := fun _ => b₁)
    (e' := fun _ => Fin.elim0) (f' := fun _ => Fin.elim0) (a' := fun _ => a') (b' := fun _ => b')
    (fun _ => hF₁) (fun _ => hF') (fun j j' h => absurd (Subsingleton.elim j j') h)
    (fun j j' h => absurd (Subsingleton.elim j j') h)
  have hga : g a₁ = a' := hg 0 (.inr (.inr 0))
  have hgb : g b₁ = b' := hg 0 (.inr (.inr 1))
  have hgg : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
  set y₀ := coordTorus Φ hcp a (Pi.mulSingle j₀ (ofAdd (1 : ZMod p))) with hy₀
  have hy₀A : y₀ ∈ A := hA ▸ ⟨_, rfl⟩
  have hspan : Submodule.span K {a₁, b₁} = pieceSub Φ a j₀ :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (by rintro _ (rfl | rfl); exacts [ha₁, hb₁]))
      (by rw [OrdPNsOm.finrank_span_pair hF₁.pab, finrank_pieceSub, hdim])
  have hgW : ∀ u ∈ pieceSub Φ a j₀, g u ∈ fixSub Φ a := by
    intro u hu
    rw [← hspan] at hu
    obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [map_add, map_smul, map_smul, hga, hgb]
    exact (fixSub Φ a).add_mem ((fixSub Φ a).smul_mem _ ha') ((fixSub Φ a).smul_mem _ hb')
  have hAfix : ∀ c ∈ A, ∀ w ∈ fixSub Φ a, c w = w := by
    intro c hc w hw
    rw [← hA] at hc
    obtain ⟨f, rfl⟩ := hc
    exact coordTorus_fixSub Φ hcp hfix ha f hw
  have hAO : ∀ c ∈ A, c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun c hc =>
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (hAΩ hc)
  set h := g * y₀ * g⁻¹ with hh
  have hsubW : ∀ v, h v - v ∈ fixSub Φ a := by
    intro v
    have h1 : h v - v = g (y₀ (g⁻¹ v) - g⁻¹ v) := by
      rw [map_sub, hgg]
      rfl
    rw [h1]
    exact hgW _ (coordTorus_sub_mem_pieceSub Φ hcp ha j₀ 1 _)
  have hfixperp : ∀ x, (∀ w ∈ fixSub Φ a, polar Q w x = 0) → h x = x := by
    intro x hx
    have h1 : y₀ (g⁻¹ x) = g⁻¹ x := by
      refine coordTorus_eq_of_polar Φ hcp hfix ha hdec hωnd j₀ fun u hu => ?_
      have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO u (g⁻¹ x)
      rw [hgg] at h2
      rw [← h2]
      exact hx _ (hgW u hu)
    change g (y₀ (g⁻¹ x)) = x
    rw [h1, hgg]
  have hcomm : ∀ c ∈ A, h * c = c * h := by
    intro c hc
    refine LinearEquiv.ext fun v => ?_
    change h (c v) = c (h v)
    have hperp : ∀ w ∈ fixSub Φ a, polar Q w (c v - v) = 0 := by
      intro w hw
      rw [polar_sub_right]
      have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hAO c hc) w v
      rw [hAfix c hc w hw] at h2
      rw [h2, sub_self]
    have k1 : h (c v) = h v + (c v - v) := by
      have e : c v = v + (c v - v) := by abel
      conv_lhs => rw [e]
      rw [map_add, hfixperp _ hperp]
    have k2 : c (h v) = c v + (h v - v) := by
      have e : h v = v + (h v - v) := by abel
      conv_lhs => rw [e]
      rw [map_add, hAfix c hc _ (hsubW v)]
    rw [k1, k2]
    abel
  have hhΩ : h ∈ orthDerived Q := conj_mem_orthDerived hgO (hAΩ hy₀A)
  have hhp : h ^ p = 1 := by
    rw [hh, conj_pow, hy₀, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one,
      mul_inv_cancel]
  have hhA := hmax h hhΩ hhp hcomm
  have k1 : h a' = a' := hAfix h hhA a' ha'
  have k2 : h a' = g (y₀ a₁) := by
    change g (y₀ (g⁻¹ a')) = g (y₀ a₁)
    rw [← hga]
    congr 2
    exact g.symm_apply_apply a₁
  rw [k2, ← hga] at k1
  have k3 : y₀ a₁ = a₁ := g.injective k1
  have k4 := eq_zero_of_coordTorus_pieceSub Φ hcp hfix ha j₀ ha₁ k3
  have k5 := hF₁.pab
  rw [k4, polar_zero_left] at k5
  exact zero_ne_one k5

private theorem exists_piece_frame_plane (hdec : ∀ d d' w w',
      polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (hdim : finrank K D = 2) (hr : 0 < r) :
    ∃ (c₀ : K), c₀ ∉ (OrdPNsOm.wp K).range ∧ ∃ (τ₀ : Bool) (j₀ : Fin r) (a₁ b₁ : V),
      a₁ ∈ pieceSub Φ a j₀ ∧ b₁ ∈ pieceSub Φ a j₀ ∧
      OrdPNsOm.IsFrame Q c₀ τ₀ (Fin.elim0 : Fin 0 → V) Fin.elim0 a₁ b₁ ∧
      OrdPNsOm.charSum Q (pieceSub Φ a j₀) = OrdPNsOm.tailSum K τ₀ := by
  classical
  have : Finite V := Module.finite_of_finite K
  obtain ⟨c₀, hc₀⟩ := OrdPNsOm.exists_not_mem_range_wp (K := K)
  set j₀ : Fin r := ⟨0, hr⟩
  obtain ⟨τ₀, a₁, b₁, ha₁, hb₁, hF₁, hS₁⟩ := OrdPNsOm.exists_frame_plane hc₀
    (nondegOn_pieceSub Φ a hdec hωnd j₀) (by rw [finrank_pieceSub, hdim])
  exact ⟨c₀, hc₀, τ₀, j₀, a₁, b₁, ha₁, hb₁, hF₁, hS₁⟩

private theorem false_of_fixSub_finrank (hQ : (polarBilin Q).Nondegenerate)
    (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (hdim : finrank K D = 2)
    (hA : (coordTorus Φ hcp a).range = A) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hr : 0 < r) (m : ℕ) (hfin : finrank K (fixSub Φ a) = 2 * (m + 1) + 2) : False := by
  classical
  have : Finite V := Module.finite_of_finite K
  obtain ⟨c₀, hc₀, τ₀, j₀, a₁, b₁, ha₁, hb₁, hF₁, -⟩ :=
    exists_piece_frame_plane Φ hdec hωnd hdim hr
  have hWnd := nondegOn_fixSub Φ a hQ hdec
  obtain ⟨τ, e, f, a', b', hmem, hF, hS⟩ :=
    OrdPNsOm.exists_frame hc₀ (m + 1) (fixSub Φ a) hWnd hfin
  obtain ⟨a'', b'', ha'', hb'', hF''⟩ := OrdPFieldNsOm.exists_frame_castSucc hF τ₀ hmem
  exact (false_of_plane Φ hcp hQ hfix ha hdec hωnd hdim hA hAΩ hmax j₀ ha₁ hb₁ hF₁ ha'' hb''
    (isFrame_elim0 hF'')).elim

theorem charSum_fixSub_modEq_neg_one (hQ : (polarBilin Q).Nondegenerate)
    (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (hdim : finrank K D = 2) (hA : (coordTorus Φ hcp a).range = A)
    (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hiso : ∀ f v, Q (coordTorus Φ hcp a f v) = Q v) (hr : 0 < r) (hW : fixSub Φ a ≠ ⊥) :
    OrdPNsOm.charSum Q (fixSub Φ a) ≡ -1 [ZMOD p] := by
  classical
  have : Finite V := Module.finite_of_finite K
  obtain ⟨c₀, hc₀, τ₀, j₀, a₁, b₁, ha₁, hb₁, hF₁, hS₁⟩ :=
    exists_piece_frame_plane Φ hdec hωnd hdim hr
  have hτ₀ : OrdPNsOm.tailSum K τ₀ ≡ 1 [ZMOD p] := by
    rw [← hS₁]
    exact charSum_pieceSub_modEq Φ hcp hfix ha hiso j₀
  have hWnd := nondegOn_fixSub Φ a hQ hdec
  have hev := even_finrank_of_nondegOn hWnd
  have hpos : finrank K (fixSub Φ a) ≠ 0 := fun h0 => hW (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨m, hm⟩ : ∃ m, finrank K (fixSub Φ a) = 2 * m + 2 := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  rcases m with _ | m
  · obtain ⟨τ, e, f, a', b', hmem, hF, hS⟩ :=
      OrdPNsOm.exists_frame hc₀ 0 (fixSub Φ a) hWnd hm
    by_cases hττ : τ = τ₀
    · subst hττ
      exact (false_of_plane Φ hcp hQ hfix ha hdec hωnd hdim hA hAΩ hmax j₀ ha₁ hb₁ hF₁
        (hmem (.inr (.inr 0))) (hmem (.inr (.inr 1))) (isFrame_elim0 hF)).elim
    · have hτ : τ = !τ₀ := by cases τ <;> cases τ₀ <;> simp_all
      rw [hS, pow_zero, one_mul, hτ, tailSum_not]
      exact hτ₀.neg
  · exact (false_of_fixSub_finrank Φ hcp hQ hfix ha hdec hωnd hdim hA hAΩ hmax hr m hm).elim

theorem finrank_fixSub_le_two (hQ : (polarBilin Q).Nondegenerate)
    (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (hdim : finrank K D = 2)
    (hA : (coordTorus Φ hcp a).range = A) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hr : 0 < r) : finrank K (fixSub Φ a) ≤ 2 := by
  classical
  have : Finite V := Module.finite_of_finite K
  by_cases hW : fixSub Φ a = ⊥
  · rw [hW, finrank_bot]
    exact Nat.zero_le _
  · have hWnd := nondegOn_fixSub Φ a hQ hdec
    have hev := even_finrank_of_nondegOn hWnd
    have hpos : finrank K (fixSub Φ a) ≠ 0 := fun h0 => hW (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨m, hm⟩ : ∃ m, finrank K (fixSub Φ a) = 2 * m + 2 := by
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    rcases m with _ | m
    · rw [hm]
    · exact (false_of_fixSub_finrank Φ hcp hQ hfix ha hdec hωnd hdim hA hAΩ hmax hr m hm).elim

omit [Finite K] [FiniteDimensional K D] in
theorem exists_sgn_mem_orthDerived [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hiso : ∀ f, coordTorus Φ hcp a f ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hW : fixSub Φ a ≠ ⊥) (i : Fin r) {σ : V ≃ₗ[K] V}
    (hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hσ : ∀ f, σ * coordTorus Φ hcp a f * σ⁻¹ = coordTorus Φ hcp a (sgnAut i f)) :
    ∃ w ∈ orthDerived Q, ∀ f, w * coordTorus Φ hcp a f * w⁻¹ = coordTorus Φ hcp a (sgnAut i f) := by
  classical
  obtain ⟨u, hu, hQu⟩ := RootPlaneD4.exists_quad_ne_zero (nondegOn_fixSub Φ a hQ hdec) hW
  let : Invertible (Q u) := invertibleOfNonzero hQu
  set ρ := TauCeti.QuadraticMap.reflection Q u with hρ
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q u
  have hρc : ∀ f, ρ * coordTorus Φ hcp a f = coordTorus Φ hcp a f * ρ := by
    intro f
    refine LinearEquiv.ext fun v => ?_
    have hfu := coordTorus_fixSub Φ hcp hfix ha f hu
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hiso f) u v
    rw [hfu] at h1
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, TauCeti.QuadraticMap.reflection_apply,
      TauCeti.QuadraticMap.reflection_apply, map_sub, map_smul, hfu, h1]
  by_cases he : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace σ))
  · exact ⟨σ, CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
      (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hσO, he⟩), hσ⟩
  · refine ⟨σ * ρ, CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
      (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨mul_mem hσO hρO, ?_⟩),
      fun f => ?_⟩
    · rw [← ZMod.natCast_eq_zero_iff_even,
        CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hσO hρO,
        CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ u]
      have h1 : ((finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace σ) : ℕ) :
          ZMod 2) ≠ 0 := by
        rwa [Ne, ZMod.natCast_eq_zero_iff_even]
      have key : ∀ x : ZMod 2, x ≠ 0 → x + ((1 : ℕ) : ZMod 2) = 0 := by decide
      exact key _ h1
    · rw [show σ * ρ * coordTorus Φ hcp a f * (σ * ρ)⁻¹ =
          σ * (ρ * coordTorus Φ hcp a f) * ρ⁻¹ * σ⁻¹ by group, hρc,
        show σ * (coordTorus Φ hcp a f * ρ) * ρ⁻¹ * σ⁻¹ = σ * coordTorus Φ hcp a f * σ⁻¹ by group,
        hσ]

end Witt

end OrthTorus

end CFSG.StandardType

end
