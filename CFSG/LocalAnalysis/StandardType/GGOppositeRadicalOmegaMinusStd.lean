module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions GGOppRad GGOppRadSpU

variable {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

omit [Finite K] in
theorem quadMinus_single_inl (i : Fin (n - 1)) :
    quadMinus n K b c (Pi.single (.inl i) 1) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

include hirr in
theorem finrank_le_of_quadMinus [CharP K 2] {W : Submodule K (Vm n K)}
    (hW : ∀ w ∈ W, quadMinus n K b c w = 0) : finrank K W ≤ n - 1 := by
  classical
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  by_contra hlt
  push Not at hlt
  set B := Module.finBasis K W
  let w : Fin (n - 1) → Vm n K := fun j => (B (Fin.castLE (by omega) j) : Vm n K)
  have hw : LinearIndependent K w :=
    (B.linearIndependent.comp _ (Fin.castLE_injective _)).map' W.subtype (Submodule.ker_subtype W)
  let u : Fin (n - 1) → Vm n K := fun j => Pi.single (.inl j) 1
  have hu : LinearIndependent K u := by
    have := (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).linearIndependent.comp
      Sum.inl Sum.inl_injective
    convert this using 1
    funext j
    simp [u]
  have hwW : ∀ j, w j ∈ W := fun j => (B _).2
  have hpolW : ∀ x ∈ W, ∀ y ∈ W, polar (quadMinus n K b c) x y = 0 := fun x hx y hy => by
    rw [QuadraticMap.polar, hW _ (add_mem hx hy), hW x hx, hW y hy, sub_zero, sub_zero]
  obtain ⟨g, hgO, hgu⟩ := exists_mem_orthogonalGroup_apply_eq hQ u w hu hw
    (fun i => by rw [hW _ (hwW i), quadMinus_single_inl])
    (fun i j => by
      rw [hpolW _ (hwW i) _ (hwW j), polar_single_minus]
      simp [u, mpr])
  have hsupp : ∀ x ∈ W, ∀ a, (∀ i, a ≠ .inl i) → (g.symm x) a = 0 := by
    intro x hx a ha
    have hy1 : ∀ i, (g.symm x) (.inr (.inl i)) = 0 := by
      intro i
      have h1 : polar (quadMinus n K b c) (u i) (g.symm x) = 0 := by
        rw [← polar_map_of_mem hgO, hgu, LinearEquiv.apply_symm_apply]
        exact hpolW _ (hwW i) _ hx
      rw [polar_single_minus] at h1
      simpa [mg, mpr] using h1
    have hQy : quadMinus n K b c (g.symm x) = 0 := by
      rw [← map_of_mem hgO, LinearEquiv.apply_symm_apply]
      exact hW x hx
    rw [quadMinus_apply] at hQy
    simp only [hy1, mul_zero, Finset.sum_const_zero, zero_add] at hQy
    have hplane : (![(g.symm x) (.inr (.inr 0)), (g.symm x) (.inr (.inr 1))] : Fin 2 → K) = 0 := by
      by_contra hne
      refine planeNorm_ne_zero hirr hne ?_
      simp only [planeNorm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination hQy
    rcases a with i | i | t
    · exact absurd rfl (ha i)
    · exact hy1 i
    · fin_cases t
      · simpa using congrFun hplane 0
      · simpa using congrFun hplane 1
  let φ : W →ₗ[K] (Fin (n - 1) → K) :=
    (LinearMap.funLeft K K Sum.inl).comp ((g.symm : Vm n K →ₗ[K] Vm n K).comp W.subtype)
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have hzero : g.symm (x : Vm n K) = 0 := by
      funext a
      rcases a with i | a
      · exact congrFun hx i
      · exact hsupp x x.2 _ (fun i h => by simp at h)
    exact Subtype.ext (by simpa using congrArg g hzero)
  have := LinearMap.finrank_le_finrank_of_injective hφ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  omega

omit [Finite K] in
theorem quadMinus_single_plane : quadMinus n K b c (Pi.single (.inr (.inr 0)) 1) = 1 := by
  rw [quadMinus_apply]
  simp

omit [Finite K] in
theorem map_reflection_stdFlag_minus [CharP K 2] {M : ℕ}
    {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ : IsMinusLevel M ℓ)
    [Invertible (quadMinus n K b c (Pi.single (.inr (.inr 0)) 1))] (k : ℕ) :
    (stdFlag ℓ k).map (TauCeti.QuadraticMap.reflection (quadMinus n K b c)
      (Pi.single (.inr (.inr 0)) 1) : Vm n K →ₗ[K] Vm n K) = stdFlag ℓ k := by
  classical
  set r := TauCeti.QuadraticMap.reflection (quadMinus n K b c)
    (Pi.single (.inr (.inr 0)) (1 : K) : Vm n K)
  have hle : (stdFlag ℓ k).map (r : Vm n K →ₗ[K] Vm n K) ≤ stdFlag ℓ k := by
    rintro _ ⟨v, hv, rfl⟩ a ha
    change (TauCeti.QuadraticMap.reflection (quadMinus n K b c) _ v) a = 0
    rw [TauCeti.QuadraticMap.reflection_apply, polar_single_minus, Pi.sub_apply, Pi.smul_apply,
      hv a ha, zero_sub, smul_eq_mul, neg_eq_zero]
    by_cases hap : a = .inr (.inr 0)
    · have h1 : v (mpr (.inr (.inr 0) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) = 0 := by
        refine hv _ ?_
        rw [hap] at ha
        have : mpr (.inr (.inr 0) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = .inr (.inr 1) := rfl
        rw [this, ← hℓ.2]
        exact ha
      rw [h1, mul_zero, mul_zero, zero_mul]
    · rw [Pi.single_eq_of_ne hap, mul_zero]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ r.injective _)).symm

theorem exists_singFlag_eq_flagMap_minus [CharP K 2] (hn : 4 ≤ n)
    (R : Subgroup (spinGroup (quadMinus n K b c))) :
    ∃ (h : spinGroup (quadMinus n K b c)) (ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ),
      IsMinusLevel (2 * finrank K (Vm n K)) ℓ ∧
      singFlag (minusForm n hirr) (minusRep n K b c) R =
        GGOppRad.flagMap (minusRep n K b c) h (stdFlag ℓ) := by
  classical
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  set Φ := minusForm n hirr with hΦ
  set ρ := minusRep n K b c with hρ
  set d := finrank K (Vm n K) with hd
  set W := singSeq Φ ρ R with hW
  have hWmono : Monotone W := singSeq_mono Φ ρ R
  have hWle : ∀ j, W j ≤ W d := fun j => by
    rcases le_total j d with h | h
    · exact hWmono h
    · exact (singSeq_eq_of_le Φ ρ R h).le
  obtain ⟨X, hX0, hXmono, hXrank, hXtop, hXW⟩ :=
    exists_finrank_chain_forall_exists_eq hWmono hWle ⟨d, rfl⟩
  set m := finrank K (W d) with hm
  have hWds : ∀ x ∈ W d, quadMinus n K b c x = 0 := isTotallySingular_singSeq Φ ρ R d
  have hmn : m ≤ n - 1 := finrank_le_of_quadMinus hirr hWds
  have hXle : ∀ i, X i ≤ W d := fun i => by
    rcases le_total i m with h | h
    · rw [← hXtop m le_rfl]
      exact hXmono h
    · rw [hXtop i h]
  obtain ⟨P, -, hPorth, hPX⟩ := CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.exists_hypPairs_of_flag_of_le m ⊤
    (polarNondegOn_top hQ) (W d) le_top hWds le_rfl m le_rfl X le_top (fun i hi => hXrank i hi)
    (fun i _ => hXmono (Nat.le_succ i)) (fun x hx => hWds x (hXle m hx))
  let u : Fin m → Vm n K := fun j => Pi.single (.inl (Fin.castLE hmn j)) 1
  have hu : LinearIndependent K u := by
    have := (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).linearIndependent.comp
      (fun j : Fin m => (Sum.inl (Fin.castLE hmn j) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2))
      (Sum.inl_injective.comp (Fin.castLE_injective hmn))
    convert this using 1
    funext j
    simp [u]
  have hu' : LinearIndependent K (fun j => (P j).e) :=
    (CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.linearIndependent_pairs hPorth).comp Sum.inl Sum.inl_injective
  obtain ⟨g, hgO, hgu⟩ := exists_mem_orthogonalGroup_apply_eq hQ u (fun j => (P j).e) hu hu'
    (fun i => by rw [(P i).Q_e, quadMinus_single_inl])
    (fun i j => by
      rw [polar_single_minus]
      by_cases hij : i = j
      · subst hij
        rw [QuadraticMap.polar_self, (P i).Q_e, smul_zero]
        simp [u, mpr]
      · rw [(hPorth i j hij).ee]
        simp [u, mpr])
  have hgX : ∀ i ≤ m, (Submodule.span K (u '' {j | (j : ℕ) < i})).map
      (g : Vm n K →ₗ[K] Vm n K) = X i := by
    intro i hi
    rw [Submodule.map_span, ← Set.image_comp, hPX i hi]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply, LinearEquiv.coe_coe, hgu]
  set D : ℕ → ℕ := fun k => finrank K (W k) with hD
  have hDmono : Monotone D := fun _ _ h => Submodule.finrank_mono (hWmono h)
  have hDm : ∀ k, D k ≤ m := fun k => Submodule.finrank_mono (hWle k)
  have hWX : ∀ k, W k = X (D k) := by
    intro k
    obtain ⟨j, hj⟩ := hXW k
    rcases le_total j m with hjm | hjm
    · rw [hj, hD]
      simp only
      rw [hj, hXrank j hjm]
    · have h1 : W k = W d := by rw [hj, hXtop j hjm]
      rw [hD]
      simp only
      rw [h1, hXtop m le_rfl]
  have hex : ∀ t : Fin (n - 1), ∃ k, (t : ℕ) < D (k + 1) ∨ d ≤ k := fun _ => ⟨d, Or.inr le_rfl⟩
  set ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ := Sum.elim (fun t => Nat.find (hex t))
    (Sum.elim (fun t => 2 * d - Nat.find (hex t)) fun _ => d) with hℓ
  have hℓd : ∀ t, Nat.find (hex t) ≤ d := fun t => Nat.find_min' (hex t) (Or.inr le_rfl)
  have hℓm : IsMinusLevel (2 * d) ℓ := by
    refine ⟨fun a => ?_, rfl⟩
    rcases a with t | t | t <;> simp only [hℓ, mpr, Sum.elim_inl, Sum.elim_inr]
    · have := hℓd t
      omega
    · have := hℓd t
      omega
    · omega
  have hD0 : D 0 = 0 := by
    change finrank K (singSeq Φ ρ R 0) = 0
    rw [singSeq_zero, finrank_bot]
  have hinl : ∀ t k, k ≤ d → (ℓ (Sum.inl t) < k ↔ (t : ℕ) < D k) := by
    intro t k hk
    simp only [hℓ, Sum.elim_inl]
    constructor
    · intro h
      have hs := Nat.find_spec (hex t)
      rcases hs with hs | hs
      · exact lt_of_lt_of_le hs (hDmono (by omega))
      · omega
    · intro h
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hD0] at h
        exact Nat.not_lt_zero _ h
      have : Nat.find (hex t) ≤ k - 1 :=
        Nat.find_min' (hex t) (Or.inl (by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]))
      omega
  have hinr : ∀ a, (∀ t, a ≠ Sum.inl t) → ∀ k, k ≤ d → ¬ ℓ a < k := by
    intro a ha k hk
    rcases a with t | t | t
    · exact absurd rfl (ha t)
    · simp only [hℓ, Sum.elim_inr, Sum.elim_inl]
      have := hℓd t
      omega
    · simp only [hℓ, Sum.elim_inr]
      omega
  have hstd : ∀ k ≤ d, stdFlag (K := K) ℓ k = Submodule.span K (u '' {j | (j : ℕ) < D k}) := by
    intro k hk
    rw [stdFlag_eq_span]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      rcases a with t | a
      · have ht := (hinl t k hk).mp ha
        refine ⟨⟨t, by have := hDm k; omega⟩, ht, ?_⟩
        simp [u]
      · exact absurd ha (hinr _ (fun t h => by simp at h) k hk)
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨Sum.inl (Fin.castLE hmn j), (hinl _ k hk).mpr (by simpa using hj)⟩, ?_⟩
      simp [u]
  have hiso : ∀ k ≤ d, W k = (stdFlag ℓ k).map (g : Vm n K →ₗ[K] Vm n K) := fun k hk => by
    rw [hWX k, hstd k hk, hgX _ (hDm k)]
  have key : ∀ h : spinGroup (quadMinus n K b c),
      (∀ k ≤ d, W k = (stdFlag ℓ k).map (ρ h)) →
      singFlag Φ ρ R = GGOppRad.flagMap ρ h (stdFlag ℓ) := fun h hk =>
    isoCompletion_eq_flagMap (isIsometric_minusRep hirr) (isSelfDual_stdFlag_minus hirr hℓm) hk
  by_cases hgΩ : g ∈ omegaGroup (quadMinus n K b c) hQ
  · obtain ⟨h, hh⟩ := exists_spinAction_eq_of_mem_omegaGroup_minus hirr hn hgΩ
    refine ⟨h, ℓ, hℓm, key h fun k hk => ?_⟩
    rw [hiso k hk]
    congr 1
    refine LinearMap.ext fun v => ?_
    rw [hρ, minusRep_apply, hh]
    rfl
  · let _ : Invertible (quadMinus n K b c (Pi.single (.inr (.inr 0)) 1)) :=
      invertibleOfNonzero (by rw [quadMinus_single_plane]; exact one_ne_zero)
    set r := TauCeti.QuadraticMap.reflection (quadMinus n K b c)
      (Pi.single (.inr (.inr 0)) (1 : K) : Vm n K) with hr
    have hrO := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (quadMinus n K b c)
      (Pi.single (.inr (.inr 0)) (1 : K) : Vm n K)
    have hr1 := finrank_commSpace_reflection hQ (Pi.single (.inr (.inr 0)) (1 : K) : Vm n K)
    have hgr : g * r ∈ omegaGroup (quadMinus n K b c) hQ := by
      refine mem_omegaGroup.mpr ⟨mul_mem hgO hrO, ?_⟩
      have hodd : ¬ Even (finrank K (commSpace g)) := fun he =>
        hgΩ (mem_omegaGroup.mpr ⟨hgO, he⟩)
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hgO hrO, hr1,
        (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp hodd), Nat.cast_one]
      rfl
    obtain ⟨h, hh⟩ := exists_spinAction_eq_of_mem_omegaGroup_minus hirr hn hgr
    refine ⟨h, ℓ, hℓm, key h fun k hk => ?_⟩
    have hρh : ρ h = (g : Vm n K →ₗ[K] Vm n K) ∘ₗ (r : Vm n K →ₗ[K] Vm n K) := by
      refine LinearMap.ext fun v => ?_
      rw [hρ, minusRep_apply, hh]
      rfl
    rw [hiso k hk, hρh, Submodule.map_comp, map_reflection_stdFlag_minus hℓm k]

end GGOppRadOmega

end CFSG.StandardType
