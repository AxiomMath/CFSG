module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFlagTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotent

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions GGOppRad GGOppRadSpU
open CFSG.LocalAnalysis.ComponentInitial

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type*} [Group H] {F : ReflForm K V} {ρ : H →* Module.End K V}

theorem rep_injective_apply (g : H) : Function.Injective (ρ g) :=
  fun x y hxy => by simpa only [rep_inv_apply_rep] using congrArg (ρ g⁻¹) hxy

theorem perp_map_of_isIsometric [FiniteDimensional K V] (hρ : IsIsometric F ρ) (g : H)
    (Y : Submodule K V) : F.perp (Y.map (ρ g)) = (F.perp Y).map (ρ g) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hρ.apply_mem_perp g ha
  · have h1 := F.finrank_perp (Y.map (ρ g))
    have h2 := F.finrank_perp Y
    have e1 : finrank K (Y.map (ρ g)) = finrank K Y :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rep_injective_apply g) _)).symm
    have e2 : finrank K ((F.perp Y).map (ρ g)) = finrank K (F.perp Y) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rep_injective_apply g) _)).symm
    omega

theorem isoCompletion_eq_flagMap [FiniteDimensional K V] (hρ : IsIsometric F ρ) {X : ℕ → Submodule K V}
    {m : ℕ} {E : ℕ → Submodule K V} (hE : IsSelfDual F E (2 * m + 1)) {g : H}
    (hiso : ∀ k ≤ m, X k = (E k).map (ρ g)) :
    isoCompletion F X m = GGOppRad.flagMap ρ g E := by
  funext k
  change isoCompletion F X m k = (E k).map (ρ g)
  by_cases hk1 : k ≤ m
  · rw [isoCompletion_of_le hk1]
    exact hiso k hk1
  by_cases hk2 : k ≤ 2 * m + 1
  · have h1 := isoCompletion_perp (F := F) (X := X) (m := m) (k := 2 * m + 1 - k) (by omega)
    rw [show 2 * m + 1 - (2 * m + 1 - k) = k by omega] at h1
    rw [h1, hiso _ (by omega), perp_map_of_isIsometric hρ, hE.perp _ (by omega),
      show 2 * m + 1 - (2 * m + 1 - k) = k by omega]
  · rw [isoCompletion_of_lt (by omega), hE.top k (by omega), Submodule.map_top,
      LinearMap.range_eq_top.mpr]
    intro v
    exact ⟨ρ g⁻¹ v, rep_apply_rep_inv ρ g v⟩

end General

variable {n : ℕ} {K : Type} [Field K]

@[expose] def lastSwap (hn : 1 ≤ n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  Equiv.swap (Sum.inl ⟨n - 1, by omega⟩) (Sum.inr ⟨n - 1, by omega⟩)

theorem IsSpLevel.comp_lastSwap {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    (hn : 1 ≤ n) : IsSpLevel M (ℓ ∘ lastSwap hn) := by
  intro i
  simp only [Function.comp_apply, lastSwap]
  by_cases hi : i = ⟨n - 1, by omega⟩
  · subst hi
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]
    exact hℓ _
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp [hi]) (by simp),
      Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hi])]
    exact hℓ i

@[expose] noncomputable def lastVec (hn : 1 ≤ n) : Fin n ⊕ Fin n → K :=
  Pi.single (Sum.inl ⟨n - 1, by omega⟩) 1 + Pi.single (Sum.inr ⟨n - 1, by omega⟩) 1

theorem quadPlus_lastVec (hn : 1 ≤ n) : quadPlus n K (lastVec hn) = 1 := by
  rw [quadPlus_apply, Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · simp [lastVec]
  · intro b _ hb
    simp [lastVec, hb]
  · simp

theorem polar_lastVec (hn : 1 ≤ n) (v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (lastVec hn) v =
      v (Sum.inr ⟨n - 1, by omega⟩) + v (Sum.inl ⟨n - 1, by omega⟩) := by
  rw [polar_quadPlus, Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · simp [lastVec]
  · intro b _ hb
    simp [lastVec, hb]
  · simp

theorem reflection_lastVec_apply [CharP K 2] (hn : 1 ≤ n)
    [Invertible (quadPlus n K (lastVec hn))] (v : Fin n ⊕ Fin n → K) (c : Fin n ⊕ Fin n) :
    TauCeti.QuadraticMap.reflection (quadPlus n K) (lastVec hn) v c = v (lastSwap hn c) := by
  have hinv : ⅟(quadPlus n K (lastVec hn)) = 1 := by
    rw [invOf_eq_inv, quadPlus_lastVec, inv_one]
  rw [TauCeti.QuadraticMap.reflection_apply, hinv, one_mul, polar_lastVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [lastVec, lastSwap, Pi.add_apply, Pi.single_apply]
  rcases c with c | c
  · by_cases hc : c = ⟨n - 1, by omega⟩
    · subst hc
      simp only [ite_true, Equiv.swap_apply_left]
      simp only [reduceCtorEq, ite_false, add_zero, mul_one]
      rw [add_comm, ← sub_sub, sub_self, zero_sub, CharTwo.neg_eq]
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [hc]) (by simp)]
      simp [hc]
  · by_cases hc : c = ⟨n - 1, by omega⟩
    · subst hc
      simp only [ite_true, Equiv.swap_apply_right]
      simp only [reduceCtorEq, ite_false, zero_add, mul_one]
      rw [← sub_sub, sub_self, zero_sub, CharTwo.neg_eq]
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hc])]
      simp [hc]

theorem map_stdFlag_comp_of_apply {f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : ∀ c, τ (τ c) = c) (hf : ∀ v c, f v c = v (τ c))
    (ℓ : Fin n ⊕ Fin n → ℕ) (k : ℕ) : (stdFlag (ℓ ∘ τ) k).map f = stdFlag (K := K) ℓ k := by
  refine le_antisymm ?_ fun w hw => ⟨fun c => w (τ c), fun a ha => ?_, funext fun c => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ c hc
    rw [hf]
    exact hv (τ c) (by simp only [Function.comp_apply, hτ]; exact hc)
  · exact hw (τ a) ha
  · rw [hf, hτ]

theorem exists_singFlag_eq_flagMap_plus [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (R : Subgroup (spinGroup (quadPlus n K))) :
    ∃ (h : spinGroup (quadPlus n K)) (ℓ : Fin n ⊕ Fin n → ℕ),
      IsSpLevel (2 * finrank K (Fin n ⊕ Fin n → K)) ℓ ∧
      singFlag (plusForm n K) (plusRep n K) R =
        GGOppRad.flagMap (plusRep n K) h (stdFlag ℓ) := by
  classical
  set Φ := plusForm n K with hΦ
  set ρ := plusRep n K with hρ
  set d := finrank K (Fin n ⊕ Fin n → K) with hd
  have hd2 : d = 2 * n := OrthogonalSplit.finrank_split
  set W := singSeq Φ ρ R with hW
  have hWmono : Monotone W := singSeq_mono Φ ρ R
  have hWle : ∀ j, W j ≤ W d := fun j => by
    rcases le_total j d with h | h
    · exact hWmono h
    · exact (singSeq_eq_of_le Φ ρ R h).le
  obtain ⟨X, hX0, hXmono, hXrank, hXtop, hXW⟩ :=
    exists_finrank_chain_forall_exists_eq hWmono hWle ⟨d, rfl⟩
  set m := finrank K (W d) with hm
  have hWds : Φ.IsTotallySingular (W d) := isTotallySingular_singSeq Φ ρ R d
  have hmn : m ≤ n := by
    have := hWds.two_mul_finrank_le
    omega
  have hXle : ∀ i, X i ≤ W d := fun i => by
    rcases le_total i m with h | h
    · rw [← hXtop m le_rfl]
      exact hXmono h
    · rw [hXtop i h]
  have hflag : (fun i : Fin m => X (i + 1)) ∈ OrthogonalSplit.singularFlags (quadPlus n K) m :=
    ⟨fun i => hXrank _ (by omega), fun i j hij => hXmono (by simpa using hij),
      fun i x hx => hWds x (hXle _ hx)⟩
  obtain ⟨g, hgO, hgX⟩ := OrthogonalSplit.exists_isometry_map_flag_eq hmn hflag
  have hgX' : ∀ i ≤ m, (OrthogonalSplit.flag n K i).map
      (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = X i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [OrthogonalSplit.flag_zero, Submodule.map_bot, hX0]
    · have := hgX ⟨i - 1, by omega⟩
      simp only [Nat.sub_add_cancel hpos] at this
      exact this
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
  have hex : ∀ t : Fin n, ∃ k, (t : ℕ) < D (k + 1) ∨ d ≤ k := fun _ => ⟨d, Or.inr le_rfl⟩
  set ℓ : Fin n ⊕ Fin n → ℕ := Sum.elim (fun t => Nat.find (hex t))
    (fun t => 2 * d - Nat.find (hex t)) with hℓ
  have hℓd : ∀ t, Nat.find (hex t) ≤ d := fun t => Nat.find_min' (hex t) (Or.inr le_rfl)
  have hℓsp : IsSpLevel (2 * d) ℓ := fun t => by
    simp only [hℓ, Sum.elim_inl, Sum.elim_inr]
    have := hℓd t
    omega
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
  have hinr : ∀ t k, k ≤ d → ¬ ℓ (Sum.inr t) < k := by
    intro t k hk
    simp only [hℓ, Sum.elim_inr]
    have := hℓd t
    omega
  have hstd : ∀ k ≤ d, stdFlag (K := K) ℓ k = OrthogonalSplit.flag n K (D k) := by
    intro k hk
    ext v
    rw [mem_stdFlag, OrthogonalSplit.mem_flag_iff_coord]
    constructor
    · intro hv
      exact ⟨fun t => hv _ (not_lt.mp (hinr t k hk)),
        fun t ht => hv _ (not_lt.mp fun h => by have := (hinl t k hk).mp h; omega)⟩
    · rintro ⟨h1, h2⟩ a ha
      rcases a with t | t
      · exact h2 t (not_lt.mp fun h => not_le.mpr ((hinl t k hk).mpr h) ha)
      · exact h1 t
  have hiso : ∀ k ≤ d, W k = (stdFlag ℓ k).map
      (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) := fun k hk => by
    rw [hWX k, hstd k hk, hgX' _ (hDm k)]
  have key : ∀ (h : spinGroup (quadPlus n K)) (ℓ' : Fin n ⊕ Fin n → ℕ), IsSpLevel (2 * d) ℓ' →
      (∀ k ≤ d, W k = (stdFlag ℓ' k).map (ρ h)) →
      singFlag Φ ρ R = GGOppRad.flagMap ρ h (stdFlag ℓ') := by
    intro h ℓ' hℓ' hk
    have hsd' : IsSelfDual Φ.polar (stdFlag ℓ') (2 * d + 1) := by
      have := isSelfDual_stdFlag (K := K) hℓ'
      rwa [← plusForm_polar] at this
    exact isoCompletion_eq_flagMap isIsometric_plusRep hsd' hk
  by_cases hgΩ : g ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
  · obtain ⟨h, hh⟩ := exists_spinAction_eq_of_mem_omegaGroup_plus hn hgΩ
    refine ⟨h, ℓ, hℓsp, key h ℓ hℓsp fun k hk => ?_⟩
    rw [hiso k hk]
    congr 1
    refine LinearMap.ext fun v => ?_
    rw [hρ, plusRep_apply, hh]
    rfl
  · have hn1 : 1 ≤ n := by omega
    let _ : Invertible (quadPlus n K (lastVec hn1)) :=
      invertibleOfNonzero (by rw [quadPlus_lastVec]; exact one_ne_zero)
    set r := TauCeti.QuadraticMap.reflection (quadPlus n K) (lastVec hn1) with hr
    have hrO := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (quadPlus n K) (lastVec hn1)
    have hr1 := finrank_commSpace_reflection (nondegenerate_polarBilin_quadPlus n K) (lastVec hn1)
    have hgr : g * r ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K) := by
      refine mem_omegaGroup.mpr ⟨mul_mem hgO hrO, ?_⟩
      have hodd : ¬ Even (finrank K (commSpace g)) := fun he =>
        hgΩ (mem_omegaGroup.mpr ⟨hgO, he⟩)
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul
        (nondegenerate_polarBilin_quadPlus n K) hgO hrO, hr1,
        (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp hodd), Nat.cast_one]
      rfl
    obtain ⟨h, hh⟩ := exists_spinAction_eq_of_mem_omegaGroup_plus hn hgr
    refine ⟨h, ℓ ∘ lastSwap hn1, IsSpLevel.comp_lastSwap hℓsp hn1,
      key h _ (IsSpLevel.comp_lastSwap hℓsp hn1) fun k hk => ?_⟩
    have hτ : ∀ c, lastSwap hn1 (lastSwap hn1 c) = c := fun c => Equiv.swap_apply_self _ _ c
    have hρh : ρ h = (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) ∘ₗ
        (r : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) := by
      refine LinearMap.ext fun v => ?_
      rw [hρ, plusRep_apply, hh]
      rfl
    rw [hiso k hk, hρh, Submodule.map_comp,
      map_stdFlag_comp_of_apply hτ (fun v c => reflection_lastVec_apply hn1 v c) ℓ k]

end GGOppRadOmega

end CFSG.StandardType
