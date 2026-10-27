module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs
public import CFSG.RankThree.LocalRank.ElementaryTwoWeights

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.RankThree.LocalRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l10b_even_of_sq_eq_neg_one {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    [FiniteDimensional (ZMod 3) M] (g : Module.End (ZMod 3) M) (hg : g * g = -1) :
    Even (Module.finrank (ZMod 3) M) := by
  have hsq : ∀ y : ZMod 3, y * y ≠ -1 := by decide
  have hneg : (-1 : Module.End (ZMod 3) M) = (-1 : ZMod 3) • (1 : Module.End (ZMod 3) M) := by
    simp
  have hdet : LinearMap.det g * LinearMap.det g = (-1) ^ Module.finrank (ZMod 3) M := by
    have h := congrArg LinearMap.det hg
    rw [Module.End.mul_eq_comp, LinearMap.det_comp, hneg, LinearMap.det_smul,
      Module.End.one_eq_id, LinearMap.det_id, mul_one] at h
    exact h
  rcases Nat.even_or_odd (Module.finrank (ZMod 3) M) with he | ho
  · exact he
  · exfalso
    have hodd : (-1 : ZMod 3) ^ Module.finrank (ZMod 3) M = -1 := ho.neg_one_pow
    rw [hodd] at hdet
    exact hsq _ hdet

theorem l10b_finrank_biSup {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : ι → Submodule K V} (hf : iSupIndep f) [DecidableEq ι]
    (s : Finset ι) :
    Module.finrank K ↥(⨆ i ∈ s, f i) = ∑ i ∈ s, Module.finrank K ↥(f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hd : Disjoint (f a) (⨆ i ∈ s, f i) := by
      have := hf.disjoint_biSup (x := a) (y := (s : Set ι)) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (f a) (⨆ i ∈ s, f i)
    rw [hd.eq_bot] at h
    simp only [finrank_bot, add_zero] at h
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    exact h

theorem l10b_card_dual {G : Type*} [CommGroup G] [Finite G] [Module (ZMod 2) (Additive G)]
    (hG : Nat.card G = 8) : Nat.card (Module.Dual (ZMod 2) (Additive G)) = 8 := by
  haveI : Module.Finite (ZMod 2) (Additive G) := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
  rw [Nat.card_zmod, Nat.card_congr Additive.toMul, hG] at h1
  have h3 : Module.finrank (ZMod 2) (Additive G) = 3 := by
    have h4 : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive G) = 2 ^ 3 := by
      rw [← h1]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) (Additive G))
  rw [Nat.card_zmod, Subspace.dual_finrank_eq, h3] at h2
  rw [h2]
  norm_num

theorem l10b_sq_surj {G : Type*} [CommGroup G] [Finite G] (hG : Nat.card G = 64)
    (hfour : ∀ g : G, g ^ 4 = 1) (hinv : Nat.card {g : G | g ^ 2 = 1} = 8) (s : G)
    (hs : s ^ 2 = 1) : ∃ a : G, a ^ 2 = s := by
  set K : Subgroup G := (powMonoidHom 2 : G →* G).ker with hKdef
  have hK : Nat.card K = 8 := by
    rw [← hinv]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [hKdef])
  have hidx : Nat.card K * K.index = Nat.card G := Subgroup.card_mul_index K
  have hrange : K.index = Nat.card (powMonoidHom 2 : G →* G).range :=
    Subgroup.index_ker (powMonoidHom 2 : G →* G)
  have hr : Nat.card (powMonoidHom 2 : G →* G).range = 8 := by
    rw [hrange, hK, hG] at hidx
    omega
  have hle : (powMonoidHom 2 : G →* G).range ≤ K := by
    rintro _ ⟨g, rfl⟩
    show (powMonoidHom 2 : G →* G) ((powMonoidHom 2 : G →* G) g) = 1
    simp only [powMonoidHom_apply]
    rw [← pow_mul]
    exact hfour g
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hK, hr])
  have hsK : s ∈ K := by
    show (powMonoidHom 2 : G →* G) s = 1
    simpa using hs
  rw [← heq] at hsK
  obtain ⟨a, ha⟩ := hsK
  exact ⟨a, by simpa using ha⟩

theorem l10b_orbit {D : Type*} [AddCommGroup D] [Module (ZMod 2) D] [Fintype D]
    (hcard : Fintype.card D = 8) (f : D →ₗ[ZMod 2] D) (hf7 : ∀ d, f^[7] d = d)
    (ψ : D) (hfix : f ψ ≠ ψ) (ξ : D) (hξ : ξ ≠ 0) : ∃ m, m < 7 ∧ f^[m] ψ = ξ := by
  classical
  have hper : Function.IsPeriodicPt f 7 ψ := hf7 ψ
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmin : Function.minimalPeriod f ψ = 7 :=
    Function.minimalPeriod_eq_prime hper (fun h => hfix h)
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    exact hfix (map_zero f)
  have hne : ∀ m, m < 7 → f^[m] ψ ≠ 0 := by
    intro m hm h0
    apply hψ0
    have h7 : f^[(7 - m) + m] ψ = ψ := by
      rw [Nat.sub_add_cancel hm.le]
      exact hf7 ψ
    rw [Function.iterate_add_apply, h0, Function.iterate_fixed (map_zero f)] at h7
    exact h7.symm
  have hinj : Set.InjOn (fun m => f^[m] ψ) (Set.Iio 7) := by
    have := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := ψ)
    rwa [hmin] at this
  set S : Finset D := (Finset.range 7).image (fun m => f^[m] ψ) with hS
  have hSc : S.card = 7 := by
    rw [hS, Finset.card_image_of_injOn]
    · exact Finset.card_range 7
    · rw [Finset.coe_range]
      exact hinj
  have hSsub : S ⊆ Finset.univ.erase 0 := by
    intro y hy
    rw [hS, Finset.mem_image] at hy
    obtain ⟨m, hm, rfl⟩ := hy
    exact Finset.mem_erase.mpr ⟨hne m (Finset.mem_range.mp hm), Finset.mem_univ _⟩
  have h1 : (Finset.univ.erase (0 : D)).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  have hEq : S = Finset.univ.erase 0 :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [h1, hSc])
  have hmem : ξ ∈ S := by
    rw [hEq]
    exact Finset.mem_erase.mpr ⟨hξ, Finset.mem_univ _⟩
  rw [hS, Finset.mem_image] at hmem
  obtain ⟨m, hm, hmξ⟩ := hmem
  exact ⟨m, Finset.mem_range.mp hm, hmξ⟩

@[expose] def l10bLin {T : Type*} [CommGroup T] [Module (ZMod 2) (Additive T)] (τ : T →* T) :
    Additive T →ₗ[ZMod 2] Additive T :=
  (MonoidHom.toAdditive τ).toZModLinearMap 2

theorem l10b_parity {A W : Type*} [CommGroup A] [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] (T : Subgroup A) [Module (ZMod 2) (Additive T)]
    (ρA : Representation (ZMod 3) A W) (χ : Module.Dual (ZMod 2) (Additive T)) (a : A)
    (s : T) (ha : a ^ 2 = (s : A)) (hχ : χ (Additive.ofMul s) = 1)
    (hV : signWeightSpace (ρA.comp T.subtype) χ ≠ ⊥) :
    2 ≤ Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) χ) := by
  have hinv : ∀ v ∈ signWeightSpace (ρA.comp T.subtype) χ,
      ρA a v ∈ signWeightSpace (ρA.comp T.subtype) χ := by
    intro v hv
    rw [mem_signWeightSpace] at hv ⊢
    intro t
    have hcomm : ρA (t : A) * ρA a = ρA a * ρA (t : A) := by
      rw [← map_mul, ← map_mul, mul_comm]
    have h1 : ρA (t : A) (ρA a v) = ρA a (ρA (t : A) v) := by
      have := LinearMap.congr_fun hcomm v
      simpa only [Module.End.mul_apply] using this
    have hvt : ρA (t : A) v = (-1 : ZMod 3) ^ ZMod.val (χ (Additive.ofMul t)) • v := hv t
    show ρA (t : A) (ρA a v) = (-1 : ZMod 3) ^ ZMod.val (χ (Additive.ofMul t)) • ρA a v
    rw [h1, hvt, map_smul]
  have hsq : ρA a * ρA a = ρA (s : A) := by
    rw [← map_mul, ← pow_two, ha]
  have hsv : ∀ v ∈ signWeightSpace (ρA.comp T.subtype) χ, ρA a (ρA a v) = -v := by
    intro v hv
    have h1 : ρA a (ρA a v) = ρA (s : A) v := by
      rw [← hsq, Module.End.mul_apply]
    have hvs : ρA (s : A) v = (-1 : ZMod 3) ^ ZMod.val (χ (Additive.ofMul s)) • v :=
      ((mem_signWeightSpace _ _ _).mp hv) s
    rw [h1, hvs, hχ, show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
    simp
  let g : Module.End (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) χ) :=
    (ρA a).restrict hinv
  have hg : g * g = -1 := by
    apply LinearMap.ext
    rintro ⟨v, hv⟩
    exact Subtype.ext (hsv v hv)
  have hev := l10b_even_of_sq_eq_neg_one g hg
  have hpos : 0 < Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) χ) := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h)⟩
  obtain ⟨k, hk⟩ := hev
  omega

theorem l10b_fin_dual {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] :
    Finite (Module.Dual (ZMod 2) M) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) M => (f : M → ZMod 2)) DFunLike.coe_injective

theorem l10b_shift {G W : Type*} [CommGroup G] [AddCommGroup W] [Module (ZMod 3) W]
    (T : Subgroup G) [Module (ZMod 2) (Additive T)] (ρA : Representation (ZMod 3) G W)
    (τT : T →* T) (X : Module.End (ZMod 3) W) (hX : ∀ t : T, ρA t * X = X * ρA (τT t))
    (χ : Module.Dual (ZMod 2) (Additive T)) (v : W)
    (hv : v ∈ signWeightSpace (ρA.comp T.subtype) χ) :
    X v ∈ signWeightSpace (ρA.comp T.subtype) (Module.Dual.transpose (l10bLin τT) χ) := by
  rw [mem_signWeightSpace] at hv ⊢
  intro t
  have h1 := LinearMap.congr_fun (hX t) v
  simp only [Module.End.mul_apply] at h1
  have h2 : ρA (τT t : G) v = (-1 : ZMod 3) ^ ZMod.val (χ (Additive.ofMul (τT t))) • v := hv (τT t)
  change ρA (t : G) (X v) = (-1 : ZMod 3) ^ ZMod.val (χ (Additive.ofMul (τT t))) • X v
  rw [h1, h2, map_smul]

theorem l10b_iter_apply {G : Type*} [CommGroup G] (T : Subgroup G) [Module (ZMod 2) (Additive T)]
    (τT : T →* T) (k : ℕ) :
    ∀ (χ : Module.Dual (ZMod 2) (Additive T)) (t : T),
      (⇑(Module.Dual.transpose (l10bLin τT)))^[k] χ (Additive.ofMul t) =
        χ (Additive.ofMul (τT^[k] t)) := by
  induction k with
  | zero => intro χ t; rfl
  | succ k ih =>
    intro χ t
    rw [Function.iterate_succ_apply']
    exact ih χ (τT t)

theorem l10b_f7 {G : Type*} [CommGroup G] (T : Subgroup G) [Module (ZMod 2) (Additive T)]
    (τT : T →* T) (hτ7 : ∀ t : T, τT^[7] t = t) (χ : Module.Dual (ZMod 2) (Additive T)) :
    (⇑(Module.Dual.transpose (l10bLin τT)))^[7] χ = χ := by
  apply LinearMap.ext
  intro y
  obtain ⟨t, rfl⟩ : ∃ t : T, Additive.ofMul t = y := ⟨Additive.toMul y, rfl⟩
  rw [l10b_iter_apply, hτ7]

theorem l10b_iter_mem {G W : Type*} [CommGroup G] [AddCommGroup W] [Module (ZMod 3) W]
    (T : Subgroup G) [Module (ZMod 2) (Additive T)] (ρA : Representation (ZMod 3) G W)
    (τT : T →* T) (X : Module.End (ZMod 3) W) (hX : ∀ t : T, ρA t * X = X * ρA (τT t))
    (k : ℕ) :
    ∀ (χ : Module.Dual (ZMod 2) (Additive T)) (v : W),
      v ∈ signWeightSpace (ρA.comp T.subtype) χ →
        (⇑X)^[k] v ∈ signWeightSpace (ρA.comp T.subtype)
          ((⇑(Module.Dual.transpose (l10bLin τT)))^[k] χ) := by
  induction k with
  | zero => intro χ v hv; exact hv
  | succ k ih =>
    intro χ v hv
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact l10b_shift T ρA τT X hX _ _ (ih χ v hv)

theorem l10b_nonfixed {G W : Type*} [CommGroup G] [Finite G] [AddCommGroup W]
    [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W] (T : Subgroup G)
    [Module (ZMod 2) (Additive T)] (ρA : Representation (ZMod 3) G W)
    (hinj : Function.Injective (ρA.comp T.subtype))
    (τT : T →* T) (hnofix : ∀ t : T, τT t = t → t = 1) (hTnt : ∃ t : T, t ≠ 1) :
    ∃ ψ : Module.Dual (ZMod 2) (Additive T), signWeightSpace (ρA.comp T.subtype) ψ ≠ ⊥ ∧
      Module.Dual.transpose (l10bLin τT) ψ ≠ ψ := by
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Finite (Module.Dual (ZMod 2) (Additive T)) := l10b_fin_dual
  haveI : Fintype (Module.Dual (ZMod 2) (Additive T)) := Fintype.ofFinite _
  have hK : (2 : ZMod 3) ≠ 0 := by decide
  have hspan := (injective_iff_span_signWeightSpace (ρA.comp T.subtype) hK).mp hinj
  by_contra hcon
  push Not at hcon
  have hfix : ∀ ψ : Module.Dual (ZMod 2) (Additive T),
      Module.Dual.transpose (l10bLin τT) ψ = ψ := by
    intro ψ
    have hψ : ψ ∈ Submodule.span (ZMod 2)
        {χ | signWeightSpace (ρA.comp T.subtype) χ ≠ ⊥} := by
      rw [hspan]
      exact Submodule.mem_top
    induction hψ using Submodule.span_induction with
    | mem χ hχ => exact hcon χ hχ
    | zero => exact map_zero _
    | add φ ψ' _ _ h1 h2 => rw [map_add, h1, h2]
    | smul c φ _ h1 => rw [map_smul, h1]
  have hτid : ∀ t : T, τT t = t := by
    intro t
    have h1 : ∀ φ : Module.Dual (ZMod 2) (Additive T),
        φ (Additive.ofMul (τT t)) = φ (Additive.ofMul t) := by
      intro φ
      have h := congrArg (fun ψ : Module.Dual (ZMod 2) (Additive T) => ψ (Additive.ofMul t))
        (hfix φ)
      exact h
    have h2 : Additive.ofMul (τT t) - Additive.ofMul t = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp ?_
      intro φ
      rw [map_sub, h1 φ, sub_self]
    have h3 : Additive.ofMul (τT t) = Additive.ofMul t := sub_eq_zero.mp h2
    exact Additive.ofMul.injective h3
  obtain ⟨t, ht⟩ := hTnt
  exact ht (hnofix t (hτid t))

theorem l10b_bound {G W : Type*} [CommGroup G] [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] (T : Subgroup G) [Module (ZMod 2) (Additive T)]
    [Fintype (Module.Dual (ZMod 2) (Additive T))] (ρA : Representation (ZMod 3) G W)
    (hiS : iSupIndep (signWeightSpace (ρA.comp T.subtype)))
    (hcard : Fintype.card (Module.Dual (ZMod 2) (Additive T)) = 8)
    (hΛ : ∀ ξ : Module.Dual (ZMod 2) (Additive T), ξ ≠ 0 →
      signWeightSpace (ρA.comp T.subtype) ξ ≠ ⊥)
    (hpar : ∀ ξ : Module.Dual (ZMod 2) (Additive T), ξ ≠ 0 →
      signWeightSpace (ρA.comp T.subtype) ξ ≠ ⊥ →
        2 ≤ Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) ξ))
    (t₀ : T) (ht₀ : t₀ ≠ 1) :
    6 ≤ Module.finrank (ZMod 3) ↥(LinearMap.ker (ρA (t₀ : G) - 1)) := by
  classical
  have hy : Additive.ofMul t₀ ≠ 0 := fun h => ht₀ (Additive.ofMul.injective h)
  obtain ⟨χ₀, hχ₀⟩ := exists_dual_apply_eq_one hy
  set P : Finset (Module.Dual (ZMod 2) (Additive T)) :=
    Finset.univ.filter (fun χ => χ (Additive.ofMul t₀) = 0) with hP
  have hPc : P.card = 4 := by
    have hQ : (Finset.univ.filter
        (fun χ : Module.Dual (ZMod 2) (Additive T) => ¬ (χ (Additive.ofMul t₀) = 0))).card
          = P.card := by
      apply Finset.card_nbij' (fun χ => dualTranslate χ₀ χ) (fun χ => dualTranslate χ₀ χ)
      ·
        intro χ hχ
        rw [Finset.mem_coe, Finset.mem_filter] at hχ
        rw [Finset.mem_coe, hP, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 : χ (Additive.ofMul t₀) = 1 := dual_apply_eq_one hχ.2
        show χ₀ (Additive.ofMul t₀) + χ (Additive.ofMul t₀) = 0
        rw [h1, hχ₀]
        decide
      ·
        intro χ hχ
        rw [Finset.mem_coe, hP, Finset.mem_filter] at hχ
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show ¬ (χ₀ (Additive.ofMul t₀) + χ (Additive.ofMul t₀) = 0)
        rw [hχ.2, hχ₀]
        decide
      · intro χ _
        exact (dualTranslate χ₀).left_inv χ
      · intro χ _
        exact (dualTranslate χ₀).right_inv χ
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ :
      Finset (Module.Dual (ZMod 2) (Additive T)))) (fun χ => χ (Additive.ofMul t₀) = 0)
    beta_reduce at hsum
    rw [Finset.card_univ, hcard, ← hP] at hsum
    omega
  have hzero : (0 : Module.Dual (ZMod 2) (Additive T)) ∈ P := by
    rw [hP, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hcard3 : (P.erase 0).card = 3 := by
    rw [Finset.card_erase_of_mem hzero, hPc]
  have hsum_le : 6 ≤ ∑ χ ∈ P.erase 0,
      Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) χ) := by
    have h1 : ∑ _χ ∈ P.erase 0, (2 : ℕ) ≤ ∑ χ ∈ P.erase 0,
        Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) χ) := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact hpar χ (Finset.ne_of_mem_erase hχ) (hΛ χ (Finset.ne_of_mem_erase hχ))
    rw [Finset.sum_const, hcard3, smul_eq_mul] at h1
    omega
  have hle : (⨆ χ ∈ P, signWeightSpace (ρA.comp T.subtype) χ) ≤
      LinearMap.ker (ρA (t₀ : G) - 1) := by
    refine iSup₂_le fun χ hχ => ?_
    intro v hv
    have hχ0 : χ (Additive.ofMul t₀) = 0 := by
      rw [hP, Finset.mem_filter] at hχ
      exact hχ.2
    have hvt : ρA (t₀ : G) v = (-1 : ZMod 3) ^ ZMod.val (χ (Additive.ofMul t₀)) • v :=
      (mem_signWeightSpace _ _ _).mp hv t₀
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hvt, hχ0,
      ZMod.val_zero, pow_zero, one_smul]
  have hfin := Submodule.finrank_mono hle
  rw [l10b_finrank_biSup hiS P] at hfin
  have hsplit := Finset.add_sum_erase P
    (fun χ => Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) χ)) hzero
  omega

theorem L10b_lin {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
    {B : Type*} [Group B] [Finite B] (A : Subgroup B) (x : B) (hAx : FourCubeSeven A x)
    (ρ : Representation (ZMod 3) B W) (hfaith : ∀ a ∈ A, a ^ 2 = 1 → a ≠ 1 → ρ a ≠ 1) :
    ∃ a ∈ A, a ^ 2 = 1 ∧ a ≠ 1 ∧ 6 ≤ Module.finrank (ZMod 3) (LinearMap.ker (ρ a - 1)) := by
  classical
  obtain ⟨hcomm, hcardA, hfour, hinv, hx7, hxn, hfixx⟩ := hAx
  have hx7' : x ^ 7 = 1 := by
    rw [← hx7]
    exact pow_orderOf_eq_one x
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }
  set T : Subgroup A := (powMonoidHom 2 : A →* A).ker with hTdef
  have hmemT : ∀ a : A, a ∈ T ↔ a ^ 2 = 1 := by
    intro a
    rw [hTdef, MonoidHom.mem_ker, powMonoidHom_apply]
  have hA64 : Nat.card A = 64 := hcardA.trans (by norm_num)
  have hfourA : ∀ a : A, a ^ 4 = 1 := fun a => Subtype.ext (by simpa using hfour a.1 a.2)
  have hinvA : Nat.card {g : A | g ^ 2 = 1} = 8 := hinv.trans (by norm_num)
  have hTcard : Nat.card T = 8 := by
    rw [← hinvA]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => hmemT g)
  have hTnt : ∃ t : T, t ≠ 1 := by
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
    exact exists_ne 1
  have h2T : ∀ y : Additive T, (2 : ℕ) • y = 0 := by
    intro y
    obtain ⟨t, rfl⟩ : ∃ t : T, Additive.ofMul t = y := ⟨Additive.toMul y, rfl⟩
    have ht : t ^ 2 = 1 := Subtype.ext (by simpa using (hmemT (t : A)).mp t.2)
    show Additive.ofMul (t ^ 2) = Additive.ofMul 1
    rw [ht]
  letI : Module (ZMod 2) (Additive T) := AddCommGroup.zmodModule h2T
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Finite (Module.Dual (ZMod 2) (Additive T)) := l10b_fin_dual
  haveI : Fintype (Module.Dual (ZMod 2) (Additive T)) := Fintype.ofFinite _
  have hDcard : Fintype.card (Module.Dual (ZMod 2) (Additive T)) = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact l10b_card_dual hTcard
  have hK : (2 : ZMod 3) ≠ 0 := by decide
  set ρA : Representation (ZMod 3) A W := ρ.comp A.subtype with hρA
  have hinj : Function.Injective (ρA.comp T.subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    by_contra hne
    have hb : ((t : A) : B) ≠ 1 := fun h => hne (Subtype.ext (Subtype.ext h))
    have hsq : ((t : A) : B) ^ 2 = 1 := by
      have h := congrArg Subtype.val ((hmemT (t : A)).mp t.2)
      simpa using h
    exact hfaith _ (t : A).2 hsq hb ht
  have hiS := iSupIndep_signWeightSpace (ρA.comp T.subtype) hK
  have hτA : ∀ a : A, x⁻¹ * (a : B) * x ∈ A := fun a =>
    ((mem_set_normalizer_iff''.mp hxn) (a : B)).mp a.2
  let τA : A →* A :=
    { toFun := fun a => ⟨x⁻¹ * (a : B) * x, hτA a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hτT : ∀ t : T, τA (t : A) ∈ T := fun t => by
    rw [hmemT, ← map_pow, (hmemT _).mp t.2, map_one]
  let τT : T →* T :=
    { toFun := fun t => ⟨τA (t : A), hτT t⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hX : ∀ t : T, ρA (t : A) * ρ x = ρ x * ρA ((τT t : T) : A) := by
    intro t
    show ρ ((t : A) : B) * ρ x = ρ x * ρ (x⁻¹ * ((t : A) : B) * x)
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hτk : ∀ (k : ℕ) (t : T),
      (((τT^[k] t : T) : A) : B) = (x ^ k)⁻¹ * ((t : A) : B) * x ^ k := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [Function.iterate_succ_apply']
      show x⁻¹ * ((((τT^[k] t : T) : A) : B)) * x = _
      rw [ih t, pow_succ, mul_inv_rev]
      simp only [mul_assoc]
  have hτ7 : ∀ t : T, τT^[7] t = t := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    rw [hτk 7 t, hx7']
    simp
  have hnofix : ∀ t : T, τT t = t → t = 1 := by
    intro t ht
    have h1 : x⁻¹ * ((t : A) : B) * x = ((t : A) : B) :=
      congrArg (fun s : T => ((s : A) : B)) ht
    have h1' : ((t : A) : B) * x = x * ((t : A) : B) := by
      calc ((t : A) : B) * x = x * (x⁻¹ * ((t : A) : B) * x) := by group
        _ = x * ((t : A) : B) := by rw [h1]
    have h2 : x * ((t : A) : B) * x⁻¹ = ((t : A) : B) := by
      rw [← h1']
      group
    have hsq : ((t : A) : B) ^ 2 = 1 := by
      have h := congrArg Subtype.val ((hmemT (t : A)).mp t.2)
      simpa using h
    have h3 : ((t : A) : B) = 1 := hfixx _ (t : A).2 hsq h2
    exact Subtype.ext (Subtype.ext h3)
  obtain ⟨ψ, hψV, hψfix⟩ := l10b_nonfixed T ρA hinj τT hnofix hTnt
  have hf7 : ∀ d : Module.Dual (ZMod 2) (Additive T),
      (⇑(Module.Dual.transpose (l10bLin τT)))^[7] d = d :=
    fun d => l10b_f7 T τT hτ7 d
  have hXinj : Function.Injective (⇑(ρ x)) := by
    intro a b hab
    have h := congrArg (⇑(ρ x⁻¹)) hab
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h
  have hΛ : ∀ ξ : Module.Dual (ZMod 2) (Additive T), ξ ≠ 0 →
      signWeightSpace (ρA.comp T.subtype) ξ ≠ ⊥ := by
    intro ξ hξ
    obtain ⟨m, -, rfl⟩ :=
      l10b_orbit hDcard (Module.Dual.transpose (l10bLin τT)) hf7 ψ hψfix ξ hξ
    intro hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hψV
    have hmem := l10b_iter_mem T ρA τT (ρ x) hX m ψ v hv
    rw [hbot, Submodule.mem_bot] at hmem
    apply hv0
    apply Function.Injective.iterate hXinj m
    rw [hmem, Function.iterate_fixed (map_zero (ρ x))]
  have hpar : ∀ ξ : Module.Dual (ZMod 2) (Additive T), ξ ≠ 0 →
      signWeightSpace (ρA.comp T.subtype) ξ ≠ ⊥ →
        2 ≤ Module.finrank (ZMod 3) ↥(signWeightSpace (ρA.comp T.subtype) ξ) := by
    intro ξ hξ hV
    obtain ⟨y, hy⟩ : ∃ y : Additive T, ξ y ≠ 0 := by
      by_contra h
      push Not at h
      exact hξ (LinearMap.ext h)
    have hy1 : ξ y = 1 := dual_apply_eq_one hy
    have hs2 : ((Additive.toMul y : T) : A) ^ 2 = 1 := (hmemT _).mp (Additive.toMul y).2
    obtain ⟨a, ha⟩ := l10b_sq_surj hA64 hfourA hinvA ((Additive.toMul y : T) : A) hs2
    exact l10b_parity T ρA ξ a (Additive.toMul y) ha hy1 hV
  obtain ⟨t₀, ht₀⟩ := hTnt
  have hbound := l10b_bound T ρA hiS hDcard hΛ hpar t₀ ht₀
  refine ⟨((t₀ : A) : B), (t₀ : A).2, ?_, ?_, hbound⟩
  · have h := congrArg Subtype.val ((hmemT (t₀ : A)).mp t₀.2)
    simpa using h
  · intro h
    apply ht₀
    exact Subtype.ext (Subtype.ext h)

end CFSG.RankThree.PartTwo.Sec13.F135Last
