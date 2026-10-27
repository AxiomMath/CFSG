module

public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

namespace B69

open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H
open scoped Matrix

section Lin

variable {K : Type} [Field K]

@[expose] def ffLinOf (x : MulAut (StdMod (Fin 2) K)) (hx : IsSemilinear x (RingEquiv.refl K)) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun := toAddMap x
  map_add' := toAddMap_add x
  map_smul' := fun c v => hx c v

theorem finrank_range_le_one_of_sq_eq_zero_two {N : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (hN : N ∘ₗ N = 0) : Module.finrank K (LinearMap.range N) ≤ 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker N
  have h2 : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun hN v
  have h3 := Submodule.finrank_mono h2
  have h4 : Module.finrank K (Fin 2 → K) = 2 := Module.finrank_fin_fun K
  omega

theorem comp_eq_zero_of_sq_eq_zero_two {M N : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (hM : M ∘ₗ M = 0) (hN : N ∘ₗ N = 0) (hMN : M ∘ₗ N = N ∘ₗ M) : M ∘ₗ N = 0 := by
  have hr := finrank_range_le_one_of_sq_eq_zero_two hN
  refine LinearMap.ext fun v => ?_
  have hmem : N v ∈ LinearMap.range N := ⟨v, rfl⟩
  have hMmem : M (N v) ∈ LinearMap.range N := by
    have : M (N v) = N (M v) := LinearMap.congr_fun hMN v
    rw [this]
    exact ⟨M v, rfl⟩
  by_cases hNv : N v = 0
  · simp only [LinearMap.comp_apply, hNv, map_zero, LinearMap.zero_apply]
  · have hline : ∃ c : K, M (N v) = c • N v := by
      have hspan : LinearMap.range N = Submodule.span K {N v} := by
        apply (Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (by simp [hmem]))
          ?_).symm
        rw [finrank_span_singleton hNv]
        exact hr
      rw [hspan] at hMmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hMmem
      exact ⟨c, hc.symm⟩
    obtain ⟨c, hc⟩ := hline
    have h2 : M (M (N v)) = c ^ 2 • N v := by
      rw [hc, map_smul, hc, smul_smul, sq]
    have h3 : M (M (N v)) = 0 := LinearMap.congr_fun hM (N v)
    rw [h3] at h2
    have hc0 : c ^ 2 = 0 := by
      by_contra hc0
      exact hNv (by
        have := h2.symm
        rwa [smul_eq_zero, or_iff_right hc0] at this)
    have : c = 0 := pow_eq_zero_iff (by norm_num) |>.mp hc0
    simp only [LinearMap.comp_apply, hc, this, zero_smul, LinearMap.zero_apply]

@[expose] noncomputable def nLin (x : MulAut (StdMod (Fin 2) K))
    (hx : IsSemilinear x (RingEquiv.refl K)) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  ffLinOf x hx - LinearMap.id

theorem nLin_apply (x : MulAut (StdMod (Fin 2) K)) (hx : IsSemilinear x (RingEquiv.refl K))
    (v : Fin 2 → K) : nLin x hx v = toAddMap x v - v := rfl

end Lin

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem ffVec_add_self (v : Fin 2 → K) : v + v = 0 :=
  funext fun _ => CharTwo.add_self_eq_zero _

theorem bounds_of_commuting {σ : K ≃+* K}
    {g e₀ : MulAut (StdMod (Fin 2) K)} (hg : IsSemilinear g σ)
    (he₀1 : e₀ ≠ 1)
    {E₀ : Subgroup (MulAut (StdMod (Fin 2) K))} (he₀E : e₀ ∈ E₀)
    (hlin : ∀ e ∈ E₀, IsSemilinear e (RingEquiv.refl K)) (hsq : ∀ e ∈ E₀, e * e = 1)
    (hcomm : ∀ e ∈ E₀, ∀ e' ∈ E₀, e * e' = e' * e) (hgE : ∀ e ∈ E₀, g * e = e * g) :
    Nat.card E₀ ≤ Nat.card {s : K // σ s = s} ∧
      Nat.card ↥(fixV (Subgroup.zpowers e₀) ⊓ fixV (Subgroup.zpowers g)) ≤
        Nat.card {s : K // σ s = s} := by
  classical
  have hsub : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : IsSemilinear e (RingEquiv.refl K))
      (a b : Fin 2 → K), toAddMap e (a - b) = toAddMap e a - toAddMap e b :=
    fun e he a b => map_sub (ffLinOf e he) a b
  have hNsq : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : e ∈ E₀),
      nLin e (hlin e he) ∘ₗ nLin e (hlin e he) = 0 := by
    intro e he
    refine LinearMap.ext fun v => ?_
    have h1 : toAddMap e (toAddMap e v) = v :=
      congrArg (fun x : MulAut (StdMod (Fin 2) K) => toAddMap x v) (hsq e he)
    simp only [LinearMap.comp_apply, nLin_apply, hsub e (hlin e he), h1, LinearMap.zero_apply]
    calc v - toAddMap e v - (toAddMap e v - v) = (v + v) - (toAddMap e v + toAddMap e v) := by abel
      _ = 0 := by rw [ffVec_add_self v, ffVec_add_self, sub_zero]
  have hNcomm : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : e ∈ E₀) (e' : MulAut (StdMod (Fin 2) K))
      (he' : e' ∈ E₀), nLin e (hlin e he) ∘ₗ nLin e' (hlin e' he') =
        nLin e' (hlin e' he') ∘ₗ nLin e (hlin e he) := by
    intro e he e' he'
    refine LinearMap.ext fun v => ?_
    have h1 : toAddMap e (toAddMap e' v) = toAddMap e' (toAddMap e v) :=
      congrArg (fun x : MulAut (StdMod (Fin 2) K) => toAddMap x v) (hcomm e he e' he')
    simp only [LinearMap.comp_apply, nLin_apply, hsub e (hlin e he), hsub e' (hlin e' he'), h1]
    abel
  have hNN : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : e ∈ E₀) (e' : MulAut (StdMod (Fin 2) K))
      (he' : e' ∈ E₀), nLin e (hlin e he) ∘ₗ nLin e' (hlin e' he') = 0 :=
    fun e he e' he' => comp_eq_zero_of_sq_eq_zero_two (hNsq e he) (hNsq e' he') (hNcomm e he e' he')
  obtain ⟨v₁, hv₁⟩ : ∃ v : Fin 2 → K, nLin e₀ (hlin e₀ he₀E) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply he₀1
    refine toAddMap_injective fun v => ?_
    have := hcon v
    rw [nLin_apply, sub_eq_zero] at this
    exact this
  obtain ⟨v₂, hv₂def⟩ : ∃ v₂ : Fin 2 → K, v₂ = nLin e₀ (hlin e₀ he₀E) v₁ := ⟨_, rfl⟩
  have hv₂ : v₂ ≠ 0 := by rw [hv₂def]; exact hv₁
  have hN₀v₂ : nLin e₀ (hlin e₀ he₀E) v₂ = 0 := by
    rw [hv₂def]
    exact LinearMap.congr_fun (hNsq e₀ he₀E) v₁
  have hrange : LinearMap.range (nLin e₀ (hlin e₀ he₀E)) = Submodule.span K {v₂} := by
    apply (Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (by
      rintro _ rfl
      exact ⟨v₁, hv₂def.symm⟩)) ?_).symm
    rw [finrank_span_singleton hv₂]
    exact finrank_range_le_one_of_sq_eq_zero_two (hNsq e₀ he₀E)
  have hker : LinearMap.ker (nLin e₀ (hlin e₀ he₀E)) = LinearMap.range (nLin e₀ (hlin e₀ he₀E)) := by
    have hle : LinearMap.range (nLin e₀ (hlin e₀ he₀E)) ≤ LinearMap.ker (nLin e₀ (hlin e₀ he₀E)) := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      exact LinearMap.congr_fun (hNsq e₀ he₀E) v
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker (nLin e₀ (hlin e₀ he₀E))
    have h2 : Module.finrank K (Fin 2 → K) = 2 := Module.finrank_fin_fun K
    have h3 : Module.finrank K (LinearMap.range (nLin e₀ (hlin e₀ he₀E))) = 1 := by
      rw [hrange, finrank_span_singleton hv₂]
    omega
  have hli : LinearIndependent K ![v₁, v₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : nLin e₀ (hlin e₀ he₀E) (s • v₁ + t • v₂) = 0 := by rw [hst, map_zero]
    rw [map_add, map_smul, map_smul, hN₀v₂, smul_zero, add_zero, ← hv₂def] at h1
    have hs : s = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hv₂
    refine ⟨hs, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    rcases smul_eq_zero.1 hst with h | h
    · exact h
    · exact absurd h hv₂
  have hspan : Submodule.span K (Set.range ![v₁, v₂]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hdec : ∀ x : Fin 2 → K, ∃ a t : K, x = a • v₁ + t • v₂ := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range ![v₁, v₂]) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    exact ⟨c 0, c 1, by rw [← hc, Fin.sum_univ_two]; simp⟩
  have hrange_ker : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : e ∈ E₀) (v : Fin 2 → K),
      nLin e (hlin e he) v ∈ Submodule.span K {v₂} := by
    intro e he v
    rw [← hrange, ← hker, LinearMap.mem_ker]
    exact LinearMap.congr_fun (hNN e₀ he₀E e he) v
  have hNe_v2 : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : e ∈ E₀),
      nLin e (hlin e he) v₂ = 0 := by
    intro e he
    rw [hv₂def]
    exact LinearMap.congr_fun (hNN e he e₀ he₀E) v₁
  have hβ : ∀ e : E₀, ∃ β : K, nLin e.1 (hlin e.1 e.2) v₁ = β • v₂ := fun e =>
    (Submodule.mem_span_singleton.1 (hrange_ker e.1 e.2 v₁)).imp fun β h => h.symm
  choose β hβ using hβ
  have hβinj : Function.Injective β := by
    intro e e' hee'
    apply Subtype.ext
    refine toAddMap_injective fun v => ?_
    obtain ⟨a, t, rfl⟩ := hdec v
    have h1 : nLin e.1 (hlin e.1 e.2) (a • v₁ + t • v₂) =
        nLin e'.1 (hlin e'.1 e'.2) (a • v₁ + t • v₂) := by
      simp only [map_add, map_smul, hNe_v2 e.1 e.2, hNe_v2 e'.1 e'.2, hβ e, hβ e', hee']
    rw [nLin_apply, nLin_apply] at h1
    exact sub_left_injective h1
  have hgadd : ∀ a b : Fin 2 → K, toAddMap g (a - b) = toAddMap g a - toAddMap g b := by
    intro a b
    have h := toAddMap_add g (a - b) b
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hgN : ∀ (e : MulAut (StdMod (Fin 2) K)) (he : e ∈ E₀) (v : Fin 2 → K),
      toAddMap g (nLin e (hlin e he) v) = nLin e (hlin e he) (toAddMap g v) := by
    intro e he v
    have h1 : toAddMap g (toAddMap e v) = toAddMap e (toAddMap g v) :=
      congrArg (fun x : MulAut (StdMod (Fin 2) K) => toAddMap x v) (hgE e he)
    rw [nLin_apply, nLin_apply, hgadd, h1]
  obtain ⟨c, hc⟩ : ∃ c : K, toAddMap g v₂ = c • v₂ := by
    have h1 : toAddMap g v₂ = nLin e₀ (hlin e₀ he₀E) (toAddMap g v₁) := by
      rw [hv₂def]
      exact hgN e₀ he₀E v₁
    have hm : toAddMap g v₂ ∈ Submodule.span K {v₂} := by
      rw [h1, ← hrange]
      exact ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    exact ⟨c, hc.symm⟩
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hv₂ ((toAddMap_eq_zero_iff g).1 hc)
  obtain ⟨a, t, hat⟩ := hdec (toAddMap g v₁)
  have hrel : ∀ e : E₀, σ (β e) * c = a * β e := by
    intro e
    have h1 := hgN e.1 e.2 v₁
    rw [hβ e, hg, hc, hat] at h1
    simp only [map_add, map_smul, hNe_v2 e.1 e.2, hβ e, smul_zero, add_zero, smul_smul] at h1
    exact smul_left_injective K hv₂ h1
  have hβ₀ : β ⟨e₀, he₀E⟩ = 1 := by
    have h1 := hβ ⟨e₀, he₀E⟩
    have h2 : v₂ = β ⟨e₀, he₀E⟩ • v₂ := by rw [← h1]; exact hv₂def
    have h3 : (1 : K) • v₂ = β ⟨e₀, he₀E⟩ • v₂ := by rw [one_smul]; exact h2
    exact (smul_left_injective K hv₂ h3).symm
  have hac : c = a := by
    have := hrel ⟨e₀, he₀E⟩
    rw [hβ₀, map_one, one_mul, mul_one] at this
    exact this
  have hσβ : ∀ e : E₀, σ (β e) = β e := by
    intro e
    have := hrel e
    rw [← hac, mul_comm c] at this
    exact mul_right_cancel₀ hc0 (by rw [this, mul_comm])
  refine ⟨?_, ?_⟩
  · exact Nat.card_le_card_of_injective (fun e : E₀ => (⟨β e, hσβ e⟩ : {s : K // σ s = s}))
      (fun e e' h => hβinj (congrArg Subtype.val h))
  · classical
    set F := fixV (Subgroup.zpowers e₀) ⊓ fixV (Subgroup.zpowers g) with hF
    have hFx : ∀ x : ↥F, ∃ s : K, Multiplicative.toAdd (x : StdMod (Fin 2) K) = s • v₂ ∧
        σ s * c = s := by
      intro x
      have h1 : e₀ (x : StdMod (Fin 2) K) = x := mem_fixV_zpowers_iff.1 x.2.1
      have h2 : g (x : StdMod (Fin 2) K) = x := mem_fixV_zpowers_iff.1 x.2.2
      have h1' : toAddMap e₀ (Multiplicative.toAdd (x : StdMod (Fin 2) K)) =
          Multiplicative.toAdd (x : StdMod (Fin 2) K) := by
        unfold toAddMap
        rw [ofAdd_toAdd, h1]
      have h2' : toAddMap g (Multiplicative.toAdd (x : StdMod (Fin 2) K)) =
          Multiplicative.toAdd (x : StdMod (Fin 2) K) := by
        unfold toAddMap
        rw [ofAdd_toAdd, h2]
      have hmem : Multiplicative.toAdd (x : StdMod (Fin 2) K) ∈
          LinearMap.ker (nLin e₀ (hlin e₀ he₀E)) := by
        rw [LinearMap.mem_ker, nLin_apply, h1', sub_self]
      rw [hker, hrange] at hmem
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨s, hs.symm, ?_⟩
      have h3 : toAddMap g (s • v₂) = s • v₂ := by rw [hs]; exact h2'
      rw [hg, hc, smul_smul] at h3
      exact smul_left_injective K hv₂ h3
    choose sf hsf₁ hsf₂ using hFx
    have hsfinj : Function.Injective sf := by
      intro x y hxy
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [hsf₁ x, hsf₁ y, hxy]
    by_cases hex : ∃ x : ↥F, sf x ≠ 0
    · obtain ⟨x₀, hx₀⟩ := hex
      have hKσ : ∀ x : ↥F, σ (sf x / sf x₀) = sf x / sf x₀ := by
        intro x
        have h1 : σ (sf x) = sf x / c := by
          rw [eq_div_iff hc0]
          exact hsf₂ x
        have h2 : σ (sf x₀) = sf x₀ / c := by
          rw [eq_div_iff hc0]
          exact hsf₂ x₀
        rw [map_div₀, h1, h2]
        field_simp
      exact Nat.card_le_card_of_injective
        (fun x : ↥F => (⟨sf x / sf x₀, hKσ x⟩ : {s : K // σ s = s}))
        (fun x y h => hsfinj ((div_left_inj' hx₀).1 (congrArg Subtype.val h)))
    · push Not at hex
      have hsub1 : Subsingleton ↥F := by
        refine ⟨fun x y => ?_⟩
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        rw [hsf₁ x, hsf₁ y, hex x, hex y]
      have h1 : Nat.card ↥F ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub1
      have h2 : 0 < Nat.card {s : K // σ s = s} :=
        Nat.card_pos_iff.2 ⟨⟨⟨0, map_zero σ⟩⟩, inferInstance⟩
      omega

omit [CharP K 2] in
theorem ffCard_fix_sq_le {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) :
    Nat.card {s : K // σ s = s} ^ 2 ≤ Nat.card K := by
  obtain ⟨u, hu⟩ : ∃ u : K, σ u ≠ u := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have hinj : Function.Injective
      (fun p : {s : K // σ s = s} × {s : K // σ s = s} => p.1.1 + p.2.1 * u) := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    simp only at h
    have h2 := congrArg σ h
    rw [map_add, map_add, map_mul, map_mul, hs, hs', ht, ht'] at h2
    have h3 : (t - t') * (σ u - u) = 0 := by linear_combination h2 - h
    have h4 : t = t' := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hu))
    have h5 : s = s' := by
      rw [h4] at h
      exact add_right_cancel h
    subst h4
    subst h5
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, ← sq] at this

omit [CharP K 2] in
theorem ffOne_lt_card_fix (σ : K ≃+* K) : 1 < Nat.card {s : K // σ s = s} := by
  have : Nontrivial {s : K // σ s = s} :=
    ⟨⟨⟨0, map_zero σ⟩, ⟨1, map_one σ⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.2 inferInstance

theorem card_mul_card_fixV_lt_of_nonlinear {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (StdMod (Fin 2) K))} (hEN : E ≤ natNorm (StatedSL 2 K))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hnl : ¬ E ≤ linSub) :
    Nat.card E * Nat.card ↥(fixV E) < Nat.card K ^ 2 := by
  classical
  have hΓ : HasScalarCommutant (StatedSL 2 K) := hasScalarCommutant_statedSL (by norm_num)
  obtain ⟨g, hgE, hgl⟩ : ∃ g ∈ E, g ∉ linSub := by
    by_contra h
    push Not at h
    exact hnl fun x hx => h x hx
  let gN : ↥(natNorm (StatedSL 2 K)) := ⟨g, hEN hgE⟩
  set σ : K ≃+* K := fieldAut hΓ gN with hσdef
  have hgσ : IsSemilinear g σ := isSemilinear_fieldAut hΓ gN
  have hσ : σ ≠ RingEquiv.refl K := by
    intro h
    apply hgl
    exact (fieldHom_eq_one_iff hΓ gN).1 h
  have hq2 : 1 < Nat.card {s : K // σ s = s} := ffOne_lt_card_fix σ
  have hsq := ffCard_fix_sq_le hσ
  have h4 : 4 ≤ Nat.card K := le_trans (by nlinarith) hsq
  have hE₀ := card_le_two_mul_card_inf_linSub hΓ hn hK hEN hE2
  by_cases hbot : E ⊓ linSub = ⊥
  · have h1 : Nat.card E ≤ 2 := by
      have := hE₀
      rw [hbot, Subgroup.card_bot] at this
      omega
    have hg2 : g ^ 2 = 1 := hE2 g hgE
    have hσ2 : σ ^ 2 = 1 := by
      have h1 : IsSemilinear (g ^ 2) (σ.trans σ) := by
        rw [pow_two]
        exact hgσ.mul hgσ
      rw [hg2] at h1
      have := h1.unique isSemilinear_one
      ext c
      exact congrArg (fun τ : K ≃+* K => τ c) this
    have hord : orderOf σ = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσ2) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hσ
      · exact h
    have hcard := (card_fixV_of_semilinear hn hK hgσ hord hg2).2
    have hfix : Nat.card ↥(fixV E) ≤ Nat.card K := by
      have hle : fixV E ≤ fixV (Subgroup.zpowers g) := fun v hv x hx =>
        hv x (Subgroup.zpowers_le.2 hgE hx)
      calc Nat.card ↥(fixV E) ≤ Nat.card ↥(fixV (Subgroup.zpowers g)) := Subgroup.card_le_of_le hle
        _ = Nat.card K := by
          rw [hcard, hK]
          congr 1
          rw [Fintype.card_fin]
          omega
    calc Nat.card E * Nat.card ↥(fixV E) ≤ 2 * Nat.card K := Nat.mul_le_mul h1 hfix
      _ < Nat.card K ^ 2 := by nlinarith
  · obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have he₀ : (a : MulAut (StdMod (Fin 2) K)) ∈ E ⊓ linSub := a.2
    have he₀1 : (a : MulAut (StdMod (Fin 2) K)) ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨hb1, hb2⟩ := bounds_of_commuting (σ := σ) hgσ he₀1 (E₀ := E ⊓ linSub) he₀
      (fun e he => mem_linSub.1 he.2)
      (fun e he => by rw [← pow_two]; exact hE2 e he.1)
      (fun e he e' he' => hEc e he.1 e' he'.1) (fun e he => hEc g hgE e he.1)
    have hfix : Nat.card ↥(fixV E) ≤ Nat.card {s : K // σ s = s} := by
      refine le_trans (Subgroup.card_le_of_le ?_) hb2
      exact le_inf (fun v hv x hx => hv x (Subgroup.zpowers_le.2 he₀.1 hx))
        (fun v hv x hx => hv x (Subgroup.zpowers_le.2 hgE hx))
    calc Nat.card E * Nat.card ↥(fixV E)
        ≤ (2 * Nat.card ↥(E ⊓ linSub)) * Nat.card {s : K // σ s = s} :=
          Nat.mul_le_mul hE₀ hfix
      _ ≤ (2 * Nat.card {s : K // σ s = s}) * Nat.card {s : K // σ s = s} :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hb1) le_rfl
      _ = 2 * Nat.card {s : K // σ s = s} ^ 2 := by ring
      _ ≤ 2 * Nat.card K := Nat.mul_le_mul_left 2 hsq
      _ < Nat.card K ^ 2 := by nlinarith

theorem le_natImage_of_offender {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (StdMod (Fin 2) K))} (hEN : E ≤ natNorm (StatedSL 2 K))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hoff : Nat.card (StdMod (Fin 2) K) ≤ Nat.card E * Nat.card ↥(fixV E)) :
    E ≤ natImage (StatedSL 2 K) := by
  have hlin : E ≤ linSub := by
    by_contra hnl
    have h := card_mul_card_fixV_lt_of_nonlinear hn hK hEN hE2 hEc hnl
    have h2 : Nat.card (StdMod (Fin 2) K) = Nat.card K ^ 2 := by
      rw [card_stdMod, Fintype.card_fin]
    omega
  intro x hx
  obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hlin hx)
  have hAA : A * A = 1 := by
    apply matHom_injective
    rw [map_mul, map_one]
    have := hE2 _ hx
    rwa [pow_two] at this
  have hdet : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h1 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ^ 2 = 1 := by
      rw [sq, ← Matrix.det_mul, ← Units.val_mul, hAA, Units.val_one, Matrix.det_one]
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have h3 : (((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det - 1) ^ 2 = 0 := by
      linear_combination h1 + (1 - ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h3)
  rw [natImage_eq_map]
  exact ⟨A, Subgroup.subset_closure hdet, rfl⟩

end Core

end B69

end CFSG.Quasithin
