module

public import CFSG.Quasithin.Vol2.Ch3zOff
public import CFSG.Quasithin.Vol2.Ch3zTorus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 RegularWreathProduct

namespace Ch3z

variable {V : Type} [CommGroup V] [Finite V]

theorem BlkCtx.of_struct (hB69 : B69Struct) (hV : ∀ v : V, v ^ 2 = 1) {X S M : Subgroup (MulAut V)}
    (hsq : ∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
      CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f)
    (hmp : MinParabolic X S M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hirr : ∀ W : Subgroup V, (∀ x ∈ X, ∀ w ∈ W, x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ v : V, v ≠ 1) : ∃ 𝓗 : Finset (Subgroup (MulAut V)), BlkCtx X S M 𝓗 := by
  obtain ⟨𝓗, hsc⟩ := (B69.b69Struct_iff.mp hB69) V hV X S M hsq hmp hO2 hFF
  refine ⟨𝓗, hV, hmp, hirr, hnt, hsc, ?_⟩
  intro hJ
  have h1 : X = ffJ X ⊔ S := hsc.2.2.2.2.2.2.2.2.1
  rw [hJ, bot_sup_eq] at h1
  exact absurd h1 (ne_of_gt hmp.lt)

omit [Finite V] in
theorem le_ffJ_of_offender {X A : Subgroup (MulAut V)} (hstrong : ¬ IsStrongFFModule X)
    (hAX : A ≤ X) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) : A ≤ ffJ X := by
  have hFF : IsFFStarOffender X A := by
    refine ⟨hAX, hA1, hAe, fun B hBA => ?_⟩
    by_cases hB : B = ⊥
    · subst hB
      have hfix : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
        ext v
        simp only [mem_fixV, Subgroup.mem_top, iff_true]
        intro x hx
        rw [Subgroup.mem_bot] at hx
        rw [hx]
        rfl
      rw [hfix, Subgroup.card_bot, Subgroup.card_top, one_mul]
      exact hoff
    · by_contra hlt
      push Not at hlt
      apply hstrong
      refine ⟨B, hBA.trans hAX, hB, ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb),
        fun a ha => hAe.2 a (hBA ha)⟩, lt_of_le_of_lt hoff hlt⟩
  exact le_iSup₂ (f := fun (A : Subgroup (MulAut V)) (_ : IsFFStarOffender X A) => A) A hFF

section Shapes

variable {X T M A : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

@[expose] def OneWit (X A : Subgroup (MulAut V)) (m : ℕ) : Prop :=
  (m = 3 ∨ m = 5) ∧ ∃ (θ : ↥X ≃* Equiv.Perm (Fin m)) (β : ↥(coreMod m) →* V),
    (∀ (x : ↥X) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u)) ∧
    β.range = ⊤ ∧ β.ker = ⊥ ∧ ∃ a ∈ A, ∃ ha : a ∈ X, Equiv.Perm.sign (θ ⟨a, ha⟩) = -1

@[expose] def TwoWit (X T A : Subgroup (MulAut V)) (m : ℕ) : Prop :=
  ∃ (H₁ H₂ : Subgroup (MulAut V)) (θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)) (θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m))
    (β₁ β₂ : ↥(coreMod m) →* V) (Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥X),
    WreathData X T m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ ∧
    ((∃ a ∈ A, ∃ ha : a ∈ H₁, Equiv.Perm.sign (θ₁ ⟨a, ha⟩) = -1) ∨
      ∃ a ∈ A, ∃ ha : a ∈ H₂, Equiv.Perm.sign (θ₂ ⟨a, ha⟩) = -1)

theorem BlkCtx.shape_wit (h : BlkCtx X T M 𝓗) (hX : IsRankTwoQuotient ↥X)
    (hsym : ∀ H ∈ 𝓗, ∃ m, SymBlk M H m) (hstrong : ¬ IsStrongFFModule X) (hAX : A ≤ X)
    (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    (∃ m, OneWit X A m) ∨ ∃ m, TwoWit X T A m := by
  have hle2 := h.card_le_two hX hsym
  have hpos : 0 < 𝓗.card := Finset.card_pos.mpr h.nonempty
  have h1or2 : 𝓗.card = 1 ∨ 𝓗.card = 2 := by omega
  rcases h1or2 with hc | hc
  · left
    obtain ⟨m, hm35, hcore⟩ := h.shape_of_card_one hX hc hsym
    obtain ⟨θ, β, hβeq, hβr, hβk⟩ := hcore
    obtain ⟨a, haA, ha, hsg⟩ := exists_odd_sym hm35 θ β hβeq hβr hβk hAX hAe hA1 hoff
    exact ⟨m, hm35, θ, β, hβeq, hβr, hβk, a, haA, ha, hsg⟩
  · right
    obtain ⟨m, H₁, H₂, θ₁, θ₂, β₁, β₂, Ψ, hd⟩ := h.shape_of_card_two hX hc hsym
    have hAJ : A ≤ H₁ ⊔ H₂ := hd.ffJ_eq ▸ le_ffJ_of_offender hstrong hAX hAe hA1 hoff
    exact ⟨m, H₁, H₂, θ₁, θ₂, β₁, β₂, Ψ, hd,
      hd.tb.exists_odd_offender θ₁ θ₂ β₁ β₂ hd.eq₁ hd.range₁ hd.ker₁ hd.eq₂ hd.range₂ hd.ker₂
        hstrong hAJ hAe hA1 hoff⟩

end Shapes

section Bad

variable {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

omit [Finite V] in
theorem NatBlockData.isPerfect {H : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ} (he : 2 ≤ e)
    (hN : NatBlockData H U e) : Group.IsPerfect ↥H := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have : Fintype K := Fintype.ofFinite K
  have hcard4 : ∃ s : Finset K, s.card = 4 := by
    have h4 : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hcard4
  exact Group.IsPerfect.ofSurjective hπs

omit [Finite V] in
theorem BlkCtx.kills_of_bad (h : BlkCtx X T M 𝓗) {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ 𝓗) {e : ℕ}
    (he : 2 ≤ e) (hN : NatBlockData H₀ (commV H₀) e) (χ : ↥X →* ℤˣ) :
    ∀ x ∈ ffJ X, ∀ hx : x ∈ X, χ ⟨x, hx⟩ = 1 := by
  have hperf : Group.IsPerfect ↥H₀ := hN.isPerfect he
  have hker : ∀ y ∈ H₀, ∀ hy : y ∈ X, χ ⟨y, hy⟩ = 1 := by
    intro y hy hyX
    set f : ↥H₀ →* ℤˣ := χ.comp (Subgroup.inclusion (h.mem_le hH₀)) with hf
    have hr : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
    have hs : Subsingleton ↥f.range := inferInstance
    have h1 : (⟨f ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  have hconj : ∀ H ∈ 𝓗, ∀ x ∈ H, ∀ hx : x ∈ X, χ ⟨x, hx⟩ = 1 := by
    intro H hH x hxH hxX
    obtain ⟨t, htT, hc⟩ := h.trans hH₀ hH
    have htX : t ∈ X := h.mp.isSylow.1 htT
    have hx' : t⁻¹ * x * t ∈ H₀ := by
      rw [← hc] at hxH
      exact B6.mem_conjSub.mp hxH
    have hmem : t⁻¹ * x * t ∈ X := X.mul_mem (X.mul_mem (X.inv_mem htX) hxX) htX
    have h1 := hker _ hx' hmem
    have e1 : (⟨t⁻¹ * x * t, hmem⟩ : ↥X) = (⟨t, htX⟩ : ↥X)⁻¹ * ⟨x, hxX⟩ * ⟨t, htX⟩ := rfl
    rw [e1, map_mul, map_mul, map_inv, mul_comm (χ ⟨t, htX⟩)⁻¹, mul_assoc, inv_mul_cancel,
      mul_one] at h1
    exact h1
  have hle : ffJ X ≤ (MonoidHom.ker χ).map X.subtype := by
    rw [h.ffJ_eq]
    refine iSup₂_le fun H hH x hx => ?_
    have hxX : x ∈ X := h.mem_le hH hx
    exact ⟨⟨x, hxX⟩, hconj H hH x hx hxX, rfl⟩
  intro x hx hxX
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxX⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem BlkCtx.isSylowTwoOf_block (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    IsSylowTwoOf (T ⊓ H) H := by
  have hJX : ffJ X ≤ X := by
    rw [h.ffJ_eq]
    exact iSup₂_le fun H' hH' => h.mem_le hH'
  have hJ : IsSylowTwoOf (T ⊓ ffJ X) (ffJ X) :=
    B6.isSylowTwoOf_inf_normal h.mp.isSylow hJX (B6.le_normalizer_ffJ X)
  have hHJ : H ≤ ffJ X := by
    rw [h.ffJ_eq]
    exact le_iSup₂ (f := fun (H : Subgroup (MulAut V)) (_ : H ∈ 𝓗) => H) H hH
  have hn : ffJ X ≤ Subgroup.normalizer (H : Set (MulAut V)) := by
    rw [h.ffJ_eq]
    refine iSup₂_le fun H' hH' x hx => ?_
    by_cases hne : H' = H
    · subst hne
      exact Subgroup.le_normalizer hx
    · refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
      · have := h.comm_of_ne hH' hH hne hx hy
        rw [this, mul_inv_cancel_right]
        exact hy
      · have := h.comm_of_ne hH' hH hne (H'.inv_mem hx) hy
        rw [this, inv_mul_cancel_right]
        exact hy
  have := B6.isSylowTwoOf_inf_normal hJ hHJ hn
  rwa [inf_assoc, inf_eq_right.mpr hHJ] at this

theorem BlkCtx.symBlk_of_fixed (h : BlkCtx X T M 𝓗) {v : V} (hv : v ≠ 1)
    (hvT : ∀ t ∈ T, t v = v) (hvM : ∀ d ∈ M, Odd (orderOf d) → d v = v) :
    ∀ H ∈ 𝓗, ∃ m, SymBlk M H m := by
  intro H hH
  rcases h.symBlk_or_bad hH with hs | ⟨e, he, hN, hM⟩
  · exact hs
  · exfalso
    obtain ⟨d, hdH, hdN, hdodd, hdv⟩ := exists_torus_of_natBlock he
      (fun h' hh u hu => apply_mem_commV_of_mem hh hu) hN (h.isSylowTwoOf_block hH)
    have hdM : d ∈ M := by
      have : d ∈ H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) :=
        ⟨hdH, hdN⟩
      rw [← hM] at this
      exact this.1
    exact hv (h.eq_one_of_fixed hH ⟨hdH, hdodd, hdv⟩ hdM hvT hvM)

end Bad

section Parity

@[expose] def wrSign (m : ℕ) : (Equiv.Perm (Fin m) ≀ᵣ Q2) →* ℤˣ where
  toFun w := ∏ q : Q2, Equiv.Perm.sign (w.left q)
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_left, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
    congr 1
    exact Equiv.prod_comp (Equiv.mulLeft a.right⁻¹) (fun q => Equiv.Perm.sign (b.left q))

theorem wrSign_wrI₁ {m : ℕ} (σ : Equiv.Perm (Fin m)) : wrSign m (wrI₁ σ) = Equiv.Perm.sign σ := by
  show ∏ q : Q2, Equiv.Perm.sign ((wrI₁ σ).left q) = _
  rw [Fintype.prod_eq_mul 1 gQ gQ_ne_one.symm ?_]
  · simp [wrI₁, gQ_ne_one]
  · intro x hx
    rcases Q2_cases x with h | h
    · exact absurd h hx.1
    · exact absurd h hx.2

theorem wrSign_wrI₂ {m : ℕ} (σ : Equiv.Perm (Fin m)) : wrSign m (wrI₂ σ) = Equiv.Perm.sign σ := by
  show ∏ q : Q2, Equiv.Perm.sign ((wrI₂ σ).left q) = _
  rw [Fintype.prod_eq_mul 1 gQ gQ_ne_one.symm ?_]
  · simp [wrI₂, gQ_ne_one]
  · intro x hx
    rcases Q2_cases x with h | h
    · exact absurd h hx.1
    · exact absurd h hx.2

variable {X T A : Subgroup (MulAut V)} {m : ℕ}

omit [Finite V] in
theorem OneWit.exists_hom (h : OneWit X A m) :
    ∃ χ : ↥X →* ℤˣ, ∃ a ∈ A, ∃ ha : a ∈ X, χ ⟨a, ha⟩ = -1 := by
  obtain ⟨-, θ, β, -, -, -, a, haA, ha, hsg⟩ := h
  exact ⟨(Equiv.Perm.sign).comp θ.toMonoidHom, a, haA, ha, by simpa using hsg⟩

omit [Finite V] in
theorem TwoWit.exists_hom (h : TwoWit X T A m) :
    ∃ χ : ↥X →* ℤˣ, ∃ a ∈ A, ∃ ha : a ∈ X, χ ⟨a, ha⟩ = -1 := by
  obtain ⟨H₁, H₂, θ₁, θ₂, β₁, β₂, Ψ, hd, hw⟩ := h
  refine ⟨(wrSign m).comp Ψ.symm.toMonoidHom, ?_⟩
  rcases hw with ⟨a, haA, ha, hsg⟩ | ⟨a, haA, ha, hsg⟩
  · have haX : a ∈ X := hd.h1X ha
    refine ⟨a, haA, haX, ?_⟩
    have hΨ : Ψ (wrI₁ (θ₁ ⟨a, ha⟩)) = ⟨a, haX⟩ := by
      apply Subtype.ext
      rw [hd.Ψ₁]
      simp
    show wrSign m (Ψ.symm ⟨a, haX⟩) = -1
    rw [← hΨ, MulEquiv.symm_apply_apply, wrSign_wrI₁, hsg]
  · have haX : a ∈ X := hd.h2X ha
    refine ⟨a, haA, haX, ?_⟩
    have hΨ : Ψ (wrI₂ (θ₂ ⟨a, ha⟩)) = ⟨a, haX⟩ := by
      apply Subtype.ext
      rw [hd.Ψ₂]
      simp
    show wrSign m (Ψ.symm ⟨a, haX⟩) = -1
    rw [← hΨ, MulEquiv.symm_apply_apply, wrSign_wrI₂, hsg]

end Parity



end Ch3z

end CFSG.Quasithin
