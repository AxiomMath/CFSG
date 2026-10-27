module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s16c7_isQuasisimple_of_isL3 {Y : Type} [Group Y] [Finite Y] (h : IsL3 Y 1) :
    CFSG.Open.IsQuasisimple Y := by
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  have hc : center Y = ⊥ := center_eq_bot_of_isL3 h
  have hcomm : commutator Y = ⊤ := by
    rcases (inferInstance : (commutator Y).Normal).eq_bot_or_eq_top with h0 | h0
    · exfalso
      have hcen : center Y = ⊤ := by
        refine (eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => ?_
        have h1 : ⁅b, a⁆ ∈ commutator Y := Subgroup.commutator_mem_commutator trivial trivial
        rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      obtain ⟨x, hx⟩ := exists_ne (1 : Y)
      have : x ∈ center Y := by rw [hcen]; trivial
      rw [hc, Subgroup.mem_bot] at this
      exact hx this
    · exact h0
  haveI : Group.IsPerfect Y := ⟨hcomm⟩
  exact CFSG.ComponentClassification.Quasisimple.simple_of_perfect Y

section Prod

variable {X : Type*} [Group X]

theorem s16c7_inl_mem_of_normal [IsSimpleGroup X] (hc : center X = ⊥) (N : Subgroup (X × X))
    [hN : N.Normal] {u v : X} (huv : (u, v) ∈ N) (hu : u ≠ 1) (x : X) : (x, 1) ∈ N := by
  have hu' : u ∉ center X := by
    rw [hc]
    exact fun h => hu (Subgroup.mem_bot.1 h)
  obtain ⟨c, hcu⟩ : ∃ c, c * u ≠ u * c := by
    by_contra hcon
    push Not at hcon
    exact hu' (Subgroup.mem_center_iff.2 hcon)
  have h1 : (⁅u, c⁆, (1 : X)) ∈ N := by
    have h2 : (c, (1 : X)) * (u, v)⁻¹ * (c, (1 : X))⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem huv) _
    have h3 := N.mul_mem huv h2
    have h4 : (u, v) * ((c, (1 : X)) * (u, v)⁻¹ * (c, (1 : X))⁻¹) = (⁅u, c⁆, (1 : X)) := by
      ext <;> simp [commutatorElement_def, mul_assoc]
    rwa [h4] at h3
  have hne : ⁅u, c⁆ ≠ 1 := by
    intro h
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact hcu h.symm
  have hN1 : (N.comap (MonoidHom.inl X X)) = ⊤ := by
    rcases (hN.comap (MonoidHom.inl X X)).eq_bot_or_eq_top with h0 | h0
    · exfalso
      have : ⁅u, c⁆ ∈ N.comap (MonoidHom.inl X X) := h1
      rw [h0, Subgroup.mem_bot] at this
      exact hne this
    · exact h0
  have hx : x ∈ N.comap (MonoidHom.inl X X) := by rw [hN1]; trivial
  exact hx

theorem s16c7_inr_mem_of_normal [IsSimpleGroup X] (hc : center X = ⊥) (N : Subgroup (X × X))
    [hN : N.Normal] {u v : X} (huv : (u, v) ∈ N) (hv : v ≠ 1) (x : X) : ((1 : X), x) ∈ N := by
  have hv' : v ∉ center X := by
    rw [hc]
    exact fun h => hv (Subgroup.mem_bot.1 h)
  obtain ⟨c, hcv⟩ : ∃ c, c * v ≠ v * c := by
    by_contra hcon
    push Not at hcon
    exact hv' (Subgroup.mem_center_iff.2 hcon)
  have h1 : ((1 : X), ⁅v, c⁆) ∈ N := by
    have h2 : ((1 : X), c) * (u, v)⁻¹ * ((1 : X), c)⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem huv) _
    have h3 := N.mul_mem huv h2
    have h4 : (u, v) * (((1 : X), c) * (u, v)⁻¹ * ((1 : X), c)⁻¹) = ((1 : X), ⁅v, c⁆) := by
      ext <;> simp [commutatorElement_def, mul_assoc]
    rwa [h4] at h3
  have hne : ⁅v, c⁆ ≠ 1 := by
    intro h
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact hcv h.symm
  have hN1 : (N.comap (MonoidHom.inr X X)) = ⊤ := by
    rcases (hN.comap (MonoidHom.inr X X)).eq_bot_or_eq_top with h0 | h0
    · exfalso
      have : ⁅v, c⁆ ∈ N.comap (MonoidHom.inr X X) := h1
      rw [h0, Subgroup.mem_bot] at this
      exact hne this
    · exact h0
  have hx : x ∈ N.comap (MonoidHom.inr X X) := by rw [hN1]; trivial
  exact hx

end Prod

section Factors

variable {Γ : Type*} [Group Γ] {A : Subgroup Γ} {X : Type*} [Group X] (φ : ↥A ≃* X × X)

@[expose] def s16c7_psi₁ : X →* Γ :=
  A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inl X X))

@[expose] def s16c7_psi₂ : X →* Γ :=
  A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inr X X))

theorem s16c7_psi₁_apply (x : X) : s16c7_psi₁ φ x = (φ.symm (x, 1) : Γ) := rfl

theorem s16c7_psi₂_apply (y : X) : s16c7_psi₂ φ y = (φ.symm (1, y) : Γ) := rfl

theorem s16c7_psi₁_injective : Function.Injective (s16c7_psi₁ φ) := by
  intro x y h
  have h1 : φ.symm (x, 1) = φ.symm (y, 1) := Subtype.ext h
  exact congrArg Prod.fst (φ.symm.injective h1)

theorem s16c7_psi₂_injective : Function.Injective (s16c7_psi₂ φ) := by
  intro x y h
  have h1 : φ.symm (1, x) = φ.symm (1, y) := Subtype.ext h
  exact congrArg Prod.snd (φ.symm.injective h1)

theorem s16c7_psi₁_mem (x : X) : s16c7_psi₁ φ x ∈ A := (φ.symm (x, 1)).2

theorem s16c7_psi₂_mem (y : X) : s16c7_psi₂ φ y ∈ A := (φ.symm (1, y)).2

theorem s16c7_psi_mul (x y : X) :
    (φ.symm (x, y) : Γ) = s16c7_psi₁ φ x * s16c7_psi₂ φ y := by
  have h : φ.symm (x, y) = φ.symm (x, 1) * φ.symm (1, y) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [h]
  rfl

theorem s16c7_conj_psi₁ {a : Γ} (ha : a ∈ A) (x : X) :
    a * s16c7_psi₁ φ x * a⁻¹ =
      s16c7_psi₁ φ ((φ ⟨a, ha⟩).1 * x * (φ ⟨a, ha⟩).1⁻¹) := by
  have e : (⟨a, ha⟩ : ↥A) = φ.symm (φ ⟨a, ha⟩) := (φ.symm_apply_apply _).symm
  have h : (⟨a, ha⟩ : ↥A) * φ.symm (x, 1) * (⟨a, ha⟩ : ↥A)⁻¹ =
      φ.symm ((φ ⟨a, ha⟩).1 * x * (φ ⟨a, ha⟩).1⁻¹, 1) := by
    conv_lhs => rw [e]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    ext <;> simp
  exact congrArg (fun z : ↥A => (z : Γ)) h

theorem s16c7_conj_psi₂ {a : Γ} (ha : a ∈ A) (y : X) :
    a * s16c7_psi₂ φ y * a⁻¹ =
      s16c7_psi₂ φ ((φ ⟨a, ha⟩).2 * y * (φ ⟨a, ha⟩).2⁻¹) := by
  have e : (⟨a, ha⟩ : ↥A) = φ.symm (φ ⟨a, ha⟩) := (φ.symm_apply_apply _).symm
  have h : (⟨a, ha⟩ : ↥A) * φ.symm (1, y) * (⟨a, ha⟩ : ↥A)⁻¹ =
      φ.symm (1, (φ ⟨a, ha⟩).2 * y * (φ ⟨a, ha⟩).2⁻¹) := by
    conv_lhs => rw [e]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    ext <;> simp
  exact congrArg (fun z : ↥A => (z : Γ)) h

theorem s16c7_fac_le_of_normal [IsSimpleGroup X] (hc : center X = ⊥) {N : Subgroup Γ}
    (hNA : N ≤ A) (hN : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N) (hne : N ≠ ⊥) :
    (s16c7_psi₁ φ).range ≤ N ∨ (s16c7_psi₂ φ).range ≤ N := by
  obtain ⟨⟨g, hgN⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  haveI hN' : (N.subgroupOf A).Normal := ⟨fun x hx b => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hN (b : Γ) b.2 (x : Γ) hx
    simpa using this⟩
  set N' : Subgroup (X × X) := (N.subgroupOf A).map φ.toMonoidHom with hN'def
  haveI : N'.Normal := Subgroup.Normal.map hN' _ φ.surjective
  have hgmem : (⟨g, hNA hgN⟩ : ↥A) ∈ N.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact hgN
  have hpN : φ ⟨g, hNA hgN⟩ ∈ N' := ⟨_, hgmem, rfl⟩
  have hone : (φ ⟨g, hNA hgN⟩).1 ≠ 1 ∨ (φ ⟨g, hNA hgN⟩).2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hp1 : φ ⟨g, hNA hgN⟩ = 1 := Prod.ext hcon.1 hcon.2
    have h2 : (⟨g, hNA hgN⟩ : ↥A) = 1 := φ.injective (by rw [hp1, map_one])
    have h3 : g = 1 := congrArg Subtype.val h2
    exact hg1 (Subtype.ext h3)
  rcases hone with h1 | h2
  · left
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz, hzx⟩ := s16c7_inl_mem_of_normal hc N' hpN h1 x
    have hz' : z = φ.symm (x, 1) := by
      rw [← hzx]
      simp
    have hz2 : z ∈ N.subgroupOf A := hz
    rw [Subgroup.mem_subgroupOf] at hz2
    rw [s16c7_psi₁_apply, ← hz']
    exact hz2
  · right
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz, hzy⟩ := s16c7_inr_mem_of_normal hc N' hpN h2 y
    have hz' : z = φ.symm (1, y) := by
      rw [← hzy]
      simp
    have hz2 : z ∈ N.subgroupOf A := hz
    rw [Subgroup.mem_subgroupOf] at hz2
    rw [s16c7_psi₂_apply, ← hz']
    exact hz2

end Factors

section Components

variable {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ} {X : Type} [Group X]

theorem s16c7_finite_of_psi (φ : ↥A ≃* X × X) : Finite X :=
  Finite.of_injective _ (s16c7_psi₁_injective φ)

theorem s16c7_card_psi₁ (hX : IsL3 X 1) (φ : ↥A ≃* X × X) :
    Nat.card (s16c7_psi₁ φ).range = 168 := by
  haveI := s16c7_finite_of_psi φ
  rw [← card_eq_of_isL3 hX]
  exact (Nat.card_congr (MonoidHom.ofInjective (s16c7_psi₁_injective φ)).toEquiv).symm

theorem s16c7_card_psi₂ (hX : IsL3 X 1) (φ : ↥A ≃* X × X) :
    Nat.card (s16c7_psi₂ φ).range = 168 := by
  haveI := s16c7_finite_of_psi φ
  rw [← card_eq_of_isL3 hX]
  exact (Nat.card_congr (MonoidHom.ofInjective (s16c7_psi₂_injective φ)).toEquiv).symm

theorem s16c7_conj_eq_factor (hX : IsL3 X 1) (φ : ↥A ≃* X × X) {H : Subgroup Γ} (hHA : H ≤ A)
    (hH : ∀ a ∈ A, ∀ x ∈ H, a * x * a⁻¹ ∈ H) (hcard : Nat.card H = 168) {n : Γ}
    (hn : n ∈ normalizer (A : Set Γ)) :
    H.map (MulAut.conj n).toMonoidHom = (s16c7_psi₁ φ).range ∨
      H.map (MulAut.conj n).toMonoidHom = (s16c7_psi₂ φ).range := by
  haveI := s16c7_finite_of_psi φ
  haveI : IsSimpleGroup X := isSimpleGroup_of_isL3 hX
  have hc : center X = ⊥ := center_eq_bot_of_isL3 hX
  have hnA : ∀ y ∈ A, n * y * n⁻¹ ∈ A := fun y hy => (Subgroup.mem_normalizer_iff.1 hn y).1 hy
  have hnA' : ∀ y ∈ A, n⁻¹ * y * n ∈ A := by
    intro y hy
    have h1 := (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * y * n)).2
    apply h1
    have : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
    rw [this]
    exact hy
  set H' : Subgroup Γ := H.map (MulAut.conj n).toMonoidHom with hH'
  have hmem : ∀ x, x ∈ H' ↔ ∃ y ∈ H, n * y * n⁻¹ = x := fun x => by
    rw [hH', Subgroup.mem_map]
    exact Iff.rfl
  have hH'A : H' ≤ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
    exact hnA y (hHA hy)
  have hH'n : ∀ a ∈ A, ∀ x ∈ H', a * x * a⁻¹ ∈ H' := by
    intro a ha x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(n⁻¹ * a * n) * y * (n⁻¹ * a * n)⁻¹, hH _ (hnA' a ha) y hy, ?_⟩
    group
  have hcard' : Nat.card H' = 168 := by
    rw [hH', Subgroup.card_map_of_injective (MulAut.conj n).injective, hcard]
  have hne : H' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard'
    omega
  rcases s16c7_fac_le_of_normal φ hc hH'A hH'n hne with h | h
  · left
    exact (Subgroup.eq_of_le_of_card_ge h (by rw [hcard', s16c7_card_psi₁ hX φ])).symm
  · right
    exact (Subgroup.eq_of_le_of_card_ge h (by rw [hcard', s16c7_card_psi₂ hX φ])).symm

theorem s16c7_components (hX : IsL3 X 1) (φ : ↥A ≃* X × X) :
    ∃ H₁ H₂ : Subgroup Γ, H₁ ≤ A ∧ H₂ ≤ A ∧ H₁ ⊔ H₂ = A ∧ H₁ ⊓ H₂ = ⊥ ∧
      IsL3 ↥H₁ 1 ∧ IsL3 ↥H₂ 1 ∧
      (∀ a ∈ A, ∀ h ∈ H₁, a * h * a⁻¹ ∈ H₁) ∧ (∀ a ∈ A, ∀ h ∈ H₂, a * h * a⁻¹ ∈ H₂) ∧
      ∀ n ∈ normalizer (A : Set Γ), ∀ H : Subgroup Γ, (H = H₁ ∨ H = H₂) →
        (H.map (MulAut.conj n).toMonoidHom = H₁ ∨ H.map (MulAut.conj n).toMonoidHom = H₂) := by
  have hnorm₁ : ∀ a ∈ A, ∀ h ∈ (s16c7_psi₁ φ).range, a * h * a⁻¹ ∈ (s16c7_psi₁ φ).range := by
    rintro a ha _ ⟨x, rfl⟩
    rw [s16c7_conj_psi₁ φ ha]
    exact ⟨_, rfl⟩
  have hnorm₂ : ∀ a ∈ A, ∀ h ∈ (s16c7_psi₂ φ).range, a * h * a⁻¹ ∈ (s16c7_psi₂ φ).range := by
    rintro a ha _ ⟨x, rfl⟩
    rw [s16c7_conj_psi₂ φ ha]
    exact ⟨_, rfl⟩
  have hle₁ : (s16c7_psi₁ φ).range ≤ A := by
    rintro _ ⟨x, rfl⟩
    exact s16c7_psi₁_mem φ x
  have hle₂ : (s16c7_psi₂ φ).range ≤ A := by
    rintro _ ⟨x, rfl⟩
    exact s16c7_psi₂_mem φ x
  refine ⟨(s16c7_psi₁ φ).range, (s16c7_psi₂ φ).range, hle₁, hle₂, ?_, ?_, ?_, ?_, hnorm₁, hnorm₂,
    ?_⟩
  · apply le_antisymm
    · exact sup_le hle₁ hle₂
    · intro a ha
      have e : φ.symm (φ ⟨a, ha⟩) = ⟨a, ha⟩ := φ.symm_apply_apply _
      have h1 : a = s16c7_psi₁ φ (φ ⟨a, ha⟩).1 * s16c7_psi₂ φ (φ ⟨a, ha⟩).2 := by
        rw [← s16c7_psi_mul]
        exact congrArg Subtype.val e.symm
      rw [h1]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    have h1 : φ.symm (1, y) = φ.symm (x, 1) := Subtype.ext hy
    have h2 := congrArg Prod.fst (φ.symm.injective h1)
    have hx : x = 1 := h2.symm
    rw [hx, map_one]
    exact Subgroup.one_mem _
  · exact CFSG.Blueprint.LieModel.of_mulEquiv
      (MonoidHom.ofInjective (s16c7_psi₁_injective φ)) hX
  · exact CFSG.Blueprint.LieModel.of_mulEquiv
      (MonoidHom.ofInjective (s16c7_psi₂_injective φ)) hX
  · intro n hn H hH
    rcases hH with rfl | rfl
    · exact s16c7_conj_eq_factor hX φ hle₁ hnorm₁ (s16c7_card_psi₁ hX φ) hn
    · exact s16c7_conj_eq_factor hX φ hle₂ hnorm₂ (s16c7_card_psi₂ hX φ) hn

end Components

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
