module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RepresentationTheory

variable {M F : Type*} [Group M] [Field F]

@[expose] def charConj (E : Subgroup M) [hE : E.Normal] (χ : E →* Fˣ) (m : M) : E →* Fˣ where
  toFun e := χ ⟨m⁻¹ * e * m, hE.conj_mem' _ e.2 m⟩
  map_one' := by
    rw [← map_one χ]
    congr 1
    apply Subtype.ext
    simp
  map_mul' e e' := by
    rw [← map_mul χ]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]

theorem charConj_apply (E : Subgroup M) [hE : E.Normal] (χ : E →* Fˣ) (m : M) (e : E) :
    charConj E χ m e = χ ⟨m⁻¹ * e * m, hE.conj_mem' _ e.2 m⟩ :=
  rfl

theorem charConj_one (E : Subgroup M) [E.Normal] (χ : E →* Fˣ) : charConj E χ 1 = χ := by
  ext e
  rw [charConj_apply]
  congr 2
  apply Subtype.ext
  simp

theorem charConj_mul (E : Subgroup M) [E.Normal] (χ : E →* Fˣ) (g g' : M) :
    charConj E χ (g * g') = charConj E (charConj E χ g') g := by
  ext e
  rw [charConj_apply, charConj_apply, charConj_apply]
  congr 2
  apply Subtype.ext
  simp [mul_assoc]

@[expose] def charOrbit (E C : Subgroup M) [E.Normal] (χ : E →* Fˣ) : Set (E →* Fˣ) :=
  {μ | ∃ c ∈ C, charConj E χ c = μ}

@[expose] def charStab (E C : Subgroup M) [E.Normal] (χ : E →* Fˣ) : Subgroup M where
  carrier := {c | c ∈ C ∧ charConj E χ c = χ}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, by rw [charConj_mul, hb.2, ha.2]⟩
  one_mem' := ⟨one_mem _, charConj_one E χ⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by
    conv_lhs => rw [← ha.2]
    rw [← charConj_mul, inv_mul_cancel, charConj_one]⟩

variable {V : Type*} [AddCommGroup V] [Module F V]

@[expose] def weightSpace (E : Subgroup M) (ρ : Representation F M V) (χ : E →* Fˣ) :
    Submodule F V where
  carrier := {v | ∀ e : E, ρ e v = ((χ e : Fˣ) : F) • v}
  add_mem' {v w} hv hw e := by rw [map_add, hv e, hw e, smul_add]
  zero_mem' e := by rw [map_zero, smul_zero]
  smul_mem' c v hv e := by rw [map_smul, hv e, smul_comm]

theorem mem_weightSpace {E : Subgroup M} {ρ : Representation F M V} {χ : E →* Fˣ} {v : V} :
    v ∈ weightSpace E ρ χ ↔ ∀ e : E, ρ e v = ((χ e : Fˣ) : F) • v :=
  Iff.rfl

theorem apply_mem_weightSpace_charConj (E : Subgroup M) [E.Normal] (ρ : Representation F M V)
    (χ : E →* Fˣ) (m : M) {v : V} (hv : v ∈ weightSpace E ρ χ) :
    ρ m v ∈ weightSpace E ρ (charConj E χ m) := by
  intro e
  have h : (e : M) * m = m * (m⁻¹ * e * m) := by group
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply, charConj_apply]
  rw [show ρ (m⁻¹ * e * m) v = _ from hv ⟨m⁻¹ * e * m, _⟩, map_smul]

theorem weight_basis_repr_apply {ι : Type*} (E : Subgroup M) (ρ : Representation F M V)
    (b : Module.Basis ι F V) (w : ι → (E →* Fˣ)) (hb : ∀ i, b i ∈ weightSpace E ρ (w i)) (e : E)
    (v : V) (i : ι) : b.repr (ρ e v) i = ((w i e : Fˣ) : F) * b.repr v i := by
  classical
  have key : (Finsupp.lapply i ∘ₗ (b.repr : V →ₗ[F] ι →₀ F) ∘ₗ ρ e) =
      ((w i e : Fˣ) : F) • (Finsupp.lapply i ∘ₗ (b.repr : V →ₗ[F] ι →₀ F)) := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe]
    rw [hb j e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [smul_zero, smul_zero]
  have := LinearMap.congr_fun key v
  simpa using this

theorem eq_repr_smul_of_mem_weightSpace {ι : Type*} (E : Subgroup M) (ρ : Representation F M V)
    (b : Module.Basis ι F V) (w : ι → (E →* Fˣ)) (hw : Function.Injective w)
    (hb : ∀ i, b i ∈ weightSpace E ρ (w i)) {i : ι} {v : V} (hv : v ∈ weightSpace E ρ (w i)) :
    v = b.repr v i • b i := by
  classical
  have hrepr : b.repr v = Finsupp.single i (b.repr v i) := by
    ext κ
    rw [Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · obtain ⟨e, he⟩ : ∃ e, w κ e ≠ w i e := by
        by_contra hall
        push Not at hall
        exact h (hw (MonoidHom.ext hall)).symm
      have h1 := weight_basis_repr_apply E ρ b w hb e v κ
      rw [hv e, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
      have h2 : (((w i e : Fˣ) : F) - ((w κ e : Fˣ) : F)) * b.repr v κ = 0 := by
        rw [sub_mul, h1, sub_self]
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (Units.ext (sub_eq_zero.1 h3)).symm he
      · exact h3
  conv_lhs => rw [← b.repr.symm_apply_apply v, hrepr]
  rw [b.repr_symm_single]

theorem representation_injective (ρ : Representation F M V) (g : M) : Function.Injective (ρ g) := by
  intro x y hxy
  have := congrArg (ρ g⁻¹) hxy
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, Module.End.one_apply] at this

theorem exists_basis_mem_of_invariant {ι : Type*} (E : Subgroup M) (ρ : Representation F M V)
    (b : Module.Basis ι F V) (w : ι → (E →* Fˣ)) (hw : Function.Injective w)
    (hb : ∀ i, b i ∈ weightSpace E ρ (w i)) (S : Submodule F V)
    (hS : ∀ m, ∀ v ∈ S, ρ m v ∈ S) {v : V} (hvS : v ∈ S) (hv0 : v ≠ 0) : ∃ i, b i ∈ S := by
  classical
  suffices key : ∀ n : ℕ, ∀ v ∈ S, v ≠ 0 → (b.repr v).support.card = n → ∃ i, b i ∈ S from
    key _ v hvS hv0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hvS hv0 hcard
    have hne : b.repr v ≠ 0 := fun h => hv0 (b.repr.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hne
    have hci : b.repr v i ≠ 0 := Finsupp.mem_support_iff.1 hi
    by_cases hsing : ∀ j ∈ (b.repr v).support, j = i
    ·
      have hrepr : b.repr v = Finsupp.single i (b.repr v i) := by
        ext κ
        rw [Finsupp.single_apply]
        split_ifs with h
        · rw [h]
        · by_contra hκ
          exact h (hsing κ (Finsupp.mem_support_iff.2 hκ)).symm
      have hv : v = b.repr v i • b i := by
        conv_lhs => rw [← b.repr.symm_apply_apply v, hrepr]
        rw [b.repr_symm_single]
      refine ⟨i, ?_⟩
      have hbi : b i = (b.repr v i)⁻¹ • v := by
        calc b i = ((b.repr v i)⁻¹ * b.repr v i) • b i := by rw [inv_mul_cancel₀ hci, one_smul]
          _ = (b.repr v i)⁻¹ • (b.repr v i • b i) := by rw [smul_smul]
          _ = (b.repr v i)⁻¹ • v := by rw [← hv]
      rw [hbi]
      exact S.smul_mem _ hvS
    · push Not at hsing
      obtain ⟨j, hj, hji⟩ := hsing
      obtain ⟨e, he⟩ : ∃ e, w j e ≠ w i e := by
        by_contra hall
        push Not at hall
        exact hji (hw (MonoidHom.ext hall))
      set v' := ρ e v - ((w i e : Fˣ) : F) • v with hv'
      have hv'S : v' ∈ S := S.sub_mem (hS e v hvS) (S.smul_mem _ hvS)
      have hrepr' : ∀ κ, b.repr v' κ = (((w κ e : Fˣ) : F) - ((w i e : Fˣ) : F)) * b.repr v κ := by
        intro κ
        rw [hv', map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
          weight_basis_repr_apply E ρ b w hb, smul_eq_mul, sub_mul]
      have hsub : (b.repr v').support ⊂ (b.repr v).support := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i, hi, ?_⟩
          rw [Finsupp.mem_support_iff, hrepr', sub_self, zero_mul, not_not]
        · intro κ hκ
          rw [Finsupp.mem_support_iff] at hκ ⊢
          intro h0
          rw [hrepr', h0, mul_zero] at hκ
          exact hκ rfl
      have hv'0 : v' ≠ 0 := by
        intro h0
        have h1 := hrepr' j
        rw [h0, map_zero, Finsupp.zero_apply] at h1
        rcases mul_eq_zero.1 h1.symm with h2 | h2
        · exact he (Units.ext (sub_eq_zero.1 h2))
        · exact Finsupp.mem_support_iff.1 hj h2
      exact ih _ (hcard ▸ Finset.card_lt_card hsub) v' hv'S hv'0 rfl

theorem weight_basis_irreducible {ι : Type*} (E : Subgroup M) [E.Normal] (ρ : Representation F M V)
    (b : Module.Basis ι F V) (w : ι → (E →* Fˣ)) (hw : Function.Injective w)
    (hb : ∀ i, b i ∈ weightSpace E ρ (w i)) (htrans : ∀ i j, ∃ g : M, charConj E (w i) g = w j)
    (S : Submodule F V) (hS : ∀ m, ∀ v ∈ S, ρ m v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ := exists_basis_mem_of_invariant E ρ b w hw hb S hS hvS hv0
  have hall : ∀ j, b j ∈ S := by
    intro j
    obtain ⟨g, hg⟩ := htrans i j
    have hmem : ρ g (b i) ∈ weightSpace E ρ (w j) :=
      hg ▸ apply_mem_weightSpace_charConj E ρ _ g (hb i)
    have heq := eq_repr_smul_of_mem_weightSpace E ρ b w hw hb hmem
    have hne : ρ g (b i) ≠ 0 := fun h0 =>
      b.ne_zero i (representation_injective ρ g (h0.trans (map_zero _).symm))
    have hc : b.repr (ρ g (b i)) j ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at heq
      exact hne heq
    have hbj : b j = (b.repr (ρ g (b i)) j)⁻¹ • ρ g (b i) := by
      calc b j = ((b.repr (ρ g (b i)) j)⁻¹ * b.repr (ρ g (b i)) j) • b j := by
            rw [inv_mul_cancel₀ hc, one_smul]
        _ = (b.repr (ρ g (b i)) j)⁻¹ • (b.repr (ρ g (b i)) j • b j) := by rw [smul_smul]
        _ = (b.repr (ρ g (b i)) j)⁻¹ • ρ g (b i) := by rw [← heq]
    rw [hbj]
    exact S.smul_mem _ (hS g _ hi)
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hall j

section Orbit

variable (E C : Subgroup M) [E.Normal] (χ₀ : E →* Fˣ)

@[expose] def orbitBase : charOrbit E C χ₀ :=
  ⟨χ₀, 1, one_mem _, charConj_one E χ₀⟩

open scoped Classical in
theorem exists_weight_basis (ρ : Representation F M V)
    (hV : DirectSum.IsInternal fun μ : charOrbit E C χ₀ => weightSpace E ρ μ)
    (hV1 : ∀ μ : charOrbit E C χ₀, Module.finrank F (weightSpace E ρ μ) = 1) :
    ∃ b : Module.Basis (charOrbit E C χ₀) F V,
      ∀ μ : charOrbit E C χ₀, b μ ∈ weightSpace E ρ μ := by
  have : ∀ μ : charOrbit E C χ₀, Module.Finite F (weightSpace E ρ μ) := fun μ =>
    Module.finite_of_finrank_eq_succ (hV1 μ)
  let v : ∀ μ : charOrbit E C χ₀, Module.Basis (Fin 1) F (weightSpace E ρ μ) :=
    fun μ => Module.finBasisOfFinrankEq F _ (hV1 μ)
  refine ⟨(hV.collectedBasis v).reindex (Equiv.sigmaUnique _ fun _ => Fin 1), fun μ => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact hV.collectedBasis_mem v _

theorem stab_fixes_base (hH : Group.IsPerfect (charStab E C χ₀)) (ρ : Representation F M V)
    (b : Module.Basis (charOrbit E C χ₀) F V)
    (hb : ∀ μ : charOrbit E C χ₀, b μ ∈ weightSpace E ρ μ) :
    ∀ h ∈ charStab E C χ₀, ρ h (b (orbitBase E C χ₀)) = b (orbitBase E C χ₀) := by
  set v₀ := b (orbitBase E C χ₀) with hv₀
  have hw : Function.Injective fun μ : charOrbit E C χ₀ => (μ : E →* Fˣ) := Subtype.val_injective
  have hscal : ∀ h ∈ charStab E C χ₀,
      ρ h v₀ = b.repr (ρ h v₀) (orbitBase E C χ₀) • v₀ := by
    intro h hh
    have hmem : ρ h v₀ ∈ weightSpace E ρ ((orbitBase E C χ₀ : charOrbit E C χ₀) : E →* Fˣ) := by
      have := apply_mem_weightSpace_charConj E ρ χ₀ h (hb (orbitBase E C χ₀))
      rwa [show charConj E χ₀ h = χ₀ from hh.2] at this
    exact eq_repr_smul_of_mem_weightSpace E ρ b (fun μ => μ) hw hb hmem
  let s : charStab E C χ₀ → F := fun h => b.repr (ρ h v₀) (orbitBase E C χ₀)
  have hs1 : s 1 = 1 := by
    change b.repr (ρ 1 v₀) (orbitBase E C χ₀) = 1
    rw [map_one, Module.End.one_apply, hv₀, b.repr_self, Finsupp.single_eq_same]
  have hsmul : ∀ h h' : charStab E C χ₀, s (h * h') = s h * s h' := by
    intro h h'
    change b.repr (ρ ((h : M) * h') v₀) (orbitBase E C χ₀) = s h * s h'
    rw [map_mul, Module.End.mul_apply, hscal h' h'.2, map_smul, hscal h h.2, smul_smul,
      map_smul, hv₀, b.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
      mul_one, mul_comm]
  let sHom : charStab E C χ₀ →* F := { toFun := s, map_one' := hs1, map_mul' := hsmul }
  have hker : ∀ h : charStab E C χ₀, sHom.toHomUnits h = 1 := by
    intro h
    have hle := Abelianization.commutator_subset_ker sHom.toHomUnits
    rw [hH.commutator_eq_top] at hle
    exact hle (Subgroup.mem_top h)
  intro h hh
  have h1 := congrArg Units.val (hker ⟨h, hh⟩)
  change s ⟨h, hh⟩ = 1 at h1
  rw [hscal h hh]
  change s ⟨h, hh⟩ • v₀ = v₀
  rw [h1, one_smul]

@[expose] noncomputable def orbitRep (μ : charOrbit E C χ₀) : M :=
  Classical.choose μ.2

theorem orbitRep_mem (μ : charOrbit E C χ₀) : orbitRep E C χ₀ μ ∈ C :=
  (Classical.choose_spec μ.2).1

theorem charConj_orbitRep (μ : charOrbit E C χ₀) :
    charConj E χ₀ (orbitRep E C χ₀ μ) = μ :=
  (Classical.choose_spec μ.2).2

@[expose] def orbitConj (μ : charOrbit E C χ₀) {c : M} (hc : c ∈ C) : charOrbit E C χ₀ :=
  ⟨charConj E μ c, c * orbitRep E C χ₀ μ, mul_mem hc (orbitRep_mem E C χ₀ μ), by
    rw [charConj_mul, charConj_orbitRep]⟩

theorem orbit_vector_conj (hH : Group.IsPerfect (charStab E C χ₀)) (ρ : Representation F M V)
    (b : Module.Basis (charOrbit E C χ₀) F V)
    (hb : ∀ μ : charOrbit E C χ₀, b μ ∈ weightSpace E ρ μ) (μ : charOrbit E C χ₀) {c : M}
    (hc : c ∈ C) :
    ρ (c * orbitRep E C χ₀ μ) (b (orbitBase E C χ₀)) =
      ρ (orbitRep E C χ₀ (orbitConj E C χ₀ μ hc)) (b (orbitBase E C χ₀)) := by
  set μ' := orbitConj E C χ₀ μ hc with hμ'
  have hh : (orbitRep E C χ₀ μ')⁻¹ * (c * orbitRep E C χ₀ μ) ∈ charStab E C χ₀ := by
    refine ⟨mul_mem (inv_mem (orbitRep_mem E C χ₀ μ'))
      (mul_mem hc (orbitRep_mem E C χ₀ μ)), ?_⟩
    have e1 : charConj E χ₀ ((orbitRep E C χ₀ μ')⁻¹ * (c * orbitRep E C χ₀ μ)) =
        charConj E (μ' : E →* Fˣ) (orbitRep E C χ₀ μ')⁻¹ := by
      rw [charConj_mul, charConj_mul, charConj_orbitRep]
      rfl
    rw [e1]
    conv_lhs => rw [← charConj_orbitRep E C χ₀ μ']
    rw [← charConj_mul, inv_mul_cancel, charConj_one]
  have hfix := stab_fixes_base E C χ₀ hH ρ b hb _ hh
  calc ρ (c * orbitRep E C χ₀ μ) (b (orbitBase E C χ₀))
      = ρ (orbitRep E C χ₀ μ' * ((orbitRep E C χ₀ μ')⁻¹ * (c * orbitRep E C χ₀ μ)))
          (b (orbitBase E C χ₀)) := by rw [mul_inv_cancel_left]
    _ = ρ (orbitRep E C χ₀ μ') (ρ ((orbitRep E C χ₀ μ')⁻¹ * (c * orbitRep E C χ₀ μ))
          (b (orbitBase E C χ₀))) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (orbitRep E C χ₀ μ') (b (orbitBase E C χ₀)) := by rw [hfix]

theorem exists_orbit_vector_basis (ρ : Representation F M V)
    (b : Module.Basis (charOrbit E C χ₀) F V)
    (hb : ∀ μ : charOrbit E C χ₀, b μ ∈ weightSpace E ρ μ) :
    ∃ B : Module.Basis (charOrbit E C χ₀) F V, ∀ μ : charOrbit E C χ₀,
      B μ = ρ (orbitRep E C χ₀ μ) (b (orbitBase E C χ₀)) := by
  have hw : Function.Injective fun μ : charOrbit E C χ₀ => (μ : E →* Fˣ) := Subtype.val_injective
  have hx : ∀ μ : charOrbit E C χ₀,
      ρ (orbitRep E C χ₀ μ) (b (orbitBase E C χ₀)) ∈ weightSpace E ρ μ := fun μ => by
    have := apply_mem_weightSpace_charConj E ρ χ₀ (orbitRep E C χ₀ μ) (hb (orbitBase E C χ₀))
    rwa [charConj_orbitRep] at this
  have hx0 : ∀ μ : charOrbit E C χ₀, ρ (orbitRep E C χ₀ μ) (b (orbitBase E C χ₀)) ≠ 0 :=
    fun μ h => b.ne_zero _ (representation_injective ρ _ (h.trans (map_zero _).symm))
  have ha : ∀ μ : charOrbit E C χ₀,
      b.repr (ρ (orbitRep E C χ₀ μ) (b (orbitBase E C χ₀))) μ ≠ 0 := fun μ h => hx0 μ (by
    rw [eq_repr_smul_of_mem_weightSpace E ρ b (fun μ => μ) hw hb (hx μ), h, zero_smul])
  refine ⟨b.unitsSMul fun μ => Units.mk0 _ (ha μ), fun μ => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_mk0,
    ← eq_repr_smul_of_mem_weightSpace E ρ b (fun μ => μ) hw hb (hx μ)]

theorem orbit_basis_action (hH : Group.IsPerfect (charStab E C χ₀)) (ρ : Representation F M V)
    (b B : Module.Basis (charOrbit E C χ₀) F V)
    (hb : ∀ μ : charOrbit E C χ₀, b μ ∈ weightSpace E ρ μ)
    (hB : ∀ μ : charOrbit E C χ₀, B μ = ρ (orbitRep E C χ₀ μ) (b (orbitBase E C χ₀)))
    (μ : charOrbit E C χ₀) {e c : M} (he : e ∈ E) (hc : c ∈ C) :
    ρ (e * c) (B μ) = (((orbitConj E C χ₀ μ hc : E →* Fˣ) ⟨e, he⟩ : Fˣ) : F) •
      B (orbitConj E C χ₀ μ hc) := by
  have hBμ : B (orbitConj E C χ₀ μ hc) ∈ weightSpace E ρ (orbitConj E C χ₀ μ hc) := by
    rw [hB]
    have := apply_mem_weightSpace_charConj E ρ χ₀ (orbitRep E C χ₀ (orbitConj E C χ₀ μ hc))
      (hb (orbitBase E C χ₀))
    rwa [charConj_orbitRep] at this
  have h1 : ρ (e * c) (B μ) = ρ e (ρ (c * orbitRep E C χ₀ μ) (b (orbitBase E C χ₀))) := by
    simp only [hB μ, map_mul, Module.End.mul_apply]
  rw [h1, orbit_vector_conj E C χ₀ hH ρ b hb μ hc, ← hB]
  exact hBμ ⟨e, he⟩

end Orbit

open scoped Classical in
theorem perfect_weight_stabilizer_monomial_module_uniqueness [Finite M]
    (E C : Subgroup M) [E.Normal] (_hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (_hEC : E ⊓ C = ⊥) (hEC : E ⊔ C = ⊤) (χ₀ : E →* Fˣ)
    (hH : Group.IsPerfect (charStab E C χ₀))
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    (ρV : Representation F M V) (ρW : Representation F M W)
    (hV : DirectSum.IsInternal fun μ : charOrbit E C χ₀ => weightSpace E ρV μ)
    (hV1 : ∀ μ : charOrbit E C χ₀, Module.finrank F (weightSpace E ρV μ) = 1)
    (hW : DirectSum.IsInternal fun μ : charOrbit E C χ₀ => weightSpace E ρW μ)
    (hW1 : ∀ μ : charOrbit E C χ₀, Module.finrank F (weightSpace E ρW μ) = 1) :
    (Nontrivial V ∧ ∀ S : Submodule F V, (∀ m, ∀ v ∈ S, ρV m v ∈ S) → S = ⊥ ∨ S = ⊤) ∧
    (Nontrivial W ∧ ∀ S : Submodule F W, (∀ m, ∀ w ∈ S, ρW m w ∈ S) → S = ⊥ ∨ S = ⊤) ∧
    ∃ f : V ≃ₗ[F] W, ∀ (m : M) (v : V), f (ρV m v) = ρW m (f v) := by
  obtain ⟨bV, hbV⟩ := exists_weight_basis E C χ₀ ρV hV hV1
  obtain ⟨bW, hbW⟩ := exists_weight_basis E C χ₀ ρW hW hW1
  have hw : Function.Injective fun μ : charOrbit E C χ₀ => (μ : E →* Fˣ) := Subtype.val_injective
  have htrans : ∀ μ ν : charOrbit E C χ₀, ∃ g : M, charConj E (μ : E →* Fˣ) g = ν := by
    intro μ ν
    refine ⟨orbitRep E C χ₀ ν * (orbitRep E C χ₀ μ)⁻¹, ?_⟩
    conv_lhs => rw [← charConj_orbitRep E C χ₀ μ]
    rw [← charConj_mul, inv_mul_cancel_right, charConj_orbitRep]
  have hntV : Nontrivial V :=
    ⟨⟨bV (orbitBase E C χ₀), 0, bV.ne_zero _⟩⟩
  have hntW : Nontrivial W :=
    ⟨⟨bW (orbitBase E C χ₀), 0, bW.ne_zero _⟩⟩
  refine ⟨⟨hntV, weight_basis_irreducible E ρV bV (fun μ => μ) hw hbV htrans⟩,
    ⟨hntW, weight_basis_irreducible E ρW bW (fun μ => μ) hw hbW htrans⟩, ?_⟩
  obtain ⟨BV, hBV⟩ := exists_orbit_vector_basis E C χ₀ ρV bV hbV
  obtain ⟨BW, hBW⟩ := exists_orbit_vector_basis E C χ₀ ρW bW hbW
  let f := BV.equiv BW (Equiv.refl _)
  have hf : ∀ μ, f (BV μ) = BW μ := fun μ => by
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
  refine ⟨f, fun m v => ?_⟩
  have hlin : f.toLinearMap ∘ₗ ρV m = ρW m ∘ₗ f.toLinearMap := by
    refine BV.ext fun μ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    obtain ⟨e, he, c, hc, rfl⟩ : ∃ e ∈ E, ∃ c ∈ C, e * c = m := by
      have hm : m ∈ ((E ⊔ C : Subgroup M) : Set M) := by
        rw [hEC]
        trivial
      rw [Subgroup.normal_mul] at hm
      exact hm
    rw [orbit_basis_action E C χ₀ hH ρV bV BV hbV hBV μ he hc, hf,
      orbit_basis_action E C χ₀ hH ρW bW BW hbW hBW μ he hc, map_smul, hf]
  exact LinearMap.congr_fun hlin v

end CFSG.RepresentationTheory
