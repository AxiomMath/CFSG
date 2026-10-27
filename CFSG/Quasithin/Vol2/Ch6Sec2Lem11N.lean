module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

variable {G : Type} [Group G]

abbrev commGroupCh611 (U : Subgroup G) [IsMulCommutative ↥U] : CommGroup ↥U :=
  .mk (IsMulCommutative.is_comm (M := ↥U)).comm

attribute [local instance] commGroupCh611

theorem pow_val_add_ch611 {K : Type*} [Monoid K] {g : K} (hg : g ^ 2 = 1) (x y : ZMod 2) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  fin_cases x <;> fin_cases y
  · show g ^ 0 = g ^ 0 * g ^ 0
    simp
  · show g ^ 1 = g ^ 0 * g ^ 1
    simp
  · show g ^ 1 = g ^ 1 * g ^ 0
    simp
  · show g ^ 0 = g ^ 1 * g ^ 1
    rw [← pow_add, hg, pow_zero]

section Coord

variable {U : Subgroup G} [IsMulCommutative ↥U]

@[expose] noncomputable def kapCh611 (b : Fin 4 → ↥U) (hb : ∀ i, b i ^ 2 = 1) :
    (Fin 4 → ZMod 2) →+ Additive ↥U where
  toFun c := Additive.ofMul (∏ i, b i ^ (c i).val)
  map_zero' := by simp
  map_add' c c' := by
    rw [← ofMul_mul, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_val_add_ch611 (hb i)]

@[expose] noncomputable def kvCh611 (b : Fin 4 → ↥U) (hb : ∀ i, b i ^ 2 = 1)
    (c : Fin 4 → ZMod 2) : G :=
  ((Additive.toMul (kapCh611 b hb c) : ↥U) : G)

variable (b : Fin 4 → ↥U) (hb : ∀ i, b i ^ 2 = 1)

theorem kvCh611_mem (c : Fin 4 → ZMod 2) : kvCh611 b hb c ∈ U :=
  (Additive.toMul (kapCh611 b hb c)).2

theorem kvCh611_add (c c' : Fin 4 → ZMod 2) :
    kvCh611 b hb (c + c') = kvCh611 b hb c * kvCh611 b hb c' := by
  simp only [kvCh611, map_add, toMul_add, Subgroup.coe_mul]

theorem kvCh611_zero : kvCh611 b hb 0 = 1 := by
  simp only [kvCh611, map_zero, toMul_zero, OneMemClass.coe_one]

theorem kvCh611_single (j : Fin 4) : kvCh611 b hb (Pi.single j 1) = b j := by
  show ((∏ i, b i ^ ((Pi.single j 1 : Fin 4 → ZMod 2) i).val : ↥U) : G) = b j
  rw [Finset.prod_eq_single j (fun i _ hij => by simp [hij])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]
  show ((b j ^ 1 : ↥U) : G) = b j
  rw [pow_one]

theorem kvCh611_mul_self (c : Fin 4 → ZMod 2) : kvCh611 b hb c * kvCh611 b hb c = 1 := by
  rw [← kvCh611_add, show c + c = 0 by ext i; exact CharTwo.add_self_eq_zero (c i),
    kvCh611_zero]

theorem kvCh611_inv (c : Fin 4 → ZMod 2) : (kvCh611 b hb c)⁻¹ = kvCh611 b hb c :=
  inv_eq_of_mul_eq_one_right (kvCh611_mul_self b hb c)

theorem kvCh611_comm (c c' : Fin 4 → ZMod 2) :
    kvCh611 b hb c * kvCh611 b hb c' = kvCh611 b hb c' * kvCh611 b hb c := by
  rw [← kvCh611_add, ← kvCh611_add, add_comm]

variable {b hb}

theorem kvCh611_injective (hind : ∀ c, kvCh611 b hb c = 1 → c = 0) :
    Function.Injective (kvCh611 b hb) := by
  intro c c' h
  have h1 : kvCh611 b hb (c + c') = 1 := by
    rw [kvCh611_add, h, kvCh611_mul_self]
  have h2 := hind _ h1
  have : c = -c' := eq_neg_of_add_eq_zero_left h2
  rw [this]
  ext i
  exact CharTwo.neg_eq (c' i)

theorem kvCh611_surj [Finite ↥U] (hind : ∀ c, kvCh611 b hb c = 1 → c = 0)
    (hU : Nat.card U = 16) :
    ∀ u ∈ U, ∃ c, kvCh611 b hb c = u := by
  classical
  have hinj : Function.Injective (fun c => (Additive.toMul (kapCh611 b hb c) : ↥U)) := by
    intro c c' h
    exact kvCh611_injective hind (congrArg Subtype.val h)
  have hsurj : Function.Surjective (fun c => (Additive.toMul (kapCh611 b hb c) : ↥U)) := by
    have hc : Nat.card (Fin 4 → ZMod 2) = Nat.card ↥U := by
      rw [hU, Nat.card_eq_fintype_card]
      rfl
    exact (Function.Injective.bijective_of_nat_card_le hinj hc.ge).2
  intro u hu
  obtain ⟨c, hc⟩ := hsurj ⟨u, hu⟩
  exact ⟨c, congrArg Subtype.val hc⟩

variable (b hb)

@[expose] def IsMatCh611 (g : G) (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ c, g * kvCh611 b hb c * g⁻¹ = kvCh611 b hb (A.mulVec c)

variable {b hb}

theorem IsMatCh611.mul {g g' : G} {A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : IsMatCh611 b hb g A) (h' : IsMatCh611 b hb g' A') :
    IsMatCh611 b hb (g * g') (A * A') := by
  unfold IsMatCh611 at h h' ⊢
  intro c
  rw [← Matrix.mulVec_mulVec, ← h, ← h', mul_inv_rev]
  group

theorem isMatCh611_one : IsMatCh611 b hb 1 1 := by
  unfold IsMatCh611
  intro c
  simp

theorem isMatCh611_of_cols {g : G} (hgU : g ∈ Subgroup.normalizer (U : Set G))
    {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hcol : ∀ j, g * b j * g⁻¹ = kvCh611 b hb (A.col j)) :
    IsMatCh611 b hb g A := by
  classical
  have hconj : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hgU u).mp hu
  let φ₁ : (Fin 4 → ZMod 2) →+ Additive ↥U :=
    { toFun := fun c => Additive.ofMul ⟨g * kvCh611 b hb c * g⁻¹,
        hconj _ (kvCh611_mem b hb c)⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [kvCh611_zero]
      map_add' := fun c c' => by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp only [toMul_ofMul, toMul_add, Subgroup.coe_mul, kvCh611_add]
        group }
  let φ₂ : (Fin 4 → ZMod 2) →+ Additive ↥U :=
    (kapCh611 b hb).comp (Matrix.mulVecLin A).toAddMonoidHom
  have heq : φ₁ = φ₂ := by
    refine AddMonoidHom.functions_ext _ φ₁ φ₂ fun j x => ?_
    have hx : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases hx x with rfl | rfl
    · rw [Pi.single_zero, map_zero, map_zero]
    · apply Additive.toMul.injective
      apply Subtype.ext
      show g * kvCh611 b hb (Pi.single j 1) * g⁻¹ =
        kvCh611 b hb (A.mulVec (Pi.single j 1))
      rw [kvCh611_single, hcol j, Matrix.mulVec_single_one]
  unfold IsMatCh611
  intro c
  have := congrArg (fun φ : (Fin 4 → ZMod 2) →+ Additive ↥U => ((Additive.toMul (φ c) : ↥U) : G))
    heq
  exact this

theorem IsMatCh611.unique (hind : ∀ c, kvCh611 b hb c = 1 → c = 0) {g : G}
    {A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : IsMatCh611 b hb g A)
    (h' : IsMatCh611 b hb g A') : A = A' := by
  have hv : ∀ c, A.mulVec c = A'.mulVec c := fun c =>
    kvCh611_injective hind ((h c).symm.trans (h' c))
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem exists_isMatCh611 [Finite ↥U] (hind : ∀ c, kvCh611 b hb c = 1 → c = 0)
    (hU : Nat.card U = 16)
    {g : G} (hgU : g ∈ Subgroup.normalizer (U : Set G)) : ∃ A, IsMatCh611 b hb g A := by
  have hsurj := kvCh611_surj hind hU
  have hc : ∀ j, ∃ c, kvCh611 b hb c = g * b j * g⁻¹ := fun j =>
    hsurj _ ((Subgroup.mem_normalizer_iff.mp hgU (b j)).mp (b j).2)
  choose col hcol using hc
  refine ⟨Matrix.of fun i j => col j i, isMatCh611_of_cols hgU fun j => ?_⟩
  rw [← hcol j]
  rfl

theorem IsMatCh611.mem_centralizer_iff [Finite ↥U] (hind : ∀ c, kvCh611 b hb c = 1 → c = 0)
    (hU : Nat.card U = 16) {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : IsMatCh611 b hb g A) : g ∈ Subgroup.centralizer (U : Set G) ↔ A = 1 := by
  constructor
  · intro hg
    refine h.unique hind fun c => ?_
    rw [Matrix.one_mulVec, ← Subgroup.mem_centralizer_iff.mp hg _ (kvCh611_mem b hb c),
      mul_inv_cancel_right]
  · rintro rfl
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨c, rfl⟩ := kvCh611_surj hind hU u hu
    have := h c
    rw [Matrix.one_mulVec] at this
    calc kvCh611 b hb c * g = g * kvCh611 b hb c * g⁻¹ * g := by rw [this]
      _ = g * kvCh611 b hb c := by group

variable (b hb)

@[expose] noncomputable def kapLineCh611 (p q : Fin 4 → ZMod 2) : Subgroup G where
  carrier := {x | ∃ α β : ZMod 2, kvCh611 b hb (α • p + β • q) = x}
  mul_mem' := by
    rintro _ _ ⟨α, β, rfl⟩ ⟨α', β', rfl⟩
    refine ⟨α + α', β + β', ?_⟩
    rw [← kvCh611_add, add_smul, add_smul, add_add_add_comm]
  one_mem' := ⟨0, 0, by rw [zero_smul, zero_smul, add_zero, kvCh611_zero]⟩
  inv_mem' := by
    rintro _ ⟨α, β, rfl⟩
    exact ⟨α, β, (kvCh611_inv b hb _).symm⟩

theorem mem_kapLineCh611 {p q : Fin 4 → ZMod 2} {x : G} :
    x ∈ kapLineCh611 b hb p q ↔ ∃ α β : ZMod 2, kvCh611 b hb (α • p + β • q) = x :=
  Iff.rfl

variable {b hb}

theorem IsMatCh611.map_kapLine {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : IsMatCh611 b hb g A) (p q : Fin 4 → ZMod 2) :
    (kapLineCh611 b hb p q).map (MulAut.conj g).toMonoidHom =
      kapLineCh611 b hb (A.mulVec p) (A.mulVec q) := by
  ext x
  constructor
  · rintro ⟨y, ⟨α, β, rfl⟩, rfl⟩
    refine ⟨α, β, ?_⟩
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
    exact (h _).symm
  · rintro ⟨α, β, rfl⟩
    refine ⟨kvCh611 b hb (α • p + β • q), ⟨α, β, rfl⟩, ?_⟩
    show g * kvCh611 b hb (α • p + β • q) * g⁻¹ = _
    rw [h, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem kapLineCh611_congr {p q p' q' : Fin 4 → ZMod 2}
    (h : ∀ α β : ZMod 2, ∃ α' β' : ZMod 2, α • p + β • q = α' • p' + β' • q')
    (h' : ∀ α β : ZMod 2, ∃ α' β' : ZMod 2, α • p' + β • q' = α' • p + β' • q) :
    kapLineCh611 b hb p q = kapLineCh611 b hb p' q' := by
  ext x
  constructor
  · rintro ⟨α, β, rfl⟩
    obtain ⟨α', β', he⟩ := h α β
    exact ⟨α', β', by rw [he]⟩
  · rintro ⟨α, β, rfl⟩
    obtain ⟨α', β', he⟩ := h' α β
    exact ⟨α', β', by rw [he]⟩

theorem kapLineCh611_ne (hind : ∀ c, kvCh611 b hb c = 1 → c = 0) {p q p' q' : Fin 4 → ZMod 2}
    {α β : ZMod 2} (hc : ∀ α' β' : ZMod 2, α • p + β • q ≠ α' • p' + β' • q') :
    kapLineCh611 b hb p q ≠ kapLineCh611 b hb p' q' := by
  intro heq
  have hmem : kvCh611 b hb (α • p + β • q) ∈ kapLineCh611 b hb p' q' := heq ▸ ⟨α, β, rfl⟩
  obtain ⟨α', β', he⟩ := hmem
  exact hc α' β' (kvCh611_injective hind he).symm

end Coord

section Perm

variable {n : ℕ}

@[expose] def PermByCh611 (Ω : Fin n → Subgroup G) (g : G) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, (Ω i).map (MulAut.conj g).toMonoidHom = Ω (σ i)

omit [Group G] in
theorem map_map_conj_ch611 {G : Type} [Group G] (K : Subgroup G) (g g' : G) :
    (K.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * g')).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem PermByCh611.mul {Ω : Fin n → Subgroup G} {g g' : G} {σ σ' : Equiv.Perm (Fin n)}
    (h : PermByCh611 Ω g σ) (h' : PermByCh611 Ω g' σ') : PermByCh611 Ω (g * g') (σ * σ') := by
  intro i
  rw [← map_map_conj_ch611, h' i, h (σ' i)]
  rfl

theorem PermByCh611.inv {Ω : Fin n → Subgroup G} {g : G} {σ : Equiv.Perm (Fin n)}
    (h : PermByCh611 Ω g σ) : PermByCh611 Ω g⁻¹ σ⁻¹ := by
  intro i
  have h1 := h (σ⁻¹ i)
  have e : σ (σ⁻¹ i) = i := by simp
  rw [e] at h1
  rw [← h1, map_map_conj_ch611, inv_mul_cancel]
  ext x
  simp

theorem PermByCh611.one (Ω : Fin n → Subgroup G) : PermByCh611 Ω 1 1 := by
  intro i
  ext x
  simp

theorem PermByCh611.unique {Ω : Fin n → Subgroup G} (hΩ : Function.Injective Ω) {g : G}
    {σ σ' : Equiv.Perm (Fin n)} (h : PermByCh611 Ω g σ) (h' : PermByCh611 Ω g σ') : σ = σ' := by
  ext i
  exact congrArg Fin.val (hΩ ((h i).symm.trans (h' i)))

theorem exists_permByCh611 {Ω : Fin n → Subgroup G} (hΩ : Function.Injective Ω) {g : G}
    (h : ∀ i, ∃ j, (Ω i).map (MulAut.conj g).toMonoidHom = Ω j) :
    ∃ σ, PermByCh611 Ω g σ := by
  choose f hf using h
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply hΩ
    have h1 : (Ω i).map (MulAut.conj g).toMonoidHom = (Ω i').map (MulAut.conj g).toMonoidHom := by
      rw [hf, hf, hii']
    exact Subgroup.map_injective (MulAut.conj g).injective h1
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  exact ⟨Equiv.ofBijective f hbij, fun i => hf i⟩

@[expose] def permStabCh611 (Ω : Fin n → Subgroup G) : Subgroup G where
  carrier := {g | ∃ σ, PermByCh611 Ω g σ}
  mul_mem' := by
    rintro g g' ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    exact ⟨σ * σ', hσ.mul hσ'⟩
  one_mem' := ⟨1, PermByCh611.one Ω⟩
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    exact ⟨σ⁻¹, hσ.inv⟩

@[expose] noncomputable def permHomCh611 (Ω : Fin n → Subgroup G) (hΩ : Function.Injective Ω) :
    ↥(permStabCh611 Ω) →* Equiv.Perm (Fin n) where
  toFun g := Classical.choose g.2
  map_one' := (Classical.choose_spec (permStabCh611 Ω).one_mem).unique hΩ (PermByCh611.one Ω)
  map_mul' g g' := (Classical.choose_spec (g * g').2).unique hΩ
    ((Classical.choose_spec g.2).mul (Classical.choose_spec g'.2))

theorem permHomCh611_spec (Ω : Fin n → Subgroup G) (hΩ : Function.Injective Ω)
    (g : ↥(permStabCh611 Ω)) : PermByCh611 Ω g (permHomCh611 Ω hΩ g) :=
  Classical.choose_spec g.2

theorem permHomCh611_eq {Ω : Fin n → Subgroup G} (hΩ : Function.Injective Ω)
    {g : ↥(permStabCh611 Ω)} {σ : Equiv.Perm (Fin n)} (h : PermByCh611 Ω g σ) :
    permHomCh611 Ω hΩ g = σ :=
  (permHomCh611_spec Ω hΩ g).unique hΩ h

end Perm

end CFSG.Quasithin.H13
