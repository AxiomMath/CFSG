module

public import CFSG.Quasithin.Background.SmithD37FMat
public import CFSG.Quasithin.Background.SmithD37Sub
public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.Quasithin.Background.SmithD37Lin

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.QuasithinUnique.Setup
open scoped Matrix TensorProduct

section Subfields

variable {F : Type} [Field F] [Finite F]

theorem card_pow_eq_self_le {q : ℕ} (hq : 2 ≤ q) :
    Nat.card {x : F // x ^ q = x} ≤ q := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set p : Polynomial F := Polynomial.X ^ q - Polynomial.X with hp
  have hdeg : p.natDegree = q := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  calc Nat.card {x : F // x ^ q = x} = (p.roots.toFinset).card := by
        rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
        refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hp,
          Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = q := hdeg

theorem pow_card_subfield (D : Subfield F) {x : F} (hx : x ∈ D) : x ^ Nat.card D = x := by
  have hfin : Fintype D := Fintype.ofFinite D
  have := FiniteField.pow_card (⟨x, hx⟩ : D)
  rw [← Nat.card_eq_fintype_card] at this
  exact congrArg Subtype.val this

theorem mem_subfield_iff_pow {D : Subfield F} {x : F} :
    x ∈ D ↔ x ^ Nat.card D = x := by
  have hD2 : 2 ≤ Nat.card D := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial D)
    omega
  refine ⟨pow_card_subfield D, fun hx => ?_⟩
  by_contra hxD
  have hle := card_pow_eq_self_le (F := F) hD2
  let f : Option D → {z : F // z ^ Nat.card D = z} := fun y =>
    Option.elim y ⟨x, hx⟩ fun d => ⟨d, pow_card_subfield D d.2⟩
  have hf : Function.Injective f := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exfalso
      have h' : x = (b : F) := congrArg Subtype.val h
      exact hxD (h' ▸ b.2)
    · exfalso
      have h' : (a : F) = x := congrArg Subtype.val h
      exact hxD (h' ▸ a.2)
    · have h' : ((f (some a) : {z : F // z ^ Nat.card D = z}) : F) = f (some b) :=
        congrArg Subtype.val h
      exact congrArg some (Subtype.ext h')
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option] at h1
  omega

theorem subfield_eq_of_card_eq {D D' : Subfield F} (h : Nat.card D = Nat.card D') : D = D' := by
  ext x
  rw [mem_subfield_iff_pow, mem_subfield_iff_pow, h]

end Subfields

section Forms

theorem exists_minimal_inv {P : Type} [AddCommGroup P] [Finite P] [Nontrivial P] {G : Type*}
    (act : G → P →+ P) :
    ∃ Y : AddSubgroup P, Y ≠ ⊥ ∧ (∀ g, ∀ y ∈ Y, act g y ∈ Y) ∧
      ∀ Y' : AddSubgroup P, Y' ≤ Y → (∀ g, ∀ y ∈ Y', act g y ∈ Y') → Y' = ⊥ ∨ Y' = Y := by
  obtain ⟨Y, hY⟩ := exists_minimal_of_wellFoundedLT
    (fun Y : AddSubgroup P => Y ≠ ⊥ ∧ ∀ g, ∀ y ∈ Y, act g y ∈ Y)
    ⟨⊤, top_ne_bot, fun _ _ _ => AddSubgroup.mem_top _⟩
  refine ⟨Y, hY.1.1, hY.1.2, fun Y' hle hinv => ?_⟩
  by_cases h : Y' = ⊥
  · exact Or.inl h
  · exact Or.inr (le_antisymm hle (hY.2 ⟨h, hinv⟩ hle))

variable {F : Type} [Field F] {P : Type} [AddCommGroup P] [Module F P]

theorem card_form {D : Subfield F} {k : ℕ} {b : Fin k → P} (hb : LinearIndependent F b)
    {Y : AddSubgroup P} (hbY : ∀ j, b j ∈ Y) (hDY : ∀ c ∈ D, ∀ y ∈ Y, c • y ∈ Y)
    (hspan : ∀ y ∈ Y, ∃ a : Fin k → F, (∀ j, a j ∈ D) ∧ y = ∑ j, a j • b j) :
    Nat.card Y = Nat.card D ^ k := by
  let f : (Fin k → D) → Y := fun a => ⟨∑ j, (a j : F) • b j,
    Y.sum_mem fun j _ => hDY _ (a j).2 _ (hbY j)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' h
      have h1 : ∑ j, (a j : F) • b j = ∑ j, (a' j : F) • b j := congrArg Subtype.val h
      have h2 := Fintype.linearIndependent_iff.mp hb (fun j => (a j : F) - a' j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self])
      funext j
      exact Subtype.ext (sub_eq_zero.mp (h2 j))
    · rintro ⟨y, hy⟩
      obtain ⟨a, haD, rfl⟩ := hspan y hy
      exact ⟨fun j => ⟨a j, haD j⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin k),
    Fintype.card_fin]

theorem mem_of_smul_mem {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)} {D : Subfield F}
    {Y : AddSubgroup P} (hY0 : Y ≠ ⊥)
    (hend : ∀ φ : P →+ P, (∀ y ∈ Y, φ y ∈ Y) → (∀ g, ∀ y ∈ Y, φ (ρ g y) = ρ g (φ y)) →
      ∃ c ∈ D, ∀ y ∈ Y, φ y = c • y)
    {c : F} (hc : ∀ y ∈ Y, c • y ∈ Y) : c ∈ D := by
  obtain ⟨d, hd, hcd⟩ := hend (DistribSMul.toAddMonoidHom P c) hc
    (fun g y _ => ((ρ g).map_smul c y).symm)
  obtain ⟨y, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hY0
  have h1 : (c - d) • (y : P) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hcd y y.2
  rcases smul_eq_zero.mp h1 with h | h
  · rwa [sub_eq_zero.mp h]
  · exact absurd (Subtype.ext h) hy0

end Forms

section Slices

variable {F : Type} [Field F] {V : Fin 2 → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module F (V i)]

theorem fin2_eq_or {i j k : Fin 2} (hij : i ≠ j) : k = i ∨ k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

@[expose] noncomputable def sliceML {i j : Fin 2} (hij : i ≠ j) (φ : Module.Dual F (V i)) :
    MultilinearMap F V (V j) where
  toFun m := φ (m i) • m j
  map_update_add' m k x y := by
    rcases fin2_eq_or (k := k) hij with rfl | rfl
    · simp [Function.update_of_ne hij.symm, add_smul]
    · simp [Function.update_of_ne hij]
  map_update_smul' m k c x := by
    rcases fin2_eq_or (k := k) hij with rfl | rfl
    · simp [Function.update_of_ne hij.symm, mul_smul]
    · simp [Function.update_of_ne hij, smul_comm c]

@[expose] noncomputable def slice {i j : Fin 2} (hij : i ≠ j) (φ : Module.Dual F (V i)) :
    (⨂[F] k, V k) →ₗ[F] V j :=
  PiTensorProduct.lift (sliceML hij φ)

theorem slice_tprod {i j : Fin 2} (hij : i ≠ j) (φ : Module.Dual F (V i)) (m : ∀ k, V k) :
    slice hij φ (PiTensorProduct.tprod F m) = φ (m i) • m j :=
  PiTensorProduct.lift.tprod m

theorem slice_factorEnd {i j : Fin 2} (hij : i ≠ j) (φ : Module.Dual F (V i))
    (g : Module.End F (V j)) (x : ⨂[F] k, V k) :
    slice hij φ (Offender.factorEnd j g x) = g (slice hij φ x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, Offender.factorEnd_tprod, slice_tprod, slice_tprod,
      Function.update_self, Function.update_of_ne hij]
    rw [LinearMap.map_smul, LinearMap.map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

@[expose] noncomputable def injAt (i : Fin 2) (m : ∀ k, V k) : V i →ₗ[F] ⨂[F] k, V k :=
  (PiTensorProduct.tprod F).toLinearMap m i

theorem injAt_apply (i : Fin 2) (m : ∀ k, V k) (v : V i) :
    injAt i m v = PiTensorProduct.tprod F (Function.update m i v) := rfl

theorem factorEnd_injAt (i : Fin 2) (m : ∀ k, V k) (f : Module.End F (V i)) (v : V i) :
    Offender.factorEnd i f (injAt i m v) = injAt i m (f v) := by
  rw [injAt_apply, injAt_apply, Offender.factorEnd_tprod, Function.update_idem,
    Function.update_self]

theorem injAt_injective (i : Fin 2) (m : ∀ k, V k) (hm : ∀ k, k ≠ i → m k ≠ 0) :
    Function.Injective (injAt (F := F) i m) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [Submodule.mem_bot]
  by_contra hv0
  apply Offender.tprod_ne_zero_of_ne_zero (m := Function.update m i v) _ hv
  intro k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self]
    exact hv0
  · rw [Function.update_of_ne hk]
    exact hm k hk

theorem slice_coord_01 [∀ k, Module.Finite F (V k)] (x : ⨂[F] k, V k)
    (a : Fin (Module.finrank F (V 0))) (c : Fin (Module.finrank F (V 1))) :
    coordLin (fun k => Module.finBasis F (V k)) x a c =
      (Module.finBasis F (V 1)).repr
        (slice (by decide : (0 : Fin 2) ≠ 1) ((Module.finBasis F (V 0)).coord a) x) c := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, coordLin_tprod, slice_tprod, Matrix.smul_apply, Finsupp.smul_apply,
      Matrix.vecMulVec_apply, Module.Basis.coord_apply, smul_eq_mul]
  | add x y hx hy => simp only [map_add, Matrix.add_apply, Finsupp.add_apply, hx, hy]

theorem slice_coord_10 [∀ k, Module.Finite F (V k)] (x : ⨂[F] k, V k)
    (a : Fin (Module.finrank F (V 0))) (c : Fin (Module.finrank F (V 1))) :
    coordLin (fun k => Module.finBasis F (V k)) x a c =
      (Module.finBasis F (V 0)).repr
        (slice (by decide : (1 : Fin 2) ≠ 0) ((Module.finBasis F (V 1)).coord c) x) a := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, coordLin_tprod, slice_tprod, Matrix.smul_apply, Finsupp.smul_apply,
      Matrix.vecMulVec_apply, Module.Basis.coord_apply, smul_eq_mul]
    ring
  | add x y hx hy => simp only [map_add, Matrix.add_apply, Finsupp.add_apply, hx, hy]

theorem eq_zero_of_slice [∀ k, Module.Finite F (V k)] {i j : Fin 2} (hij : i ≠ j)
    (x : ⨂[F] k, V k) (h : ∀ φ : Module.Dual F (V i), slice hij φ x = 0) : x = 0 := by
  apply (coordLin_bijective (fun k => Module.finBasis F (V k))).1
  rw [map_zero]
  ext a c
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rw [slice_coord_01, h, map_zero]
    rfl
  · rw [slice_coord_10, h, map_zero]
    rfl
  · exact absurd rfl hij

end Slices

section Transport

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] {V : Fin 2 → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
  [∀ i, Module.Finite F (V i)] [∀ i, Nontrivial (V i)]

@[expose] noncomputable def transMap (i : Fin 2) (e : Additive U ≃+ ⨂[F] k, V k)
    (g : MulAut U) : V i →+ ⨂[F] k, V k :=
  e.toAddMonoidHom.comp ((MulEquiv.toAdditive g).toAddMonoidHom.comp
    (e.symm.toAddMonoidHom.comp
      (injAt i fun k => (exists_ne (0 : V k)).choose).toAddMonoidHom))

omit [∀ i, Module.Finite F (V i)] in
theorem transMap_injective (i : Fin 2) (e : Additive U ≃+ ⨂[F] k, V k) (g : MulAut U) :
    Function.Injective (transMap i e g) := by
  have h1 : Function.Injective (injAt (F := F) i fun k => (exists_ne (0 : V k)).choose) :=
    injAt_injective i _ fun k _ => (exists_ne (0 : V k)).choose_spec
  intro a b h
  apply h1
  apply e.symm.injective
  apply (MulEquiv.toAdditive g).injective
  apply e.injective
  exact h

omit [∀ i, Module.Finite F (V i)] in
theorem transMap_intertwine {i j : Fin 2} (ρ : ∀ k, ↥(pair L₁ L₂ k) →* (V k ≃ₗ[F] V k))
    (e : Additive U ≃+ ⨂[F] k, V k)
    (hact : ∀ k (g : ↥(pair L₁ L₂ k)) (u : U), e (Additive.ofMul ((g : MulAut U) u)) =
      Offender.factorEnd k ((ρ k g : V k ≃ₗ[F] V k) : Module.End F (V k))
        (e (Additive.ofMul u)))
    (g : MulAut U) (l : ↥(pair L₁ L₂ i)) (k : ↥(pair L₁ L₂ j))
    (hk : (k : MulAut U) = g * l * g⁻¹) (y : V i) :
    transMap i e g (ρ i l y) =
      Offender.factorEnd j ((ρ j k : V j ≃ₗ[F] V j) : Module.End F (V j)) (transMap i e g y) := by
  set q : ∀ k, V k := fun k => (exists_ne (0 : V k)).choose
  set u : U := Additive.toMul (e.symm (injAt i q y)) with hu
  have hy : injAt i q y = e (Additive.ofMul u) := by
    rw [hu]
    exact (e.apply_symm_apply _).symm
  have h1 : injAt (F := F) i q (ρ i l y) = e (Additive.ofMul ((l : MulAut U) u)) := by
    rw [hact i l u, ← hy]
    exact (factorEnd_injAt i q _ y).symm
  have h2 : (g : MulAut U) ((l : MulAut U) u) = (k : MulAut U) (g u) := by
    rw [hk]
    simp [MulAut.mul_apply]
  show e (MulEquiv.toAdditive g (e.symm (injAt i q (ρ i l y)))) =
    Offender.factorEnd j _ (e (MulEquiv.toAdditive g (e.symm (injAt i q y))))
  rw [h1, AddEquiv.symm_apply_apply, hy, AddEquiv.symm_apply_apply]
  show e (Additive.ofMul (g ((l : MulAut U) u))) =
    Offender.factorEnd j _ (e (Additive.ofMul (g u)))
  rw [h2, hact j k]

omit [∀ i, Module.Finite F (V i)] in
theorem transMap_smul (i : Fin 2) (e : Additive U ≃+ ⨂[F] k, V k) (g : MulAut U)
    (τ : F ≃+* F) (hτ : ∀ (c : F) (x : ⨂[F] k, V k),
      e (Additive.ofMul (g (Additive.toMul (e.symm (c • x))))) =
        τ c • e (Additive.ofMul (g (Additive.toMul (e.symm x)))))
    (c : F) (y : V i) : transMap i e g (c • y) = τ c • transMap i e g y := by
  show e (MulEquiv.toAdditive g (e.symm (injAt i _ (c • y)))) =
    τ c • e (MulEquiv.toAdditive g (e.symm (injAt i _ y)))
  rw [map_smul]
  exact hτ c _

theorem exists_transport {i j : Fin 2} (hij : i ≠ j)
    (ρ : ∀ k, ↥(pair L₁ L₂ k) →* (V k ≃ₗ[F] V k)) (e : Additive U ≃+ ⨂[F] k, V k)
    (hact : ∀ k (g : ↥(pair L₁ L₂ k)) (u : U), e (Additive.ofMul ((g : MulAut U) u)) =
      Offender.factorEnd k ((ρ k g : V k ≃ₗ[F] V k) : Module.End F (V k))
        (e (Additive.ofMul u)))
    (g : MulAut U) (hg : ∀ k ∈ pair L₁ L₂ j, ∃ l ∈ pair L₁ L₂ i, k = g * l * g⁻¹)
    (hg' : ∀ l ∈ pair L₁ L₂ i, g * l * g⁻¹ ∈ pair L₁ L₂ j)
    (τ : F ≃+* F) (hτ : ∀ (c : F) (x : ⨂[F] k, V k),
      e (Additive.ofMul (g (Additive.toMul (e.symm (c • x))))) =
        τ c • e (Additive.ofMul (g (Additive.toMul (e.symm x)))))
    (Y : AddSubgroup (V i)) (hY0 : Y ≠ ⊥) (hYinv : ∀ l, ∀ y ∈ Y, ρ i l y ∈ Y)
    (hYmin : ∀ Y' : AddSubgroup (V i), Y' ≤ Y → (∀ l, ∀ y ∈ Y', ρ i l y ∈ Y') →
      Y' = ⊥ ∨ Y' = Y)
    (D : Subfield F) (hDY : ∀ c ∈ D, ∀ y ∈ Y, c • y ∈ Y) :
    ∃ Z : AddSubgroup (V j), Z ≠ ⊥ ∧ (∀ k, ∀ z ∈ Z, ρ j k z ∈ Z) ∧
      (∀ Z' : AddSubgroup (V j), Z' ≤ Z → (∀ k, ∀ z ∈ Z', ρ j k z ∈ Z') → Z' = ⊥ ∨ Z' = Z) ∧
      Nat.card Z = Nat.card Y ∧ ∀ c ∈ D, ∀ z ∈ Z, τ c • z ∈ Z := by
  set Θ := transMap i e g with hΘ
  have hΘinj : Function.Injective Θ := transMap_injective i e g
  set T : AddSubgroup (⨂[F] k, V k) := Y.map Θ with hT
  have hconj : ∀ l : ↥(pair L₁ L₂ i), ∀ y, Θ (ρ i l y) =
      Offender.factorEnd j ((ρ j ⟨g * l * g⁻¹, hg' l l.2⟩ : V j ≃ₗ[F] V j) : Module.End F (V j))
        (Θ y) := fun l y => transMap_intertwine ρ e hact g l _ rfl y
  have hTinv : ∀ k : ↥(pair L₁ L₂ j), ∀ x ∈ T,
      Offender.factorEnd j ((ρ j k : V j ≃ₗ[F] V j) : Module.End F (V j)) x ∈ T := by
    rintro k _ ⟨y, hy, rfl⟩
    obtain ⟨l, hl, hk⟩ := hg k k.2
    have hk' : k = ⟨g * l * g⁻¹, hg' l hl⟩ := Subtype.ext hk
    refine ⟨ρ i ⟨l, hl⟩ y, hYinv _ y hy, ?_⟩
    rw [hk']
    exact hconj ⟨l, hl⟩ y
  have hTmin : ∀ T' : AddSubgroup (⨂[F] k, V k), T' ≤ T → (∀ k : ↥(pair L₁ L₂ j), ∀ x ∈ T',
      Offender.factorEnd j ((ρ j k : V j ≃ₗ[F] V j) : Module.End F (V j)) x ∈ T') →
      T' = ⊥ ∨ T' = T := by
    intro T' hle hinv
    rcases hYmin (T'.comap Θ ⊓ Y) inf_le_right (fun l y hy => ⟨by
        show Θ (ρ i l y) ∈ T'
        rw [hconj]
        exact hinv _ _ hy.1, hYinv l y hy.2⟩) with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hle hx
      have : y ∈ T'.comap Θ ⊓ Y := ⟨hx, hy⟩
      rw [h, AddSubgroup.mem_bot] at this
      rw [this, map_zero, AddSubgroup.mem_bot]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨y, hy, rfl⟩
      have : y ∈ T'.comap Θ ⊓ Y := by rw [h]; exact hy
      exact this.1
  obtain ⟨y₀, hy₀⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hY0
  have hx₀ : Θ y₀ ≠ 0 := fun h => hy₀ (Subtype.ext (hΘinj (h.trans (map_zero Θ).symm)))
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F (V i), slice hij φ (Θ y₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx₀ (eq_zero_of_slice hij _ hall)
  set σl := slice hij φ with hσl
  have hσinv : ∀ (k : ↥(pair L₁ L₂ j)) x, σl (Offender.factorEnd j
      ((ρ j k : V j ≃ₗ[F] V j) : Module.End F (V j)) x) = ρ j k (σl x) := fun k x =>
    slice_factorEnd hij φ _ x
  have hker : ∀ x ∈ T, σl x = 0 → x = 0 := by
    have hK := hTmin (T ⊓ (LinearMap.ker σl).toAddSubgroup) inf_le_left (fun k x hx =>
      ⟨hTinv k x hx.1, show σl _ = 0 by rw [hσinv, show σl x = 0 from hx.2, map_zero]⟩)
    rcases hK with h | h
    · intro x hx hσx
      have : x ∈ T ⊓ (LinearMap.ker σl).toAddSubgroup := ⟨hx, hσx⟩
      rwa [h, AddSubgroup.mem_bot] at this
    · exfalso
      have : Θ y₀ ∈ T ⊓ (LinearMap.ker σl).toAddSubgroup := by
        rw [h]
        exact ⟨y₀, y₀.2, rfl⟩
      exact hφ this.2
  set Z : AddSubgroup (V j) := T.map σl.toAddMonoidHom with hZ
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have : σl (Θ y₀) ∈ Z := ⟨Θ y₀, ⟨y₀, y₀.2, rfl⟩, rfl⟩
    rw [h, AddSubgroup.mem_bot] at this
    exact hφ this
  · rintro k _ ⟨x, hx, rfl⟩
    exact ⟨_, hTinv k x hx, hσinv k x⟩
  · intro Z' hle hinv
    rcases hTmin (T ⊓ Z'.comap σl.toAddMonoidHom) inf_le_left (fun k x hx =>
      ⟨hTinv k x hx.1, show σl _ ∈ Z' by rw [hσinv]; exact hinv k _ hx.2⟩) with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hle hz
      have : x ∈ T ⊓ Z'.comap σl.toAddMonoidHom := ⟨hx, hz⟩
      rw [h, AddSubgroup.mem_bot] at this
      rw [AddSubgroup.mem_bot]
      show σl x = 0
      rw [this, map_zero]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ T ⊓ Z'.comap σl.toAddMonoidHom := by rw [h]; exact hx
      exact this.2
  · have h1 : Nat.card Z = Nat.card T := by
      refine (Nat.card_congr (Equiv.ofBijective (fun x : T => (⟨σl x, x, x.2, rfl⟩ : Z))
        ⟨fun a b hab => ?_, ?_⟩)).symm
      · have h2 : σl ((a : ⨂[F] k, V k) - b) = 0 := by
          rw [map_sub, sub_eq_zero]
          exact congrArg Subtype.val hab
        exact Subtype.ext (sub_eq_zero.mp (hker _ (T.sub_mem a.2 b.2) h2))
      · rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [h1, hT, AddSubgroup.card_map_of_injective hΘinj]
  · rintro c hc _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨Θ (c • y), ⟨c • y, hDY c hc y hy, rfl⟩, ?_⟩
    show σl (Θ (c • y)) = τ c • σl (Θ y)
    rw [transMap_smul i e g τ hτ, map_smul]

end Transport

section Common

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] {V : Fin 2 → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module F (V i)] [∀ i, Module.Finite F (V i)] [∀ i, Nontrivial (V i)]

@[expose] def IsForm {G : Type*} [Group G] {P : Type} [AddCommGroup P] [Module F P]
    (ρ : G →* (P ≃ₗ[F] P)) (Y : AddSubgroup P) (D : Subfield F) {k : ℕ} (b : Fin k → P) :
    Prop :=
  Y ≠ ⊥ ∧ (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) ∧
    (∀ Y' : AddSubgroup P, Y' ≤ Y → (∀ g, ∀ y ∈ Y', ρ g y ∈ Y') → Y' = ⊥ ∨ Y' = Y) ∧
    (∀ j, b j ∈ Y) ∧ LinearIndependent F b ∧ Submodule.span F (Set.range b) = ⊤ ∧
    (∀ c ∈ D, ∀ y ∈ Y, c • y ∈ Y) ∧
    (∀ y ∈ Y, ∃ a : Fin k → F, (∀ j, a j ∈ D) ∧ y = ∑ j, a j • b j) ∧
    (∀ φ : P →+ P, (∀ y ∈ Y, φ y ∈ Y) → (∀ g, ∀ y ∈ Y, φ (ρ g y) = ρ g (φ y)) →
      ∃ c ∈ D, ∀ y ∈ Y, φ y = c • y)

theorem exists_isForm {G : Type*} [Group G] {P : Type} [AddCommGroup P] [Module F P]
    [Module.Finite F P] [Nontrivial P] (ρ : G →* (P ≃ₗ[F] P))
    (hspan : Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    (Y : AddSubgroup P) (hY0 : Y ≠ ⊥) (hYinv : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    (hYmin : ∀ Y' : AddSubgroup P, Y' ≤ Y → (∀ g, ∀ y ∈ Y', ρ g y ∈ Y') → Y' = ⊥ ∨ Y' = Y) :
    ∃ (D : Subfield F) (k : ℕ) (b : Fin k → P), IsForm ρ Y D b := by
  obtain ⟨D, k, b, h1, h2, h3, h4, h5, h6⟩ :=
    exists_subfield_form ρ hspan Y hY0 hYinv hYmin
  exact ⟨D, k, b, hY0, hYinv, hYmin, h1, h2, h3, h4, h5, h6⟩

omit [Fintype F] in
theorem IsForm.card {G : Type*} [Group G] {P : Type} [AddCommGroup P] [Module F P]
    {ρ : G →* (P ≃ₗ[F] P)} {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P}
    (h : IsForm ρ Y D b) : Nat.card Y = Nat.card D ^ k :=
  card_form h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1

omit [Fintype F] in
theorem IsForm.k_eq {G : Type*} [Group G] {P : Type} [AddCommGroup P] [Module F P]
    [Module.Finite F P] {ρ : G →* (P ≃ₗ[F] P)} {Y : AddSubgroup P} {D : Subfield F} {k : ℕ}
    {b : Fin k → P} (h : IsForm ρ Y D b) : k = Module.finrank F P := by
  have h1 := finrank_span_eq_card h.2.2.2.2.1
  rw [h.2.2.2.2.2.1, finrank_top, Fintype.card_fin] at h1
  exact h1.symm

omit [Fintype F] in
theorem IsForm.mem_of_smul {G : Type*} [Group G] {P : Type} [AddCommGroup P] [Module F P]
    {ρ : G →* (P ≃ₗ[F] P)} {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P}
    (h : IsForm ρ Y D b) {c : F} (hc : ∀ y ∈ Y, c • y ∈ Y) : c ∈ D :=
  mem_of_smul_mem h.1 h.2.2.2.2.2.2.2.2 hc

theorem exists_common_forms (ρ : ∀ k, ↥(pair L₁ L₂ k) →* (V k ≃ₗ[F] V k))
    (e : Additive U ≃+ ⨂[F] k, V k)
    (hact : ∀ k (g : ↥(pair L₁ L₂ k)) (u : U), e (Additive.ofMul ((g : MulAut U) u)) =
      Offender.factorEnd k ((ρ k g : V k ≃ₗ[F] V k) : Module.End F (V k))
        (e (Additive.ofMul u)))
    (hspan : ∀ k, Submodule.span F
      (Set.range fun g => ((ρ k g : V k ≃ₗ[F] V k) : Module.End F (V k))) = ⊤)
    (s : MulAut U)
    (hs01 : ∀ k ∈ pair L₁ L₂ 1, ∃ l ∈ pair L₁ L₂ 0, k = s * l * s⁻¹)
    (hs01' : ∀ l ∈ pair L₁ L₂ 0, s * l * s⁻¹ ∈ pair L₁ L₂ 1)
    (hs10 : ∀ k ∈ pair L₁ L₂ 0, ∃ l ∈ pair L₁ L₂ 1, k = s⁻¹ * l * s⁻¹⁻¹)
    (hs10' : ∀ l ∈ pair L₁ L₂ 1, s⁻¹ * l * s⁻¹⁻¹ ∈ pair L₁ L₂ 0)
    (τ τ' : F ≃+* F)
    (hτ : ∀ (c : F) (x : ⨂[F] k, V k),
      e (Additive.ofMul (s (Additive.toMul (e.symm (c • x))))) =
        τ c • e (Additive.ofMul (s (Additive.toMul (e.symm x)))))
    (hτ' : ∀ (c : F) (x : ⨂[F] k, V k),
      e (Additive.ofMul (s⁻¹ (Additive.toMul (e.symm (c • x))))) =
        τ' c • e (Additive.ofMul (s⁻¹ (Additive.toMul (e.symm x))))) :
    ∃ (D : Subfield F) (d : ℕ) (Y : AddSubgroup (V 0)) (Z : AddSubgroup (V 1))
      (b₀ : Fin d → V 0) (b₁ : Fin d → V 1), IsForm (ρ 0) Y D b₀ ∧ IsForm (ρ 1) Z D b₁ := by
  have : ∀ k, Finite (V k) := fun k => Module.finite_of_finite F
  obtain ⟨Y, hY0, hYinv, hYmin⟩ := exists_minimal_inv
    (fun l : ↥(pair L₁ L₂ 0) => ((ρ 0 l : V 0 ≃ₗ[F] V 0) : V 0 →ₗ[F] V 0).toAddMonoidHom)
  obtain ⟨D₀, k₀, b₀, hF0⟩ := exists_isForm (ρ 0) (hspan 0) Y hY0 hYinv hYmin
  obtain ⟨Z, hZ0, hZinv, hZmin, hZcard, hZstab⟩ := exists_transport (by decide) ρ e hact s
    hs01 hs01' τ hτ Y hY0 hYinv hYmin D₀ hF0.2.2.2.2.2.2.1
  obtain ⟨D₁, k₁, b₁, hF1⟩ := exists_isForm (ρ 1) (hspan 1) Z hZ0 hZinv hZmin
  obtain ⟨Y', hY'0, hY'inv, hY'min, hY'card, hY'stab⟩ := exists_transport (by decide) ρ e hact
    s⁻¹ hs10 hs10' τ' hτ' Z hZ0 hZinv hZmin D₁ hF1.2.2.2.2.2.2.1
  obtain ⟨D₀', k₀', b₀', hF0'⟩ := exists_isForm (ρ 0) (hspan 0) Y' hY'0 hY'inv hY'min
  have hk₀ : k₀' = k₀ := hF0'.k_eq.trans hF0.k_eq.symm
  have hk₀pos : k₀ ≠ 0 := by
    rw [hF0.k_eq]
    exact (Module.finrank_pos (R := F) (M := V 0)).ne'
  have hle₁ : Nat.card D₀ ≤ Nat.card D₁ := Nat.card_le_card_of_injective
    (fun c : D₀ => (⟨τ c, hF1.mem_of_smul (hZstab c c.2)⟩ : D₁))
    (fun a b h => Subtype.ext (τ.injective (congrArg Subtype.val h)))
  have hle₂ : Nat.card D₁ ≤ Nat.card D₀' := Nat.card_le_card_of_injective
    (fun c : D₁ => (⟨τ' c, hF0'.mem_of_smul (hY'stab c c.2)⟩ : D₀'))
    (fun a b h => Subtype.ext (τ'.injective (congrArg Subtype.val h)))
  have hcard' : Nat.card D₀' = Nat.card D₀ := by
    have h1 : Nat.card D₀' ^ k₀ = Nat.card D₀ ^ k₀ := by
      rw [← hk₀, ← hF0'.card, hk₀, hY'card, hZcard, hF0.card]
    exact Nat.pow_left_injective hk₀pos h1
  have hD : D₁ = D₀ := subfield_eq_of_card_eq (by omega)
  subst hD
  have hk : k₁ = k₀ := by
    have h1 : Nat.card D₁ ^ k₁ = Nat.card D₁ ^ k₀ := by
      rw [← hF1.card, hZcard, hF0.card]
    have h2 : 2 ≤ Nat.card D₁ := by
      have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial D₁)
      omega
    exact Nat.pow_right_injective h2 h1
  subst hk
  exact ⟨D₁, k₁, Y, Z, b₀, b₁, hF0, hF1⟩

end Common

section Top

variable {F : Type} [Field F] {P : Type} [AddCommGroup P] [Module F P]

@[expose] noncomputable def IsForm.basis {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b) :
    Module.Basis (Fin k) F P :=
  Module.Basis.mk h.2.2.2.2.1 h.2.2.2.2.2.1.ge

theorem IsForm.basis_apply {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    (j : Fin k) : h.basis j = b j :=
  Module.Basis.mk_apply _ _ j

theorem IsForm.repr_mem {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    {y : P} (hy : y ∈ Y) (j : Fin k) : h.basis.repr y j ∈ D := by
  obtain ⟨a, haD, rfl⟩ := h.2.2.2.2.2.2.2.1 y hy
  have : ∑ i, a i • b i = h.basis.equivFun.symm a := by
    rw [Module.Basis.equivFun_symm_apply]
    simp only [IsForm.basis_apply]
  rw [this, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  exact haD j

theorem IsForm.matrix_mem {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    (g : G) (a c : Fin k) :
    LinearMap.toMatrix h.basis h.basis ((ρ g : P ≃ₗ[F] P) : P →ₗ[F] P) a c ∈ D := by
  rw [LinearMap.toMatrix_apply, IsForm.basis_apply]
  exact h.repr_mem (h.2.1 g _ (h.2.2.2.1 c)) a

theorem IsForm.eq_top_of_top {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    (hD : D = ⊤) : Y = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [← h.basis.sum_repr v]
  refine Y.sum_mem fun j _ => ?_
  rw [IsForm.basis_apply]
  have hmem : ∀ c : F, c ∈ D := fun c => by rw [hD]; exact Subfield.mem_top c
  exact h.2.2.2.2.2.2.1 _ (hmem _) _ (h.2.2.2.1 j)

end Top

section TopU

variable {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] {V : Fin 2 → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]

@[expose] noncomputable def formBasis {G₀ G₁ : Type*} [Group G₀] [Group G₁]
    {ρ₀ : G₀ →* (V 0 ≃ₗ[F] V 0)} {ρ₁ : G₁ →* (V 1 ≃ₗ[F] V 1)} {Y : AddSubgroup (V 0)}
    {Z : AddSubgroup (V 1)} {D : Subfield F} {d : ℕ} {b₀ : Fin d → V 0} {b₁ : Fin d → V 1}
    (h₀ : IsForm ρ₀ Y D b₀) (h₁ : IsForm ρ₁ Z D b₁) : ∀ i, Module.Basis (Fin d) F (V i) :=
  Fin.cons h₀.basis
    (Fin.cons (α := fun j : Fin 1 => Module.Basis (Fin d) F (V j.succ)) h₁.basis finZeroElim)

theorem form_eq_top (ρ : ∀ k, ↥(pair L₁ L₂ k) →* (V k ≃ₗ[F] V k))
    (e : Additive U ≃+ ⨂[F] k, V k)
    (hact : ∀ k (g : ↥(pair L₁ L₂ k)) (u : U), e (Additive.ofMul ((g : MulAut U) u)) =
      Offender.factorEnd k ((ρ k g : V k ≃ₗ[F] V k) : Module.End F (V k))
        (e (Additive.ofMul u)))
    (hirr : ∀ J : Subgroup U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤)
    {D : Subfield F} {d : ℕ} {Y : AddSubgroup (V 0)} {Z : AddSubgroup (V 1)}
    {b₀ : Fin d → V 0} {b₁ : Fin d → V 1} (h₀ : IsForm (ρ 0) Y D b₀)
    (h₁ : IsForm (ρ 1) Z D b₁) (hd : 0 < d) : D = ⊤ := by
  set B := formBasis h₀ h₁ with hB
  set Wf : AddSubgroup (⨂[F] k, V k) :=
    { carrier := {x | ∀ a c, coordLin B x a c ∈ D}
      zero_mem' := fun a c => by rw [map_zero]; exact D.zero_mem
      add_mem' := fun hx hy a c => by
        rw [map_add, Matrix.add_apply]
        exact D.add_mem (hx a c) (hy a c)
      neg_mem' := fun hx a c => by rw [map_neg, Matrix.neg_apply]; exact D.neg_mem (hx a c) }
  set W₀ : Subgroup U := subOf (Wf.comap e.toAddMonoidHom)
  have hmem₀ : ∀ (l : ↥(pair L₁ L₂ 0)) a c, matOf B 0 ((ρ 0 l : V 0 ≃ₗ[F] V 0) :
      Module.End F (V 0)) a c ∈ D := fun l a c => h₀.matrix_mem l a c
  have hmem₁ : ∀ (k : ↥(pair L₁ L₂ 1)) a c, matOf B 1 ((ρ 1 k : V 1 ≃ₗ[F] V 1) :
      Module.End F (V 1)) a c ∈ D := fun k a c => h₁.matrix_mem k a c
  have hinv₀ : IsInvBy L₁ W₀ := by
    intro l hl u hu a c
    show coordLin B (e (Additive.ofMul (l u))) a c ∈ D
    rw [hact 0 ⟨l, hl⟩ u, coordLin_factorEnd_zero, Matrix.mul_apply]
    exact D.sum_mem fun m _ => D.mul_mem (hmem₀ ⟨l, hl⟩ a m) (hu m c)
  have hinv₁ : IsInvBy L₂ W₀ := by
    intro k hk u hu a c
    show coordLin B (e (Additive.ofMul (k u))) a c ∈ D
    rw [hact 1 ⟨k, hk⟩ u, coordLin_factorEnd_one, Matrix.mul_apply]
    exact D.sum_mem fun m _ => D.mul_mem (hu a m) (hmem₁ ⟨k, hk⟩ c m)
  set x₀ : ⨂[F] k, V k := PiTensorProduct.tprod F fun i => B i ⟨0, hd⟩
  have hx₀ : ∀ a c, coordLin B x₀ a c = (if a = ⟨0, hd⟩ then 1 else 0) *
      (if c = ⟨0, hd⟩ then 1 else 0) := by
    intro a c
    rw [coordLin_tprod, Matrix.vecMulVec_apply, Module.Basis.repr_self, Module.Basis.repr_self,
      Finsupp.single_apply, Finsupp.single_apply]
    simp only [eq_comm]
  have hW₀ : W₀ = ⊤ := by
    rcases hirr W₀ (isInvBy_sup hinv₀ hinv₁) with h | h
    · exfalso
      have hu : Additive.toMul (e.symm x₀) ∈ W₀ := by
        intro a c
        show coordLin B (e (e.symm x₀)) a c ∈ D
        rw [AddEquiv.apply_symm_apply, hx₀]
        split_ifs <;> simp
      rw [h, Subgroup.mem_bot] at hu
      have hx0 : x₀ = 0 := by
        rw [← e.apply_symm_apply x₀]
        have : e.symm x₀ = 0 := hu
        rw [this, map_zero]
      exact Offender.tprod_ne_zero_of_ne_zero (fun i => (B i).ne_zero _) hx0
    · exact h
  rw [eq_top_iff]
  intro c _
  have hu : Additive.toMul (e.symm (c • x₀)) ∈ W₀ := hW₀ ▸ Subgroup.mem_top _
  have h1 := hu ⟨0, hd⟩ ⟨0, hd⟩
  change coordLin B (e (e.symm (c • x₀))) ⟨0, hd⟩ ⟨0, hd⟩ ∈ D at h1
  rw [AddEquiv.apply_symm_apply, map_smul, Matrix.smul_apply, hx₀] at h1
  simpa using h1

end TopU

section Coords

variable {F : Type} [Field F] {P : Type} [AddCommGroup P] [Module F P]

theorem IsForm.equivFun_apply_rho {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    (g : G) (v : P) :
    h.basis.equivFun (ρ g v) =
      LinearMap.toMatrix h.basis h.basis ((ρ g : P ≃ₗ[F] P) : P →ₗ[F] P) *ᵥ h.basis.equivFun v := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rfl

theorem IsForm.irr_coord {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    (hY : Y = ⊤) (S : AddSubgroup (Fin k → F))
    (hS : ∀ g : G, ∀ v ∈ S,
      LinearMap.toMatrix h.basis h.basis ((ρ g : P ≃ₗ[F] P) : P →ₗ[F] P) *ᵥ v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  set E := h.basis.equivFun
  rcases h.2.2.1 (S.comap E.toLinearMap.toAddMonoidHom) (hY ▸ le_top) (fun g v hv => by
      show E (ρ g v) ∈ S
      rw [h.equivFun_apply_rho]
      exact hS g _ hv) with h1 | h1
  · left
    rw [eq_bot_iff]
    intro w hw
    have : E.symm w ∈ S.comap E.toLinearMap.toAddMonoidHom := by
      show E (E.symm w) ∈ S
      rwa [LinearEquiv.apply_symm_apply]
    rw [h1, AddSubgroup.mem_bot] at this
    rw [AddSubgroup.mem_bot, ← E.apply_symm_apply w, this, map_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have : E.symm w ∈ S.comap E.toLinearMap.toAddMonoidHom := by
      rw [h1, hY]
      exact AddSubgroup.mem_top _
    have h2 : E (E.symm w) ∈ S := this
    rwa [LinearEquiv.apply_symm_apply] at h2

theorem IsForm.end_coord {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}
    {Y : AddSubgroup P} {D : Subfield F} {k : ℕ} {b : Fin k → P} (h : IsForm ρ Y D b)
    (hY : Y = ⊤) (φ : (Fin k → F) →+ (Fin k → F))
    (hφ : ∀ (g : G) v, φ (LinearMap.toMatrix h.basis h.basis ((ρ g : P ≃ₗ[F] P) : P →ₗ[F] P) *ᵥ v) =
      LinearMap.toMatrix h.basis h.basis ((ρ g : P ≃ₗ[F] P) : P →ₗ[F] P) *ᵥ φ v) :
    ∃ c : F, ∀ v, φ v = c • v := by
  set E := h.basis.equivFun
  let φ' : P →+ P := E.symm.toLinearMap.toAddMonoidHom.comp (φ.comp E.toLinearMap.toAddMonoidHom)
  obtain ⟨c, -, hc⟩ := h.2.2.2.2.2.2.2.2 φ' (fun _ _ => hY ▸ AddSubgroup.mem_top _)
    (fun g y _ => by
      show E.symm (φ (E (ρ g y))) = ρ g (E.symm (φ (E y)))
      rw [h.equivFun_apply_rho, hφ]
      apply E.injective
      rw [LinearEquiv.apply_symm_apply, h.equivFun_apply_rho, LinearEquiv.apply_symm_apply])
  refine ⟨c, fun v => ?_⟩
  have h1 := hc (E.symm v) (hY ▸ AddSubgroup.mem_top _)
  have h2 : E (φ' (E.symm v)) = E (c • E.symm v) := by rw [h1]
  simpa [φ'] using h2

end Coords

section Model

variable {U : Type} [CommGroup U] [Finite U]

@[expose] noncomputable def glRep {G : Type*} [Group G] {F : Type} [Field F] {P : Type}
    [AddCommGroup P] [Module F P] {d : ℕ} (B : Module.Basis (Fin d) F P)
    (ρ : G →* (P ≃ₗ[F] P)) : G →* Matrix.GeneralLinearGroup (Fin d) F :=
  (Units.map (LinearMap.toMatrixAlgEquiv B).toMonoidHom).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F P).symm.toMonoidHom.comp ρ)

theorem exists_matModel [Nontrivial U] (hU : ∀ u : U, u ^ 2 = 1) {L₁ L₂ : Subgroup (MulAut U)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hirr : ∀ J : Subgroup U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤)
    (s : MulAut U) (hs₁ : L₁.map (MulAut.conj s).toMonoidHom = L₂)
    (hs₂ : L₂.map (MulAut.conj s).toMonoidHom = L₁) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (d : ℕ),
      0 < d ∧ Nonempty (MatModel L₁ L₂ F d) := by
  obtain ⟨F, _, _, _, V, _, _, ρ, e, hnt, hfin, hact, hspan, hsemi⟩ :=
    exists_tensor_decomp hU hcomm hirr
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have : ∀ i, Module.Finite F (V i) := fun i => Module.Finite.of_finite
  have hs₁' : L₂.map (MulAut.conj s⁻¹).toMonoidHom = L₁ := by
    rw [← hs₁, Subgroup.map_map]
    convert Subgroup.map_id L₁ using 2
    ext x u
    simp [MulAut.conj_apply]
  have hsup : (L₁ ⊔ L₂).map (MulAut.conj s).toMonoidHom = L₁ ⊔ L₂ := by
    rw [Subgroup.map_sup, hs₁, hs₂, sup_comm]
  have hsup' : (L₁ ⊔ L₂).map (MulAut.conj s⁻¹).toMonoidHom = L₁ ⊔ L₂ := by
    have hs₂' : L₁.map (MulAut.conj s⁻¹).toMonoidHom = L₂ := by
      rw [← hs₂, Subgroup.map_map]
      convert Subgroup.map_id L₂ using 2
      ext x u
      simp [MulAut.conj_apply]
    rw [Subgroup.map_sup, hs₁', hs₂', sup_comm]
  obtain ⟨τ, hτ⟩ := hsemi s hsup
  obtain ⟨τ', hτ'⟩ := hsemi s⁻¹ hsup'
  have hs01 : ∀ k ∈ pair L₁ L₂ 1, ∃ l ∈ pair L₁ L₂ 0, k = s * l * s⁻¹ := by
    intro k hk
    have hk' : k ∈ L₁.map (MulAut.conj s).toMonoidHom := hs₁ ▸ hk
    obtain ⟨l, hl, rfl⟩ := hk'
    exact ⟨l, hl, rfl⟩
  have hs01' : ∀ l ∈ pair L₁ L₂ 0, s * l * s⁻¹ ∈ pair L₁ L₂ 1 := fun l hl => by
    show s * l * s⁻¹ ∈ L₂
    rw [← hs₁]
    exact ⟨l, hl, rfl⟩
  have hs10 : ∀ k ∈ pair L₁ L₂ 0, ∃ l ∈ pair L₁ L₂ 1, k = s⁻¹ * l * s⁻¹⁻¹ := by
    intro k hk
    refine ⟨s * k * s⁻¹, hs01' k hk, ?_⟩
    group
  have hs10' : ∀ l ∈ pair L₁ L₂ 1, s⁻¹ * l * s⁻¹⁻¹ ∈ pair L₁ L₂ 0 := fun l hl => by
    show s⁻¹ * l * s⁻¹⁻¹ ∈ L₁
    rw [← hs₁']
    exact ⟨l, hl, rfl⟩
  obtain ⟨D, d, Y, Z, b₀, b₁, h₀, h₁⟩ :=
    exists_common_forms ρ e hact hspan s hs01 hs01' hs10 hs10' τ τ' hτ hτ'
  have hd : 0 < d := by
    rw [h₀.k_eq]
    exact Module.finrank_pos
  have hD : D = ⊤ := form_eq_top ρ e hact hirr h₀ h₁ hd
  have hY : Y = ⊤ := h₀.eq_top_of_top hD
  have hZ : Z = ⊤ := h₁.eq_top_of_top hD
  set B := formBasis h₀ h₁ with hB
  set Ξ : Additive U ≃+ Matrix (Fin d) (Fin d) F := e.trans (coordEquiv B).toAddEquiv with hΞ
  let β : U ≃* Multiplicative (Matrix (Fin d) (Fin d) F) :=
    { toFun := fun u => Multiplicative.ofAdd (Ξ (Additive.ofMul u))
      invFun := fun X => Additive.toMul (Ξ.symm (Multiplicative.toAdd X))
      left_inv := fun u => by simp
      right_inv := fun X => by simp
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (Ξ (Additive.ofMul a + Additive.ofMul b)) = _
        rw [map_add, ofAdd_add] }
  have hβ : ∀ u, β u = Multiplicative.ofAdd (coordLin B (e (Additive.ofMul u))) := fun _ => rfl
  have hact₁ : ∀ (l : ↥L₁) (u : U), β ((l : MulAut U) u) = Multiplicative.ofAdd
      (((glRep (B 0) (ρ 0) l : Matrix.GeneralLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β u)) := by
    intro l u
    rw [hβ, hβ, toAdd_ofAdd, hact 0 l u, coordLin_factorEnd_zero]
    rfl
  have hact₂ : ∀ (k : ↥L₂) (u : U), β ((k : MulAut U) u) = Multiplicative.ofAdd
      (Multiplicative.toAdd (β u) * ((glRep (B 1) (ρ 1) k : Matrix.GeneralLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F)ᵀ) := by
    intro k u
    rw [hβ, hβ, toAdd_ofAdd, hact 1 k u, coordLin_factorEnd_one]
    rfl
  have hinj : ∀ {G : Subgroup (MulAut U)} (R : ↥G →* Matrix.GeneralLinearGroup (Fin d) F)
      (f : Matrix (Fin d) (Fin d) F → Matrix (Fin d) (Fin d) F → Matrix (Fin d) (Fin d) F),
      (∀ (g : ↥G) u, β ((g : MulAut U) u) = Multiplicative.ofAdd
        (f (R g) (Multiplicative.toAdd (β u)))) → Function.Injective R := by
    intro G R f hf g g' hgg
    apply Subtype.ext
    apply MulEquiv.ext
    intro u
    apply β.injective
    rw [hf, hf, hgg]
  have hspanM : ∀ i, Submodule.span F (Set.range fun g : ↥(pair L₁ L₂ i) =>
      ((glRep (B i) (ρ i) g : Matrix.GeneralLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F)) = ⊤ := by
    intro i
    have h1 : (Set.range fun g : ↥(pair L₁ L₂ i) =>
        ((glRep (B i) (ρ i) g : Matrix.GeneralLinearGroup (Fin d) F) :
          Matrix (Fin d) (Fin d) F)) =
        (LinearMap.toMatrix (B i) (B i)) '' Set.range fun g =>
          ((ρ i g : V i ≃ₗ[F] V i) : Module.End F (V i)) := by
      rw [← Set.range_comp]
      rfl
    have h2 := Submodule.span_image (LinearMap.toMatrix (B i) (B i)).toLinearMap
      (s := Set.range fun g => ((ρ i g : V i ≃ₗ[F] V i) : Module.End F (V i)))
    rw [LinearEquiv.coe_coe] at h2
    rw [h1, h2, hspan i, Submodule.map_top]
    exact LinearEquiv.range _
  exact ⟨F, inferInstance, inferInstance, inferInstance, d, hd, ⟨{
    β := β
    R₁ := glRep (B 0) (ρ 0)
    R₂ := glRep (B 1) (ρ 1)
    act₁ := hact₁
    act₂ := hact₂
    inj₁ := hinj (glRep (B 0) (ρ 0)) (fun A X => A * X) hact₁
    inj₂ := hinj (glRep (B 1) (ρ 1)) (fun A X => X * Aᵀ) hact₂
    span₁ := hspanM 0
    span₂ := hspanM 1
    irr₁ := fun S hS => h₀.irr_coord hY S hS
    end₁ := fun φ hφ => h₀.end_coord hY φ hφ
    irr₂ := fun S hS => h₁.irr_coord hZ S hS
    end₂ := fun φ hφ => h₁.end_coord hZ φ hφ }⟩⟩

end Model

end CFSG.Quasithin.SmithD37
