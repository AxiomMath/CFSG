module

public import CFSG.Quasithin.MS93.ML3Stmt

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F]

@[expose] def lnStab : Subgroup (SL3 F) where
  carrier := {g | ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0}
  mul_mem' := fun {g h} hg hh => by
    change ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((h : SL3 F) : Matrix _ _ F) ∈
      {A : Matrix (Fin 3) (Fin 3) F | A 2 0 = 0 ∧ A 2 1 = 0}
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hh.1, hh.2]
    simp
  one_mem' := by
    change ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ _
    simp
  inv_mem' := fun {g} hg => by
    change ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [hg.1, hg.2]

theorem mem_lnStab {g : SL3 F} : g ∈ (lnStab : Subgroup (SL3 F)) ↔
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
  Iff.rfl

@[expose] noncomputable def tor (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : SL3 F :=
  ⟨Matrix.diagonal ![a, b, (a * b)⁻¹], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp⟩

theorem coe_tor (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((tor a b ha hb : SL3 F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, b, (a * b)⁻¹] :=
  rfl

theorem tor_conj_rootElt (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) (i j : Fin 3) (c : F) :
    tor a b ha hb * rootElt i j c * (tor a b ha hb)⁻¹ =
      rootElt i j (![a, b, (a * b)⁻¹] i * (![a, b, (a * b)⁻¹] j)⁻¹ * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp [rootElt_self]
  apply Subtype.ext
  change ((tor a b ha hb : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt i j c : SL3 F) :
      Matrix _ _ F) = ((rootElt i j _ : SL3 F) : Matrix _ _ F) *
      ((tor a b ha hb : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt hij, coe_rootElt hij, coe_tor]
  set d := ![a, b, (a * b)⁻¹] with hd_def
  have hd : ∀ k, d k ≠ 0 := by
    intro k; fin_cases k <;> simp [d, ha, hb]
  ext k l
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases hkl : k = l
  · subst hkl
    have : ¬ (i = k ∧ j = k) := fun h => hij (h.1.trans h.2.symm)
    simp [this]
  · by_cases h : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hkl]
      simp only [and_self, ite_true, zero_add]
      field_simp [hd j]
    · simp [hkl, h]

theorem tor_mem_lnStab (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    tor a b ha hb ∈ (lnStab : Subgroup (SL3 F)) := by
  simp [mem_lnStab, coe_tor]

theorem tor_mem_ptStab (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    tor a b ha hb ∈ (ptStab : Subgroup (SL3 F)) := by
  change ((tor a b ha hb : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ _
  simp [coe_tor]

theorem tor_mulVec_e0 (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((tor a b ha hb : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = a • ![1, 0, 0] := by
  rw [coe_tor]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem sl3_ext {g g' : SL3 F}
    (h : ∀ v : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) : g = g' :=
  Subtype.ext (Matrix.ext_of_mulVec_single fun _ => h _)

theorem coe_mul_mulVec (g h : SL3 F) (v : Fin 3 → F) :
    ((g * h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem rootElt_mulVec {i j : Fin 3} (hij : i ≠ j) (c : F) (v : Fin 3 → F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      fun k => v k + if k = i then c * v j else 0 := by
  rw [coe_rootElt hij, Matrix.add_mulVec, Matrix.one_mulVec]
  funext k
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.single_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

section Perm

variable [CharP F 2]

@[expose] noncomputable def pmat (σ : Equiv.Perm (Fin 3)) : SL3 F :=
  ⟨Equiv.Perm.permMatrix F σ⁻¹, by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h]
    · simp
    · simp [CharTwo.neg_eq]⟩

theorem coe_pmat_apply (σ : Equiv.Perm (Fin 3)) (k l : Fin 3) :
    ((pmat σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) k l = if k = σ l then 1 else 0 := by
  change Equiv.Perm.permMatrix F σ⁻¹ k l = _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  have : (σ⁻¹ k = l) ↔ (k = σ l) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  by_cases h : k = σ l
  · simp [h]
  · simp only [this, h]

theorem pmat_mulVec (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → F) :
    ((pmat σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = fun k => x (σ⁻¹ k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, coe_pmat_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ⁻¹ k)]
  · simp
  · intro l _ hl
    have : ¬ k = σ l := fun h => hl (by rw [h]; simp)
    simp [this]
  · simp

theorem pmat_mul (σ τ : Equiv.Perm (Fin 3)) : (pmat σ : SL3 F) * pmat τ = pmat (σ * τ) := by
  refine sl3_ext fun v => ?_
  rw [coe_mul_mulVec, pmat_mulVec, pmat_mulVec, pmat_mulVec]
  funext k
  simp [_root_.mul_inv_rev]

theorem pmat_one : (pmat 1 : SL3 F) = 1 := by
  apply Subtype.ext
  change ((pmat 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1
  ext k l
  rw [coe_pmat_apply, Matrix.one_apply]
  by_cases h : k = l <;> simp [h]

theorem pmat_inv (σ : Equiv.Perm (Fin 3)) : (pmat σ : SL3 F)⁻¹ = pmat σ⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, pmat_mul, mul_inv_cancel, pmat_one]

theorem pmat_conj_rootElt (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) (c : F) :
    pmat σ * rootElt i j c * (pmat σ)⁻¹ = rootElt (σ i) (σ j) c := by
  rw [mul_inv_eq_iff_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp [rootElt_self]
  have hij' : σ i ≠ σ j := fun h => hij (σ.injective h)
  refine sl3_ext fun v => ?_
  rw [coe_mul_mulVec, coe_mul_mulVec, pmat_mulVec, pmat_mulVec, rootElt_mulVec hij,
    rootElt_mulVec hij']
  funext k
  by_cases hk : k = σ i
  · subst hk
    simp
  · have hk' : σ.symm k ≠ i := fun h => hk (by rw [← h]; simp)
    simp [hk, hk']

end Perm

theorem exists_third (i j : Fin 3) (hij : i ≠ j) : ∃ l : Fin 3, i ≠ l ∧ l ≠ j := by
  revert i j; decide

theorem hom_eq_one {G : Type*} [CommGroup G] (f : SL3 F →* G) (g : SL3 F) : f g = 1 := by
  have h : f.ker = ⊤ := by
    refine eq_top_of_rootElt_mem fun i j c hij => ?_
    obtain ⟨l, hil, hlj⟩ := exists_third i j hij
    rw [MonoidHom.mem_ker, ← mul_one c, ← rootElt_commutator hil hlj hij, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g)

section Module

variable {V : Type*} [CommGroup V]

theorem comm_mem_of_comm_comm_mem (ρ : SL3 F →* MulAut V) (S : Subgroup V) (v : V)
    (h : ∀ g k : SL3 F, ρ g (ρ k v * v⁻¹) * (ρ k v * v⁻¹)⁻¹ ∈ S) (g : SL3 F) :
    ρ g v * v⁻¹ ∈ S := by
  let φ : SL3 F →* V ⧸ S :=
    { toFun := fun g => (QuotientGroup.mk (ρ g v * v⁻¹) : V ⧸ S)
      map_one' := by simp
      map_mul' := fun g k => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hk := h g k
        have he : (ρ (g * k) v * v⁻¹)⁻¹ * (ρ g v * v⁻¹ * (ρ k v * v⁻¹)) =
            (ρ g (ρ k v * v⁻¹) * (ρ k v * v⁻¹)⁻¹)⁻¹ := by
          rw [map_mul, MulAut.mul_apply, map_mul (ρ g), map_inv (ρ g)]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [he]
        exact S.inv_mem hk }
  have h1 := hom_eq_one φ g
  change (QuotientGroup.mk (ρ g v * v⁻¹) : V ⧸ S) = 1 at h1
  rwa [QuotientGroup.eq_one_iff] at h1

theorem fix_of_comm_fix (ρ : SL3 F →* MulAut V) (v : V)
    (h : ∀ g k : SL3 F, ρ g (ρ k v * v⁻¹) = ρ k v * v⁻¹) (g : SL3 F) : ρ g v = v := by
  have := comm_mem_of_comm_comm_mem ρ ⊥ v (fun g k => by
    rw [h g k, mul_inv_cancel]
    exact Subgroup.one_mem _) g
  rw [Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

theorem mem_fixV_range {ρ : SL3 F →* MulAut V} {v : V} : v ∈ fixV ρ.range ↔ ∀ g, ρ g v = v := by
  rw [mem_fixV]
  constructor
  · intro h g; exact h _ ⟨g, rfl⟩
  · rintro h _ ⟨g, rfl⟩; exact h g

theorem comm_mem_commV (ρ : SL3 F →* MulAut V) (g : SL3 F) (v : V) :
    ρ g v * v⁻¹ ∈ commV ρ.range :=
  Subgroup.subset_closure ⟨ρ g, ⟨g, rfl⟩, v, rfl⟩

theorem rho_mem_commV (ρ : SL3 F →* MulAut V) (g : SL3 F) {v : V} (hv : v ∈ commV ρ.range) :
    ρ g v ∈ commV ρ.range := by
  induction hv using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨_, ⟨k, rfl⟩, u, rfl⟩ := hw
    have he : ρ g (ρ k u * u⁻¹) = ρ (g * k * g⁻¹) (ρ g u) * (ρ g u)⁻¹ := by
      simp [map_mul, MulAut.mul_apply]
    rw [he]
    exact comm_mem_commV ρ _ _
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem rho_mem_fixV (ρ : SL3 F →* MulAut V) (g : SL3 F) {v : V} (hv : v ∈ fixV ρ.range) :
    ρ g v ∈ fixV ρ.range := by
  rw [mem_fixV_range] at hv ⊢
  intro k
  rw [hv, hv]

theorem rho_mul (ρ : SL3 F →* MulAut V) (g k : SL3 F) (v : V) : ρ (g * k) v = ρ g (ρ k v) := by
  rw [map_mul, MulAut.mul_apply]

theorem rho_inv_rho (ρ : SL3 F →* MulAut V) (g : SL3 F) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← rho_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem rho_rho_inv (ρ : SL3 F →* MulAut V) (g : SL3 F) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← rho_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem mem_map_rho {ρ : SL3 F →* MulAut V} {A : Subgroup V} {g : SL3 F} {v : V} :
    v ∈ A.map (ρ g).toMonoidHom ↔ ρ g⁻¹ v ∈ A := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ρ g⁻¹ (ρ g w) ∈ A
    rwa [rho_inv_rho]
  · intro h
    exact ⟨ρ g⁻¹ v, h, rho_rho_inv ρ g v⟩

theorem rho_mem_map_rho {ρ : SL3 F →* MulAut V} {A : Subgroup V} (g : SL3 F) {v : V}
    (hv : v ∈ A) : ρ g v ∈ A.map (ρ g).toMonoidHom :=
  ⟨v, hv, rfl⟩

theorem map_rho_le_iff {ρ : SL3 F →* MulAut V} {A B : Subgroup V} {g : SL3 F} :
    A.map (ρ g).toMonoidHom ≤ B ↔ ∀ v ∈ A, ρ g v ∈ B := by
  rw [Subgroup.map_le_iff_le_comap]
  rfl

theorem map_rho_mul (ρ : SL3 F →* MulAut V) (A : Subgroup V) (g k : SL3 F) :
    A.map (ρ (g * k)).toMonoidHom = (A.map (ρ k).toMonoidHom).map (ρ g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext v
  simp

theorem map_rho_one (ρ : SL3 F →* MulAut V) (A : Subgroup V) :
    A.map (ρ 1).toMonoidHom = A := by
  ext v
  simp

theorem map_rho_eq {ρ : SL3 F →* MulAut V} {H : Subgroup (SL3 F)} {A : Subgroup V}
    (hA : ∀ k ∈ H, ∀ v ∈ A, ρ k v ∈ A) {k : SL3 F} (hk : k ∈ H) :
    A.map (ρ k).toMonoidHom = A := by
  refine le_antisymm (map_rho_le_iff.mpr fun v hv => hA k hk v hv) fun v hv => ?_
  rw [mem_map_rho]
  exact hA _ (H.inv_mem hk) v hv

theorem map_rho_eq_map_rho {ρ : SL3 F →* MulAut V} {H : Subgroup (SL3 F)} {A : Subgroup V}
    (hA : ∀ k ∈ H, ∀ v ∈ A, ρ k v ∈ A) {g g' : SL3 F} (hg : g⁻¹ * g' ∈ H) :
    A.map (ρ g').toMonoidHom = A.map (ρ g).toMonoidHom := by
  rw [show g' = g * (g⁻¹ * g') by group, map_rho_mul, map_rho_eq hA hg]

@[expose] noncomputable def restrAut (ρ : SL3 F →* MulAut V) (H : Subgroup V)
    (hH : ∀ g : SL3 F, ∀ v ∈ H, ρ g v ∈ H) (g : SL3 F) : MulAut ↥H where
  toFun v := ⟨ρ g v, hH g v v.2⟩
  invFun v := ⟨ρ g⁻¹ v, hH g⁻¹ v v.2⟩
  left_inv v := Subtype.ext (rho_inv_rho ρ g v)
  right_inv v := Subtype.ext (rho_rho_inv ρ g v)
  map_mul' v w := Subtype.ext (map_mul (ρ g) (v : V) w)

@[expose] noncomputable def restr (ρ : SL3 F →* MulAut V) (H : Subgroup V)
    (hH : ∀ g : SL3 F, ∀ v ∈ H, ρ g v ∈ H) : SL3 F →* MulAut ↥H where
  toFun := restrAut ρ H hH
  map_one' := MulEquiv.ext fun v => Subtype.ext (by simp [restrAut])
  map_mul' g k := MulEquiv.ext fun v => Subtype.ext (by simp [restrAut])

theorem map_rho_eq_self {ρ : SL3 F →* MulAut V} {Z : Subgroup V}
    (hZ : ∀ g : SL3 F, ∀ z ∈ Z, ρ g z ∈ Z) (g : SL3 F) : Z.map (ρ g).toMonoidHom = Z :=
  map_rho_eq (H := ⊤) (fun k _ => hZ k) (Subgroup.mem_top g)

@[expose] noncomputable def quotAct (ρ : SL3 F →* MulAut V) (Z : Subgroup V)
    (hZ : ∀ g : SL3 F, ∀ z ∈ Z, ρ g z ∈ Z) : SL3 F →* MulAut (V ⧸ Z) where
  toFun g := QuotientGroup.congr Z Z (ρ g) (map_rho_eq_self hZ g)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H v => simp
  map_mul' g k := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H v =>
      change (QuotientGroup.mk (ρ (g * k) v) : V ⧸ Z) = QuotientGroup.mk (ρ g (ρ k v))
      rw [rho_mul]

end Module

end CFSG.Quasithin.MS93.M16
