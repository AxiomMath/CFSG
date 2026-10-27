module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct

public section

namespace CFSG.StandardType

open CFSG.RankThree.CentralCover (zmodPowHom zmodPowHom_apply)

namespace TableBExc.Three

variable {n : ℕ}

@[expose] def shiftAut (π : Equiv.Perm (Fin n)) : MulAut (Multiplicative (Fin n → ZMod 3)) where
  toFun v := .ofAdd fun i => v.toAdd (π.symm i)
  invFun v := .ofAdd fun i => v.toAdd (π i)
  left_inv v := by simp
  right_inv v := by simp
  map_mul' _ _ := rfl

theorem toAdd_shiftAut (π : Equiv.Perm (Fin n)) (v : Multiplicative (Fin n → ZMod 3))
    (i : Fin n) : (shiftAut π v).toAdd i = v.toAdd (π.symm i) :=
  rfl

theorem toAdd_shiftAut_pow (π : Equiv.Perm (Fin n)) (k : ℕ) (v : Multiplicative (Fin n → ZMod 3))
    (i : Fin n) : ((shiftAut π ^ k) v).toAdd i = v.toAdd ((π ^ k).symm i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, toAdd_shiftAut, ih, pow_succ', Equiv.Perm.mul_def,
      Equiv.symm_trans_apply]

theorem shiftAut_pow_three {π : Equiv.Perm (Fin n)} (hπ : π ^ 3 = 1) : shiftAut π ^ 3 = 1 := by
  refine MulEquiv.ext fun v => ?_
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_shiftAut_pow, hπ]
  rfl

@[expose] def phi (π : Equiv.Perm (Fin n)) (hπ : π ^ 3 = 1) :
    Multiplicative (ZMod 3) →* MulAut (Multiplicative (Fin n → ZMod 3)) :=
  zmodPowHom (shiftAut π) (shiftAut_pow_three hπ)

abbrev Model (π : Equiv.Perm (Fin n)) (hπ : π ^ 3 = 1) : Type :=
  Multiplicative (Fin n → ZMod 3) ⋊[phi π hπ] Multiplicative (ZMod 3)

variable {π : Equiv.Perm (Fin n)} {hπ : π ^ 3 = 1}

theorem phi_ofAdd_natCast (k : ℕ) : phi π hπ (.ofAdd (k : ZMod 3)) = shiftAut π ^ k := by
  rw [phi, zmodPowHom_apply, ZMod.val_natCast]
  exact (pow_eq_pow_mod k (shiftAut_pow_three hπ)).symm

theorem phi_ofAdd_one : phi π hπ (.ofAdd 1) = shiftAut π := by
  have h := phi_ofAdd_natCast (π := π) (hπ := hπ) 1
  rwa [Nat.cast_one, pow_one] at h

theorem phi_ofAdd_two : phi π hπ (.ofAdd 2) = shiftAut π ^ 2 := by
  have h := phi_ofAdd_natCast (π := π) (hπ := hπ) 2
  rwa [Nat.cast_ofNat] at h

theorem card_model : Nat.card (Model π hπ) = 3 ^ n * 3 := by
  rw [SemidirectProduct.card, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
    Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

variable {M : Type*} [Group M]

variable (π) in
structure IsModel (g : Fin n → M) (c : M) : Prop where
  g_pow : ∀ i, g i ^ 3 = 1
  g_comm : ∀ i j, g i * g j = g j * g i
  c_pow : c ^ 3 = 1
  c_conj : ∀ i, c * g i * c⁻¹ = g (π i)

variable {g : Fin n → M} {c : M}

theorem IsModel.comm (h : IsModel π g c) :
    Pairwise fun i j => ∀ x y : Multiplicative (ZMod 3),
      Commute (zmodPowHom (g i) (h.g_pow i) x) (zmodPowHom (g j) (h.g_pow j) y) :=
  fun i j _ _ _ => Commute.pow_pow (h.g_comm i j) _ _

@[expose] noncomputable def modelN (h : IsModel π g c) : Multiplicative (Fin n → ZMod 3) →* M :=
  (MonoidHom.noncommPiCoprod (fun i => zmodPowHom (g i) (h.g_pow i)) h.comm).comp
    (MulEquiv.funMultiplicative (Fin n) (ZMod 3)).toMonoidHom

theorem modelN_single (h : IsModel π g c) (i : Fin n) (a : ZMod 3) :
    modelN h (.ofAdd (Pi.single i a)) = g i ^ a.val := by
  have e : (MulEquiv.funMultiplicative (Fin n) (ZMod 3)) (.ofAdd (Pi.single i a)) =
      Pi.mulSingle i (.ofAdd a) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [modelN, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e,
    MonoidHom.noncommPiCoprod_mulSingle, zmodPowHom_apply]

theorem hom_ext_of_single {f f' : Multiplicative (Fin n → ZMod 3) →* M}
    (h : ∀ i a, f (.ofAdd (Pi.single i a)) = f' (.ofAdd (Pi.single i a))) : f = f' := by
  classical
  have hcl : Subgroup.closure (Set.range fun ia : Fin n × ZMod 3 =>
      (Multiplicative.ofAdd (Pi.single ia.1 ia.2) : Multiplicative (Fin n → ZMod 3))) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∏ i, Multiplicative.ofAdd (Pi.single i (v.toAdd i)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_ofAdd]
      exact (Finset.univ_sum_single _).symm
    rw [hv]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨(i, _), rfl⟩
  exact MonoidHom.eq_of_eqOn_dense hcl (by rintro _ ⟨⟨i, a⟩, rfl⟩; exact h i a)

theorem shiftAut_pow_single (k : ℕ) (i : Fin n) (a : ZMod 3) :
    (shiftAut π ^ k) (.ofAdd (Pi.single i a)) = .ofAdd (Pi.single ((π ^ k) i) a) := by
  apply Multiplicative.toAdd.injective
  funext j
  rw [toAdd_shiftAut_pow, toAdd_ofAdd, toAdd_ofAdd]
  by_cases hj : j = (π ^ k) i
  · subst hj
    simp
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne]
    intro he
    exact hj (by rw [← he, Equiv.apply_symm_apply])

theorem c_pow_conj (h : IsModel π g c) (k : ℕ) (i : Fin n) :
    c ^ k * g i * (c ^ k)⁻¹ = g ((π ^ k) i) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_inv_rev, pow_succ', Equiv.Perm.mul_apply, ← h.c_conj, ← ih]
    group

theorem modelN_compat (h : IsModel π g c) (m : Multiplicative (ZMod 3)) :
    (modelN h).comp (phi π hπ m).toMonoidHom =
      (MulAut.conj (zmodPowHom c h.c_pow m)).toMonoidHom.comp (modelN h) := by
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective m
  refine hom_ext_of_single fun i a => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, phi, zmodPowHom_apply, zmodPowHom_apply,
    shiftAut_pow_single, modelN_single, modelN_single, ← c_pow_conj h, conj_pow]

@[expose] noncomputable def modelHom (h : IsModel π g c) : Model π hπ →* M :=
  SemidirectProduct.lift (modelN h) (zmodPowHom c h.c_pow) (modelN_compat h)

theorem modelHom_inl (h : IsModel π g c) (v : Multiplicative (Fin n → ZMod 3)) :
    modelHom (hπ := hπ) h (SemidirectProduct.inl v) = modelN h v :=
  SemidirectProduct.lift_inl _ _ _ v

theorem modelHom_inr (h : IsModel π g c) (m : ZMod 3) :
    modelHom (hπ := hπ) h (SemidirectProduct.inr (.ofAdd m)) = c ^ m.val := by
  rw [modelHom, SemidirectProduct.lift_inr, zmodPowHom_apply]

theorem modelHom_apply (h : IsModel π g c) (y : Model π hπ) :
    modelHom h y = modelN h y.left * c ^ (Multiplicative.toAdd y.right).val :=
  rfl

theorem pow_smul_eq_of_smul_eq {X : Type*} [MulAction M X] {a : M} {x : X} (ha : a • x = x)
    (k : ℕ) : a ^ k • x = x := by
  induction k with
  | zero => rw [pow_zero, one_smul]
  | succ k ih => rw [pow_succ, mul_smul, ha, ih]

theorem eq_prod_single (v : Multiplicative (Fin n → ZMod 3)) :
    v = ∏ j, Multiplicative.ofAdd (Pi.single j (v.toAdd j)) := by
  classical
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  simp only [toAdd_ofAdd]
  exact (Finset.univ_sum_single _).symm

theorem modelN_injective {X : Type*} [MulAction M X] (h : IsModel π g c) (e : Fin n → X)
    (hfix : ∀ i j, i ≠ j → g j • e i = e i)
    (hmove : ∀ i, g i • e i ≠ e i ∧ g i ^ 2 • e i ≠ e i) : Function.Injective (modelN h) := by
  classical
  rw [injective_iff_map_eq_one]
  intro v hv
  apply Multiplicative.toAdd.injective
  funext i
  have hstab : ∀ w : Multiplicative (Fin n → ZMod 3), w.toAdd i = 0 →
      modelN h w • e i = e i := by
    intro w hw
    rw [eq_prod_single w]
    refine Finset.prod_induction _ (fun w => modelN h w • e i = e i)
      (fun a b ha hb => by rw [map_mul, mul_smul, hb, ha]) (by rw [map_one, one_smul]) ?_
    intro j _
    rw [modelN_single]
    by_cases hj : j = i
    · subst hj
      rw [hw, ZMod.val_zero, pow_zero, one_smul]
    · exact pow_smul_eq_of_smul_eq (hfix i j (Ne.symm hj)) _
  set a := v.toAdd i with ha
  have hsplit : v = Multiplicative.ofAdd (Pi.single i a) *
      Multiplicative.ofAdd (v.toAdd - Pi.single i a) := by
    apply Multiplicative.toAdd.injective
    exact (add_sub_cancel _ _).symm
  have h1 := hstab (Multiplicative.ofAdd (v.toAdd - Pi.single i a)) (by simp [ha])
  have h2 : g i ^ a.val • e i = e i := by
    have h3 : modelN h v • e i = (1 : M) • e i := by rw [hv]
    rw [hsplit, map_mul, mul_smul, h1, modelN_single, one_smul] at h3
    exact h3
  show a = 0
  have hlt := ZMod.val_lt a
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ a.val = 2) with h0 | h0 | h0
  · exact (ZMod.val_eq_zero a).mp h0
  · rw [h0, pow_one] at h2
    exact absurd h2 (hmove i).1
  · rw [h0] at h2
    exact absurd h2 (hmove i).2

theorem modelHom_injective (h : IsModel π g c) (hN : Function.Injective (modelN h))
    (hc : ∃ i, g (π i) ≠ g i ∧ g ((π ^ 2) i) ≠ g i) :
    Function.Injective (modelHom (hπ := hπ) h) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  rw [modelHom_apply] at hy
  set m := (Multiplicative.toAdd y.right).val with hm
  have hcm : c ^ m = (modelN h y.left)⁻¹ := eq_inv_of_mul_eq_one_right hy
  have hm0 : m = 0 := by
    obtain ⟨i, hi1, hi2⟩ := hc
    have hlt : m < 3 := ZMod.val_lt _
    by_contra hne
    have hgi : g i = modelN h (.ofAdd (Pi.single i 1)) := by
      rw [modelN_single, ZMod.val_one, pow_one]
    have hcomm' : Commute (modelN h y.left) (g i) := by
      rw [hgi]
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul, mul_comm]
    have hcomm : c ^ m * g i = g i * c ^ m := by
      rw [hcm]
      exact hcomm'.inv_left
    have hconj := c_pow_conj h m i
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at hconj
    rcases (by omega : m = 1 ∨ m = 2) with h1 | h1
    · rw [h1, pow_one] at hconj
      exact hi1 hconj.symm
    · rw [h1] at hconj
      exact hi2 hconj.symm
  have hr : y.right = 1 :=
    Multiplicative.toAdd.injective (((ZMod.val_eq_zero _).mp hm0).trans toAdd_one.symm)
  have hl : y.left = 1 := by
    rw [hm0, pow_zero, mul_one] at hy
    exact hN (hy.trans (map_one _).symm)
  exact SemidirectProduct.ext hl hr

theorem card_range_modelHom (h : IsModel π g c) (hinj : Function.Injective (modelHom (hπ := hπ) h)) :
    Nat.card (modelHom (hπ := hπ) h).range = 3 ^ n * 3 := by
  rw [← card_model (π := π) (hπ := hπ)]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

end TableBExc.Three

end CFSG.StandardType
