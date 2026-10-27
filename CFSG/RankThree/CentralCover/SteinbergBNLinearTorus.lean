module

public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.RankThree.CentralCover

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
open scoped MatrixGroups

section ZModPow

variable {M : Type*} [Group M] {p : ℕ} [NeZero p]

@[expose] def zmodPowHom (ζ : M) (hζ : ζ ^ p = 1) : Multiplicative (ZMod p) →* M where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem zmodPowHom_apply (ζ : M) (hζ : ζ ^ p = 1) (x : ZMod p) :
    zmodPowHom ζ hζ (.ofAdd x) = ζ ^ x.val := rfl

theorem zmodPowHom_injective {ζ : M} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    Function.Injective (zmodPowHom ζ hζ) := by
  intro x y h
  have h1 : ζ ^ (Multiplicative.toAdd x).val = ζ ^ (Multiplicative.toAdd y).val := h
  rw [pow_eq_pow_iff_modEq, hζo] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
  exact Multiplicative.toAdd.injective h2

end ZModPow

section Torus

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

@[expose] def torusExp {m : ℕ} (a : Fin m → ZMod p) : Fin (m + 1) → ZMod p :=
  Fin.snoc a (-∑ i, a i)

omit [NeZero p] in
theorem torusExp_castSucc {m : ℕ} (a : Fin m → ZMod p) (j : Fin m) :
    torusExp a j.castSucc = a j := Fin.snoc_castSucc ..

omit [NeZero p] in
theorem torusExp_last {m : ℕ} (a : Fin m → ZMod p) : torusExp a (Fin.last m) = -∑ i, a i :=
  Fin.snoc_last ..

omit [NeZero p] in
theorem torusExp_add {m : ℕ} (a b : Fin m → ZMod p) :
    torusExp (a + b) = torusExp a + torusExp b := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Pi.add_apply, torusExp_last, torusExp_last, torusExp_last]
    simp only [Pi.add_apply, Finset.sum_add_distrib, neg_add]
  · rw [Pi.add_apply, torusExp_castSucc, torusExp_castSucc, torusExp_castSucc, Pi.add_apply]

omit [NeZero p] in
theorem sum_torusExp {m : ℕ} (a : Fin m → ZMod p) : ∑ i, torusExp a i = 0 := by
  rw [Fin.sum_univ_castSucc, torusExp_last]
  simp only [torusExp_castSucc]
  ring

@[expose] def torusEntries (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Fin m → ZMod p) :
    Fin (m + 1) → kˣ :=
  fun i => zmodPowHom ζ hζ (.ofAdd (torusExp a i))

theorem prod_torusEntries (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Fin m → ZMod p) :
    ∏ i, torusEntries ζ hζ a i = 1 := by
  simp only [torusEntries]
  rw [← map_prod, ← ofAdd_sum, sum_torusExp, ofAdd_zero, map_one]

@[expose] def torusElem (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Fin m → ZMod p) : SL(m + 1, k) :=
  ⟨diagonal fun i => (torusEntries ζ hζ a i : k), by
    rw [det_diagonal, ← Units.coe_prod, prod_torusEntries, Units.val_one]⟩

theorem coe_torusElem (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Fin m → ZMod p) :
    (torusElem ζ hζ a : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      diagonal fun i => (torusEntries ζ hζ a i : k) := rfl

theorem torusEntries_add (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a b : Fin m → ZMod p) :
    torusEntries ζ hζ (a + b) = torusEntries ζ hζ a * torusEntries ζ hζ b := by
  funext l
  simp only [torusEntries, torusExp_add, Pi.add_apply, ofAdd_add, map_mul, Pi.mul_apply]

theorem torusEntries_zero (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} :
    torusEntries ζ hζ (0 : Fin m → ZMod p) = 1 := by
  funext l
  simp only [torusEntries, Pi.one_apply]
  rw [show torusExp (0 : Fin m → ZMod p) l = 0 by
    refine Fin.lastCases ?_ (fun j => ?_) l
    · rw [torusExp_last]
      simp
    · rw [torusExp_castSucc]
      rfl]
  rw [ofAdd_zero, map_one]

theorem torusElem_add (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a b : Fin m → ZMod p) :
    torusElem ζ hζ (a + b) = torusElem ζ hζ a * torusElem ζ hζ b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_torusElem, coe_torusElem, coe_torusElem,
    diagonal_mul_diagonal, torusEntries_add]
  rfl

theorem torusElem_zero (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} :
    torusElem ζ hζ (0 : Fin m → ZMod p) = 1 := by
  ext i j
  rw [coe_torusElem, torusEntries_zero, Matrix.SpecialLinearGroup.coe_one]
  simp only [Pi.one_apply, Units.val_one]
  rfl

@[expose] def torusSL (ζ : kˣ) (hζ : ζ ^ p = 1) (m : ℕ) :
    Multiplicative (Fin m → ZMod p) →* SL(m + 1, k) where
  toFun a := torusElem ζ hζ (Multiplicative.toAdd a)
  map_one' := torusElem_zero ζ hζ
  map_mul' _ _ := torusElem_add ζ hζ _ _

theorem torusSL_apply (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Multiplicative (Fin m → ZMod p)) :
    torusSL ζ hζ m a = torusElem ζ hζ (Multiplicative.toAdd a) := rfl

end Torus

section Swap

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem torusExp_single_comp_swap {m : ℕ} (j j' : Fin m) :
    torusExp (Pi.single j (1 : ZMod p)) ∘ Equiv.swap j.castSucc j'.castSucc =
      torusExp (Pi.single j' (1 : ZMod p)) := by
  funext i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last j).ne'
      (Fin.castSucc_lt_last j').ne', torusExp_last, torusExp_last, Finset.sum_pi_single',
      Finset.sum_pi_single']
    simp
  · rw [Function.comp_apply, Fin.castSucc_injective m |>.swap_apply, torusExp_castSucc,
      torusExp_castSucc]
    simp only [Pi.single_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all

end Swap

section SwapElem

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

theorem prod_update_neg_one {m : ℕ} :
    ∏ i, ((Function.update (1 : Fin (m + 1) → kˣ) (Fin.last m) (-1) i : kˣ) : k) = -1 := by
  rw [← Units.coe_prod, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

@[expose] noncomputable def swapElem {m : ℕ} (j j' : Fin m) (hjj : j ≠ j') : SL(m + 1, k) :=
  ⟨((diagHom (m + 1) (Function.update 1 (Fin.last m) (-1)) *
      permGL (Equiv.swap j.castSucc j'.castSucc) : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k), by
    rw [Units.val_mul, det_mul, det_diagHom, det_permGL,
      Equiv.Perm.sign_swap (Fin.castSucc_injective m |>.ne hjj), prod_update_neg_one]
    simp⟩

theorem toGL_swapElem {m : ℕ} (j j' : Fin m) (hjj : j ≠ j') :
    Matrix.SpecialLinearGroup.toGL (swapElem (k := k) j j' hjj) =
      diagHom (m + 1) (Function.update 1 (Fin.last m) (-1)) *
        permGL (Equiv.swap j.castSucc j'.castSucc) := Units.ext rfl

theorem toGL_torusElem (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Fin m → ZMod p) :
    Matrix.SpecialLinearGroup.toGL (torusElem ζ hζ a) = diagHom (m + 1) (torusEntries ζ hζ a) :=
  Units.ext rfl

theorem swapElem_conj (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (j j' : Fin m) (hjj : j ≠ j') :
    swapElem j j' hjj * torusElem ζ hζ (Pi.single j 1) * (swapElem j j' hjj)⁻¹ =
      torusElem ζ hζ (Pi.single j' 1) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, toGL_swapElem, toGL_torusElem, toGL_torusElem,
    _root_.mul_inv_rev]
  set c : Fin (m + 1) → kˣ := Function.update 1 (Fin.last m) (-1)
  set σ := Equiv.swap j.castSucc j'.castSucc
  have h1 : diagHom (m + 1) c * permGL σ * diagHom (m + 1) (torusEntries ζ hζ (Pi.single j 1)) *
      ((permGL σ)⁻¹ * (diagHom (m + 1) c)⁻¹) = diagHom (m + 1) c *
      (permGL σ * diagHom (m + 1) (torusEntries ζ hζ (Pi.single j 1)) * (permGL σ)⁻¹) *
      (diagHom (m + 1) c)⁻¹ := by group
  rw [h1, permGL_mul_diagHom_mul_inv, (diagHom_commute _ _).eq, mul_inv_cancel_right]
  congr 1
  rw [Equiv.symm_swap]
  funext i
  simp only [torusEntries, Function.comp_apply]
  rw [← torusExp_single_comp_swap j j']
  rfl

end SwapElem

section Proj

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

@[expose] noncomputable def torusPSL (ζ : kˣ) (hζ : ζ ^ p = 1) (m : ℕ) :
    Multiplicative (Fin m → ZMod p) →* PSL(m + 1, k) :=
  (QuotientGroup.mk' (Subgroup.center SL(m + 1, k))).comp (torusSL ζ hζ m)

theorem torusExp_eq_of_mem_ker {ζ : kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {m : ℕ}
    {a : Multiplicative (Fin m → ZMod p)} (ha : a ∈ (torusPSL ζ hζ m).ker) (i i' : Fin (m + 1)) :
    torusExp (Multiplicative.toAdd a) i = torusExp (Multiplicative.toAdd a) i' := by
  have hmem : torusSL ζ hζ m a ∈ Subgroup.center SL(m + 1, k) :=
    (QuotientGroup.eq_one_iff _).1 ha
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
  have hent : ∀ l, (torusEntries ζ hζ (Multiplicative.toAdd a) l : k) = r := by
    intro l
    have := congrFun (congrFun hr l) l
    rw [torusSL_apply, coe_torusElem, scalar_apply, diagonal_apply_eq, diagonal_apply_eq] at this
    exact this.symm
  have h1 : torusEntries ζ hζ (Multiplicative.toAdd a) i =
      torusEntries ζ hζ (Multiplicative.toAdd a) i' := Units.ext ((hent i).trans (hent i').symm)
  have h2 := zmodPowHom_injective hζo hζ h1
  exact Multiplicative.ofAdd.injective h2

theorem card_ker_torusPSL_le {ζ : kˣ} (hp : p.Prime) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (torusPSL ζ hζ m).ker ≤ p ^ (if p ∣ m + 1 then 1 else 0) := by
  classical
  set i₀ : Fin m := ⟨0, hm⟩
  have hconst : ∀ a ∈ (torusPSL ζ hζ m).ker, ∀ j, Multiplicative.toAdd a j =
      Multiplicative.toAdd a i₀ := by
    intro a ha j
    have := torusExp_eq_of_mem_ker hζo hζ ha j.castSucc i₀.castSucc
    rwa [torusExp_castSucc, torusExp_castSucc] at this
  have hsum : ∀ a ∈ (torusPSL ζ hζ m).ker, ((m + 1 : ℕ) : ZMod p) * Multiplicative.toAdd a i₀ =
      0 := by
    intro a ha
    have h1 := torusExp_eq_of_mem_ker hζo hζ ha (Fin.last m) i₀.castSucc
    rw [torusExp_last, torusExp_castSucc, Finset.sum_congr rfl fun j _ => hconst a ha j,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    push_cast
    linear_combination -h1
  split_ifs with hpm
  ·
    rw [pow_one]
    let ev : (torusPSL ζ hζ m).ker → ZMod p := fun a => Multiplicative.toAdd a.1 i₀
    have hev : Function.Injective ev := by
      intro a a' h
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext j
      rw [hconst a a.2 j, hconst a' a'.2 j]
      exact h
    calc Nat.card (torusPSL ζ hζ m).ker ≤ Nat.card (ZMod p) := Nat.card_le_card_of_injective _ hev
      _ = p := Nat.card_zmod p
  ·
    rw [pow_zero]
    have hcop : Nat.Coprime (m + 1) p :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm))
    have hbot : (torusPSL ζ hζ m).ker = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
      have hc : Multiplicative.toAdd a i₀ = 0 := by
        have h1 := hsum a ha
        have h2 : ((ZMod.unitOfCoprime (m + 1) hcop)⁻¹ : (ZMod p)ˣ) *
            (((m + 1 : ℕ) : ZMod p) * Multiplicative.toAdd a i₀) = 0 := by rw [h1, mul_zero]
        rwa [← mul_assoc, ← ZMod.coe_unitOfCoprime (m + 1) hcop, Units.inv_mul, one_mul] at h2
      apply Multiplicative.toAdd.injective
      funext j
      rw [hconst a ha j, hc]
      rfl
    rw [hbot, Subgroup.card_bot]

end Proj

section Package

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

theorem swapElem_comm {m : ℕ} (j j' : Fin m) (hjj : j ≠ j') :
    swapElem (k := k) j j' hjj = swapElem j' j hjj.symm := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_swapElem, toGL_swapElem, Equiv.swap_comm]

omit [NeZero p] in
theorem pow_eq_one_of_zmod {m : ℕ} (a : Multiplicative (Fin m → ZMod p)) : a ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    Pi.zero_apply]

omit [NeZero p] in
theorem card_multiplicative_fin_zmod (m : ℕ) :
    Nat.card (Multiplicative (Fin m → ZMod p)) = p ^ m := by
  change Nat.card (Fin m → ZMod p) = _
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

variable {Y : Type*} [Group Y]

theorem torusPSL_package {ζ : kˣ} (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {m : ℕ} (hm : 1 ≤ m) {φ : Y →* PSL(m + 1, k)}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) :
    (∀ x ∈ (torusPSL ζ hζ m).range, x ^ p = 1) ∧
      (∀ x ∈ (torusPSL ζ hζ m).range.comap φ, ∀ y ∈ (torusPSL ζ hζ m).range.comap φ,
        x * y = y * x) ∧
      p ^ (m - if p ∣ m + 1 then 1 else 0) ≤ Nat.card (torusPSL ζ hζ m).range := by
  classical
  set θ := torusPSL ζ hζ m with hθ
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  ·
    have hgen : ∀ j j' : Fin m, liftComm φ hφ (θ (.ofAdd (Pi.single j 1)))
        (θ (.ofAdd (Pi.single j' 1))) = 1 := by
      intro j j'
      rcases eq_or_ne j j' with rfl | hjj
      · exact liftComm_self hφ _
      have hcomm : Commute (θ (.ofAdd (Pi.single j 1))) (θ (.ofAdd (Pi.single j' 1))) :=
        (Commute.all _ _).map θ
      refine liftComm_eq_one_of_conj_swap hφ hker (hp.odd_of_ne_two hp2) hcomm
        (by rw [← map_pow, pow_eq_one_of_zmod, map_one])
        (QuotientGroup.mk' _ (swapElem j j' hjj)) ?_ ?_
      · change QuotientGroup.mk' _ (swapElem j j' hjj * torusElem ζ hζ (Pi.single j 1) *
          (swapElem j j' hjj)⁻¹) = _
        rw [swapElem_conj]
        rfl
      · change QuotientGroup.mk' _ (swapElem j j' hjj * torusElem ζ hζ (Pi.single j' 1) *
          (swapElem j j' hjj)⁻¹) = _
        rw [swapElem_comm, swapElem_conj]
        rfl
    have hall : ∀ s ∈ θ.range, ∀ t ∈ θ.range, liftComm φ hφ s t = 1 := by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      refine liftComm_eq_one_of_closure hφ hker θ closure_range_single_eq_top ?_ a a'
      rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩
      exact hgen j j'
    exact fun x hx y hy => mul_comm_of_liftComm_eq_one hφ hker hall hx hy
  ·
    set ε := if p ∣ m + 1 then 1 else 0 with hε
    have hkcard := card_ker_torusPSL_le hp hζo hζ hm
    rw [← hε] at hkcard
    have h1 : Nat.card θ.ker * Nat.card θ.range = p ^ m := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index, card_multiplicative_fin_zmod]
    have hεm : ε ≤ m := by
      rw [hε]
      split_ifs <;> omega
    have h2 : p ^ m ≤ Nat.card θ.range * p ^ ε := by
      rw [← h1, mul_comm]
      exact Nat.mul_le_mul_left _ hkcard
    have h3 : p ^ m = p ^ (m - ε) * p ^ ε := by rw [← pow_add, Nat.sub_add_cancel hεm]
    rw [h3] at h2
    exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.pos _)

end Package

section Equal

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

@[expose] def coordDiffHom {m : ℕ} (i i' : Fin m) :
    Multiplicative (Fin m → ZMod p) →* Multiplicative (ZMod p) where
  toFun a := .ofAdd (Multiplicative.toAdd a i - Multiplicative.toAdd a i')
  map_one' := by simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, Pi.add_apply, toAdd_ofAdd]
    ring

theorem card_ker_coordDiffHom {m : ℕ} {i i' : Fin m} (hii : i ≠ i') :
    Nat.card (coordDiffHom (p := p) i i').ker = p ^ (m - 1) := by
  classical
  have hsurj : Function.Surjective (coordDiffHom (p := p) i i') := by
    intro t
    refine ⟨.ofAdd (Pi.single i (Multiplicative.toAdd t)), ?_⟩
    apply Multiplicative.toAdd.injective
    change (Pi.single i (Multiplicative.toAdd t) : Fin m → ZMod p) i -
      (Pi.single i (Multiplicative.toAdd t) : Fin m → ZMod p) i' = Multiplicative.toAdd t
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hii.symm, sub_zero]
  have h1 := Subgroup.card_mul_index (coordDiffHom (p := p) i i').ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    card_multiplicative_fin_zmod] at h1
  have h2 : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
  rw [h2] at h1
  have hm : 1 ≤ m := by
    rcases m with _ | m
    · exact i.elim0
    · omega
  have h3 : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne p)) h1

theorem card_map_ker_coordDiffHom {ζ : kˣ} (hp : p.Prime) (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {m : ℕ} (hm : 2 ≤ m) :
    p ^ (m - 1 - if p ∣ m + 1 then 1 else 0) ≤
      Nat.card ((coordDiffHom (p := p) ⟨0, by omega⟩ ⟨1, by omega⟩).ker.map
        (torusPSL ζ hζ m)) := by
  set V' := (coordDiffHom (p := p) (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩).ker
  set θ := torusPSL ζ hζ m
  set ε := if p ∣ m + 1 then 1 else 0 with hε
  have hkcard := card_ker_torusPSL_le hp hζo hζ (show 1 ≤ m by omega)
  rw [← hε] at hkcard
  set θ' := θ.comp V'.subtype
  have hrange : θ'.range = V'.map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker' : Nat.card θ'.ker ≤ Nat.card θ.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : Multiplicative (Fin m → ZMod p)),
      x.2⟩) fun x y h => ?_
    have h' := Subtype.ext_iff.1 h
    exact Subtype.ext (Subtype.ext h')
  have h1 : Nat.card θ'.ker * Nat.card θ'.range = p ^ (m - 1) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index,
      card_ker_coordDiffHom (show (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ by simp)]
  have hεm : ε ≤ m - 1 := by
    rw [hε]
    split_ifs <;> omega
  have h2 : p ^ (m - 1) ≤ Nat.card θ'.range * p ^ ε := by
    rw [← h1, mul_comm]
    exact Nat.mul_le_mul_left _ (hker'.trans hkcard)
  have h3 : p ^ (m - 1) = p ^ (m - 1 - ε) * p ^ ε := by rw [← pow_add, Nat.sub_add_cancel hεm]
  rw [h3] at h2
  rw [← hrange]
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.pos _)

end Equal

section Special

variable {k : Type} [Field k] {N : ℕ}

@[expose] def rootElem {i j : Fin N} (hij : i ≠ j) (t : k) : SL(N, k) :=
  ⟨transvection i j t, det_transvection_of_ne _ _ hij t⟩

theorem coe_rootElem {i j : Fin N} (hij : i ≠ j) (t : k) :
    (rootElem hij t : Matrix (Fin N) (Fin N) k) = transvection i j t := rfl

theorem rootElem_add {i j : Fin N} (hij : i ≠ j) (t t' : k) :
    rootElem hij (t + t') = rootElem hij t * rootElem hij t' := by
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootElem, coe_rootElem, coe_rootElem,
    transvection_mul_transvection_same _ _ hij]

theorem rootElem_zero {i j : Fin N} (hij : i ≠ j) : rootElem (k := k) hij 0 = 1 := by
  ext a b
  rw [coe_rootElem, transvection_zero, Matrix.SpecialLinearGroup.coe_one]

theorem rootElem_apply_ij {i j : Fin N} (hij : i ≠ j) (t : k) :
    (rootElem hij t : Matrix (Fin N) (Fin N) k) i j = t := by
  rw [coe_rootElem, transvection, Matrix.add_apply, Matrix.one_apply_ne hij,
    Matrix.single_apply_same, zero_add]

theorem rootElem_injective {i j : Fin N} (hij : i ≠ j) :
    Function.Injective (rootElem (k := k) hij) := by
  intro t t' h
  have := congrArg (fun g : SL(N, k) => (g : Matrix (Fin N) (Fin N) k) i j) h
  simpa only [rootElem_apply_ij] using this

theorem rootElem_not_mem_center {i j : Fin N} (hij : i ≠ j) {t : k} (ht : t ≠ 0) :
    rootElem hij t ∉ Subgroup.center SL(N, k) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have := congrFun (congrFun hr i) j
  rw [rootElem_apply_ij, scalar_apply, diagonal_apply_ne _ hij] at this
  exact ht this.symm

theorem diag_conj_rootElem {i j : Fin N} (hij : i ≠ j) (d : Fin N → kˣ) (t : k)
    (A : SL(N, k)) (hA : (A : Matrix (Fin N) (Fin N) k) = diagonal fun l => (d l : k)) :
    A * rootElem hij t * A⁻¹ = rootElem hij ((d i : k) * (d j : k)⁻¹ * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hA, coe_rootElem,
    coe_rootElem, diagonal_mul, mul_diagonal]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [this]
  · by_cases h2 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [hab, ↓reduceIte, true_and, zero_add]
      field_simp
    · simp [hab, h2]

end Special


section Diag

variable {k : Type} [Field k] {N : ℕ}

theorem commute_of_coe_diagonal {A B : SL(N, k)} {d d' : Fin N → k}
    (hA : (A : Matrix (Fin N) (Fin N) k) = diagonal d)
    (hB : (B : Matrix (Fin N) (Fin N) k) = diagonal d') : Commute A B := by
  rw [Commute, SemiconjBy]
  apply Subtype.ext
  change (A : Matrix (Fin N) (Fin N) k) * B = (B : Matrix (Fin N) (Fin N) k) * A
  rw [hA, hB, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Diag

section NegPair

variable {k : Type} [Field k] {N : ℕ}

@[expose] noncomputable def negPairElem {i i' : Fin N} (hii : i ≠ i') : SL(N, k) :=
  ⟨diagonal fun l => if l = i ∨ l = i' then (-1 : k) else 1, by
    rw [det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have : (Finset.univ.filter fun l : Fin N => l = i ∨ l = i').card = 2 := by
      rw [show (Finset.univ.filter fun l : Fin N => l = i ∨ l = i') = {i, i'} by
        ext l; simp]
      exact Finset.card_pair hii
    rw [this]
    norm_num⟩

theorem coe_negPairElem {i i' : Fin N} (hii : i ≠ i') :
    (negPairElem (k := k) hii : Matrix (Fin N) (Fin N) k) =
      diagonal fun l => if l = i ∨ l = i' then (-1 : k) else 1 := rfl

theorem negPairElem_sq {i i' : Fin N} (hii : i ≠ i') : negPairElem (k := k) hii ^ 2 = 1 := by
  ext a b
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_negPairElem, diagonal_mul_diagonal,
    Matrix.SpecialLinearGroup.coe_one]
  congr 1
  funext l
  split_ifs <;> norm_num

theorem negPairElem_not_mem_center (hk : ringChar k ≠ 2) {i i' i'' : Fin N} (hii : i ≠ i')
    (h1 : i'' ≠ i) (h2 : i'' ≠ i') : negPairElem (k := k) hii ∉ Subgroup.center SL(N, k) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have e1 := congrFun (congrFun hr i) i
  have e2 := congrFun (congrFun hr i'') i''
  rw [coe_negPairElem, scalar_apply, diagonal_apply_eq, diagonal_apply_eq] at e1 e2
  simp only [true_or, ↓reduceIte, h1, h2, or_self] at e1 e2
  exact hk (neg_one_eq_one_iff.1 (e1.symm.trans e2))

end NegPair

end CFSG.RankThree.CentralCover
