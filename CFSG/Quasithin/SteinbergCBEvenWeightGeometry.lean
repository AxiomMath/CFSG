module

public import CFSG.Quasithin.SteinbergCBDeletedModule
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module Equiv Equiv.Perm Subgroup

@[expose] def permAct7 (g : Perm (Fin 7)) : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 7 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹

theorem permAct7_apply (g : Perm (Fin 7)) (x : Fin 7 → ZMod 2) (i : Fin 7) :
    permAct7 g x i = x (g⁻¹ i) :=
  rfl

theorem permAct7_mul (g h : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    permAct7 (g * h) x = permAct7 g (permAct7 h x) := by
  funext i
  simp only [permAct7_apply, mul_inv_rev, Perm.mul_apply]

theorem permAct7_one (x : Fin 7 → ZMod 2) : permAct7 1 x = x := by
  funext i
  rfl

theorem permAct7_inv_apply (g : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    permAct7 g⁻¹ (permAct7 g x) = x := by
  rw [← permAct7_mul, inv_mul_cancel, permAct7_one]

theorem permAct7_apply_inv (g : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    permAct7 g (permAct7 g⁻¹ x) = x := by
  rw [← permAct7_mul, mul_inv_cancel, permAct7_one]

theorem permAct7_single (g : Perm (Fin 7)) (i : Fin 7) :
    permAct7 g (Pi.single i 1) = Pi.single (g i) 1 := by
  funext k
  rw [permAct7_apply]
  by_cases hk : k = g i
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne]
    intro h
    exact hk (by rw [← h, Perm.inv_def, Equiv.apply_symm_apply])

theorem permAct7_mem_evenWeight (g : Perm (Fin 7)) {x : Fin 7 → ZMod 2} (hx : x ∈ evenWeight 7) :
    permAct7 g x ∈ evenWeight 7 :=
  funLeft_inv_mem_evenWeight g hx

theorem hammingNorm_permAct7 (g : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    hammingNorm (permAct7 g x) = hammingNorm x := by
  unfold hammingNorm
  refine Finset.card_bij (fun i _ => g⁻¹ i) (fun i hi => ?_) (fun i _ j _ h => g⁻¹.injective h)
    (fun j hj => ⟨g j, ?_, by simp⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [permAct7_apply, Perm.inv_def, Equiv.symm_apply_apply]
    exact hj

@[expose] def fixedEven (X : Subgroup (Perm (Fin 7))) : Submodule (ZMod 2) (Fin 7 → ZMod 2) where
  carrier := {v | v ∈ evenWeight 7 ∧ ∀ x ∈ X, permAct7 x v = v}
  add_mem' := fun {u v} hu hv => ⟨(evenWeight 7).add_mem hu.1 hv.1, fun x hx => by
    rw [map_add, hu.2 x hx, hv.2 x hx]⟩
  zero_mem' := ⟨(evenWeight 7).zero_mem, fun x _ => map_zero _⟩
  smul_mem' := fun c v hv => ⟨(evenWeight 7).smul_mem c hv.1, fun x hx => by
    rw [map_smul, hv.2 x hx]⟩

theorem mem_fixedEven {X : Subgroup (Perm (Fin 7))} {v : Fin 7 → ZMod 2} :
    v ∈ fixedEven X ↔ v ∈ evenWeight 7 ∧ ∀ x ∈ X, permAct7 x v = v :=
  Iff.rfl

@[expose] def hyperplaneSum (B : Subgroup (Perm (Fin 7))) : Submodule (ZMod 2) (Fin 7 → ZMod 2) :=
  ⨆ (X : Subgroup (Perm (Fin 7))) (_ : X ≤ B ∧ (X.subgroupOf B).index = 2), fixedEven X

@[expose] def commSpan (B : Subgroup (Perm (Fin 7))) : Submodule (ZMod 2) (Fin 7 → ZMod 2) :=
  Submodule.span (ZMod 2) {u | ∃ w ∈ hyperplaneSum B, ∃ b ∈ B, u = w + permAct7 b w}

theorem permAct7_conj (σ g : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    permAct7 (σ * g * σ⁻¹) x = permAct7 σ (permAct7 g (permAct7 σ⁻¹ x)) := by
  rw [permAct7_mul, permAct7_mul]

theorem fixedEven_map_conj (σ : Perm (Fin 7)) (X : Subgroup (Perm (Fin 7))) :
    fixedEven (X.map (MulAut.conj σ).toMonoidHom) = (fixedEven X).map (permAct7 σ) := by
  ext v
  constructor
  · intro hv
    refine ⟨permAct7 σ⁻¹ v, ⟨?_, fun x hx => ?_⟩, permAct7_apply_inv σ v⟩
    · exact permAct7_mem_evenWeight _ hv.1
    · have h := hv.2 (σ * x * σ⁻¹) ⟨x, hx, rfl⟩
      rw [permAct7_conj] at h
      have h' := congrArg (permAct7 σ⁻¹) h
      rwa [permAct7_inv_apply] at h'
  · rintro ⟨u, ⟨huE, hu⟩, rfl⟩
    refine ⟨permAct7_mem_evenWeight _ huE, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change permAct7 (σ * x * σ⁻¹) (permAct7 σ u) = permAct7 σ u
    rw [permAct7_conj, permAct7_inv_apply, hu x hx]

theorem hyperplaneSum_map_conj (σ : Perm (Fin 7)) (B : Subgroup (Perm (Fin 7))) :
    hyperplaneSum (B.map (MulAut.conj σ).toMonoidHom) = (hyperplaneSum B).map (permAct7 σ) := by
  set c := (MulAut.conj σ).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj σ).injective
  have hidx : ∀ X : Subgroup (Perm (Fin 7)), X ≤ B →
      ((X.map c).subgroupOf (B.map c)).index = (X.subgroupOf B).index := by
    intro X _
    exact Subgroup.relIndex_map_map_of_injective X B hcinj
  rw [hyperplaneSum, hyperplaneSum, Submodule.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun Y ⟨hYB, hYidx⟩ => ?_
    set X := Y.map (MulAut.conj σ).symm.toMonoidHom with hX
    have hYX : Y = X.map c := by
      rw [hX, Subgroup.map_map]
      convert (Subgroup.map_id Y).symm
      ext g
      simp [hc]
    have hXB : X ≤ B := by
      rw [hX]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨b, hb, rfl⟩ := hYB hy
      change (MulAut.conj σ).symm (MulAut.conj σ b) ∈ B
      rw [MulEquiv.symm_apply_apply]
      exact hb
    refine le_iSup_of_le X ?_
    rw [Submodule.map_iSup]
    refine le_iSup_of_le ⟨hXB, by rw [← hidx X hXB, ← hYX]; exact hYidx⟩ ?_
    rw [hYX, fixedEven_map_conj]
  · refine iSup_le fun X => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun ⟨hXB, hXidx⟩ => ?_
    refine le_iSup₂_of_le (X.map c) ⟨Subgroup.map_mono hXB, by rw [hidx X hXB]; exact hXidx⟩ ?_
    rw [fixedEven_map_conj]

theorem commSpan_map_conj (σ : Perm (Fin 7)) (B : Subgroup (Perm (Fin 7))) :
    commSpan (B.map (MulAut.conj σ).toMonoidHom) = (commSpan B).map (permAct7 σ) := by
  rw [commSpan, commSpan, Submodule.map_span, hyperplaneSum_map_conj]
  congr 1
  ext u
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨w + permAct7 b w, ⟨w, hw, b, hb, rfl⟩, ?_⟩
    change permAct7 σ (w + permAct7 b w) = permAct7 σ w + permAct7 (σ * b * σ⁻¹) (permAct7 σ w)
    rw [map_add, permAct7_conj, permAct7_inv_apply]
  · rintro ⟨_, ⟨w, hw, b, hb, rfl⟩, rfl⟩
    refine ⟨permAct7 σ w, ⟨w, hw, rfl⟩, σ * b * σ⁻¹, ⟨b, hb, rfl⟩, ?_⟩
    rw [map_add, permAct7_conj, permAct7_inv_apply]


@[expose] def vecStab (v : Fin 7 → ZMod 2) : Subgroup (Perm (Fin 7)) where
  carrier := {g | permAct7 g v = v}
  one_mem' := permAct7_one v
  mul_mem' := fun {g h} hg hh => by
    change permAct7 (g * h) v = v
    rw [permAct7_mul]
    rw [show permAct7 h v = v from hh, show permAct7 g v = v from hg]
  inv_mem' := fun {g} hg => by
    change permAct7 g⁻¹ v = v
    have hg' : permAct7 g v = v := hg
    conv_lhs => rw [← hg']
    exact permAct7_inv_apply g v

@[expose] def kleinStd : Subgroup (Perm (Fin 7)) :=
  closure {swap 0 1 * swap 2 3, swap 0 2 * swap 1 3}

@[expose] def kleinStdFun : Fin 4 → Perm (Fin 7) :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem kleinStdFun_mul : ∀ i j : Fin 4, ∃ k, kleinStdFun i * kleinStdFun j = kleinStdFun k := by
  decide +kernel

theorem kleinStdFun_inv : ∀ i : Fin 4, ∃ k, (kleinStdFun i)⁻¹ = kleinStdFun k := by
  decide +kernel

theorem kleinStdFun_injective : Function.Injective kleinStdFun := by
  unfold Function.Injective
  decide +kernel

theorem mem_kleinStd_iff {g : Perm (Fin 7)} : g ∈ kleinStd ↔ ∃ i, g = kleinStdFun i := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | one => exact ⟨0, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact kleinStdFun_mul i j
    | inv x _ hx =>
      obtain ⟨i, rfl⟩ := hx
      exact kleinStdFun_inv i
  · rintro ⟨i, rfl⟩
    have h1 : (swap 0 1 * swap 2 3 : Perm (Fin 7)) ∈ kleinStd := subset_closure (by simp)
    have h2 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) ∈ kleinStd := subset_closure (by simp)
    have h3 : (swap 0 3 * swap 1 2 : Perm (Fin 7)) =
        (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3) := by decide
    fin_cases i
    · exact one_mem _
    · exact h1
    · exact h2
    · change (swap 0 3 * swap 1 2 : Perm (Fin 7)) ∈ kleinStd
      rw [h3]
      exact mul_mem h1 h2

theorem nat_card_kleinStd : Nat.card kleinStd = 4 := by
  have e : kleinStd ≃ Fin 4 :=
    { toFun := fun g => Classical.choose (mem_kleinStd_iff.1 g.2)
      invFun := fun i => ⟨kleinStdFun i, mem_kleinStd_iff.2 ⟨i, rfl⟩⟩
      left_inv := fun g => Subtype.ext (Classical.choose_spec (mem_kleinStd_iff.1 g.2)).symm
      right_inv := fun i => kleinStdFun_injective
        (Classical.choose_spec (mem_kleinStd_iff.1 (mem_kleinStd_iff.2 ⟨i, rfl⟩))).symm }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def hyperplaneStd : Submodule (ZMod 2) (Fin 7 → ZMod 2) where
  carrier := {x | ∑ i, x i = 0 ∧ x 0 + x 1 + x 2 + x 3 = 0}
  add_mem' := fun {x y} hx hy => ⟨by simp [Finset.sum_add_distrib, hx.1, hy.1], by
    simp only [Pi.add_apply]
    linear_combination hx.2 + hy.2⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := fun c x hx => ⟨by simp [← Finset.mul_sum, hx.1], by
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * hx.2⟩

theorem mem_hyperplaneStd {x : Fin 7 → ZMod 2} :
    x ∈ hyperplaneStd ↔ ∑ i, x i = 0 ∧ x 0 + x 1 + x 2 + x 3 = 0 :=
  Iff.rfl

@[expose] def vecFirstFour : Fin 7 → ZMod 2 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1

theorem fixed_by_involution_le : ∀ k : Fin 4, k ≠ 0 → ∀ v : Fin 7 → ZMod 2,
    ∑ i, v i = 0 → (fun i => v ((kleinStdFun k)⁻¹ i)) = v → v 0 + v 1 + v 2 + v 3 = 0 := by
  decide +kernel

theorem hyperplaneStd_decomp : ∀ x : Fin 7 → ZMod 2, ∑ i, x i = 0 → x 0 + x 1 + x 2 + x 3 = 0 →
    x = x 1 • (Pi.single 0 1 + Pi.single 1 1) + x 2 • (Pi.single 0 1 + Pi.single 2 1) +
      x 3 • (Pi.single 0 1 + Pi.single 3 1) + x 5 • (Pi.single 4 1 + Pi.single 5 1) +
      x 6 • (Pi.single 4 1 + Pi.single 6 1) := by
  decide +kernel

theorem commutator_std : ∀ k : Fin 4, ∀ w : Fin 7 → ZMod 2, ∑ i, w i = 0 →
    w 0 + w 1 + w 2 + w 3 = 0 → w + (fun i => w ((kleinStdFun k)⁻¹ i)) = 0 ∨
      w + (fun i => w ((kleinStdFun k)⁻¹ i)) = vecFirstFour := by
  decide +kernel

theorem fixed_std_iff : ∀ v : Fin 7 → ZMod 2, (∑ i, v i = 0 ∧
    (fun i => v ((swap 0 1 * swap 2 3 : Perm (Fin 7))⁻¹ i)) = v ∧
    (fun i => v ((swap 0 2 * swap 1 3 : Perm (Fin 7))⁻¹ i)) = v) ↔
    ∃ c₁ c₂ c₃ : ZMod 2, v = c₁ • vecFirstFour + c₂ • (Pi.single 4 1 + Pi.single 5 1) +
      c₃ • (Pi.single 4 1 + Pi.single 6 1) := by
  decide +kernel


theorem card_image_std : ∀ k : Fin 4, k ≠ 0 → (Finset.univ.filter fun y : Fin 7 → ZMod 2 =>
    ∃ x : Fin 7 → ZMod 2, ∑ i, x i = 0 ∧ (fun i => x ((kleinStdFun k)⁻¹ i)) - x = y).card = 4 := by
  decide +kernel

theorem kleinStdFun_sq : ∀ k : Fin 4, kleinStdFun k * kleinStdFun k = 1 := by
  decide +kernel

theorem kleinStdFun_ne_one : ∀ k : Fin 4, k ≠ 0 → kleinStdFun k ≠ 1 := by
  decide +kernel

theorem fixed_pair_std : ∀ k : Fin 4, ∀ p : Fin 7 × Fin 7,
    p ∈ ({(0, 1), (4, 5), (4, 6)} : Finset (Fin 7 × Fin 7)) ∨ (k = 2 ∧ p = (0, 2)) ∨
      (k = 3 ∧ p = (0, 3)) →
    k = 1 ∨ p.1 = 4 ∨ (k = 2 ∧ p = (0, 2)) ∨ (k = 3 ∧ p = (0, 3)) →
    (fun i => (Pi.single p.1 1 + Pi.single p.2 1 : Fin 7 → ZMod 2) ((kleinStdFun k)⁻¹ i)) =
      Pi.single p.1 1 + Pi.single p.2 1 := by
  decide +kernel

theorem first_four_eq_comm : vecFirstFour = (Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) +
    fun i => (Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) ((kleinStdFun 2)⁻¹ i) := by
  decide +kernel

theorem mem_fixedEven_zpowers {g : Perm (Fin 7)} {v : Fin 7 → ZMod 2} (hv : v ∈ evenWeight 7)
    (hg : permAct7 g v = v) : v ∈ fixedEven (zpowers g) :=
  ⟨hv, fun x hx => (zpowers_le.2 (show g ∈ vecStab v from hg) hx : x ∈ vecStab v)⟩

theorem zpowers_kleinStdFun_le (k : Fin 4) : zpowers (kleinStdFun k) ≤ kleinStd :=
  zpowers_le.2 (mem_kleinStd_iff.2 ⟨k, rfl⟩)

theorem index_zpowers_kleinStdFun {k : Fin 4} (hk : k ≠ 0) :
    ((zpowers (kleinStdFun k)).subgroupOf kleinStd).index = 2 := by
  have h2 : orderOf (kleinStdFun k) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact kleinStdFun_sq k) (kleinStdFun_ne_one k hk)
  have h := card_mul_index ((zpowers (kleinStdFun k)).subgroupOf kleinStd)
  rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_kleinStdFun_le k)).toEquiv, Nat.card_zpowers,
    h2, nat_card_kleinStd] at h
  omega

theorem pair_mem_hyperplaneSum {k : Fin 4} (hk : k ≠ 0) {a b : Fin 7}
    (hfix : (fun i => (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) ((kleinStdFun k)⁻¹ i)) =
      Pi.single a 1 + Pi.single b 1) :
    (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) ∈ hyperplaneSum kleinStd := by
  have hE : (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) ∈ evenWeight 7 := by
    rw [mem_evenWeight]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    decide
  refine (le_iSup₂ (f := fun X (_ : X ≤ kleinStd ∧ (X.subgroupOf kleinStd).index = 2) =>
    fixedEven X) (zpowers (kleinStdFun k)) ⟨zpowers_kleinStdFun_le k,
      index_zpowers_kleinStdFun hk⟩) ?_
  exact mem_fixedEven_zpowers hE hfix

theorem hyperplaneSum_kleinStd : hyperplaneSum kleinStd = hyperplaneStd := by
  apply le_antisymm
  · refine iSup₂_le fun X ⟨hXB, hXidx⟩ => ?_
    have hXcard : Nat.card X = 2 := by
      have h := card_mul_index (X.subgroupOf kleinStd)
      rw [hXidx, Nat.card_congr (subgroupOfEquivOfLe hXB).toEquiv, nat_card_kleinStd] at h
      omega
    obtain ⟨⟨c, hcX⟩, hc1⟩ : ∃ c : X, c ≠ 1 := by
      have : Nontrivial X := by
        rw [← Finite.one_lt_card_iff_nontrivial, hXcard]
        norm_num
      exact exists_ne 1
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    obtain ⟨k, rfl⟩ := mem_kleinStd_iff.1 (hXB hcX)
    have hk : k ≠ 0 := by
      rintro rfl
      exact hc1' rfl
    intro v hv
    exact ⟨mem_evenWeight.1 hv.1, fixed_by_involution_le k hk v (mem_evenWeight.1 hv.1)
      (hv.2 _ hcX)⟩
  · intro x hx
    rw [hyperplaneStd_decomp x hx.1 hx.2]
    have h1 := pair_mem_hyperplaneSum (k := 1) (by decide) (a := 0) (b := 1)
      (fixed_pair_std 1 (0, 1) (by decide) (by decide))
    have h2 := pair_mem_hyperplaneSum (k := 2) (by decide) (a := 0) (b := 2)
      (fixed_pair_std 2 (0, 2) (by decide) (by decide))
    have h3 := pair_mem_hyperplaneSum (k := 3) (by decide) (a := 0) (b := 3)
      (fixed_pair_std 3 (0, 3) (by decide) (by decide))
    have h4 := pair_mem_hyperplaneSum (k := 1) (by decide) (a := 4) (b := 5)
      (fixed_pair_std 1 (4, 5) (by decide) (by decide))
    have h5 := pair_mem_hyperplaneSum (k := 1) (by decide) (a := 4) (b := 6)
      (fixed_pair_std 1 (4, 6) (by decide) (by decide))
    exact add_mem (add_mem (add_mem (add_mem (Submodule.smul_mem _ _ h1)
      (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)) (Submodule.smul_mem _ _ h4))
      (Submodule.smul_mem _ _ h5)

theorem commSpan_kleinStd : commSpan kleinStd = Submodule.span (ZMod 2) {vecFirstFour} := by
  apply le_antisymm
  · rw [commSpan, Submodule.span_le]
    rintro _ ⟨w, hw, c, hc, rfl⟩
    rw [hyperplaneSum_kleinStd] at hw
    obtain ⟨k, rfl⟩ := mem_kleinStd_iff.1 hc
    rcases commutator_std k w hw.1 hw.2 with h | h
    · rw [show w + permAct7 (kleinStdFun k) w = 0 from h]
      exact zero_mem _
    · rw [show w + permAct7 (kleinStdFun k) w = vecFirstFour from h]
      exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    apply Submodule.subset_span
    refine ⟨Pi.single 0 1 + Pi.single 1 1, ?_, kleinStdFun 2, mem_kleinStd_iff.2 ⟨2, rfl⟩,
      first_four_eq_comm⟩
    rw [hyperplaneSum_kleinStd, mem_hyperplaneStd]
    decide

theorem fixedEven_kleinStd : fixedEven kleinStd = Submodule.span (ZMod 2)
    {vecFirstFour, Pi.single 4 1 + Pi.single 5 1, Pi.single 4 1 + Pi.single 6 1} := by
  ext v
  have hkey : v ∈ fixedEven kleinStd ↔ ∑ i, v i = 0 ∧
      (fun i => v ((swap 0 1 * swap 2 3 : Perm (Fin 7))⁻¹ i)) = v ∧
      (fun i => v ((swap 0 2 * swap 1 3 : Perm (Fin 7))⁻¹ i)) = v := by
    constructor
    · intro hv
      exact ⟨hv.1, hv.2 _ (subset_closure (by simp)), hv.2 _ (subset_closure (by simp))⟩
    · rintro ⟨hE, ha, hb⟩
      refine ⟨hE, fun x hx => ?_⟩
      have hle : kleinStd ≤ vecStab v := by
        rw [kleinStd, closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact ha
        · exact hb
      exact hle hx
  rw [hkey, fixed_std_iff]
  simp only [Submodule.mem_span_insert, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c₁, c₂, c₃, rfl⟩
    exact ⟨c₁, _, ⟨c₂, _, ⟨c₃, rfl⟩, rfl⟩, by abel⟩
  · rintro ⟨c₁, z, ⟨c₂, y, ⟨c₃, rfl⟩, rfl⟩, rfl⟩
    exact ⟨c₁, c₂, c₃, by abel⟩

theorem finrank_image_kleinStd {k : Fin 4} (hk : k ≠ 0) :
    finrank (ZMod 2) ((evenWeight 7).map (permAct7 (kleinStdFun k) - LinearMap.id)) = 2 := by
  have hcard : Nat.card ((evenWeight 7).map (permAct7 (kleinStdFun k) - LinearMap.id)) = 4 := by
    rw [← card_image_std k hk, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [Submodule.mem_map]
    rfl
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
  have : (2 : ℕ) ^ finrank (ZMod 2) ((evenWeight 7).map (permAct7 (kleinStdFun k) -
      LinearMap.id)) = 2 ^ 2 := by rw [hcard]; norm_num
  exact Nat.pow_right_injective le_rfl this


@[expose] def regularFourCond (g : Perm (Fin 7)) : Prop :=
  g 4 = 4 ∧ g 5 = 5 ∧ g 6 = 6 ∧ g * g = 1 ∧ (g = 1 ∨ (g 0 ≠ 0 ∧ g 1 ≠ 1 ∧ g 2 ≠ 2 ∧ g 3 ≠ 3))

instance : DecidablePred regularFourCond := fun g => by
  unfold regularFourCond
  infer_instance

theorem card_filter_regularFourCond : (Finset.univ.filter regularFourCond).card = 4 := by
  decide +kernel

theorem regularFourCond_kleinStdFun : ∀ k, regularFourCond (kleinStdFun k) := by
  unfold regularFourCond
  decide +kernel

theorem exists_kleinStdFun_of_regularFourCond {g : Perm (Fin 7)} (hg : regularFourCond g) :
    ∃ k, g = kleinStdFun k := by
  have himage : Finset.univ.image kleinStdFun = Finset.univ.filter regularFourCond := by
    refine Finset.eq_of_subset_of_card_le (fun g hg => ?_) ?_
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, regularFourCond_kleinStdFun k⟩
    · rw [card_filter_regularFourCond, Finset.card_image_of_injective _ kleinStdFun_injective]
      rfl
  have : g ∈ Finset.univ.image kleinStdFun := by
    rw [himage]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 this
  exact ⟨k, hk.symm⟩

theorem hammingNorm_pair : ∀ i i' : Fin 7, i ≠ i' →
    hammingNorm (Pi.single i 1 + Pi.single i' 1 : Fin 7 → ZMod 2) = 2 ∧
      (Pi.single i 1 + Pi.single i' 1 : Fin 7 → ZMod 2) ≠ 0 := by
  decide +kernel

theorem pair_mem_evenWeight (i i' : Fin 7) :
    (Pi.single i 1 + Pi.single i' 1 : Fin 7 → ZMod 2) ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

theorem exists_perm_mem_iff {O T : Finset (Fin 7)} (h : O.card = T.card) :
    ∃ σ : Perm (Fin 7), ∀ x, x ∈ O ↔ σ x ∈ T := by
  classical
  have h1 : Fintype.card {x // x ∈ O} = Fintype.card {x // x ∈ T} := by simp [h]
  have h2 : Fintype.card {x // x ∉ O} = Fintype.card {x // x ∉ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  set e₁ := Fintype.equivOfCardEq h1
  set e₂ := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e₁ e₂, fun x => ?_⟩
  by_cases hx : x ∈ O
  · have : Equiv.subtypeCongr e₁ e₂ x = e₁ ⟨x, hx⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
    rw [this]
    exact iff_of_true hx (e₁ ⟨x, hx⟩).2
  · have : Equiv.subtypeCongr e₁ e₂ x = e₂ ⟨x, hx⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hx]
    rw [this]
    exact iff_of_false hx (e₂ ⟨x, hx⟩).2

theorem subgroupOf_map_subtype_self (B : Subgroup (Perm (Fin 7))) (S : Subgroup B) :
    (S.map B.subtype).subgroupOf B = S := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [show y = x from Subtype.ext hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem finrank_image_conj (σ b : Perm (Fin 7)) :
    finrank (ZMod 2) ((evenWeight 7).map (permAct7 (σ * b * σ⁻¹) - LinearMap.id)) =
      finrank (ZMod 2) ((evenWeight 7).map (permAct7 b - LinearMap.id)) := by
  have hmap : (evenWeight 7).map (permAct7 (σ * b * σ⁻¹) - LinearMap.id) =
      ((evenWeight 7).map (permAct7 b - LinearMap.id)).map (permAct7 σ) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.sub_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨permAct7 b (permAct7 σ⁻¹ x) - permAct7 σ⁻¹ x,
        ⟨permAct7 σ⁻¹ x, permAct7_mem_evenWeight _ hx, rfl⟩, ?_⟩
      rw [map_sub, permAct7_conj, permAct7_apply_inv]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨permAct7 σ x, permAct7_mem_evenWeight _ hx, ?_⟩
      rw [map_sub, permAct7_conj, permAct7_inv_apply]
  have hinj : Function.Injective (permAct7 σ) := fun u v h => by
    have := congrArg (permAct7 σ⁻¹) h
    rwa [permAct7_inv_apply, permAct7_inv_apply] at this
  rw [hmap]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _).symm


theorem zmod_two_add_self : ∀ a : ZMod 2, a + a = 0 := by
  decide

theorem A7_even_weight_hyperplane_centralizer_geometry {B : Subgroup (Perm (Fin 7))}
    (hB : CFSG.IsElementaryAbelian 2 B) (hB4 : 4 ≤ Nat.card B)
    (hW : ∀ v ∈ commSpan B, v ≠ 0 → hammingNorm v = 4) :
    ∃ σ : Perm (Fin 7),
      B.map (MulAut.conj σ).toMonoidHom = kleinStd ∧
      (∀ b ∈ B, ∀ i : Fin 7, 4 ≤ i.val → (σ * b * σ⁻¹) i = i) ∧
      (hyperplaneSum B).map (permAct7 σ) = hyperplaneStd ∧
      (commSpan B).map (permAct7 σ) = Submodule.span (ZMod 2) {vecFirstFour} ∧
      (fixedEven B).map (permAct7 σ) = Submodule.span (ZMod 2)
        {vecFirstFour, Pi.single 4 1 + Pi.single 5 1, Pi.single 4 1 + Pi.single 6 1} ∧
      fixedEven B ≤ hyperplaneSum B ∧
      ∀ b ∈ B, b ≠ 1 →
        finrank (ZMod 2) ((evenWeight 7).map (permAct7 b - LinearMap.id)) = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 B := CFSG.IsElementaryAbelian.isPGroup 2 B
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (@CFSG.IsElementaryAbelian.exponent_dvd_p 2 B _ hB) ⟨b, hb⟩
    have h' := congrArg Subtype.val h
    simpa [pow_two] using h'
  have hncard7 : ∀ s : Set (Fin 7), s.ncard ≤ 7 := fun s =>
    (Set.ncard_le_ncard (Set.subset_univ s) (Set.toFinite _)).trans
      (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin])
  have horb1 : ∀ x : Fin 7, (MulAction.orbit B x).ncard = 1 ↔ ∀ b ∈ B, b x = x := by
    intro x
    rw [Set.ncard_eq_one]
    constructor
    · rintro ⟨y, hy⟩ b hb
      have h1 : x ∈ MulAction.orbit B x := MulAction.mem_orbit_self x
      have h2 : (⟨b, hb⟩ : B) • x ∈ MulAction.orbit B x := MulAction.mem_orbit _ _
      rw [hy, Set.mem_singleton_iff] at h1 h2
      exact h2.trans h1.symm
    · intro h
      refine ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨MulAction.mem_orbit_self x, ?_⟩⟩
      rintro _ ⟨⟨b, hb⟩, rfl⟩
      exact h b hb
  obtain ⟨j, hj⟩ : ∃ j : Fin 7, ∀ b ∈ B, b j = j := by
    have h := hBp.card_modEq_card_fixedPoints (Fin 7)
    by_contra hne
    push Not at hne
    have hempty : MulAction.fixedPoints B (Fin 7) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      obtain ⟨b, hb, hby⟩ := hne y
      exact hby (hy ⟨b, hb⟩)
    have h0 : Nat.card (∅ : Set (Fin 7)) = 0 := by simp
    rw [hempty, h0, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact absurd h (by decide)
  obtain ⟨m, hm⟩ := hBp.exists_card_eq
  have horbsize : ∀ x : Fin 7, (MulAction.orbit B x).ncard = 1 ∨ (MulAction.orbit B x).ncard = 2 ∨
      (MulAction.orbit B x).ncard = 4 := by
    intro x
    have hdvd : (MulAction.orbit B x).ncard ∣ 2 ^ m := by
      rw [← MulAction.index_stabilizer, ← hm]
      exact Subgroup.index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hle := hncard7 (MulAction.orbit B x)
    rw [hk] at hle ⊢
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k <;> simp
  have hno2 : ∀ i : Fin 7, (MulAction.orbit B i).ncard ≠ 2 := by
    intro i hi
    set X := (MulAction.stabilizer B i).map B.subtype with hX
    have hXB : X ≤ B := Subgroup.map_subtype_le _
    have hXidx : (X.subgroupOf B).index = 2 := by
      rw [hX, subgroupOf_map_subtype_self, MulAction.index_stabilizer, hi]
    have hv : (Pi.single i 1 + Pi.single j 1 : Fin 7 → ZMod 2) ∈ hyperplaneSum B := by
      refine (le_iSup₂ (f := fun X (_ : X ≤ B ∧ (X.subgroupOf B).index = 2) => fixedEven X) X
        ⟨hXB, hXidx⟩) ⟨pair_mem_evenWeight i j, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have hsi : (s : Perm (Fin 7)) i = i := hs
      rw [map_add, permAct7_single, permAct7_single, Subgroup.coe_subtype, hsi, hj s s.2]
    obtain ⟨b, hb, hbi⟩ : ∃ b ∈ B, b i ≠ i := by
      by_contra h
      push Not at h
      rw [(horb1 i).2 h] at hi
      exact absurd hi (by norm_num)
    have hu : (Pi.single i 1 + Pi.single (b i) 1 : Fin 7 → ZMod 2) ∈ commSpan B := by
      apply Submodule.subset_span
      refine ⟨_, hv, b, hb, ?_⟩
      rw [map_add, permAct7_single, permAct7_single, hj b hb]
      funext k
      simp only [Pi.add_apply]
      linear_combination (-1 : ZMod 2) * zmod_two_add_self ((Pi.single j 1 : Fin 7 → ZMod 2) k)
    obtain ⟨hw2, hne⟩ := hammingNorm_pair i (b i) (fun h => hbi h.symm)
    have := hW _ hu hne
    omega
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    push Not at h
    have : B = ⊥ := eq_bot_iff.2 fun b hb => (Subgroup.mem_bot).2 (h b hb)
    rw [this, Subgroup.card_bot] at hB4
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x, b₀ x ≠ x := by
    by_contra h
    push Not at h
    exact hb₀1 (Equiv.Perm.ext h)
  have hx₀4 : (MulAction.orbit B x₀).ncard = 4 := by
    rcases horbsize x₀ with h | h | h
    · exact absurd ((horb1 x₀).1 h b₀ hb₀) hx₀
    · exact absurd h (hno2 x₀)
    · exact h
  set O := MulAction.orbit B x₀ with hO
  have hout : ∀ y ∉ O, ∀ b ∈ B, b y = y := by
    intro y hy
    rw [← horb1]
    rcases horbsize y with h | h | h
    · exact h
    · exact absurd h (hno2 y)
    · exfalso
      have hdisj : Disjoint O (MulAction.orbit B y) := by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        apply hy
        have h1 : MulAction.orbit B z = O := MulAction.orbit_eq_iff.2 hz1
        have h2 : MulAction.orbit B z = MulAction.orbit B y := MulAction.orbit_eq_iff.2 hz2
        rw [← h1, h2]
        exact MulAction.mem_orbit_self y
      have := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
      have := hncard7 (O ∪ MulAction.orbit B y)
      omega
  have hreg : ∀ x ∈ O, ∀ b ∈ B, b x = x → b = 1 := by
    intro x hx b hb hbx
    refine Equiv.Perm.ext fun y => ?_
    by_cases hy : y ∈ O
    · have hyx : y ∈ MulAction.orbit B x := by
        rw [MulAction.orbit_eq_iff.2 hx]
        exact hy
      obtain ⟨⟨c, hc⟩, rfl⟩ := hyx
      change b (c x) = c x
      have := congrArg (· x) (hcomm b hb c hc)
      simp only [Perm.mul_apply, hbx] at this
      exact this
    · exact hout y hy b hb
  have hcardB : Nat.card B = 4 := by
    have hstab : MulAction.stabilizer B x₀ = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨b, hb⟩ hbx
      exact (Subgroup.mem_bot).2 (Subtype.ext (hreg x₀ (MulAction.mem_orbit_self x₀) b hb hbx))
    have h := MulAction.index_stabilizer B x₀
    rw [hstab, Subgroup.index_bot] at h
    rw [h, hx₀4]
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff (O := O.toFinset) (T := {0, 1, 2, 3})
    (by rw [← Set.ncard_eq_toFinset_card', hx₀4]; rfl)
  have hσ' : ∀ x, x ∈ O ↔ (σ x).val < 4 := by
    intro x
    rw [← Set.mem_toFinset, hσ]
    generalize σ x = y
    revert y
    decide
  have hσσ : ∀ t, σ (σ⁻¹ t) = t := fun t => by rw [Perm.inv_def, Equiv.apply_symm_apply]
  have hfix : ∀ b ∈ B, ∀ i : Fin 7, 4 ≤ i.val → (σ * b * σ⁻¹) i = i := by
    intro b hb i hi
    have hnot : σ⁻¹ i ∉ O := by
      rw [hσ', hσσ]
      omega
    rw [Perm.mul_apply, Perm.mul_apply, hout _ hnot b hb, hσσ]
  have hconj : ∀ b ∈ B, regularFourCond (σ * b * σ⁻¹) := by
    intro b hb
    refine ⟨hfix b hb 4 (by decide), hfix b hb 5 (by decide), hfix b hb 6 (by decide), ?_, ?_⟩
    · rw [show σ * b * σ⁻¹ * (σ * b * σ⁻¹) = σ * (b * b) * σ⁻¹ by group, hsq b hb, mul_one,
        mul_inv_cancel]
    · by_cases hb1 : b = 1
      · left
        rw [hb1, mul_one, mul_inv_cancel]
      · right
        have hnf : ∀ t : Fin 7, t.val < 4 → (σ * b * σ⁻¹) t ≠ t := by
          intro t ht h
          apply hb1
          have hmem : σ⁻¹ t ∈ O := by
            rw [hσ', hσσ]
            exact ht
          refine hreg _ hmem b hb ?_
          rw [Perm.mul_apply, Perm.mul_apply] at h
          have := congrArg (⇑(σ⁻¹)) h
          rwa [Perm.inv_def, Equiv.symm_apply_apply, ← Perm.inv_def] at this
        exact ⟨hnf 0 (by decide), hnf 1 (by decide), hnf 2 (by decide), hnf 3 (by decide)⟩
  have hmapB : B.map (MulAut.conj σ).toMonoidHom = kleinStd := by
    have hle : B.map (MulAut.conj σ).toMonoidHom ≤ kleinStd := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨k, hk⟩ := exists_kleinStdFun_of_regularFourCond (hconj b hb)
      exact mem_kleinStd_iff.2 ⟨k, hk⟩
    refine eq_of_le_of_card_ge hle ?_
    rw [nat_card_kleinStd, Subgroup.card_map_of_injective (MulAut.conj σ).injective, hcardB]
  have hinj : Function.Injective (permAct7 σ) := fun u v h => by
    have := congrArg (permAct7 σ⁻¹) h
    rwa [permAct7_inv_apply, permAct7_inv_apply] at this
  refine ⟨σ, hmapB, hfix, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hyperplaneSum_map_conj, hmapB, hyperplaneSum_kleinStd]
  · rw [← commSpan_map_conj, hmapB, commSpan_kleinStd]
  · rw [← fixedEven_map_conj, hmapB, fixedEven_kleinStd]
  · rw [← Submodule.map_le_map_iff_of_injective hinj, ← fixedEven_map_conj,
      ← hyperplaneSum_map_conj, hmapB, fixedEven_kleinStd, hyperplaneSum_kleinStd,
      Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> (rw [SetLike.mem_coe, mem_hyperplaneStd]; decide)
  · intro b hb hb1
    rw [← finrank_image_conj σ b]
    obtain ⟨k, hk⟩ := exists_kleinStdFun_of_regularFourCond (hconj b hb)
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hb1
      have h1 : σ * b * σ⁻¹ = 1 := hk
      calc b = σ⁻¹ * (σ * b * σ⁻¹) * σ := by group
        _ = 1 := by rw [h1]; group
    exact finrank_image_kleinStd hk0

end CFSG.Quasithin.SteinbergCB
