module

public import CFSG.Timmesfeld.Transvection.PresSpRoots
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Roots.Levels
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
import all CFSG.LieType.Universal.Unitary.Roots
import Mathlib.Tactic.NoncommRing
public import CFSG.LieType.Steinberg.Isogeny.Lift

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

variable {m : ℕ}

@[expose] def crd : Fin (m / 2) ⊕ Fin (m / 2) → Fin m
  | .inl a => lowIdx a
  | .inr a => Fin.rev (lowIdx a)

@[simp] theorem crd_inl (a : Fin (m / 2)) : crd (Sum.inl a : Fin (m / 2) ⊕ Fin (m / 2)) =
    lowIdx a := rfl

@[simp] theorem crd_inr (a : Fin (m / 2)) : crd (Sum.inr a : Fin (m / 2) ⊕ Fin (m / 2)) =
    Fin.rev (lowIdx a) := rfl

theorem crd_swap (a : Fin (m / 2) ⊕ Fin (m / 2)) : crd (Sum.swap a) = Fin.rev (crd a) := by
  rcases a with a | a <;> simp

theorem crd_injective : Function.Injective (crd (m := m)) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [crd_inl, crd_inr, Fin.rev_inj] at h
  · have := congrArg Fin.val h
    simp only [val_lowIdx] at this
    exact congrArg Sum.inl (Fin.ext this)
  · exact absurd h (lowIdx_ne_rev a b)
  · exact absurd h.symm (lowIdx_ne_rev b a)
  · have := congrArg Fin.val h
    simp only [val_lowIdx] at this
    exact congrArg Sum.inr (Fin.ext this)

theorem crd_ne_rev (a : Fin (m / 2) ⊕ Fin (m / 2)) : crd a ≠ Fin.rev (crd a) := by
  rw [← crd_swap]
  exact fun h => swap_ne_self a (crd_injective h).symm

theorem crd_eq_rev_iff {a b : Fin (m / 2) ⊕ Fin (m / 2)} :
    crd b = Fin.rev (crd a) ↔ b = Sum.swap a := by
  rw [← crd_swap]
  exact crd_injective.eq_iff

theorem weight_crd (a : Fin (m / 2) ⊕ Fin (m / 2)) : weight m (crd a) = wt a := by
  rcases a with a | a
  · exact weight_lowIdx a
  · exact weight_rev_lowIdx a

theorem exists_crd_eq (he : Even m) (i : Fin m) : ∃ a, crd a = i := by
  have hi : i ≠ Fin.rev i := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    obtain ⟨k, hk⟩ := he
    omega
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · exact ⟨Sum.inl a, rfl⟩
  · exact ⟨Sum.inr a, rfl⟩

theorem crd_ne_crd_swap {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) :
    crd a ≠ crd (Sum.swap b) := fun e => by
  have := crd_injective e
  rw [this, idx_swap] at h
  exact h rfl

section Elements

variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def suElt (a b : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) : SU σ m :=
  if h : idx a ≠ idx b then
    rootHom σ hσ (crd_ne_crd_swap h) (crd_ne_rev a) (crd_ne_rev (Sum.swap b))
      (Multiplicative.ofAdd c)
  else 1

open Classical in
@[expose] noncomputable def suLong (a : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) : SU σ m :=
  if h : c + σ c = 0 then longRootHom σ (crd_ne_rev a) (Multiplicative.ofAdd ⟨c, h⟩) else 1

variable {σ}

theorem mat_suElt {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) (c : F) :
    mat σ m (suElt σ hσ a b c) =
      1 + single (crd a) (crd (Sum.swap b)) c - single (crd b) (crd (Sum.swap a)) (σ c) := by
  rw [suElt, dite_eq_left h, mat_apply, coe_rootHom, toAdd_ofAdd, rootMatrix, crd_swap b,
    Fin.rev_rev, ← crd_swap a]

theorem mat_suLong (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F} (h : c + σ c = 0) :
    mat σ m (suLong σ a c) = 1 + single (crd a) (crd (Sum.swap a)) c := by
  rw [suLong, dite_eq_left h, mat_apply, coe_longRootHom, toAdd_ofAdd, longRootMatrix, crd_swap]

theorem suElt_add {a b : Fin (m / 2) ⊕ Fin (m / 2)} (c d : F) :
    suElt σ hσ a b (c + d) = suElt σ hσ a b c * suElt σ hσ a b d := by
  by_cases h : idx a ≠ idx b
  · simp only [suElt, dite_eq_left h, ofAdd_add, map_mul]
  · simp only [suElt, dite_eq_right h, mul_one]

theorem suElt_zero (a b : Fin (m / 2) ⊕ Fin (m / 2)) : suElt σ hσ a b (0 : F) = 1 := by
  by_cases h : idx a ≠ idx b
  · simp only [suElt, dite_eq_left h, ofAdd_zero, map_one]
  · simp only [suElt, dite_eq_right h]

theorem suLong_add (a : Fin (m / 2) ⊕ Fin (m / 2)) {c d : F} (hc : c + σ c = 0)
    (hd : d + σ d = 0) : suLong σ a (c + d) = suLong σ a c * suLong σ a d := by
  have hcd : c + d + σ (c + d) = 0 := by rw [map_add, add_add_add_comm, hc, hd, add_zero]
  rw [suLong, dite_eq_left hcd, suLong, dite_eq_left hc, suLong, dite_eq_left hd, ← map_mul]
  rfl

theorem suLong_zero (a : Fin (m / 2) ⊕ Fin (m / 2)) : suLong σ a (0 : F) = 1 := by
  have h0 : (0 : F) + σ 0 = 0 := by simp
  rw [suLong, dite_eq_left h0]
  exact map_one _

theorem suElt_swap {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) (c : F) :
    suElt σ hσ b a c = suElt σ hσ a b (-σ c) := by
  apply mat_injective
  rw [mat_suElt hσ (Ne.symm h), mat_suElt hσ h, map_neg, hσ]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, single_apply]
  split_ifs <;> simp_all <;> ring

theorem suElt_mem {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) {γ : Fin (m / 2) → ℤ}
    (hγ : toStd m γ = rt a b) (c : F) : suElt σ hσ a b c ∈ rootGroup σ hσ m γ := by
  rw [suElt, dite_eq_left h]
  refine rootHom_mem hσ _ _ _ ?_ ?_ _
  · rw [crd_swap b, Ne, Fin.rev_inj]
    exact fun e => ne_of_idx_ne h (crd_injective e)
  · rw [weight_crd, weight_crd, hγ, rt, CFSG.LieType.Steinberg.Sp.wt_swap, sub_neg_eq_add]

theorem suLong_mem (a : Fin (m / 2) ⊕ Fin (m / 2)) {γ : Fin (m / 2) → ℤ}
    (hγ : toStd m γ = rt a a) (c : F) : suLong σ a c ∈ rootGroup σ hσ m γ := by
  by_cases h : c + σ c = 0
  · rw [suLong, dite_eq_left h]
    refine longRootHom_mem hσ _ ?_ _
    rw [weight_crd, hγ, rt, two_nsmul]
  · rw [suLong, dite_eq_right h]
    exact one_mem _

end Elements

section Range

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem rev_ne_self_of_even (he : Even m) (k : Fin m) : Fin.rev k ≠ k := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_rev] at this
  obtain ⟨r, hr⟩ := he
  omega

theorem exists_weight_eq_wt (he : Even m) (i : Fin m) : ∃ e, crd e = i ∧ weight m i = wt e := by
  obtain ⟨e, rfl⟩ := exists_crd_eq he i
  exact ⟨e, rfl, weight_crd e⟩

theorem mem_rootGroup_iff_suElt (he : Even m) {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) (g : SU σ m) :
    g ∈ rootGroup σ hσ m γ ↔ ∃ c, suElt σ hσ a b c = g := by
  refine ⟨fun hg => ?_, fun ⟨c, hc⟩ => hc ▸ suElt_mem hσ hab hγ c⟩
  set T := (rootHom σ hσ (crd_ne_crd_swap hab) (crd_ne_rev a) (crd_ne_rev (Sum.swap b))).range
  have hT : ∀ g ∈ T, ∃ c, suElt σ hσ a b c = g := by
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, by rw [suElt, dite_eq_left hab]; rfl⟩
  have hji₀ : crd (Sum.swap b) ≠ Fin.rev (crd a) := by
    rw [crd_swap b, Ne, Fin.rev_inj]
    exact fun e => ne_of_idx_ne hab (crd_injective e)
  have hw₀ : weight m (crd a) - weight m (crd (Sum.swap b)) = toStd m γ := by
    rw [weight_crd, weight_crd, hγ, rt, CFSG.LieType.Steinberg.Sp.wt_swap, sub_neg_eq_add]
  refine hT g ?_
  revert hg
  refine fun hg => (show rootGroup σ hσ m γ ≤ T from ?_) hg
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun hji => iSup_le fun hw => ?_
    rcases eq_of_weight_sub_eq_sub (crd_ne_crd_swap hab) (crd_ne_rev a) (crd_ne_rev _) hji₀
      (hw.trans hw₀.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_rfl
    · rintro _ ⟨c, rfl⟩
      refine ⟨Multiplicative.ofAdd (-σ (Multiplicative.toAdd c)), ?_⟩
      apply mat_injective
      rw [mat_apply, mat_apply, coe_rootHom, coe_rootHom, toAdd_ofAdd]
      simp only [rootMatrix, Fin.rev_rev, map_neg, hσ]
      rw [← single_neg, ← single_neg]
      abel
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    exfalso
    obtain ⟨e, -, hwe⟩ := exists_weight_eq_wt he i
    rw [hwe, hγ] at hw
    have h1 := congrArg (fun v => v ⬝ᵥ v) hw
    simp only [smul_dotProduct, dotProduct_smul, CFSG.LieType.Steinberg.Sp.dot_wt_self,
      rt_dot_rt, wt_dot_of_idx_ne hab] at h1
    norm_num at h1
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact absurd hk (rev_ne_self_of_even he k)

theorem mem_rootGroup_iff_suLong (he : Even m) (a : Fin (m / 2) ⊕ Fin (m / 2))
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) (g : SU σ m) :
    g ∈ rootGroup σ hσ m γ ↔ ∃ c, c + σ c = 0 ∧ suLong σ a c = g := by
  refine ⟨fun hg => ?_, fun ⟨c, _, hc⟩ => hc ▸ suLong_mem hσ a hγ c⟩
  set T := (longRootHom σ (crd_ne_rev a)).range
  have hT : ∀ g ∈ T, ∃ c, c + σ c = 0 ∧ suLong σ a c = g := by
    rintro _ ⟨c, rfl⟩
    have hc : ((Multiplicative.toAdd c : traceZero σ) : F) +
        σ ((Multiplicative.toAdd c : traceZero σ) : F) = 0 := (Multiplicative.toAdd c).2
    refine ⟨((Multiplicative.toAdd c : traceZero σ) : F), hc, ?_⟩
    rw [suLong, dite_eq_left hc]
    rfl
  have hwa : wt a ≠ 0 := fun h => by
    have := CFSG.LieType.Steinberg.Sp.dot_wt_self a
    rw [h, zero_dotProduct] at this
    exact zero_ne_one this
  refine hT g ?_
  revert hg
  refine fun hg => (show rootGroup σ hσ m γ ≤ T from ?_) hg
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun hji => iSup_le fun hw => ?_
    exfalso
    rw [hγ, rt, ← two_nsmul] at hw
    exact hji (eq_rev_of_weight_sub_eq_two_smul hw hwa).1
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rw [hγ, rt, ← two_nsmul, ← weight_crd a] at hw
    have hw' : weight m i = weight m (crd a) := by
      funext c
      have := congrFun hw c
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
      omega
    obtain rfl := weight_injective hw'
    exact le_rfl
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact absurd hk (rev_ne_self_of_even he k)

end Range

section Commutators

theorem single_mul_single' {n : ℕ} {R : Type*} [Semiring R] (i j k l : Fin n) (a b : R) :
    single i j a * single k l b = if j = k then single i l (a * b) else 0 := by
  split_ifs with h
  · subst h
    exact single_mul_single_same _ _ _ _ _
  · exact single_mul_single_of_ne _ _ _ _ h _

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem mat_commutator_eq {x y : SU σ m} {A B : Matrix (Fin m) (Fin m) F}
    (hx : mat σ m x = 1 + A) (hy : mat σ m y = 1 + B) (hA : A * A = 0) (hB : B * B = 0) :
    mat σ m ⁅x, y⁆ = 1 + (A * B - B * A) - A * B * A + B * A * B + A * B * A * B := by
  have hinv : ∀ (z : SU σ m) (C : Matrix (Fin m) (Fin m) F), mat σ m z = 1 + C → C * C = 0 →
      mat σ m z⁻¹ = 1 - C := by
    intro z C hz hC
    have h1 : mat σ m z⁻¹ * mat σ m z = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    calc mat σ m z⁻¹ = mat σ m z⁻¹ * ((1 + C) * (1 - C)) := by
          rw [show (1 + C) * (1 - C) = 1 - C * C by noncomm_ring, hC, sub_zero, mul_one]
      _ = 1 - C := by rw [← mul_assoc, ← hz, h1, one_mul]
  rw [commutatorElement_def, map_mul, map_mul, map_mul, hx, hy, hinv x A hx hA, hinv y B hy hB]
  have e : (1 + A) * (1 + B) * (1 - A) * (1 - B) =
      1 + (A * B - B * A) - A * B * A + B * A * B + A * B * A * B - A * A - B * B -
        A * (B * B) + A * A * B := by noncomm_ring
  rw [e, hA, hB]
  simp

variable [CharP F 2]

theorem mat_suElt_two {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) (c : F) :
    mat σ m (suElt σ hσ a b c) =
      1 + (single (crd a) (crd (Sum.swap b)) c + single (crd b) (crd (Sum.swap a)) (σ c)) := by
  rw [mat_suElt hσ h, sub_eq_add_neg, single_neg, CharTwo.neg_eq, add_assoc]

theorem ne_facts {p q : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx p ≠ idx q) :
    p ≠ q ∧ Sum.swap p ≠ q ∧ p ≠ Sum.swap q ∧ Sum.swap p ≠ Sum.swap q := by
  refine ⟨Ne.symm (ne_of_idx_ne h), fun e => h ?_, fun e => h ?_, fun e => h ?_⟩
  · rw [← e, idx_swap]
  · rw [e, idx_swap]
  · rw [← idx_swap p, e, idx_swap]

theorem suElt_comm_short {a b d : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    (hbd : idx b ≠ idx d) (had : idx a ≠ idx d) (s t : F) :
    ⁅suElt σ hσ a b s, suElt σ hσ (Sum.swap b) d t⁆ = suElt σ hσ a d (s * t) := by
  have hbd' : idx (Sum.swap b) ≠ idx d := by rwa [idx_swap]
  obtain ⟨n1, n2, n3, n4⟩ := ne_facts hab
  obtain ⟨n5, n6, n7, n8⟩ := ne_facts hbd
  obtain ⟨n9, n10, n11, n12⟩ := ne_facts had
  obtain ⟨n1', n2', n3', n4'⟩ := ne_facts hab.symm
  obtain ⟨n5', n6', n7', n8'⟩ := ne_facts hbd.symm
  obtain ⟨n9', n10', n11', n12'⟩ := ne_facts had.symm
  have sa := swap_ne_self a
  have sb := swap_ne_self b
  have sd := swap_ne_self d
  have sa' := (swap_ne_self a).symm
  have sb' := (swap_ne_self b).symm
  have sd' := (swap_ne_self d).symm
  apply mat_injective
  rw [mat_commutator_eq (mat_suElt_two hσ hab s) (mat_suElt_two hσ hbd' t), mat_suElt_two hσ had]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_true, ite_false, add_zero, zero_add, zero_mul, sub_zero, map_mul, *]
    rw [sub_eq_add_neg, single_neg, CharTwo.neg_eq, mul_comm (σ t)]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff,
      ite_false, add_zero, *]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_false, add_zero, *]

theorem add_map_eq_zero_iff {c : F} : c + σ c = 0 ↔ σ c = c := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq, eq_comm]

theorem suElt_comm_shortLong {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) (s : F)
    {t : F} (ht : σ t = t) :
    ⁅suElt σ hσ a b s, suLong σ (Sum.swap b) t⁆ =
      suElt σ hσ a (Sum.swap b) (s * t) * suLong σ a (σ s * s * t) := by
  have hab' : idx a ≠ idx (Sum.swap b) := by rwa [idx_swap]
  obtain ⟨n1, n2, n3, n4⟩ := ne_facts hab
  obtain ⟨n1', n2', n3', n4'⟩ := ne_facts hab.symm
  have sa := swap_ne_self a
  have sb := swap_ne_self b
  have sa' := (swap_ne_self a).symm
  have sb' := (swap_ne_self b).symm
  have ht0 : t + σ t = 0 := add_map_eq_zero_iff.2 ht
  have hc0 : σ s * s * t + σ (σ s * s * t) = 0 := by
    rw [add_map_eq_zero_iff, map_mul, map_mul, hσ, ht, mul_comm (σ s) s]
  apply mat_injective
  rw [mat_commutator_eq (mat_suElt_two hσ hab s) (mat_suLong (Sum.swap b) ht0), map_mul,
    mat_suElt_two hσ hab', mat_suLong a hc0]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_true, ite_false, add_zero, zero_add, map_mul, mul_one, *]
    rw [sub_eq_add_neg, single_neg, CharTwo.neg_eq, sub_eq_add_neg, single_neg, CharTwo.neg_eq,
      mul_comm t (σ s), show s * t * σ s = σ s * s * t by ring, one_mul]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff,
      ite_false, add_zero, *]
  · simp only [single_mul_single', crd_injective.eq_iff, Sum.swap_swap, ite_false, *]

theorem suLong_comm_short {a d : Fin (m / 2) ⊕ Fin (m / 2)} (had : idx a ≠ idx d) {s : F}
    (hs : σ s = s) (t : F) :
    ⁅suLong σ a s, suElt σ hσ (Sum.swap a) d t⁆ =
      suElt σ hσ a d (s * t) * suLong σ d (s * σ t * t) := by
  have had' : idx (Sum.swap a) ≠ idx d := by rwa [idx_swap]
  obtain ⟨n1, n2, n3, n4⟩ := ne_facts had
  obtain ⟨n1', n2', n3', n4'⟩ := ne_facts had.symm
  have sa := swap_ne_self a
  have sd := swap_ne_self d
  have sa' := (swap_ne_self a).symm
  have sd' := (swap_ne_self d).symm
  have hs0 : s + σ s = 0 := add_map_eq_zero_iff.2 hs
  have hc0 : s * σ t * t + σ (s * σ t * t) = 0 := by
    rw [add_map_eq_zero_iff, map_mul, map_mul, hσ, hs, mul_assoc, mul_assoc, mul_comm (σ t)]
  apply mat_injective
  rw [mat_commutator_eq (mat_suLong a hs0) (mat_suElt_two hσ had' t), map_mul,
    mat_suElt_two hσ had, mat_suLong d hc0]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_true, ite_false, add_zero, zero_add, sub_zero, map_mul, mul_one, zero_mul, one_mul, *]
    rw [sub_eq_add_neg, single_neg, CharTwo.neg_eq, mul_comm (σ t) s]
  · simp only [single_mul_single', crd_injective.eq_iff, ite_false, *]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_false, add_zero, *]

theorem suElt_comm_trace {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) (s t : F) :
    ⁅suElt σ hσ a b s, suElt σ hσ a (Sum.swap b) t⁆ = suLong σ a (s * σ t + σ s * t) := by
  have hab' : idx a ≠ idx (Sum.swap b) := by rwa [idx_swap]
  obtain ⟨n1, n2, n3, n4⟩ := ne_facts hab
  obtain ⟨n1', n2', n3', n4'⟩ := ne_facts hab.symm
  have sa := swap_ne_self a
  have sb := swap_ne_self b
  have sa' := (swap_ne_self a).symm
  have sb' := (swap_ne_self b).symm
  have hc0 : s * σ t + σ s * t + σ (s * σ t + σ s * t) = 0 := by
    rw [add_map_eq_zero_iff, map_add, map_mul, map_mul, hσ, hσ, add_comm, mul_comm (σ s),
      mul_comm s]
  apply mat_injective
  rw [mat_commutator_eq (mat_suElt_two hσ hab s) (mat_suElt_two hσ hab' t), mat_suLong a hc0]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_true, ite_false, add_zero, zero_add, sub_zero, zero_mul, *]
    rw [sub_eq_add_neg, single_neg, CharTwo.neg_eq, ← single_add, mul_comm t (σ s)]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff,
      ite_false, add_zero, *]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, Sum.swap_swap,
      ite_false, add_zero, *]

theorem swap_ne_of_ne_swap {p q : Fin (m / 2) ⊕ Fin (m / 2)} (h : q ≠ Sum.swap p) :
    Sum.swap q ≠ p := fun e => h (by rw [← e, Sum.swap_swap])

theorem suLong_comm_long {a c : Fin (m / 2) ⊕ Fin (m / 2)} (hca : c ≠ Sum.swap a) {s t : F}
    (hs : σ s = s) (ht : σ t = t) : ⁅suLong σ a s, suLong σ c t⁆ = 1 := by
  have h1 := Ne.symm hca
  have h2 := swap_ne_of_ne_swap hca
  have sa := swap_ne_self a
  have sc := swap_ne_self c
  have sa' := (swap_ne_self a).symm
  have sc' := (swap_ne_self c).symm
  apply mat_injective
  rw [mat_commutator_eq (mat_suLong a (add_map_eq_zero_iff.2 hs))
    (mat_suLong c (add_map_eq_zero_iff.2 ht)), map_one]
  · simp only [single_mul_single', crd_injective.eq_iff, ite_false, *]
    simp
  · simp only [single_mul_single', crd_injective.eq_iff, ite_false, *]
  · simp only [single_mul_single', crd_injective.eq_iff, ite_false, *]

theorem suLong_comm_shortGen {a c d : Fin (m / 2) ⊕ Fin (m / 2)} (hcd : idx c ≠ idx d)
    (hca : c ≠ Sum.swap a) (hda : d ≠ Sum.swap a) {s : F} (hs : σ s = s) (t : F) :
    ⁅suLong σ a s, suElt σ hσ c d t⁆ = 1 := by
  obtain ⟨n1, n2, n3, n4⟩ := ne_facts hcd
  obtain ⟨n1', n2', n3', n4'⟩ := ne_facts hcd.symm
  have h1 := Ne.symm hca
  have h2 := swap_ne_of_ne_swap hca
  have h3 := Ne.symm hda
  have h4 := swap_ne_of_ne_swap hda
  have sa := swap_ne_self a
  have sa' := (swap_ne_self a).symm
  have sc := swap_ne_self c
  have sc' := (swap_ne_self c).symm
  have sd := swap_ne_self d
  have sd' := (swap_ne_self d).symm
  apply mat_injective
  rw [mat_commutator_eq (mat_suLong a (add_map_eq_zero_iff.2 hs)) (mat_suElt_two hσ hcd t),
    map_one]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, ite_false, add_zero,
      *]
    simp
  · simp only [single_mul_single', crd_injective.eq_iff, ite_false, *]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, ite_false, add_zero,
      *]

theorem suElt_comm_shortGen {a b c d : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    (hcd : idx c ≠ idx d) (hca : c ≠ Sum.swap a) (hcb : c ≠ Sum.swap b) (hda : d ≠ Sum.swap a)
    (hdb : d ≠ Sum.swap b) (s t : F) : ⁅suElt σ hσ a b s, suElt σ hσ c d t⁆ = 1 := by
  obtain ⟨n1, n2, n3, n4⟩ := ne_facts hab
  obtain ⟨n1', n2', n3', n4'⟩ := ne_facts hab.symm
  obtain ⟨n5, n6, n7, n8⟩ := ne_facts hcd
  obtain ⟨n5', n6', n7', n8'⟩ := ne_facts hcd.symm
  have h1 := Ne.symm hca
  have h2 := swap_ne_of_ne_swap hca
  have h3 := Ne.symm hda
  have h4 := swap_ne_of_ne_swap hda
  have h5 := Ne.symm hcb
  have h6 := swap_ne_of_ne_swap hcb
  have h7 := Ne.symm hdb
  have h8 := swap_ne_of_ne_swap hdb
  have sa := swap_ne_self a
  have sa' := (swap_ne_self a).symm
  have sb := swap_ne_self b
  have sb' := (swap_ne_self b).symm
  have sc := swap_ne_self c
  have sc' := (swap_ne_self c).symm
  have sd := swap_ne_self d
  have sd' := (swap_ne_self d).symm
  apply mat_injective
  rw [mat_commutator_eq (mat_suElt_two hσ hab s) (mat_suElt_two hσ hcd t), map_one]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, ite_false, add_zero,
      *]
    simp
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, ite_false, add_zero,
      *]
  · simp only [add_mul, mul_add, single_mul_single', crd_injective.eq_iff, ite_false, add_zero,
      *]

end Commutators

end CFSG.Timmesfeld.Transvection.Pres
