module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreOrbits
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Algebra.Module.Pi
public import Mathlib.GroupTheory.Perm.Cycle.Basic

public section

namespace CFSG.StandardType.GGK0ExcCentreU

private def lk0xpa3_orb {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Set (Fin n) :=
  Set.range (fun k : ℤ => (σ ^ k) i)

private def lk0xpa3_Q {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Type :=
  {O : Set (Fin n) // ∃ i ∈ S, O = lk0xpa3_orb σ i}

private lemma lk0xpa3_numOrbitsOn_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    numOrbitsOn σ S = Nat.card (lk0xpa3_Q σ S) := by
  rw [numOrbitsOn]
  exact (Nat.card_coe_set_eq _).symm

private lemma lk0xpa3_mem_orb_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    j ∈ lk0xpa3_orb σ i ↔ σ.SameCycle i j :=
  Iff.rfl

private lemma lk0xpa3_mem_orb_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∈ lk0xpa3_orb σ i :=
  (lk0xpa3_mem_orb_iff σ i i).mpr (Equiv.Perm.SameCycle.refl σ i)

private lemma lk0xpa3_orb_eq_of_sameCycle {n : ℕ} (σ : Equiv.Perm (Fin n)) {i j : Fin n}
    (h : σ.SameCycle i j) : lk0xpa3_orb σ j = lk0xpa3_orb σ i := by
  ext x
  rw [lk0xpa3_mem_orb_iff, lk0xpa3_mem_orb_iff]
  exact ⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩

private lemma lk0xpa3_orb_sigma {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    lk0xpa3_orb σ (σ i) = lk0xpa3_orb σ i :=
  lk0xpa3_orb_eq_of_sameCycle σ ⟨1, by simp⟩

private lemma lk0xpa3_sigma_mem_orb_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (i0 i : Fin n) :
    σ i ∈ lk0xpa3_orb σ i0 ↔ i ∈ lk0xpa3_orb σ i0 := by
  rw [lk0xpa3_mem_orb_iff, lk0xpa3_mem_orb_iff]
  exact ⟨fun h => h.trans ⟨-1, by simp⟩, fun h => h.trans ⟨1, by simp⟩⟩

private lemma lk0xpa3_zpow_mem_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hS : ∀ i, σ i ∈ S ↔ i ∈ S) (k : ℤ) (i : Fin n) : (σ ^ k) i ∈ S ↔ i ∈ S := by
  have hnat : ∀ m : ℕ, ∀ i, (σ ^ m) i ∈ S ↔ i ∈ S := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih => intro i; rw [pow_succ', Equiv.Perm.mul_apply, hS, ih]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; exact hnat m i
  · rw [hm]
    have hz : σ ^ (-(m : ℤ)) = (σ ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz]
    simpa using (hnat m ((σ ^ m)⁻¹ i)).symm

private lemma lk0xpa3_orb_subset {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hS : ∀ i, σ i ∈ S ↔ i ∈ S) {i : Fin n} (hi : i ∈ S) : lk0xpa3_orb σ i ⊆ S := by
  intro j hj
  obtain ⟨k, rfl⟩ := (lk0xpa3_mem_orb_iff σ i j).mp hj
  exact (lk0xpa3_zpow_mem_iff σ S hS k i).mpr hi

private lemma lk0xpa3_zpow_apply_eq {n p : ℕ} (σ : Equiv.Perm (Fin n)) (t : Fin n → ZMod p)
    (ht : ∀ i, t (σ i) = t i) (k : ℤ) (i : Fin n) : t ((σ ^ k) i) = t i := by
  have hnat : ∀ m : ℕ, ∀ i, t ((σ ^ m) i) = t i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih => intro i; rw [pow_succ', Equiv.Perm.mul_apply, ht, ih]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; exact hnat m i
  · rw [hm]
    have hz : σ ^ (-(m : ℤ)) = (σ ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz]
    simpa using (hnat m ((σ ^ m)⁻¹ i)).symm

private lemma lk0xpa3_orb_apply_eq {n p : ℕ} (σ : Equiv.Perm (Fin n)) (t : Fin n → ZMod p)
    (ht : ∀ i, t (σ i) = t i) {i j : Fin n} (h : j ∈ lk0xpa3_orb σ i) : t j = t i := by
  obtain ⟨k, rfl⟩ := (lk0xpa3_mem_orb_iff σ i j).mp h
  exact lk0xpa3_zpow_apply_eq σ t ht k i

private noncomputable def lk0xpa3_lam {n p : ℕ} (c : Fin n → ZMod p) :
    (Fin n → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun t := ∑ i, c i * t i
  map_add' t u := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a t := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm]

private def lk0xpa3_W (p : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    Submodule (ZMod p) (Fin n → ZMod p) where
  carrier := {t | (∀ i, i ∉ S → t i = 0) ∧ (∀ i, t (σ i) = t i)}
  zero_mem' := by
    constructor <;> intro i <;> simp
  add_mem' := by
    rintro t u ⟨htA, htB⟩ ⟨huA, huB⟩
    constructor
    · intro i hi; simp [htA i hi, huA i hi]
    · intro i; simp [htB i, huB i]
  smul_mem' := by
    rintro a t ⟨htA, htB⟩
    constructor
    · intro i hi; simp [htA i hi]
    · intro i; simp [htB i]

private noncomputable def lk0xpa3_lamW {n p : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (c : Fin n → ZMod p) : lk0xpa3_W p σ S →ₗ[ZMod p] ZMod p :=
  (lk0xpa3_lam c).comp (lk0xpa3_W p σ S).subtype

private noncomputable def lk0xpa3_rep {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (q : lk0xpa3_Q σ S) : Fin n :=
  Classical.choose q.2

private lemma lk0xpa3_rep_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (q : lk0xpa3_Q σ S) : lk0xpa3_rep σ S q ∈ S :=
  (Classical.choose_spec q.2).1

private lemma lk0xpa3_orb_rep {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (q : lk0xpa3_Q σ S) : lk0xpa3_orb σ (lk0xpa3_rep σ S q) = q.1 :=
  (Classical.choose_spec q.2).2.symm

private noncomputable def lk0xpa3_cls {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) : lk0xpa3_Q σ S :=
  ⟨lk0xpa3_orb σ i, i, hi, rfl⟩

private noncomputable def lk0xpa3_toFun {n p : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    lk0xpa3_W p σ S → (lk0xpa3_Q σ S → ZMod p) :=
  fun t q => t.1 (lk0xpa3_rep σ S q)

private noncomputable def lk0xpa3_ofFun {n p : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hS : ∀ i, σ i ∈ S ↔ i ∈ S) : (lk0xpa3_Q σ S → ZMod p) → lk0xpa3_W p σ S := by
  classical
  exact fun f =>
    ⟨fun i => if h : i ∈ S then f ⟨lk0xpa3_orb σ i, i, h, rfl⟩ else 0, by
      constructor
      · intro i hi
        simp [hi]
      · intro i
        by_cases hi : i ∈ S
        · have hsi : σ i ∈ S := (hS i).mpr hi
          simp only [dif_pos hi, dif_pos hsi]
          exact congrArg f (Subtype.ext (lk0xpa3_orb_sigma σ i))
        · have hsi : σ i ∉ S := fun h => hi ((hS i).mp h)
          simp [hi, hsi]⟩

private noncomputable def lk0xpa3_equivWQ {n p : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hS : ∀ i, σ i ∈ S ↔ i ∈ S) :
    lk0xpa3_W p σ S ≃ (lk0xpa3_Q σ S → ZMod p) where
  toFun := lk0xpa3_toFun σ S
  invFun := lk0xpa3_ofFun σ S hS
  left_inv := by
    classical
    intro t
    refine Subtype.ext ?_
    funext i
    by_cases hi : i ∈ S
    · have hmem : lk0xpa3_rep σ S (lk0xpa3_cls σ S i hi) ∈ lk0xpa3_orb σ i := by
        have h0 : lk0xpa3_rep σ S (lk0xpa3_cls σ S i hi)
            ∈ lk0xpa3_orb σ (lk0xpa3_rep σ S (lk0xpa3_cls σ S i hi)) :=
          lk0xpa3_mem_orb_self σ _
        rwa [lk0xpa3_orb_rep] at h0
      show (if h : i ∈ S then lk0xpa3_toFun σ S t ⟨lk0xpa3_orb σ i, i, h, rfl⟩ else 0) = t.1 i
      rw [dif_pos hi]
      exact lk0xpa3_orb_apply_eq σ t.1 t.2.2 hmem
    · show (if h : i ∈ S then lk0xpa3_toFun σ S t ⟨lk0xpa3_orb σ i, i, h, rfl⟩ else 0) = t.1 i
      rw [dif_neg hi]
      exact (t.2.1 i hi).symm
  right_inv := by
    classical
    intro f
    funext q
    show (if h : lk0xpa3_rep σ S q ∈ S then
        f ⟨lk0xpa3_orb σ (lk0xpa3_rep σ S q), lk0xpa3_rep σ S q, h, rfl⟩ else 0) = f q
    rw [dif_pos (lk0xpa3_rep_mem σ S q)]
    exact congrArg f (Subtype.ext (lk0xpa3_orb_rep σ S q))

private noncomputable def lk0xpa3_kerEquiv {n p : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (c : Fin n → ZMod p) :
    {t : Fin n → ZMod p // (∀ i, i ∉ S → t i = 0) ∧ (∀ i, t (σ i) = t i) ∧
      ∑ i, c i * t i = 0} ≃
    {t : lk0xpa3_W p σ S // lk0xpa3_lamW σ S c t = 0} where
  toFun t := ⟨⟨t.1, t.2.1, t.2.2.1⟩, t.2.2.2⟩
  invFun s := ⟨s.1.1, s.1.2.1, s.1.2.2, s.2⟩
  left_inv t := rfl
  right_inv s := rfl

theorem PA3_card_invariant_hyperplane {p n : ℕ} (hp : p.Prime) (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hS : ∀ i, σ i ∈ S ↔ i ∈ S) (c : Fin n → ZMod p)
    (hc : ∀ i, c (σ i) = c i) (hnz : ∃ i ∈ S, c i * (orbitSize σ i : ZMod p) ≠ 0) :
    Nat.card {t : Fin n → ZMod p // (∀ i, i ∉ S → t i = 0) ∧ (∀ i, t (σ i) = t i) ∧
      ∑ i, c i * t i = 0} = p ^ (numOrbitsOn σ S - 1) := by
  classical
  haveI : Fact p.Prime := Fact.mk hp
  obtain ⟨i0, hi0S, hi0nz⟩ := hnz
  haveI : Finite (lk0xpa3_Q σ S) := by
    haveI : Finite (Set (Fin n)) := Set.instFinite
    exact Subtype.finite
  have hcardW : Nat.card (lk0xpa3_W p σ S) = p ^ Nat.card (lk0xpa3_Q σ S) := by
    rw [Nat.card_congr (lk0xpa3_equivWQ σ S hS)]
    rw [Nat.card_fun, Nat.card_zmod]
  let F : Finset (Fin n) := Finset.univ.filter (fun i => i ∈ lk0xpa3_orb σ i0)
  have hFset : (F : Set (Fin n)) = lk0xpa3_orb σ i0 := by
    ext i; simp [F]
  have hFcard : F.card = orbitSize σ i0 := by
    rw [← Set.ncard_coe_finset F, hFset]
    rfl
  have hsum : (∑ i, c i * (if i ∈ lk0xpa3_orb σ i0 then (1 : ZMod p) else 0))
      = c i0 * (orbitSize σ i0 : ZMod p) := by
    rw [show (∑ i, c i * (if i ∈ lk0xpa3_orb σ i0 then (1 : ZMod p) else 0))
        = ∑ i, (if i ∈ lk0xpa3_orb σ i0 then c i else 0) from
      Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)]
    rw [← Finset.sum_filter]
    have hconst : ∀ i ∈ F, c i = c i0 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact lk0xpa3_orb_apply_eq σ c hc hi.2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hFcard, mul_comm]
  let t0 : Fin n → ZMod p := fun i => if i ∈ lk0xpa3_orb σ i0 then 1 else 0
  have ht0A : ∀ i, i ∉ S → t0 i = 0 := by
    intro i hi
    have hni : i ∉ lk0xpa3_orb σ i0 := fun h => hi (lk0xpa3_orb_subset σ S hS hi0S h)
    simp [t0, hni]
  have ht0B : ∀ i, t0 (σ i) = t0 i := by
    intro i
    have hiff := lk0xpa3_sigma_mem_orb_iff σ i0 i
    by_cases h : i ∈ lk0xpa3_orb σ i0
    · have h' : σ i ∈ lk0xpa3_orb σ i0 := hiff.mpr h
      simp [t0, h, h']
    · have h' : σ i ∉ lk0xpa3_orb σ i0 := fun hh => h (hiff.mp hh)
      simp [t0, h, h']
  let t0W : lk0xpa3_W p σ S := ⟨t0, ht0A, ht0B⟩
  have hlam0 : (lk0xpa3_lam c) t0 ≠ 0 := by
    have hval : (lk0xpa3_lam c) t0
        = ∑ i, c i * (if i ∈ lk0xpa3_orb σ i0 then (1 : ZMod p) else 0) := rfl
    rw [hval, hsum]
    exact hi0nz
  have hlamW_ne : lk0xpa3_lamW σ S c ≠ 0 := by
    intro h
    have hzero : lk0xpa3_lamW σ S c t0W = 0 := by rw [h]; rfl
    apply hlam0
    rwa [show lk0xpa3_lamW σ S c t0W = (lk0xpa3_lam c) t0 from rfl] at hzero
  have hsurj : Function.Surjective (lk0xpa3_lamW σ S c) := LinearMap.surjective hlamW_ne
  have hker : Nat.card (AddMonoidHom.ker (lk0xpa3_lamW σ S c).toAddMonoidHom) * p
      = Nat.card (lk0xpa3_W p σ S) := by
    have hh := AddSubgroup.card_ker_mul_card_of_surjective
      (f := (lk0xpa3_lamW σ S c).toAddMonoidHom) hsurj
    rwa [Nat.card_zmod] at hh
  haveI : Nonempty (lk0xpa3_Q σ S) := ⟨lk0xpa3_cls σ S i0 hi0S⟩
  have hk : 1 ≤ Nat.card (lk0xpa3_Q σ S) := Nat.card_pos
  have hfinal : Nat.card (AddMonoidHom.ker (lk0xpa3_lamW σ S c).toAddMonoidHom)
      = p ^ (Nat.card (lk0xpa3_Q σ S) - 1) := by
    have h1 : Nat.card (AddMonoidHom.ker (lk0xpa3_lamW σ S c).toAddMonoidHom) * p
        = p ^ Nat.card (lk0xpa3_Q σ S) := by
      rw [hker, hcardW]
    have h2 : p ^ Nat.card (lk0xpa3_Q σ S)
        = p * p ^ (Nat.card (lk0xpa3_Q σ S) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    rw [h2, mul_comm p] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  rw [lk0xpa3_numOrbitsOn_eq σ S, ← hfinal]
  exact Nat.card_congr (lk0xpa3_kerEquiv σ S c)

end CFSG.StandardType.GGK0ExcCentreU

end
