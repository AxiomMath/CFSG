module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4CombAux2

public section

namespace CFSG.StandardType

private lemma coxeterB_apply {n : ℕ} (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1
        else if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨
          ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
        else if ((j : ℕ) + 1 = (i : ℕ)) ∨ ((i : ℕ) + 1 = (j : ℕ)) then 3 else 2) := by
  rw [CoxeterMatrix.B]
  simp only [Matrix.of_apply]

private lemma coxeterB_entry_even {n : ℕ} {i j : Fin n}
    (hlast : (i : ℕ) + 1 = n ∨ (j : ℕ) + 1 = n) (hij : i ≠ j) :
    Even ((CoxeterMatrix.B n) i j) := by
  rw [coxeterB_apply, if_neg hij]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs with h4 h3
  · exact ⟨2, rfl⟩
  · exfalso
    omega
  · exact ⟨1, rfl⟩

private lemma neg_one_pow_eq_one_of_even {m : ℕ} (h : Even m) : (-1 : ℤˣ) ^ m = 1 := by
  obtain ⟨k, hk⟩ := h
  rw [hk, ← two_mul, pow_mul]
  norm_num

private lemma coxeterB_liftable (n : ℕ) :
    (CoxeterMatrix.B n).IsLiftable
      (fun i : Fin n => if i.val + 1 < n then (1 : ℤˣ) else -1) := by
  intro i j
  change ((if i.val + 1 < n then (1 : ℤˣ) else -1) *
    (if j.val + 1 < n then (1 : ℤˣ) else -1)) ^ ((CoxeterMatrix.B n) i j) = 1
  by_cases hij : i = j
  · subst hij
    have hsq : ((if i.val + 1 < n then (1 : ℤˣ) else -1) *
        (if i.val + 1 < n then (1 : ℤˣ) else -1)) = 1 := by
      by_cases hi : i.val + 1 < n <;> simp [hi]
    rw [hsq, one_pow]
  · by_cases hi : i.val + 1 < n <;> by_cases hj : j.val + 1 < n
    · simp [hi, hj]
    · have hlast : (j : ℕ) + 1 = n := by have := j.isLt; omega
      have hfi : (if i.val + 1 < n then (1 : ℤˣ) else -1) = 1 := if_pos hi
      have hfj : (if j.val + 1 < n then (1 : ℤˣ) else -1) = -1 := if_neg hj
      rw [hfi, hfj, one_mul]
      exact neg_one_pow_eq_one_of_even (coxeterB_entry_even (Or.inr hlast) hij)
    · have hlast : (i : ℕ) + 1 = n := by have := i.isLt; omega
      have hfi : (if i.val + 1 < n then (1 : ℤˣ) else -1) = -1 := if_neg hi
      have hfj : (if j.val + 1 < n then (1 : ℤˣ) else -1) = 1 := if_pos hj
      rw [hfi, hfj, mul_one]
      exact neg_one_pow_eq_one_of_even (coxeterB_entry_even (Or.inl hlast) hij)
    · exfalso
      have h1 : (i : ℕ) + 1 = n := by have := i.isLt; omega
      have h2 : (j : ℕ) + 1 = n := by have := j.isLt; omega
      exact hij (Fin.ext (by omega))

noncomputable def coxeterBSign (n : ℕ) : (CoxeterMatrix.B n).Group →* ℤˣ :=
  (CoxeterMatrix.B n).toCoxeterSystem.lift
    ⟨fun i => if i.val + 1 < n then 1 else -1, coxeterB_liftable n⟩

theorem coxeterBSign_simple (n : ℕ) (i : Fin n) :
    coxeterBSign n ((CoxeterMatrix.B n).simple i) = if i.val + 1 < n then 1 else -1 := by
  exact CoxeterSystem.lift_apply_simple (cs := (CoxeterMatrix.B n).toCoxeterSystem)
    (coxeterB_liftable n) i

section SignedModel

open SpJoin

variable {n p : ℕ}

private structure SignedElt (n p : ℕ) where
  perm : Equiv.Perm (Fin n)
  flip : Fin n → Bool

private def SignedElt.toPerm (D : SignedElt n p) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p)) where
  toFun v t := if D.flip t then (v (D.perm.symm t))⁻¹ else v (D.perm.symm t)
  invFun v t := if D.flip (D.perm t) then (v (D.perm t))⁻¹ else v (D.perm t)
  left_inv v := by
    funext t
    by_cases ht : D.flip (D.perm t) <;> simp [ht, inv_inv]
  right_inv v := by
    funext t
    by_cases ht : D.flip t <;> simp [ht, inv_inv]

@[simp] private theorem SignedElt.toPerm_apply (D : SignedElt n p)
    (v : Fin n → Multiplicative (ZMod p)) (t : Fin n) :
    D.toPerm v t = if D.flip t then (v (D.perm.symm t))⁻¹ else v (D.perm.symm t) := rfl

private def SignedElt.mul (D E : SignedElt n p) : SignedElt n p where
  perm := D.perm * E.perm
  flip t := D.flip t != E.flip (D.perm.symm t)

private def SignedElt.inv (D : SignedElt n p) : SignedElt n p where
  perm := D.perm⁻¹
  flip t := D.flip (D.perm t)

@[simp] private theorem SignedElt.inv_perm (D : SignedElt n p) :
    (D.inv).perm = D.perm⁻¹ := rfl

@[simp] private theorem SignedElt.inv_flip (D : SignedElt n p) (t : Fin n) :
    (D.inv).flip t = D.flip (D.perm t) := rfl

@[simp] private theorem SignedElt.perm_inv_symm (D : SignedElt n p) :
    (D.perm⁻¹).symm = D.perm := by
  rw [Equiv.Perm.inv_def]
  exact Equiv.symm_symm D.perm

private def SignedElt.one (n p : ℕ) : SignedElt n p := ⟨1, fun _ => false⟩

private theorem SignedElt.toPerm_one : (SignedElt.one n p).toPerm = 1 := by
  ext v t
  simp [SignedElt.toPerm_apply, SignedElt.one, Equiv.Perm.one_symm]

private theorem SignedElt.mul_inv (D : SignedElt n p) : D.mul D.inv = SignedElt.one n p := by
  cases D with
  | mk σ c =>
    have hflip : (fun t => c t != c (σ (σ.symm t))) = fun _ => false := by
      funext t
      simp
    rw [SignedElt.mul, SignedElt.inv, SignedElt.one, mul_inv_cancel, hflip]

private theorem SignedElt.toPerm_mul (D E : SignedElt n p) :
    D.toPerm * E.toPerm = (D.mul E).toPerm := by
  apply Equiv.ext
  intro v
  funext t
  rw [Equiv.Perm.mul_apply, SignedElt.toPerm_apply, SignedElt.toPerm_apply,
    SignedElt.toPerm_apply, SignedElt.mul, Equiv.Perm.mul_def, Equiv.symm_trans_apply]
  by_cases hd : D.flip t <;> by_cases he : E.flip (D.perm.symm t) <;>
    simp [hd, he, inv_inv]

private theorem SignedElt.toPerm_inv (D : SignedElt n p) :
    D.toPerm⁻¹ = (D.inv).toPerm := by
  have h : D.toPerm * (D.inv).toPerm = 1 := by
    rw [SignedElt.toPerm_mul, SignedElt.mul_inv, SignedElt.toPerm_one]
  exact inv_eq_of_mul_eq_one_right h

private def signedSubgroup (n p : ℕ) :
    Subgroup (Equiv.Perm (Fin n → Multiplicative (ZMod p))) where
  carrier := {g | ∃ D : SignedElt n p, g = D.toPerm}
  one_mem' := ⟨SignedElt.one n p, SignedElt.toPerm_one⟩
  mul_mem' := by
    rintro g h ⟨D, rfl⟩ ⟨E, rfl⟩
    exact ⟨D.mul E, SignedElt.toPerm_mul D E⟩
  inv_mem' := by
    rintro g ⟨D, rfl⟩
    exact ⟨D.inv, SignedElt.toPerm_inv D⟩

private theorem spReflPerm_mem_signedSubgroup (k : Fin n) :
    SpJoin.spReflPerm n p k ∈ signedSubgroup n p := by
  by_cases hk : k.val + 1 < n
  · rw [SpJoin.spReflPerm_of_lt n p k hk]
    refine ⟨⟨Equiv.swap k ⟨k.val + 1, hk⟩, fun _ => false⟩, ?_⟩
    apply Equiv.ext
    intro v
    funext t
    simp [SignedElt.toPerm_apply]
  · rw [SpJoin.spReflPerm_of_not_lt n p k hk]
    refine ⟨⟨1, fun t => t = k⟩, ?_⟩
    apply Equiv.ext
    intro v
    funext t
    by_cases ht : t = k <;>
      simp [SignedElt.toPerm_apply, SpJoin.coordInv_apply, ht, Equiv.Perm.one_symm]

private theorem exists_signedElt_of_mem_spSignedGroup
    {g : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (hg : g ∈ SpJoin.spSignedGroup n p) : ∃ D : SignedElt n p, g = D.toPerm := by
  have hle : SpJoin.spSignedGroup n p ≤ signedSubgroup n p := by
    rw [SpJoin.spSignedGroup]
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨k, rfl⟩; exact spReflPerm_mem_signedSubgroup k)
  have h := hle hg
  change ∃ D : SignedElt n p, g = D.toPerm at h
  exact h

private def SignedElt.supp (D : SignedElt n p) : Set (Fin n) :=
  {t | D.flip t = true ∨ D.perm t ≠ t}

private theorem mem_supp_iff (D : SignedElt n p) (t : Fin n) :
    t ∈ D.supp ↔ D.flip t = true ∨ D.perm t ≠ t := Iff.rfl

private theorem SignedElt.supp_perm_mem {D : SignedElt n p} {t : Fin n} (ht : t ∈ D.supp) :
    D.perm t ∈ D.supp := by
  rw [mem_supp_iff] at ht ⊢
  rcases ht with h | h
  · by_cases hpt : D.perm t = t
    · exact Or.inl (by rw [hpt]; exact h)
    · exact Or.inr (fun hpp => hpt (D.perm.injective hpp))
  · exact Or.inr (fun hpp => h (D.perm.injective hpp))

private theorem SignedElt.supp_perm_symm_mem {D : SignedElt n p} {t : Fin n} (ht : t ∈ D.supp) :
    D.perm.symm t ∈ D.supp := by
  rw [mem_supp_iff] at ht ⊢
  by_contra h
  rw [not_or] at h
  obtain ⟨hf, hp⟩ := h
  have hp' : D.perm (D.perm.symm t) = D.perm.symm t := not_not.mp hp
  have hst : t = D.perm.symm t := by
    rw [← hp']
    exact (Equiv.apply_symm_apply D.perm t).symm
  rcases ht with h | h
  · exact hf (hst ▸ h)
  · exact (hst ▸ h) hp'

private theorem SignedElt.notMem_supp {D : SignedElt n p} {t : Fin n} (ht : t ∉ D.supp) :
    D.flip t = false ∧ D.perm t = t := by
  rw [mem_supp_iff, not_or] at ht
  exact ⟨by simpa using ht.1, by simpa using ht.2⟩

private def coordSupp (g : Equiv.Perm (Fin n → Multiplicative (ZMod p))) : Set (Fin n) :=
  {t | ∃ v, g v t ≠ v t}

private lemma ofAdd_one_inv_ne_one [Fact p.Prime] (hp2 : p ≠ 2) :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p))⁻¹ ≠
      Multiplicative.ofAdd 1 := by
  have h2p : Fact (2 < p) := ⟨by have h2 := (Fact.out : p.Prime).two_le; omega⟩
  intro h
  have h' : Multiplicative.ofAdd (-1 : ZMod p) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa using h
  exact @ZMod.neg_one_ne_one p h2p (Multiplicative.ofAdd.injective h')

private lemma ofAdd_inv_ne_one [Fact p.Prime] :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p))⁻¹ ≠ 1 := by
  intro h
  have h' : (-1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (by simpa using h)
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)) h'

private lemma ofAdd_one_ne_one [Fact p.Prime] :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := by
  intro h
  have h' : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective h
  exact (one_ne_zero : (1 : ZMod p) ≠ 0) h'

private theorem mem_coordSupp_iff [Fact p.Prime] (hp2 : p ≠ 2) (D : SignedElt n p)
    (t : Fin n) :
    t ∈ coordSupp D.toPerm ↔ t ∈ D.supp := by
  constructor
  · rintro ⟨v, hv⟩
    rw [mem_supp_iff]
    by_contra h
    rw [not_or] at h
    have hperm : D.perm t = t := not_not.mp h.2
    have hsymm : D.perm.symm t = t := by
      rw [Equiv.symm_apply_eq]
      exact hperm.symm
    exact hv (by rw [SignedElt.toPerm_apply, if_neg h.1, hsymm])
  · intro ht
    rw [mem_supp_iff] at ht
    rcases ht with hf | hp
    · by_cases hpt : D.perm t = t
      · refine ⟨(Pi.mulSingle t (Multiplicative.ofAdd 1) : Fin n → Multiplicative (ZMod p)), ?_⟩
        have hsym : D.perm.symm t = t := by
          rw [Equiv.symm_apply_eq]
          exact hpt.symm
        rw [SignedElt.toPerm_apply, if_pos hf, hsym, Pi.mulSingle_eq_same]
        exact ofAdd_one_inv_ne_one hp2
      · refine ⟨(Pi.mulSingle (D.perm.symm t) (Multiplicative.ofAdd 1) :
          Fin n → Multiplicative (ZMod p)), ?_⟩
        have hne : D.perm.symm t ≠ t := by
          intro h
          exact hpt (by simpa [h] using Equiv.apply_symm_apply D.perm t)
        have h1 : (Pi.mulSingle (D.perm.symm t) (Multiplicative.ofAdd (1 : ZMod p)) :
            Fin n → Multiplicative (ZMod p)) t = 1 := by
          rw [Pi.mulSingle_apply, if_neg]
          exact fun h => hne h.symm
        rw [SignedElt.toPerm_apply, if_pos hf, Pi.mulSingle_eq_same, h1]
        exact ofAdd_inv_ne_one
    · refine ⟨(Pi.mulSingle (D.perm.symm t) (Multiplicative.ofAdd 1) :
          Fin n → Multiplicative (ZMod p)), ?_⟩
      have hne : D.perm.symm t ≠ t := by
        intro h
        exact hp (by simpa [h] using Equiv.apply_symm_apply D.perm t)
      have h1 : (Pi.mulSingle (D.perm.symm t) (Multiplicative.ofAdd (1 : ZMod p)) :
          Fin n → Multiplicative (ZMod p)) t = 1 := by
        rw [Pi.mulSingle_apply, if_neg]
        exact fun h => hne h.symm
      by_cases hflip : D.flip t
      · rw [SignedElt.toPerm_apply, if_pos hflip, Pi.mulSingle_eq_same, h1]
        exact ofAdd_inv_ne_one
      · rw [SignedElt.toPerm_apply, if_neg hflip, Pi.mulSingle_eq_same, h1]
        exact ofAdd_one_ne_one

private theorem SignedElt.mul_comm_perm {D E : SignedElt n p} (h : Disjoint D.supp E.supp) :
    D.perm * E.perm = E.perm * D.perm := by
  obtain ⟨σ, c⟩ := D
  obtain ⟨τ, d⟩ := E
  change σ * τ = τ * σ
  have hEfix : ∀ t, (c t = true ∨ σ t ≠ t) → τ t = t := fun t ht =>
    (SignedElt.notMem_supp (Set.disjoint_left.mp h ht)).2
  apply Equiv.ext
  intro t
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  by_cases ht : c t = true ∨ σ t ≠ t
  · rw [hEfix t ht, hEfix (σ t) (SignedElt.supp_perm_mem (p := p)
      (D := (⟨σ, c⟩ : SignedElt n p)) ht)]
  · have hτt : ¬ (c (τ t) = true ∨ σ (τ t) ≠ τ t) := by
      by_cases het : d t = true ∨ τ t ≠ t
      · exact Set.disjoint_right.mp h (SignedElt.supp_perm_mem (p := p)
          (D := (⟨τ, d⟩ : SignedElt n p)) het)
      · rw [(SignedElt.notMem_supp (p := p) (D := ⟨τ, d⟩) het).2]
        exact ht
    rw [(SignedElt.notMem_supp (p := p) (D := ⟨σ, c⟩) ht).2,
      (SignedElt.notMem_supp (p := p) (D := ⟨σ, c⟩) hτt).2]

private theorem SignedElt.mul_comm_flip {D E : SignedElt n p} (h : Disjoint D.supp E.supp) :
    (fun t => D.flip t != E.flip (D.perm.symm t)) =
      fun t => E.flip t != D.flip (E.perm.symm t) := by
  obtain ⟨σ, c⟩ := D
  obtain ⟨τ, d⟩ := E
  change (fun t => c t != d (σ.symm t)) = fun t => d t != c (τ.symm t)
  funext t
  by_cases ht : c t = true ∨ σ t ≠ t
  · have hEt : d t = false ∧ τ t = t := SignedElt.notMem_supp (Set.disjoint_left.mp h ht)
    have hEσ : d (σ.symm t) = false :=
      (SignedElt.notMem_supp (Set.disjoint_left.mp h
        (SignedElt.supp_perm_symm_mem (p := p) (D := (⟨σ, c⟩ : SignedElt n p)) ht))).1
    have hτsymm : τ.symm t = t := by
      rw [Equiv.symm_apply_eq]
      exact hEt.2.symm
    rw [hEt.1, hEσ, hτsymm]
    cases c t <;> rfl
  · have hDt : c t = false ∧ σ t = t := SignedElt.notMem_supp (p := p) (D := ⟨σ, c⟩) ht
    have hτsymm_not : ¬ (c (τ.symm t) = true ∨ σ (τ.symm t) ≠ τ.symm t) := by
      by_cases het : d t = true ∨ τ t ≠ t
      · exact Set.disjoint_right.mp h (SignedElt.supp_perm_symm_mem (p := p)
          (D := (⟨τ, d⟩ : SignedElt n p)) het)
      · have hsymm : τ.symm t = t := by
          rw [Equiv.symm_apply_eq]
          exact (SignedElt.notMem_supp (p := p) (D := ⟨τ, d⟩) het).2.symm
        rwa [hsymm]
    have hDflip : c (τ.symm t) = false :=
      (SignedElt.notMem_supp (p := p) (D := ⟨σ, c⟩) hτsymm_not).1
    have hσsymm : σ.symm t = t := by
      rw [Equiv.symm_apply_eq]
      exact hDt.2.symm
    rw [hDt.1, hσsymm, hDflip]
    cases d t <;> rfl

private theorem SignedElt.mul_comm_of_disjoint_supp {D E : SignedElt n p}
    (h : Disjoint D.supp E.supp) : D.mul E = E.mul D := by
  have hperm := SignedElt.mul_comm_perm h
  have hflip := SignedElt.mul_comm_flip h
  simp only [SignedElt.mul]
  rw [hperm, hflip]

private theorem coordInv_eq_toPerm (j : Fin n) :
    coordInv n p j = (⟨1, fun t => t = j⟩ : SignedElt n p).toPerm := by
  apply Equiv.ext
  intro v
  funext t
  rw [SpJoin.coordInv_apply, SignedElt.toPerm_apply, Equiv.Perm.one_symm,
    Function.update_apply]
  by_cases ht : t = j <;> simp [ht]

private theorem coordPerm_eq_toPerm (σ : Equiv.Perm (Fin n)) :
    coordPerm n p σ = (⟨σ, fun _ => false⟩ : SignedElt n p).toPerm := by
  apply Equiv.ext
  intro v
  funext t
  rw [SpJoin.coordPerm_apply, SignedElt.toPerm_apply]
  simp

private theorem SignedElt.perm_conj_swap (D : SignedElt n p) (a b : Fin n) :
    D.perm * Equiv.swap a b * D.perm.symm = Equiv.swap (D.perm a) (D.perm b) := by
  apply Equiv.ext
  intro t
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  by_cases h : t = D.perm a
  · subst h
    simp [Equiv.swap_apply_left]
  · by_cases h' : t = D.perm b
    · subst h'
      simp [Equiv.swap_apply_right]
    · have h1 : D.perm.symm t ≠ a := by
        intro hh
        apply h
        rw [← hh, Equiv.apply_symm_apply]
      have h2 : D.perm.symm t ≠ b := by
        intro hh
        apply h'
        rw [← hh, Equiv.apply_symm_apply]
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.apply_symm_apply,
        Equiv.swap_apply_of_ne_of_ne h h']

private theorem conj_coordInv (D : SignedElt n p) (j : Fin n) :
    D.toPerm * coordInv n p j * D.toPerm⁻¹ = coordInv n p (D.perm j) := by
  apply Equiv.ext
  intro v
  funext t
  rw [SignedElt.toPerm_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    SignedElt.toPerm_apply, SpJoin.coordInv_apply, Function.update_apply,
    SignedElt.toPerm_apply (D := D.inv), SpJoin.coordInv_apply, Function.update_apply]
  by_cases htj : t = D.perm j
  · subst htj
    have h1 : D.perm.symm (D.perm j) = j := by simp
    by_cases ht : D.flip (D.perm j) <;> simp [ht, h1, inv_inv]
  · have h1 : ¬ (D.perm.symm t = j) := by
      intro hh
      exact htj (by rw [← hh, Equiv.apply_symm_apply])
    by_cases ht : D.flip t <;> simp [ht, htj, h1, inv_inv]

private theorem coordPerm_swap_mul_coordInv {a b : Fin n} (hab : a ≠ b) :
    coordPerm n p (Equiv.swap a b) * coordInv n p a * coordInv n p b =
      (⟨Equiv.swap a b, fun t => t = a ∨ t = b⟩ : SignedElt n p).toPerm := by
  apply Equiv.ext
  intro v
  funext t
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, SpJoin.coordPerm_apply,
    SpJoin.coordInv_apply, Function.update_apply, SpJoin.coordInv_apply,
    Function.update_apply, SignedElt.toPerm_apply]
  by_cases ht : t = a
  · subst ht
    simp [hab, Ne.symm hab]
  · by_cases ht' : t = b
    · subst ht'
      simp [ht, hab]
    · have h1 : Equiv.swap a b t ≠ a := by
        intro h
        exact ht' (by simpa using (Equiv.swap_apply_eq_iff.mp h))
      have h2 : Equiv.swap a b t ≠ b := by
        intro h
        exact ht (by simpa using (Equiv.swap_apply_eq_iff.mp h))
      simp [ht, ht', h1, h2]

private theorem conj_swap_aux (D : SignedElt n p) {a b : Fin n} :
    D.toPerm * coordPerm n p (Equiv.swap a b) * D.toPerm⁻¹ =
      (⟨Equiv.swap (D.perm a) (D.perm b),
        fun t => D.flip t != D.flip (Equiv.swap (D.perm a) (D.perm b) t)⟩ :
          SignedElt n p).toPerm := by
  have hρ : D.perm * Equiv.swap a b * D.perm.symm =
      Equiv.swap (D.perm a) (D.perm b) := SignedElt.perm_conj_swap D a b
  apply Equiv.ext
  intro v
  funext t
  rw [SignedElt.toPerm_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    SignedElt.toPerm_apply, SpJoin.coordPerm_apply, SignedElt.toPerm_apply (D := D.inv),
    SignedElt.toPerm_apply, Equiv.symm_swap]
  have harg : D.perm (Equiv.swap a b (D.perm.symm t)) =
      Equiv.swap (D.perm a) (D.perm b) t := by
    have h := congrArg (fun e : Equiv.Perm (Fin n) => e t) hρ
    simpa [Equiv.Perm.mul_apply, Equiv.symm_swap] using h
  simp only [SignedElt.inv_flip, Equiv.symm_swap, harg]
  by_cases ht : D.flip t <;> by_cases hu : D.flip (Equiv.swap (D.perm a) (D.perm b) t) <;>
    simp [ht, hu, inv_inv, harg]

private theorem conj_swap_or (D : SignedElt n p) {a b : Fin n} (hab : a ≠ b) :
    D.toPerm * coordPerm n p (Equiv.swap a b) * D.toPerm⁻¹ =
        coordPerm n p (Equiv.swap (D.perm a) (D.perm b)) ∨
      D.toPerm * coordPerm n p (Equiv.swap a b) * D.toPerm⁻¹ =
        coordPerm n p (Equiv.swap (D.perm a) (D.perm b)) * coordInv n p (D.perm a) *
          coordInv n p (D.perm b) := by
  have hpq : D.perm a ≠ D.perm b := fun h => hab (D.perm.injective h)
  by_cases hc : D.flip (D.perm a) = D.flip (D.perm b)
  · left
    rw [conj_swap_aux D]
    apply Equiv.ext
    intro v
    funext t
    rw [SignedElt.toPerm_apply, SpJoin.coordPerm_apply]
    have hf : (D.flip t != D.flip (Equiv.swap (D.perm a) (D.perm b) t)) = false := by
      by_cases ht : t = D.perm a
      · subst ht
        rw [Equiv.swap_apply_left]
        simp [hc]
      · by_cases ht' : t = D.perm b
        · subst ht'
          rw [Equiv.swap_apply_right]
          simp [hc]
        · rw [Equiv.swap_apply_of_ne_of_ne ht ht']
          simp
    simp [hf]
  · right
    rw [conj_swap_aux D, coordPerm_swap_mul_coordInv hpq]
    apply Equiv.ext
    intro v
    funext t
    rw [SignedElt.toPerm_apply, SignedElt.toPerm_apply]
    have hf : (D.flip t != D.flip (Equiv.swap (D.perm a) (D.perm b) t)) =
        (t = D.perm a ∨ t = D.perm b) := by
      by_cases ht : t = D.perm a
      · subst ht
        rw [Equiv.swap_apply_left]
        simp [hc]
      · by_cases ht' : t = D.perm b
        · subst ht'
          rw [Equiv.swap_apply_right]
          have hlt : (D.flip (D.perm b) != D.flip (D.perm a)) = true := by
            rw [bne_iff_ne]
            exact Ne.symm hc
          simp [ht, hlt]
        · rw [Equiv.swap_apply_of_ne_of_ne ht ht']
          simp [ht, ht']
    simp [hf]

private def coordInvEl (j : Fin n) : SpJoin.spSignedGroup n p :=
  ⟨coordInv n p j, SpJoin.coordInv_mem_spSignedGroup j⟩

private def coordPermEl (σ : Equiv.Perm (Fin n)) : SpJoin.spSignedGroup n p :=
  ⟨coordPerm n p σ, SpJoin.coordPerm_mem_spSignedGroup σ⟩

@[simp] private theorem coordInvEl_coe (j : Fin n) :
    ((coordInvEl (p := p) j : SpJoin.spSignedGroup n p) :
      Equiv.Perm (Fin n → Multiplicative (ZMod p))) = coordInv n p j := rfl

@[simp] private theorem coordPermEl_coe (σ : Equiv.Perm (Fin n)) :
    ((coordPermEl (p := p) σ : SpJoin.spSignedGroup n p) :
      Equiv.Perm (Fin n → Multiplicative (ZMod p))) = coordPerm n p σ := rfl

private theorem coordSupp_coordInv [Fact p.Prime] (hp2 : p ≠ 2) (j : Fin n) :
    coordSupp (coordInv n p j) = {j} := by
  rw [coordInv_eq_toPerm]
  ext t
  rw [mem_coordSupp_iff hp2]
  simp [SignedElt.supp]

private theorem coordSupp_coordPerm_swap [Fact p.Prime] (hp2 : p ≠ 2) {a b : Fin n}
    (hab : a ≠ b) : coordSupp (coordPerm n p (Equiv.swap a b)) = {a, b} := by
  rw [coordPerm_eq_toPerm]
  ext t
  rw [mem_coordSupp_iff hp2]
  simp [SignedElt.supp, Equiv.swap_apply_ne_self_iff, hab]

private theorem coordSupp_swap_mul [Fact p.Prime] (hp2 : p ≠ 2) {a b : Fin n} (hab : a ≠ b) :
    coordSupp (coordPerm n p (Equiv.swap a b) * coordInv n p a * coordInv n p b) = {a, b} := by
  rw [coordPerm_swap_mul_coordInv hab]
  ext t
  rw [mem_coordSupp_iff hp2]
  simp [SignedElt.supp, Equiv.swap_apply_ne_self_iff]

private theorem commute_of_disjoint_coordSupp [Fact p.Prime] (hp2 : p ≠ 2)
    {g h : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (hg : g ∈ SpJoin.spSignedGroup n p) (hh : h ∈ SpJoin.spSignedGroup n p)
    (hd : Disjoint (coordSupp g) (coordSupp h)) : g * h = h * g := by
  obtain ⟨D, rfl⟩ := exists_signedElt_of_mem_spSignedGroup hg
  obtain ⟨E, rfl⟩ := exists_signedElt_of_mem_spSignedGroup hh
  have hD : D.supp = coordSupp D.toPerm := Set.ext fun t => (mem_coordSupp_iff hp2 D t).symm
  have hE : E.supp = coordSupp E.toPerm := Set.ext fun t => (mem_coordSupp_iff hp2 E t).symm
  have hcomm : D.mul E = E.mul D := SignedElt.mul_comm_of_disjoint_supp (by rwa [hD, hE])
  rw [SignedElt.toPerm_mul, SignedElt.toPerm_mul, hcomm]

end SignedModel

section LinRefl

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

private theorem IsLinRefl.conj {g T : V ≃ₗ[ZMod p] V} (h : IsLinRefl T) :
    IsLinRefl (g * T * g⁻¹) := by
  obtain ⟨x, f, hfx, hT⟩ := h
  refine ⟨g x, f.comp g.symm.toLinearMap, ?_, fun v => ?_⟩
  · simpa using hfx
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hT, map_sub, map_smul,
      show (g⁻¹ : V ≃ₗ[ZMod p] V) = g.symm from rfl, LinearEquiv.apply_symm_apply]
    rfl

end LinRefl

private theorem coordInvEl_eq_conj {n p : ℕ} [Fact p.Prime] (hn : 1 ≤ n) (j : Fin n) :
    ∃ u : SpJoin.spSignedGroup n p,
      coordInvEl (p := p) j = u * coordInvEl (p := p) ⟨n - 1, by omega⟩ * u⁻¹ := by
  let last : Fin n := ⟨n - 1, by omega⟩
  refine ⟨coordPermEl (p := p) (Equiv.swap last j), ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coordPermEl_coe, coordInvEl_coe,
    coordInvEl_coe]
  rw [coordPerm_eq_toPerm (p := p) (Equiv.swap last j),
    conj_coordInv (⟨Equiv.swap last j, fun _ => false⟩ : SignedElt n p) last]
  congr 1
  simp [last, Equiv.swap_apply_left]

private theorem swap_eq_of_pair_eq {n : ℕ} {x y p q : Fin n} (hx : x ≠ y)
    (h : ({x, y} : Set (Fin n)) = {p, q}) : Equiv.swap x y = Equiv.swap p q := by
  have hxmem : x ∈ ({p, q} : Set (Fin n)) := by rw [← h]; simp
  have hymem : y ∈ ({p, q} : Set (Fin n)) := by rw [← h]; simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem hymem
  rcases hxmem with hx1 | hx2 <;> rcases hymem with hy1 | hy2
  · exact absurd (hx1.trans hy1.symm) hx
  · rw [hx1, hy2]
  · rw [hx2, hy1, Equiv.swap_comm]
  · exact absurd (hx2.trans hy2.symm) hx

section MainProof

open SpJoin

variable {n p : ℕ} {κ : Type*}

private structure Ctx (n p : ℕ) (κ : Type*) where
  e : (CoxeterMatrix.B n).Group ≃* SpJoin.spSignedGroup n p
  he : ∀ i : Fin n, ((e ((CoxeterMatrix.B n).simple i) : SpJoin.spSignedGroup n p) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p))) = SpJoin.spReflPerm n p i
  s : κ → (CoxeterMatrix.B n).Group
  w : κ → (CoxeterMatrix.B n).Group
  i : κ → Fin n
  hw : ∀ a, s a = w a * (CoxeterMatrix.B n).simple (i a) * (w a)⁻¹
  D : κ → SignedElt n p
  hDval : ∀ a, ((e (w a) : SpJoin.spSignedGroup n p) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p))) = (D a).toPerm

private def Ctx.f (C : Ctx n p κ) (a : κ) : SpJoin.spSignedGroup n p := C.e (C.s a)

private def Ctx.H (C : Ctx n p κ) : Subgroup (SpJoin.spSignedGroup n p) :=
  Subgroup.closure (Set.range C.f)

private def Ctx.S (C : Ctx n p κ) (a : κ) : Set (Fin n) :=
  coordSupp ((C.f a : SpJoin.spSignedGroup n p) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p)))

private def Ctx.edge (C : Ctx n p κ) (x y : Fin n) : Prop :=
  ∃ b, ∃ _hb : (C.i b).val + 1 < n, C.S b = {x, y}

private def Ctx.J (C : Ctx n p κ) : Set (Fin n) :=
  {j | coordInvEl (p := p) j ∈ C.H}

private def Ctx.K (C : Ctx n p κ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | coordPermEl (p := p) σ ∈ C.H}
  one_mem' := by
    show coordPermEl (p := p) (1 : Equiv.Perm (Fin n)) ∈ C.H
    have h : coordPermEl (p := p) (1 : Equiv.Perm (Fin n)) = 1 := by
      apply Subtype.ext
      rw [coordPermEl_coe]
      exact okCl_coordPerm_one n p
    rw [h]
    exact C.H.one_mem
  mul_mem' := by
    intro σ τ hσ hτ
    show coordPermEl (p := p) (σ * τ) ∈ C.H
    have h : coordPermEl (p := p) (σ * τ) =
        coordPermEl (p := p) σ * coordPermEl (p := p) τ := by
      apply Subtype.ext
      rw [coordPermEl_coe, okCl_coordPerm_mul]
      rfl
    rw [h]
    exact C.H.mul_mem hσ hτ
  inv_mem' := by
    intro σ hσ
    show coordPermEl (p := p) σ⁻¹ ∈ C.H
    have h : coordPermEl (p := p) σ⁻¹ = (coordPermEl (p := p) σ)⁻¹ := by
      apply Subtype.ext
      rw [coordPermEl_coe, okCl_coordPerm_inv]
      rfl
    rw [h]
    exact C.H.inv_mem hσ

private theorem gen_conj (C : Ctx n p κ) :
    ∀ a, ((C.f a : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) =
      (C.D a).toPerm * SpJoin.spReflPerm n p (C.i a) * ((C.D a).toPerm)⁻¹ := by
  intro a
  have h1 : C.f a = C.e (C.w a) * C.e ((CoxeterMatrix.B n).simple (C.i a)) *
      (C.e (C.w a))⁻¹ := by
    simp only [Ctx.f, C.hw a, map_mul, map_inv]
  have h2 := congrArg (fun x : SpJoin.spSignedGroup n p =>
    (x : Equiv.Perm (Fin n → Multiplicative (ZMod p)))) h1
  simpa [C.hDval a, C.he (C.i a)] using h2

private theorem gen_long [Fact p.Prime] (C : Ctx n p κ) :
    ∀ a, ¬ (C.i a).val + 1 < n →
      ((C.f a : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) = coordInv n p ((C.D a).perm (C.i a)) := by
  intro a hi
  rw [gen_conj C a, SpJoin.spReflPerm_of_not_lt n p (C.i a) hi]
  exact conj_coordInv (C.D a) (C.i a)

private theorem ne_idx (C : Ctx n p κ) (a : κ) (hi : (C.i a).val + 1 < n) :
    C.i a ≠ ⟨(C.i a).val + 1, hi⟩ := by
  intro h
  have hv := congrArg Fin.val h
  simp only at hv
  omega

private theorem gen_short [Fact p.Prime] (C : Ctx n p κ) :
    ∀ a (hi : (C.i a).val + 1 < n),
      ((C.f a : SpJoin.spSignedGroup n p) :
          Equiv.Perm (Fin n → Multiplicative (ZMod p))) =
          coordPerm n p (Equiv.swap ((C.D a).perm (C.i a))
            ((C.D a).perm ⟨(C.i a).val + 1, hi⟩)) ∨
        ((C.f a : SpJoin.spSignedGroup n p) :
          Equiv.Perm (Fin n → Multiplicative (ZMod p))) =
          coordPerm n p (Equiv.swap ((C.D a).perm (C.i a))
            ((C.D a).perm ⟨(C.i a).val + 1, hi⟩)) *
            coordInv n p ((C.D a).perm (C.i a)) *
              coordInv n p ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) := by
  intro a hi
  rw [gen_conj C a, SpJoin.spReflPerm_of_lt n p (C.i a) hi]
  exact conj_swap_or (C.D a) (ne_idx C a hi)

private theorem gen_supp_long [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) :
    ∀ a (_hi : ¬ (C.i a).val + 1 < n), C.S a = {(C.D a).perm (C.i a)} := by
  intro a _hi
  change coordSupp ((C.f a : SpJoin.spSignedGroup n p) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p))) = _
  rw [gen_long C a _hi]
  exact coordSupp_coordInv hp2 _

private theorem gen_supp_short [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) :
    ∀ a (hi : (C.i a).val + 1 < n),
      C.S a = {(C.D a).perm (C.i a), (C.D a).perm ⟨(C.i a).val + 1, hi⟩} := by
  intro a hi
  change coordSupp ((C.f a : SpJoin.spSignedGroup n p) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p))) = _
  have hne := (C.D a).perm.injective.ne (ne_idx C a hi)
  rcases gen_short C a hi with h | h
  · rw [h]
    exact coordSupp_coordPerm_swap hp2 hne
  · rw [h]
    exact coordSupp_swap_mul hp2 hne

private theorem gen_supp_nonempty [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (a : κ) :
    (C.S a).Nonempty := by
  by_cases hi : (C.i a).val + 1 < n
  · rw [gen_supp_short hp2 C a hi]
    exact ⟨_, Set.mem_insert _ _⟩
  · rw [gen_supp_long hp2 C a hi]
    exact ⟨_, Set.mem_singleton _⟩

private theorem cover_comm [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (j : Fin n)
    (a : κ) (hj : j ∉ C.S a) :
    C.s a * C.e.symm (coordInvEl (p := p) j) =
      C.e.symm (coordInvEl (p := p) j) * C.s a := by
  have hdisj : Disjoint (C.S a) (coordSupp (coordInv n p j)) := by
    rw [coordSupp_coordInv hp2 j]
    exact Set.disjoint_singleton_right.mpr hj
  have hcomm_perm : ((C.f a : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) *
      coordInv n p j = coordInv n p j *
        ((C.f a : SpJoin.spSignedGroup n p) :
          Equiv.Perm (Fin n → Multiplicative (ZMod p))) :=
    commute_of_disjoint_coordSupp hp2 (C.f a).2
      (SpJoin.coordInv_mem_spSignedGroup j) hdisj
  have hcomm_sub : C.f a * coordInvEl (p := p) j = coordInvEl (p := p) j * C.f a :=
    Subtype.ext hcomm_perm
  have h := congrArg C.e.symm hcomm_sub
  simpa [Ctx.f, map_mul] using h

private theorem eps_conj [Fact p.Prime] (C : Ctx n p κ) (hn : 1 ≤ n) (j : Fin n) :
    ∃ u : (CoxeterMatrix.B n).Group,
      C.e.symm (coordInvEl (p := p) j) =
        u * (CoxeterMatrix.B n).simple ⟨n - 1, by omega⟩ * u⁻¹ := by
  let last : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨u₀, hu₀⟩ := coordInvEl_eq_conj (p := p) hn j
  refine ⟨C.e.symm u₀, ?_⟩
  apply C.e.injective
  rw [map_mul, map_mul, map_inv]
  have hsimple : (C.e ((CoxeterMatrix.B n).simple last) : SpJoin.spSignedGroup n p) =
      coordInvEl (p := p) last := by
    apply Subtype.ext
    rw [C.he last, SpJoin.spReflPerm_of_not_lt n p last (by
      simp only [last]
      omega)]
    rfl
  rw [show C.e (C.e.symm (coordInvEl (p := p) j)) = coordInvEl (p := p) j from by simp,
    show C.e (C.e.symm u₀) = u₀ from by simp, hsimple, hu₀]

private theorem eps_refl [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (C : Ctx n p κ) (hn : 1 ≤ n) (ρ : (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V))
    (hrefl : ∀ i : Fin n, IsLinRefl (ρ ((CoxeterMatrix.B n).simple i))) (j : Fin n) :
    IsLinRefl (ρ (C.e.symm (coordInvEl (p := p) j))) := by
  obtain ⟨u, hu⟩ := eps_conj C hn j
  rw [hu, map_mul, map_mul, map_inv]
  exact IsLinRefl.conj (hrefl _)

private theorem cover_ne [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (C : Ctx n p κ)
    (ρ : (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
    (j : Fin n) (a : κ) (hj : j ∉ C.S a) :
    ρ (C.e.symm (coordInvEl (p := p) j)) ≠ ρ (C.s a) := by
  intro hEq
  have heq : C.e.symm (coordInvEl (p := p) j) = C.s a := hρ hEq
  apply hj
  have hEq2 : coordInvEl (p := p) j = C.f a := by
    rw [← show C.e (C.e.symm (coordInvEl (p := p) j)) = coordInvEl (p := p) j from by simp,
      heq]
    rfl
  have hcoe : coordInv n p j = ((C.f a : SpJoin.spSignedGroup n p) :
      Equiv.Perm (Fin n → Multiplicative (ZMod p))) := by
    rw [← hEq2]
    rfl
  have hmem : j ∈ coordSupp (coordInv n p j) := by
    rw [coordSupp_coordInv hp2 j]
    exact Set.mem_singleton j
  rwa [hcoe] at hmem

private theorem cover_fix [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (C : Ctx n p κ) (hn : 1 ≤ n)
    (ρ : (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
    (hrefl : ∀ i : Fin n, IsLinRefl (ρ ((CoxeterMatrix.B n).simple i)))
    (j : Fin n) (hj : ∀ a, j ∉ C.S a) (v : V)
    (hv : ρ (C.e.symm (coordInvEl (p := p) j)) v = -v) :
    ∀ a, ρ (C.s a) v = v := by
  intro a
  have hcomm_rho : ρ (C.e.symm (coordInvEl (p := p) j)) * ρ (C.s a) =
      ρ (C.s a) * ρ (C.e.symm (coordInvEl (p := p) j)) := by
    rw [← map_mul, ← map_mul, cover_comm hp2 C j a (hj a)]
  have hrefl_a : IsLinRefl (ρ (C.s a)) := by
    rw [C.hw a, map_mul, map_mul, map_inv]
    exact IsLinRefl.conj (hrefl (C.i a))
  exact IsLinRefl.comm_fix hp2 (eps_refl C hn ρ hrefl j) hrefl_a hcomm_rho
    (cover_ne hp2 C ρ hρ j a (hj a)) hv

private theorem gen_cover [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (hn : 1 ≤ n)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
    (hrefl : ∀ i : Fin n, IsLinRefl (ρ ((CoxeterMatrix.B n).simple i)))
    (hfix : ∀ v : V, (∀ a, ρ (C.s a) v = v) → v = 0) :
    ∀ j : Fin n, ∃ a, j ∈ C.S a := by
  intro j
  by_contra hj
  push Not at hj
  obtain ⟨v, hv0, hv⟩ := (eps_refl C hn ρ hrefl j).exists_anti hp2
  exact hv0 (hfix v (cover_fix hp2 C hn ρ hρ hrefl j hj v hv))

private theorem exists_sign_gen (C : Ctx n p κ)
    (hD : ¬ Subgroup.closure (Set.range C.s) ≤ (coxeterBSign n).ker) :
    ∃ a, coxeterBSign n (C.s a) ≠ 1 := by
  obtain ⟨a, ha⟩ : ∃ a, C.s a ∉ (coxeterBSign n).ker := by
    by_contra h
    apply hD
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, rfl⟩
    by_contra hx
    exact h ⟨b, hx⟩
  refine ⟨a, ?_⟩
  rwa [MonoidHom.mem_ker] at ha

private theorem exists_long_gen (C : Ctx n p κ)
    (hD : ¬ Subgroup.closure (Set.range C.s) ≤ (coxeterBSign n).ker) :
    ∃ a, ¬ (C.i a).val + 1 < n := by
  obtain ⟨a, ha⟩ := exists_sign_gen C hD
  refine ⟨a, ?_⟩
  intro hi
  apply ha
  have hconj : coxeterBSign n (C.s a) =
      coxeterBSign n ((CoxeterMatrix.B n).simple (C.i a)) := by
    rw [C.hw a, map_mul, map_mul, map_inv]
    simp only [mul_comm (coxeterBSign n (C.w a))
      (coxeterBSign n ((CoxeterMatrix.B n).simple (C.i a))), mul_inv_cancel_right]
  rw [hconj, coxeterBSign_simple n (C.i a), if_pos hi]

private theorem J_of_long [Fact p.Prime] (C : Ctx n p κ) {a₀ : κ}
    (h : ¬ (C.i a₀).val + 1 < n) : (C.D a₀).perm (C.i a₀) ∈ C.J := by
  have hlong_eq : C.f a₀ = coordInvEl (p := p) ((C.D a₀).perm (C.i a₀)) := by
    apply Subtype.ext
    rw [coordInvEl_coe]
    exact gen_long C a₀ h
  change coordInvEl (p := p) ((C.D a₀).perm (C.i a₀)) ∈ C.H
  rw [← hlong_eq]
  exact Subgroup.subset_closure ⟨a₀, rfl⟩

private theorem supp_within [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (a : κ) :
    ∀ x ∈ C.S a, ∀ y ∈ C.S a, Relation.ReflTransGen C.edge x y := by
  intro x hx y hy
  by_cases hi : (C.i a).val + 1 < n
  · have hSa := gen_supp_short hp2 C a hi
    have hedge : Relation.ReflTransGen C.edge ((C.D a).perm (C.i a))
        ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) :=
      Relation.ReflTransGen.single ⟨a, hi, hSa⟩
    have hedge' : Relation.ReflTransGen C.edge ((C.D a).perm ⟨(C.i a).val + 1, hi⟩)
        ((C.D a).perm (C.i a)) :=
      Relation.ReflTransGen.single ⟨a, hi, by rw [hSa, Set.pair_comm]⟩
    rw [hSa] at hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · subst hx; subst hy; exact Relation.ReflTransGen.refl
    · subst hx; subst hy; exact hedge
    · subst hx; subst hy; exact hedge'
    · subst hx; subst hy; exact Relation.ReflTransGen.refl
  · have hSa := gen_supp_long hp2 C a hi
    rw [hSa] at hx hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy; exact Relation.ReflTransGen.refl

private theorem supp_inter [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) {a b : κ}
    (hne : C.s a * C.s b ≠ C.s b * C.s a) : ∃ t, t ∈ C.S a ∧ t ∈ C.S b := by
  by_contra h
  push Not at h
  have hdisj : Disjoint (C.S a) (C.S b) := Set.disjoint_left.mpr (fun t ht1 ht2 => h t ht1 ht2)
  have hcomm : ((C.f a : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) *
      ((C.f b : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) =
      ((C.f b : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) *
        ((C.f a : SpJoin.spSignedGroup n p) :
          Equiv.Perm (Fin n → Multiplicative (ZMod p))) :=
    commute_of_disjoint_coordSupp hp2 (C.f a).2 (C.f b).2 hdisj
  apply hne
  have hsub : C.f a * C.f b = C.f b * C.f a := Subtype.ext hcomm
  have h := congrArg C.e.symm hsub
  simpa [Ctx.f, map_mul] using h

private theorem supp_step [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) {a b : κ}
    (hne : C.s a * C.s b ≠ C.s b * C.s a) :
    ∀ x ∈ C.S a, ∀ y ∈ C.S b, Relation.ReflTransGen C.edge x y := by
  intro x hx y hy
  obtain ⟨t, ht1, ht2⟩ := supp_inter hp2 C hne
  exact (supp_within hp2 C a x hx t ht1).trans (supp_within hp2 C b t ht2 y hy)

private theorem supp_connected [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => C.s a * C.s b ≠ C.s b * C.s a) a b)
    (hcover : ∀ j : Fin n, ∃ a, j ∈ C.S a) :
    ∀ x y : Fin n, Relation.ReflTransGen C.edge x y := by
  have hconn_pt : ∀ a b : κ, ∀ x ∈ C.S a, ∀ y ∈ C.S b, Relation.ReflTransGen C.edge x y := by
    intro a b
    refine (hconn a b).trans_induction_on
      (motive := fun {a b} _ => ∀ x ∈ C.S a, ∀ y ∈ C.S b, Relation.ReflTransGen C.edge x y)
      ?_ ?_ ?_
    · intro a x hx y hy
      exact supp_within hp2 C a x hx y hy
    · intro a b hab x hx y hy
      exact supp_step hp2 C hab x hx y hy
    · intro a b c hab hbc ih1 ih2 x hx y hy
      obtain ⟨z, hz⟩ := gen_supp_nonempty hp2 C b
      exact (ih1 x hx z hz).trans (ih2 z hz y hy)
  intro x y
  obtain ⟨ax, hx⟩ := hcover x
  obtain ⟨ay, hy⟩ := hcover y
  exact hconn_pt ax ay x hx y hy

private theorem conj_pq [Fact p.Prime] (C : Ctx n p κ) (a : κ)
    (hi : (C.i a).val + 1 < n) :
    ((C.f a : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) *
      coordInv n p ((C.D a).perm (C.i a)) *
        (((C.f a : SpJoin.spSignedGroup n p) :
          Equiv.Perm (Fin n → Multiplicative (ZMod p))))⁻¹ =
    coordInv n p ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) := by
  rcases gen_short C a hi with h | h
  · rw [h, coordPerm_eq_toPerm (p := p)
      (σ := Equiv.swap ((C.D a).perm (C.i a)) ((C.D a).perm ⟨(C.i a).val + 1, hi⟩))]
    simpa using conj_coordInv (⟨Equiv.swap ((C.D a).perm (C.i a))
      ((C.D a).perm ⟨(C.i a).val + 1, hi⟩), fun _ => false⟩ : SignedElt n p)
      ((C.D a).perm (C.i a))
  · rw [h, coordPerm_swap_mul_coordInv (p := p) ((C.D a).perm.injective.ne (ne_idx C a hi))]
    simpa using conj_coordInv (⟨Equiv.swap ((C.D a).perm (C.i a))
      ((C.D a).perm ⟨(C.i a).val + 1, hi⟩), fun t => t = (C.D a).perm (C.i a) ∨
        t = (C.D a).perm ⟨(C.i a).val + 1, hi⟩⟩ : SignedElt n p) ((C.D a).perm (C.i a))

private theorem conj_qp [Fact p.Prime] (C : Ctx n p κ) (a : κ)
    (hi : (C.i a).val + 1 < n) :
    ((C.f a : SpJoin.spSignedGroup n p) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) *
      coordInv n p ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) *
        (((C.f a : SpJoin.spSignedGroup n p) :
          Equiv.Perm (Fin n → Multiplicative (ZMod p))))⁻¹ =
    coordInv n p ((C.D a).perm (C.i a)) := by
  rcases gen_short C a hi with h | h
  · rw [h, coordPerm_eq_toPerm (p := p)
      (σ := Equiv.swap ((C.D a).perm (C.i a)) ((C.D a).perm ⟨(C.i a).val + 1, hi⟩))]
    simpa using conj_coordInv (⟨Equiv.swap ((C.D a).perm (C.i a))
      ((C.D a).perm ⟨(C.i a).val + 1, hi⟩), fun _ => false⟩ : SignedElt n p)
      ((C.D a).perm ⟨(C.i a).val + 1, hi⟩)
  · rw [h, coordPerm_swap_mul_coordInv (p := p) ((C.D a).perm.injective.ne (ne_idx C a hi))]
    simpa using conj_coordInv (⟨Equiv.swap ((C.D a).perm (C.i a))
      ((C.D a).perm ⟨(C.i a).val + 1, hi⟩), fun t => t = (C.D a).perm (C.i a) ∨
        t = (C.D a).perm ⟨(C.i a).val + 1, hi⟩⟩ : SignedElt n p)
      ((C.D a).perm ⟨(C.i a).val + 1, hi⟩)

private theorem conj_pq_sub [Fact p.Prime] (C : Ctx n p κ) (a : κ)
    (hi : (C.i a).val + 1 < n) :
    C.f a * coordInvEl (p := p) ((C.D a).perm (C.i a)) * (C.f a)⁻¹ =
      coordInvEl (p := p) ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) := by
  apply Subtype.ext
  simpa using conj_pq C a hi

private theorem conj_qp_sub [Fact p.Prime] (C : Ctx n p κ) (a : κ)
    (hi : (C.i a).val + 1 < n) :
    C.f a * coordInvEl (p := p) ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) * (C.f a)⁻¹ =
      coordInvEl (p := p) ((C.D a).perm (C.i a)) := by
  apply Subtype.ext
  simpa using conj_qp C a hi

private theorem edge_J_pair [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (a : κ)
    (hi : (C.i a).val + 1 < n) (x y : Fin n) (hS : C.S a = {x, y}) :
    x ∈ ({(C.D a).perm (C.i a), (C.D a).perm ⟨(C.i a).val + 1, hi⟩} : Set (Fin n)) ∧
      y ∈ ({(C.D a).perm (C.i a), (C.D a).perm ⟨(C.i a).val + 1, hi⟩} : Set (Fin n)) ∧
      x ≠ y := by
  have hpair : ({x, y} : Set (Fin n)) =
      {(C.D a).perm (C.i a), (C.D a).perm ⟨(C.i a).val + 1, hi⟩} := by
    rw [← hS, gen_supp_short hp2 C a hi]
  have hpq : (C.D a).perm (C.i a) ≠ (C.D a).perm ⟨(C.i a).val + 1, hi⟩ :=
    (C.D a).perm.injective.ne (ne_idx C a hi)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hpair]; exact Set.mem_insert x {y}
  · rw [← hpair]; exact Set.mem_insert_of_mem x (Set.mem_singleton y)
  · rintro rfl
    have hsingle : ({x, x} : Set (Fin n)) = {x} := Set.pair_eq_singleton x
    rw [hsingle] at hpair
    have hp : (C.D a).perm (C.i a) = x := by
      have hmem : (C.D a).perm (C.i a) ∈ ({x} : Set (Fin n)) := by
        rw [hpair]; exact Set.mem_insert _ _
      simpa using hmem
    have hq : (C.D a).perm ⟨(C.i a).val + 1, hi⟩ = x := by
      have hmem : (C.D a).perm ⟨(C.i a).val + 1, hi⟩ ∈ ({x} : Set (Fin n)) := by
        rw [hpair]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      simpa using hmem
    exact hpq (hp.trans hq.symm)

private theorem edge_J [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (a : κ)
    (hi : (C.i a).val + 1 < n) (x y : Fin n) (hS : C.S a = {x, y})
    (hx : x ∈ C.J) : y ∈ C.J := by
  obtain ⟨hxS, hyS, hxy⟩ := edge_J_pair hp2 C a hi x y hS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS hyS
  rcases hxS with hxp | hxq
  · have hyq : y = (C.D a).perm ⟨(C.i a).val + 1, hi⟩ := by
      rcases hyS with h | h
      · exact absurd (hxp.trans h.symm) hxy
      · exact h
    rw [hyq]
    change coordInvEl (p := p) ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) ∈ C.H
    rw [← conj_pq_sub C a hi]
    have hx' : coordInvEl (p := p) ((C.D a).perm (C.i a)) ∈ C.H := by
      rwa [hxp] at hx
    exact C.H.mul_mem (C.H.mul_mem (Subgroup.subset_closure ⟨a, rfl⟩) hx')
      (C.H.inv_mem (Subgroup.subset_closure ⟨a, rfl⟩))
  · have hyp : y = (C.D a).perm (C.i a) := by
      rcases hyS with h | h
      · exact h
      · exact absurd (hxq.trans h.symm) hxy
    rw [hyp]
    change coordInvEl (p := p) ((C.D a).perm (C.i a)) ∈ C.H
    rw [← conj_qp_sub C a hi]
    have hx' : coordInvEl (p := p) ((C.D a).perm ⟨(C.i a).val + 1, hi⟩) ∈ C.H := by
      rwa [hxq] at hx
    exact C.H.mul_mem (C.H.mul_mem (Subgroup.subset_closure ⟨a, rfl⟩) hx')
      (C.H.inv_mem (Subgroup.subset_closure ⟨a, rfl⟩))

private theorem edge_J' [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) {x y : Fin n}
    (h : C.edge x y) (hx : x ∈ C.J) : y ∈ C.J := by
  obtain ⟨a, hi, hS⟩ := h
  exact edge_J hp2 C a hi x y hS hx

private theorem rtg_J [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) {x y : Fin n}
    (h : Relation.ReflTransGen C.edge x y) (hx : x ∈ C.J) : y ∈ C.J := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact edge_J' hp2 C hbc ih

private theorem supp_sub_J [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => C.s a * C.s b ≠ C.s b * C.s a) a b)
    {a₀ : κ} (hlong : ¬ (C.i a₀).val + 1 < n) : ∀ a, C.S a ⊆ C.J := by
  have hS_a0 : C.S a₀ ⊆ C.J := by
    rw [gen_supp_long hp2 C a₀ hlong]
    exact Set.singleton_subset_iff.mpr (J_of_long C hlong)
  intro a
  refine (hconn a₀ a).trans_induction_on
    (motive := fun {a b} _ => C.S a ⊆ C.J → C.S b ⊆ C.J) (fun a => id) ?_ ?_ hS_a0
  · intro a b hne ha y hy
    obtain ⟨t, ht1, ht2⟩ := supp_inter hp2 C hne
    exact rtg_J hp2 C (supp_within hp2 C b t ht2 y hy) (ha ht1)
  · intro a b c hab hbc ih1 ih2
    exact fun ha => ih2 (ih1 ha)

private theorem J_eq_univ [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ) (hn : 1 ≤ n)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
    (hrefl : ∀ i : Fin n, IsLinRefl (ρ ((CoxeterMatrix.B n).simple i)))
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => C.s a * C.s b ≠ C.s b * C.s a) a b)
    (hD : ¬ Subgroup.closure (Set.range C.s) ≤ (coxeterBSign n).ker)
    (hfix : ∀ v : V, (∀ a, ρ (C.s a) v = v) → v = 0) :
    C.J = Set.univ := by
  have hcover := gen_cover hp2 C hn ρ hρ hrefl hfix
  obtain ⟨a₀, hlong⟩ := exists_long_gen C hD
  have hsub := supp_sub_J hp2 C hconn hlong
  ext j
  constructor
  · intro _; exact Set.mem_univ j
  · intro _
    obtain ⟨a, ha⟩ := hcover j
    exact hsub a ha

private theorem inv_mem (C : Ctx n p κ) (hJ : C.J = Set.univ) (j : Fin n) :
    coordInvEl (p := p) j ∈ C.H := by
  have : j ∈ C.J := by rw [hJ]; exact Set.mem_univ j
  exact this

private theorem transposition_mem [Fact p.Prime] (C : Ctx n p κ)
    (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H) (b : κ)
    (hb : (C.i b).val + 1 < n) :
    coordPermEl (p := p) (Equiv.swap ((C.D b).perm (C.i b))
      ((C.D b).perm ⟨(C.i b).val + 1, hb⟩)) ∈ C.H := by
  rcases gen_short C b hb with h | h
  · have hEq : coordPermEl (p := p)
        (Equiv.swap ((C.D b).perm (C.i b)) ((C.D b).perm ⟨(C.i b).val + 1, hb⟩)) =
        C.f b := by
      apply Subtype.ext
      rw [coordPermEl_coe]
      exact h.symm
    rw [hEq]
    exact Subgroup.subset_closure ⟨b, rfl⟩
  · have hsub : C.f b = coordPermEl (p := p)
        (Equiv.swap ((C.D b).perm (C.i b)) ((C.D b).perm ⟨(C.i b).val + 1, hb⟩)) *
        coordInvEl (p := p) ((C.D b).perm (C.i b)) *
          coordInvEl (p := p) ((C.D b).perm ⟨(C.i b).val + 1, hb⟩) := by
      apply Subtype.ext
      simpa using h
    have h1 : C.f b ∈ C.H := Subgroup.subset_closure ⟨b, rfl⟩
    have h2 : coordInvEl (p := p) ((C.D b).perm (C.i b)) ∈ C.H := hInv _
    have h3 : coordInvEl (p := p) ((C.D b).perm ⟨(C.i b).val + 1, hb⟩) ∈ C.H := hInv _
    have hEq : C.f b * (coordInvEl (p := p) ((C.D b).perm ⟨(C.i b).val + 1, hb⟩))⁻¹ *
        (coordInvEl (p := p) ((C.D b).perm (C.i b)))⁻¹ =
        coordPermEl (p := p)
          (Equiv.swap ((C.D b).perm (C.i b)) ((C.D b).perm ⟨(C.i b).val + 1, hb⟩)) := by
      rw [hsub]; group
    rw [← hEq]
    exact C.H.mul_mem (C.H.mul_mem h1 (C.H.inv_mem h3)) (C.H.inv_mem h2)

private theorem swap_mem_K_of_edge [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ)
    (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H) {x y : Fin n} (h : C.edge x y) :
    Equiv.swap x y ∈ C.K := by
  obtain ⟨b, hb, hSb⟩ := h
  have hpair : ({x, y} : Set (Fin n)) =
      {(C.D b).perm (C.i b), (C.D b).perm ⟨(C.i b).val + 1, hb⟩} := by
    rw [← hSb, gen_supp_short hp2 C b hb]
  by_cases hxe : x = y
  · subst hxe
    rw [Equiv.swap_self]
    exact C.K.one_mem
  · rw [swap_eq_of_pair_eq hxe hpair]
    exact transposition_mem C hInv b hb

private theorem swap_mem_K [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => C.s a * C.s b ≠ C.s b * C.s a) a b)
    (hcover : ∀ j : Fin n, ∃ a, j ∈ C.S a) (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H) :
    ∀ x y : Fin n, Equiv.swap x y ∈ C.K := by
  have hedge_conn := supp_connected hp2 C hconn hcover
  intro x y
  refine (hedge_conn x y).trans_induction_on
    (motive := fun {a b} _ => Equiv.swap a b ∈ C.K) ?_ ?_ ?_
  · intro a
    rw [Equiv.swap_self]
    exact C.K.one_mem
  · intro a b hab
    exact swap_mem_K_of_edge hp2 C hInv hab
  · intro a b c hab hbc ih1 ih2
    exact SubmonoidClass.swap_mem_trans C.K ih1 ih2

private theorem K_eq_top [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => C.s a * C.s b ≠ C.s b * C.s a) a b)
    (hcover : ∀ j : Fin n, ∃ a, j ∈ C.S a) (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H) :
    C.K = ⊤ := by
  have hswap : ∀ x y : Fin n, Equiv.swap x y ∈ C.K := swap_mem_K hp2 C hconn hcover hInv
  rw [eq_top_iff]
  intro σ _
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact C.K.one_mem
  | swap_mul f x y hxy ih => exact C.K.mul_mem (hswap x y) (ih (Subgroup.mem_top f))

private theorem perm_mem [Fact p.Prime] (hp2 : p ≠ 2) (C : Ctx n p κ)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => C.s a * C.s b ≠ C.s b * C.s a) a b)
    (hcover : ∀ j : Fin n, ∃ a, j ∈ C.S a) (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H)
    (σ : Equiv.Perm (Fin n)) : coordPermEl (p := p) σ ∈ C.H := by
  have hK := K_eq_top hp2 C hconn hcover hInv
  have : σ ∈ C.K := by rw [hK]; exact Subgroup.mem_top σ
  exact this

private theorem mem_map_iff (C : Ctx n p κ) (x : Equiv.Perm (Fin n → Multiplicative (ZMod p)))
    (hx : x ∈ SpJoin.spSignedGroup n p) :
    ((⟨x, hx⟩ : SpJoin.spSignedGroup n p) ∈ C.H) ↔
      x ∈ Subgroup.map (Subgroup.subtype (SpJoin.spSignedGroup n p)) C.H := by
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem _ h
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    have hye : y = (⟨x, hx⟩ : SpJoin.spSignedGroup n p) := Subtype.ext hyx
    rwa [← hye]

private theorem gen_mem [Fact p.Prime] (C : Ctx n p κ)
    (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H)
    (hPerm : ∀ σ : Equiv.Perm (Fin n), coordPermEl (p := p) σ ∈ C.H) (k : Fin n) :
    (⟨SpJoin.spReflPerm n p k,
      Subgroup.subset_closure (Set.mem_range_self (f := SpJoin.spReflPerm n p) k)⟩ :
        SpJoin.spSignedGroup n p) ∈ C.H := by
  refine (mem_map_iff C (SpJoin.spReflPerm n p k)
    (Subgroup.subset_closure (Set.mem_range_self (f := SpJoin.spReflPerm n p) k))).mpr ?_
  by_cases hk : k.val + 1 < n
  · rw [SpJoin.spReflPerm_of_lt n p k hk]
    exact Subgroup.mem_map_of_mem _ (hPerm _)
  · rw [SpJoin.spReflPerm_of_not_lt n p k hk]
    exact Subgroup.mem_map_of_mem _ (hInv k)

private theorem H_eq_top [Fact p.Prime] (C : Ctx n p κ)
    (hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H)
    (hPerm : ∀ σ : Equiv.Perm (Fin n), coordPermEl (p := p) σ ∈ C.H) :
    C.H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (⟨(g : Equiv.Perm (Fin n → Multiplicative (ZMod p))), g.2⟩ :
      SpJoin.spSignedGroup n p) ∈ C.H := by
    refine Subgroup.closure_induction (k := Set.range (SpJoin.spReflPerm n p))
      (p := fun x hx => (⟨x, hx⟩ : SpJoin.spSignedGroup n p) ∈ C.H) ?_ ?_ ?_ ?_ g.2
    · rintro _ ⟨k, rfl⟩
      exact gen_mem C hInv hPerm k
    · have h1 : (⟨1, Subgroup.one_mem _⟩ : SpJoin.spSignedGroup n p) = 1 := Subtype.ext rfl
      rw [h1]
      exact C.H.one_mem
    · intro x y hx hy ihx ihy
      have hxy : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : SpJoin.spSignedGroup n p) =
          (⟨x, hx⟩ : SpJoin.spSignedGroup n p) * ⟨y, hy⟩ := Subtype.ext rfl
      rw [hxy]
      exact C.H.mul_mem ihx ihy
    · intro x hx ih
      have hx' : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : SpJoin.spSignedGroup n p) =
          (⟨x, hx⟩ : SpJoin.spSignedGroup n p)⁻¹ := Subtype.ext rfl
      rw [hx']
      exact C.H.inv_mem ih
  exact hg

end MainProof

open SpJoin in
theorem coxeterB_closure_eq_top_of_fix_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
    (hrefl : ∀ i : Fin n, IsLinRefl (ρ ((CoxeterMatrix.B n).simple i)))
    {κ : Type*} (s : κ → (CoxeterMatrix.B n).Group)
    (hs : ∀ a, ∃ (w : (CoxeterMatrix.B n).Group) (i : Fin n),
      s a = w * (CoxeterMatrix.B n).simple i * w⁻¹)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => s a * s b ≠ s b * s a) a b)
    (hD : ¬ Subgroup.closure (Set.range s) ≤ (coxeterBSign n).ker)
    (hfix : ∀ v : V, (∀ a, ρ (s a) v = v) → v = 0) :
    Subgroup.closure (Set.range s) = ⊤ := by
  classical
  obtain ⟨e, he⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 hn
  choose w i hw using hs
  choose D hDval using fun a =>
    exists_signedElt_of_mem_spSignedGroup (p := p) (e (w a)).2
  let C : Ctx n p κ := ⟨e, he, s, w, i, hw, D, hDval⟩
  have hcover := gen_cover hp2 C (by omega) ρ hρ hrefl hfix
  have hJ : C.J = Set.univ := J_eq_univ hp2 C (by omega) ρ hρ hrefl hconn hD hfix
  have hInv : ∀ j : Fin n, coordInvEl (p := p) j ∈ C.H := inv_mem C hJ
  have hPerm : ∀ σ : Equiv.Perm (Fin n), coordPermEl (p := p) σ ∈ C.H :=
    perm_mem hp2 C hconn hcover hInv
  have hH : C.H = ⊤ := H_eq_top C hInv hPerm
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ Subgroup.map (e : (CoxeterMatrix.B n).Group →*
      SpJoin.spSignedGroup n p) (Subgroup.closure (Set.range s)) := by
    rw [MonoidHom.map_closure]
    change e x ∈ Subgroup.closure ((fun y => e y) '' Set.range s)
    have himg : (fun y => e y) '' Set.range s = Set.range C.f := by
      ext y
      constructor
      · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨s a, ⟨a, rfl⟩, rfl⟩
    rw [himg, show Subgroup.closure (Set.range C.f) = C.H from rfl, hH]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  rw [← e.injective hxy]
  exact hy

end CFSG.StandardType

end
