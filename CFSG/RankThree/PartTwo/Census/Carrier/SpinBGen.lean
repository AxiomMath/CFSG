module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDGen

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.RankThree.PartTwo.Census.Carrier.SpinD (RootMem rootMem_comm rootMem_symm)
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : OddFrame Q n) (G : Subgroup (V ≃ₗ[K] V))

@[expose] def ShortMem (i : Fin n) (s : Bool) : Prop :=
  ∀ c : K, eichler Q (F.vec i s) (c • F.z) ∈ G

@[expose] def ChainMem : Prop :=
  ∀ (k : Fin n) (hk : k.val + 1 < n),
    RootMem F.toHypFrame G k true ⟨k.val + 1, hk⟩ false ∧
      RootMem F.toHypFrame G ⟨k.val + 1, hk⟩ true k false

variable {F G}

theorem rootMem_diff_up_of_chain (h : ChainMem F G) :
    ∀ (d : ℕ) (i j : Fin n), i.val + d + 1 = j.val → RootMem F.toHypFrame G i true j false := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have hk : i.val + 1 < n := by omega
    have e : j = ⟨i.val + 1, hk⟩ := Fin.ext (by simp only; omega)
    subst e
    exact (h i hk).1
  | succ d ih =>
    intro i j hij
    have hk : j.val - 1 < n := by omega
    set k : Fin n := ⟨j.val - 1, hk⟩
    have h1 : RootMem F.toHypFrame G i true k false := ih i k (by simp only [k]; omega)
    have hk1 : k.val + 1 < n := by simp only [k]; omega
    have e : j = ⟨k.val + 1, hk1⟩ := Fin.ext (by simp only [k]; omega)
    have h2 : RootMem F.toHypFrame G k true j false := by
      rw [e]
      exact (h k hk1).1
    exact rootMem_comm (r := false) (Fin.ne_of_val_ne (by simp only [k]; omega))
      (Fin.ne_of_val_ne (by simp only [k]; omega)) (Fin.ne_of_val_ne (by omega)) h1 h2

theorem rootMem_diff_down_of_chain (h : ChainMem F G) :
    ∀ (d : ℕ) (i j : Fin n), j.val + d + 1 = i.val → RootMem F.toHypFrame G i true j false := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have hk : j.val + 1 < n := by omega
    have e : i = ⟨j.val + 1, hk⟩ := Fin.ext (by simp only; omega)
    subst e
    exact (h j hk).2
  | succ d ih =>
    intro i j hij
    have hk : j.val + 1 < n := by omega
    set k : Fin n := ⟨j.val + 1, hk⟩
    have h1 : RootMem F.toHypFrame G i true k false := ih i k (by simp only [k]; omega)
    have h2 : RootMem F.toHypFrame G k true j false := (h j hk).2
    exact rootMem_comm (r := false) (Fin.ne_of_val_ne (by simp only [k]; omega))
      (Fin.ne_of_val_ne (by simp only [k]; omega)) (Fin.ne_of_val_ne (by omega)) h1 h2

theorem rootMem_diff_of_chain (h : ChainMem F G) {i j : Fin n} (hij : i ≠ j) :
    RootMem F.toHypFrame G i true j false ∧ RootMem F.toHypFrame G i false j true := by
  have key : ∀ {i j : Fin n}, i ≠ j → RootMem F.toHypFrame G i true j false := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact rootMem_diff_up_of_chain h (j.val - i.val - 1) i j (by omega)
    · exact rootMem_diff_down_of_chain h (i.val - j.val - 1) i j (by omega)
  exact ⟨key hij, rootMem_symm (Ne.symm hij) (key (Ne.symm hij))⟩

theorem polar_vec_z_smul (i : Fin n) (s : Bool) (d : K) : polar Q (F.vec i s) (d • F.z) = 0 := by
  rw [polar_smul_right, F.polar_vec_z, smul_zero]

theorem eichler_short_apply (k : Fin n) (t' : Bool) (c d : K) :
    eichler Q (F.vec k t') (d • F.z) (c • F.vec k (!t')) - c • F.vec k (!t') =
      (c * d) • F.z - (c * d ^ 2) • F.vec k t' := by
  rw [eichler_apply (F.map_vec k t') (polar_vec_z_smul k t' d)]
  have h1 : polar Q (c • F.vec k (!t')) (F.vec k t') = c := by
    rw [polar_smul_left, F.toHypFrame.polar_not_vec, smul_eq_mul, mul_one]
  have h2 : polar Q (c • F.vec k (!t')) (d • F.z) = 0 := by
    rw [polar_smul_left, polar_smul_right, F.polar_vec_z, smul_zero, smul_zero]
  rw [h1, h2, QuadraticMap.map_smul, F.map_z, zero_add, smul_eq_mul, mul_one, smul_smul,
    show d * d * c = c * d ^ 2 by ring]
  abel

theorem shortMem_of_long (h2 : (2 : K) ≠ 0) {i k : Fin n} (hik : i ≠ k) {s t : Bool}
    (hlong : RootMem F.toHypFrame G k t i s) (hshort : ShortMem F G k (!t)) :
    ShortMem F G i s ∧ RootMem F.toHypFrame G k (!t) i s := by
  set u := F.vec i s
  have hpolz : ∀ e : K, polar Q u (e • F.z) = 0 := fun e => polar_vec_z_smul i s e
  have hpolk : ∀ (e : K) (r : Bool), polar Q u (e • F.vec k r) = 0 := fun e r => by
    rw [polar_smul_right, F.polar_vec_of_ne hik, smul_zero]
  have key : ∀ c d : K, eichler Q u ((c * d) • F.z) *
      eichler Q u ((-(c * d ^ 2)) • F.vec k (!t)) ∈ G := by
    intro c d
    set a := eichler Q (F.vec k (!t)) (d • F.z)
    have ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q _ _
    have hfix : a u = u := by
      rw [eichler_apply (F.map_vec k (!t)) (polar_vec_z_smul k (!t) d)]
      have e1 : polar Q u (F.vec k (!t)) = 0 := F.polar_vec_of_ne hik s (!t)
      have e2 : polar Q u (d • F.z) = 0 := hpolz d
      simp only [e1, e2, zero_smul, mul_zero, add_zero, sub_zero]
    have hcomm := commutatorElement_eichler ha hfix (hpolk c t)
    have hmove : a (c • F.vec k t) - c • F.vec k t =
        (c * d) • F.z + (-(c * d ^ 2)) • F.vec k (!t) := by
      have := eichler_short_apply (F := F) k (!t) c d
      rw [Bool.not_not] at this
      rw [this, neg_smul, sub_eq_add_neg]
    rw [hmove, ← eichler_mul (hpolz _) (hpolk _ _)] at hcomm
    rw [← hcomm, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hshort d) (hlong c)) (inv_mem (hshort d)))
      (inv_mem (hlong c))
  have hA : ∀ e : K, eichler Q u (e • F.z) * eichler Q u ((-e) • F.vec k (!t)) ∈ G := by
    intro e
    have h := key e 1
    rwa [mul_one, one_pow, mul_one] at h
  have hB : ∀ e : K, eichler Q u (e • F.z) * eichler Q u (e • F.vec k (!t)) ∈ G := by
    intro e
    have h := key (-e) (-1)
    rwa [neg_mul_neg, mul_one, neg_one_sq, mul_one, neg_neg] at h
  have hlong' : RootMem F.toHypFrame G k (!t) i s := by
    intro μ
    set e := μ / 2
    have e1 : (eichler Q u (e • F.z) * eichler Q u ((-e) • F.vec k (!t)))⁻¹ *
        (eichler Q u (e • F.z) * eichler Q u (e • F.vec k (!t))) =
        (eichler Q u ((-e) • F.vec k (!t)))⁻¹ * eichler Q u (e • F.vec k (!t)) := by
      group
    have e2 : (eichler Q u ((-e) • F.vec k (!t)))⁻¹ * eichler Q u (e • F.vec k (!t)) =
        eichler Q u (μ • F.vec k (!t)) := by
      rw [eichler_inv (hpolk _ _), ← neg_smul, neg_neg, eichler_mul (hpolk _ _) (hpolk _ _),
        ← add_smul]
      congr 2
      simp only [e]
      field_simp
      ring
    show eichler Q u (μ • F.vec k (!t)) ∈ G
    rw [← e2, ← e1]
    exact mul_mem (inv_mem (hA e)) (hB e)
  refine ⟨fun c => ?_, hlong'⟩
  have e : eichler Q u (c • F.z) = (eichler Q u (c • F.z) *
      eichler Q u ((-c) • F.vec k (!t))) * eichler Q u (c • F.vec k (!t)) := by
    rw [mul_assoc, eichler_mul (hpolk _ _) (hpolk _ _), ← add_smul, neg_add_cancel, zero_smul,
      eichler_zero_right, mul_one]
  rw [e]
  exact mul_mem (hA c) (hlong' c)

theorem rootMem_shortMem_of_simple (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (hc : ChainMem F G)
    (hs : ∀ s, ShortMem F G ⟨n - 1, by omega⟩ s) :
    (∀ {i j : Fin n}, i ≠ j → ∀ s t, RootMem F.toHypFrame G i s j t) ∧
      ∀ i s, ShortMem F G i s := by
  set l : Fin n := ⟨n - 1, by omega⟩
  have hl : ∀ {i : Fin n}, i ≠ l → ∀ s, ShortMem F G i s ∧ RootMem F.toHypFrame G l s i s := by
    intro i hil s
    have hd := rootMem_diff_of_chain hc (Ne.symm hil)
    cases s
    · have h := shortMem_of_long h2 hil (s := false) (t := true) hd.1 (hs (!true))
      exact h
    · have h := shortMem_of_long h2 hil (s := true) (t := false) hd.2 (hs (!false))
      exact h
  have hshort : ∀ i s, ShortMem F G i s := by
    intro i s
    by_cases hil : i = l
    · rw [hil]
      exact hs s
    · exact (hl hil s).1
  refine ⟨fun {i j} hij s t => ?_, hshort⟩
  by_cases hst : s = t
  · subst hst
    by_cases hjl : j = l
    · subst hjl
      exact rootMem_symm (Ne.symm hij) (hl hij s).2
    · by_cases hil : i = l
      · subst hil
        exact (hl hjl s).2
      ·
        have h1 : RootMem F.toHypFrame G i s l (!s) := by
          cases s
          · exact (rootMem_diff_of_chain hc hil).2
          · exact (rootMem_diff_of_chain hc hil).1
        have h2' : RootMem F.toHypFrame G l (!(!s)) j s := by
          rw [Bool.not_not]
          exact (hl hjl s).2
        exact rootMem_comm hil hjl hij h1 h2'
  · cases s <;> cases t
    · exact absurd rfl hst
    · exact (rootMem_diff_of_chain hc hij).2
    · exact (rootMem_diff_of_chain hc hij).1
    · exact absurd rfl hst

theorem elementaryGroup_le_of_simpleB {K : Type} [Field K] {n : ℕ} (h2 : (2 : K) ≠ 0)
    (hn : 2 ≤ n) {G : Subgroup ((Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K))}
    (hc : ChainMem (oddFrame n K) G) (hs : ∀ s, ShortMem (oddFrame n K) G ⟨n - 1, by omega⟩ s) :
    elementaryGroup (quadOdd n K) ≤ G := by
  obtain ⟨hlong, hshort⟩ := rootMem_shortMem_of_simple h2 hn hc hs
  refine (oddFrame n K).toHypFrame.elementaryGroup_le (fun hij s t c => hlong hij s t c)
    (fun i s v hv => ?_) (fun v hv hQ => ?_)
  · rw [eq_smul_oddZ_of_polar_oddFrame_vec hv]
    exact hshort i s _
  · rw [eq_smul_oddZ_of_polar_oddFrame_vec hv] at hQ ⊢
    rw [QuadraticMap.map_smul, oddFrame_z, quadOdd_oddZ, smul_eq_mul, mul_one,
      mul_self_eq_zero] at hQ
    rw [hQ, zero_smul]

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB
