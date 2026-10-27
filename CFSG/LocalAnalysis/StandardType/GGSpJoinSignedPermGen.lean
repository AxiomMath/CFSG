module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase

public section

namespace CFSG.StandardType.SpJoin

variable {n p : ℕ}

private theorem coordPerm_symm_apply (n p : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → Multiplicative (ZMod p)) (t : Fin n) :
    ((coordPerm n p σ)⁻¹) v t = v (σ t) := rfl

private theorem coordPerm_mul (n p : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    coordPerm n p (σ * τ) = coordPerm n p σ * coordPerm n p τ := by
  apply Equiv.ext
  intro v
  funext t
  simp only [coordPerm_apply, Equiv.Perm.mul_apply]
  rw [Equiv.Perm.mul_def σ τ, Equiv.symm_trans_apply]

private theorem coordPerm_one (n p : ℕ) :
    coordPerm n p (1 : Equiv.Perm (Fin n)) = 1 := by
  apply Equiv.ext
  intro v
  funext t
  simp only [coordPerm_apply, Equiv.Perm.one_symm, Equiv.Perm.one_apply]

private theorem coordPerm_inv (n p : ℕ) (σ : Equiv.Perm (Fin n)) :
    coordPerm n p σ⁻¹ = (coordPerm n p σ)⁻¹ := by
  apply Equiv.ext
  intro v
  funext t
  rw [coordPerm_apply, coordPerm_symm_apply, Equiv.Perm.inv_def, Equiv.symm_symm]

private theorem coordPerm_conj_coordInv (n p : ℕ) (ρ : Equiv.Perm (Fin n)) (a : Fin n) :
    coordPerm n p ρ * coordInv n p a * (coordPerm n p ρ)⁻¹ = coordInv n p (ρ a) := by
  apply Equiv.ext
  intro v
  funext t
  simp only [Equiv.Perm.mul_apply, coordInv_apply, coordPerm_apply, coordPerm_symm_apply,
    Function.update_apply, Equiv.apply_symm_apply]
  have hiff : ρ.symm t = a ↔ t = ρ a := Equiv.symm_apply_eq ρ
  by_cases h : t = ρ a
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

theorem coordPerm_mem_spSignedGroup (σ : Equiv.Perm (Fin n)) :
    coordPerm n p σ ∈ spSignedGroup n p := by
  rcases n with _ | m
  · have h : coordPerm 0 p σ = 1 := Subsingleton.elim _ _
    rw [h]
    exact Subgroup.one_mem _
  · let S : Set (Equiv.Perm (Fin (m + 1))) :=
      Set.range (fun i : Fin m => Equiv.swap i.castSucc i.succ)
    have hgen : Subgroup.closure S = ⊤ :=
      Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ m)
    have hmem : ∀ x ∈ S, coordPerm (m + 1) p x ∈ spSignedGroup (m + 1) p := by
      rintro x ⟨i, rfl⟩
      change coordPerm (m + 1) p (Equiv.swap i.castSucc i.succ) ∈ spSignedGroup (m + 1) p
      have hlt : i.castSucc.val + 1 < m + 1 := by
        rw [Fin.val_castSucc]
        exact Nat.succ_lt_succ i.isLt
      have heq : (⟨i.castSucc.val + 1, hlt⟩ : Fin (m + 1)) = i.succ := by
        ext
        simp [Fin.val_succ, Fin.val_castSucc]
      rw [← heq, ← spReflPerm_of_lt (m + 1) p i.castSucc hlt]
      exact spReflPerm_mem_spSignedGroup (m + 1) p i.castSucc
    refine Subgroup.closure_induction (k := S)
      (p := fun x _ => coordPerm (m + 1) p x ∈ spSignedGroup (m + 1) p)
      hmem ?_ ?_ ?_ ?_
    · rw [coordPerm_one]
      exact Subgroup.one_mem _
    · intro x y _ _ hpx hpy
      rw [coordPerm_mul]
      exact Subgroup.mul_mem _ hpx hpy
    · intro x _ hpx
      rw [coordPerm_inv]
      exact Subgroup.inv_mem _ hpx
    · show σ ∈ Subgroup.closure S
      rw [hgen]
      exact Subgroup.mem_top σ

theorem coordInv_mem_spSignedGroup (i : Fin n) : coordInv n p i ∈ spSignedGroup n p := by
  rcases n with _ | m
  · exact i.elim0
  · have hlast : coordInv (m + 1) p (Fin.last m) ∈ spSignedGroup (m + 1) p := by
      rw [← spReflPerm_of_not_lt (m + 1) p (Fin.last m) (by simp [Fin.val_last])]
      exact spReflPerm_mem_spSignedGroup (m + 1) p (Fin.last m)
    have hconj : coordPerm (m + 1) p (Equiv.swap i (Fin.last m)) *
          coordInv (m + 1) p (Fin.last m) *
          (coordPerm (m + 1) p (Equiv.swap i (Fin.last m)))⁻¹ =
        coordInv (m + 1) p i := by
      rw [coordPerm_conj_coordInv, Equiv.swap_apply_right]
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (coordPerm_mem_spSignedGroup _) hlast)
      (Subgroup.inv_mem _ (coordPerm_mem_spSignedGroup _))

theorem exists_mem_spSignedGroup_mulSingle (i j : Fin n) (b : Multiplicative (ZMod p)) :
    ∃ h ∈ spSignedGroup n p, h (Pi.mulSingle i b) = Pi.mulSingle j b := by
  refine ⟨coordPerm n p (Equiv.swap i j), coordPerm_mem_spSignedGroup _, ?_⟩
  ext t
  simp only [coordPerm_apply, Equiv.symm_swap, Pi.mulSingle_apply]
  by_cases h : t = j
  · subst h
    simp [Equiv.swap_apply_right]
  · have h' : Equiv.swap i j t ≠ i := by
      intro hh
      exact h (by simpa [Equiv.swap_apply_left] using
        (Equiv.swap_apply_eq_iff (x := i) (y := j) (z := t) (w := i)).mp hh)
    simp [h, h']

private noncomputable def flipFinset (n p : ℕ) (T : Finset (Fin n)) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p)) where
  toFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  invFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  left_inv v := by
    funext t
    by_cases h : t ∈ T <;> simp [h]
  right_inv v := by
    funext t
    by_cases h : t ∈ T <;> simp [h]

@[simp] private theorem flipFinset_apply (n p : ℕ) (T : Finset (Fin n))
    (v : Fin n → Multiplicative (ZMod p)) (t : Fin n) :
    flipFinset n p T v t = if t ∈ T then (v t)⁻¹ else v t := rfl

private theorem flipFinset_mem_spSignedGroup (T : Finset (Fin n)) :
    flipFinset n p T ∈ spSignedGroup n p := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      have h : flipFinset n p ∅ = 1 := by
        ext v t
        simp [flipFinset_apply]
      rw [h]
      exact Subgroup.one_mem _
  | insert a T ha ih =>
      have hstep : flipFinset n p (insert a T) = coordInv n p a * flipFinset n p T := by
        ext v t
        rw [flipFinset_apply, Equiv.Perm.mul_apply, coordInv_apply]
        by_cases ht : t = a
        · subst ht
          simp [Function.update_apply, ha]
        · rw [Function.update_apply, if_neg ht, flipFinset_apply]
          simp [Finset.mem_insert, ht]
      rw [hstep]
      exact Subgroup.mul_mem _ (coordInv_mem_spSignedGroup a) ih

private noncomputable def signedPerm (n p : ℕ) (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p)) :=
  coordPerm n p σ * flipFinset n p T

private theorem signedPerm_mem_spSignedGroup (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) :
    signedPerm n p σ T ∈ spSignedGroup n p :=
  Subgroup.mul_mem _ (coordPerm_mem_spSignedGroup σ) (flipFinset_mem_spSignedGroup T)

private theorem signedPerm_apply_mulSingle (g : Multiplicative (ZMod p))
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) (i t : Fin n) :
    signedPerm n p σ T (Pi.mulSingle i g) t =
      if σ.symm t = i then (if i ∈ T then g⁻¹ else g) else 1 := by
  rw [signedPerm, Equiv.Perm.mul_apply, coordPerm_apply, flipFinset_apply]
  by_cases h : σ.symm t = i <;> simp [Pi.mulSingle_apply, h]

private theorem signedPerm_apply_mulSingle_ne_one_iff (g : Multiplicative (ZMod p))
    (hg : g ≠ 1) (hginv : g⁻¹ ≠ 1)
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) (i t : Fin n) :
    signedPerm n p σ T (Pi.mulSingle i g) t ≠ 1 ↔ σ.symm t = i := by
  rw [signedPerm_apply_mulSingle]
  by_cases h : σ.symm t = i
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => by by_cases hT : i ∈ T <;> simp [hT, hg, hginv]⟩
  · rw [if_neg h]
    exact ⟨fun hh => (hh rfl).elim, fun hh => (h hh).elim⟩

private theorem signedPerm_apply_mulSingle_self (g : Multiplicative (ZMod p))
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) (i : Fin n) :
    signedPerm n p σ T (Pi.mulSingle i g) (σ i) = if i ∈ T then g⁻¹ else g := by
  rw [signedPerm_apply_mulSingle, Equiv.symm_apply_apply]
  simp

private theorem signedPerm_injective_of_odd (g : Multiplicative (ZMod p))
    (hg : g ≠ 1) (hginv : g⁻¹ ≠ 1) (hgne : g ≠ g⁻¹) :
    Function.Injective (fun x : Equiv.Perm (Fin n) × Finset (Fin n) =>
      signedPerm n p x.1 x.2) := by
  rintro ⟨σ, T⟩ ⟨σ', T'⟩ hxy
  change signedPerm n p σ T = signedPerm n p σ' T' at hxy
  have hsymm : ∀ t, σ'.symm t = σ.symm t := by
    intro t
    have hiff : ∀ i : Fin n, σ.symm t = i ↔ σ'.symm t = i := by
      intro i
      have hv : signedPerm n p σ T (Pi.mulSingle i g) t =
          signedPerm n p σ' T' (Pi.mulSingle i g) t := by rw [hxy]
      rw [← signedPerm_apply_mulSingle_ne_one_iff g hg hginv σ T i t, hv,
        signedPerm_apply_mulSingle_ne_one_iff g hg hginv σ' T' i t]
    exact (hiff (σ.symm t)).mp rfl
  have hσ : σ' = σ := by
    have h : σ'.symm = σ.symm := Equiv.ext hsymm
    have h' := congrArg Equiv.symm h
    simpa [Equiv.symm_symm] using h'
  have hT : T = T' := by
    apply Finset.ext
    intro i
    have hval : signedPerm n p σ T (Pi.mulSingle i g) (σ i) =
        signedPerm n p σ T' (Pi.mulSingle i g) (σ i) := by
      rw [hxy, hσ]
    rw [signedPerm_apply_mulSingle_self, signedPerm_apply_mulSingle_self] at hval
    constructor
    · intro hiT
      by_contra hiT'
      simp [hiT, hiT'] at hval
      exact hgne hval.symm
    · intro hiT'
      by_contra hiT
      simp [hiT, hiT'] at hval
      exact hgne hval
  exact Prod.ext hσ.symm hT

private theorem signedPerm_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (fun x : Equiv.Perm (Fin n) × Finset (Fin n) =>
      signedPerm n p x.1 x.2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have h2p : 2 < p := by
    have := hp.two_le
    omega
  haveI : Fact (2 < p) := ⟨h2p⟩
  let g : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have hg_eq : g = Multiplicative.ofAdd (1 : ZMod p) := rfl
  have hg : g ≠ 1 := by
    intro h
    rw [hg_eq] at h
    exact one_ne_zero ((ofAdd_eq_one).mp h)
  have hginv : g⁻¹ ≠ 1 := fun h => hg ((inv_eq_one).mp h)
  have hgne : g ≠ g⁻¹ := by
    intro h
    rw [hg_eq] at h
    have h' : Multiplicative.ofAdd (1 : ZMod p) = Multiplicative.ofAdd (-1) := by
      simpa using h
    have h1 : (1 : ZMod p) = -1 := Multiplicative.ofAdd.injective h'
    exact ZMod.neg_one_ne_one h1.symm
  exact signedPerm_injective_of_odd g hg hginv hgne

theorem two_pow_mul_factorial_le_card_spSignedGroup (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ n * n.factorial ≤ Nat.card (spSignedGroup n p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hcard : Nat.card (Equiv.Perm (Fin n) × Finset (Fin n)) = n.factorial * 2 ^ n := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_finset,
      Fintype.card_fin]
  rw [mul_comm, ← hcard]
  exact Nat.card_le_card_of_injective
    (fun x : Equiv.Perm (Fin n) × Finset (Fin n) =>
      ⟨signedPerm n p x.1 x.2, signedPerm_mem_spSignedGroup x.1 x.2⟩)
    (fun _ _ hxy => signedPerm_injective hp hp2 (Subtype.ext_iff.mp hxy))

end CFSG.StandardType.SpJoin
