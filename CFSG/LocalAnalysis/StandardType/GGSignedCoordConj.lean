module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

open scoped BigOperators

variable {n p : ℕ}

private theorem conj_toMonoidHom_apply (g x : MulAut (Fin n → Multiplicative (ZMod p))) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ :=
  MulAut.conj_apply g x

private theorem conj_negAut_eq_one :
    MulAut.conj (OrthExcEven.negAut (p := p) (k := n) :
      MulAut (Fin n → Multiplicative (ZMod p))) = 1 := by
  refine MulEquiv.ext fun u => ?_
  rw [MulAut.conj_apply, OrthExcEven.negAut_mul_comm u, mul_assoc, mul_inv_cancel,
    mul_one]
  rfl

private theorem map_conj_negAut (S : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) :
    S.map (MulAut.conj (OrthExcEven.negAut (p := p) (k := n) :
      MulAut (Fin n → Multiplicative (ZMod p)))).toMonoidHom = S := by
  rw [conj_negAut_eq_one]
  exact Subgroup.map_id S

private theorem sgnAut_conj_self (i : Fin n)
    (x : MulAut (Fin n → Multiplicative (ZMod p))) :
    sgnAut i * (sgnAut i * x * sgnAut i) * sgnAut i = x := by
  have h2 : (sgnAut i : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut i = 1 := by
    simpa [sq] using sgnAut_sq i
  calc sgnAut i * (sgnAut i * x * sgnAut i) * sgnAut i
      = (sgnAut i * sgnAut i) * x * (sgnAut i * sgnAut i) := by group
    _ = x := by rw [h2, one_mul, mul_one]

private theorem isSignedPerm_of_mem_bSignedFull
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ : δ ∈ bSignedFull n p) :
    IsSignedPerm ⇑δ := by
  have h := hδ
  rw [bSignedFull_eq_signedPermSubgroup] at h
  exact h

private theorem conj_sgnAut_eq {u : MulAut (Fin n → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (i : Fin n) :
    u * sgnAut i * u⁻¹ = sgnAut (π i) := by
  have h := IsSignedPerm.mul_sgnAut (u := u) (π := π) (ε := ε) hu i
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private theorem perm_swap_apply (π : Equiv.Perm (Fin n)) (a b i : Fin n) :
    π (Equiv.swap a b i) = Equiv.swap (π a) (π b) (π i) := by
  by_cases hia : i = a
  · rw [hia, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hib : i = b
    · rw [hib, Equiv.swap_apply_right, Equiv.swap_apply_right]
    · have h1 : π i ≠ π a := fun h => hia (π.injective h)
      have h2 : π i ≠ π b := fun h => hib (π.injective h)
      rw [Equiv.swap_apply_of_ne_of_ne hia hib, Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem conj_permAut_swap_apply {u : MulAut (Fin n → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (a b : Fin n) (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    toAdd (((u * permAut (Equiv.swap a b) * u⁻¹ :
      MulAut (Fin n → Multiplicative (ZMod p))) f (π i))) =
      ε i * ε (Equiv.swap a b i) * toAdd (f (π (Equiv.swap a b i))) := by
  have hinv : ∀ x : Fin n, toAdd ((u⁻¹ f) x) = ε x * toAdd (f (π x)) := by
    intro x
    have h := hu (u⁻¹ f) x
    rw [MulAut.apply_inv_self] at h
    calc toAdd ((u⁻¹ f) x) = (ε x * ε x) * toAdd ((u⁻¹ f) x) := by
          rw [coord_sign_mul_self (hε x), one_mul]
      _ = ε x * (ε x * toAdd ((u⁻¹ f) x)) := by ring
      _ = ε x * toAdd (f (π x)) := by rw [← h]
  rw [MulAut.mul_apply, MulAut.mul_apply, hu, permAut_apply, Function.comp_apply]
  change ε i * toAdd ((u⁻¹ f) (Equiv.swap a b i)) =
    ε i * ε (Equiv.swap a b i) * toAdd (f (π (Equiv.swap a b i)))
  rw [hinv]
  ring

theorem conj_permAut_swap_eq_of_mul_eq_one
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {a b : Fin n}
    (hs : ε a * ε b = 1) :
    u * permAut (Equiv.swap a b) * u⁻¹ = permAut (Equiv.swap (π a) (π b)) := by
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
  rw [conj_permAut_swap_apply hε hu a b f i, permAut_apply, Function.comp_apply]
  change ε i * ε (Equiv.swap a b i) * toAdd (f (π (Equiv.swap a b i))) =
    toAdd (f (Equiv.swap (π a) (π b) (π i)))
  rw [← perm_swap_apply π a b i]
  have hsign : ε i * ε (Equiv.swap a b i) = 1 := by
    by_cases hia : i = a
    · rw [hia, Equiv.swap_apply_left, hs]
    · by_cases hib : i = b
      · rw [hib, Equiv.swap_apply_right, mul_comm, hs]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib, coord_sign_mul_self (hε i)]
  rw [hsign, one_mul]

theorem conj_permAut_swap_eq_of_mul_eq_neg_one
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {a b : Fin n}
    (hab : a ≠ b) (hs : ε a * ε b = -1) :
    u * permAut (Equiv.swap a b) * u⁻¹ =
      sgnAut (π a) * permAut (Equiv.swap (π a) (π b)) * (sgnAut (π a))⁻¹ := by
  have hcd : π a ≠ π b := fun h => hab (π.injective h)
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
  rw [conj_permAut_swap_apply hε hu a b f i]
  rw [negTrans_apply (p := p) (π a) (π b) hcd f (π i)]
  by_cases hia : i = a
  · rw [hia, Equiv.swap_apply_left, if_pos rfl, toAdd_inv, hs]
    ring
  · by_cases hib : i = b
    · rw [hib, Equiv.swap_apply_right, if_neg (Ne.symm hcd), if_pos rfl, toAdd_inv]
      have hba : ε b * ε a = -1 := by rw [mul_comm, hs]
      rw [hba]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib,
        if_neg (fun h => hia (π.injective h)), if_neg (fun h => hib (π.injective h)),
        coord_sign_mul_self (hε i), one_mul]

private theorem conj_negTrans_eq_of_mul_eq_one
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {a b : Fin n}
    (hs : ε a * ε b = 1) :
    u * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) * u⁻¹ =
      sgnAut (π a) * permAut (Equiv.swap (π a) (π b)) * (sgnAut (π a))⁻¹ := by
  calc
    u * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) * u⁻¹
        = (u * sgnAut a * u⁻¹) * (u * permAut (Equiv.swap a b) * u⁻¹) *
            (u * sgnAut a * u⁻¹)⁻¹ := by group
    _ = sgnAut (π a) * permAut (Equiv.swap (π a) (π b)) *
          (sgnAut (π a))⁻¹ := by
        rw [conj_sgnAut_eq hu a, conj_permAut_swap_eq_of_mul_eq_one hε hu hs]

private theorem conj_negTrans_eq_of_mul_eq_neg_one
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {a b : Fin n}
    (hab : a ≠ b) (hs : ε a * ε b = -1) :
    u * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) * u⁻¹ =
      permAut (Equiv.swap (π a) (π b)) := by
  calc
    u * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) * u⁻¹
        = (u * sgnAut a * u⁻¹) * (u * permAut (Equiv.swap a b) * u⁻¹) *
            (u * sgnAut a * u⁻¹)⁻¹ := by group
    _ = permAut (Equiv.swap (π a) (π b)) := by
        rw [conj_sgnAut_eq hu a,
          conj_permAut_swap_eq_of_mul_eq_neg_one hε hu hab hs]
        have h2 : (sgnAut (π a) : MulAut (Fin n → Multiplicative (ZMod p))) *
            sgnAut (π a) = 1 := by
          simpa [sq] using sgnAut_sq (π a)
        rw [inv_eq_of_mul_eq_one_right h2]
        exact sgnAut_conj_self (π a) (permAut (Equiv.swap (π a) (π b)))

theorem permAut_conj_swap (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    permAut (p := p) π * permAut (Equiv.swap a b) * (permAut (p := p) π)⁻¹ =
      permAut (Equiv.swap (π a) (π b)) := by
  refine MulEquiv.ext fun f => funext fun i => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, permAut_apply, permAut_inv_apply,
    permAut_apply, permAut_apply]
  change f (π (Equiv.swap a b (π⁻¹ i))) =
    f (Equiv.swap (π a) (π b) i)
  rw [show π (Equiv.swap a b (π⁻¹ i)) = Equiv.swap (π a) (π b) i by
    simpa using perm_swap_apply π a b (π⁻¹ i)]

private theorem map_conj_permAut (π : Equiv.Perm (Fin n)) :
    (aPermutationFull n p).map (MulAut.conj (permAut (p := p) π)).toMonoidHom =
      aPermutationFull n p := by
  apply le_antisymm
  · rw [aPermutationFull, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro r ⟨g, ⟨a, b, hab, rfl⟩, rfl⟩
    rw [conj_toMonoidHom_apply, permAut_conj_swap (p := p) π a b]
    exact Subgroup.subset_closure ⟨π a, π b, fun h => hab (π.injective h), rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro r ⟨a, b, hab, rfl⟩
    have hne : π⁻¹ a ≠ π⁻¹ b := fun h => hab (by simpa using congrArg π h)
    refine Subgroup.mem_map.mpr ⟨permAut (Equiv.swap (π⁻¹ a) (π⁻¹ b)),
      Subgroup.subset_closure ⟨_, _, hne, rfl⟩, ?_⟩
    rw [conj_toMonoidHom_apply, permAut_conj_swap (p := p) π (π⁻¹ a) (π⁻¹ b)]
    simp

private theorem conj_mul_map (S : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (g h : MulAut (Fin n → Multiplicative (ZMod p))) :
    (S.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      S.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem prod_toAdd_sgnAut (i : Fin n) (f : Fin n → Multiplicative (ZMod p)) :
    ∏ j, toAdd (sgnAut i f j) = -∏ j, toAdd (f j) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => toAdd (sgnAut i f j))
      (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => toAdd (f j)) (Finset.mem_univ i)]
  have h : ∏ j ∈ Finset.univ.erase i, toAdd (sgnAut i f j) =
      ∏ j ∈ Finset.univ.erase i, toAdd (f j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [sgnAut_apply, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h, sgnAut_apply, Function.update_self, toAdd_inv]
  ring

private theorem prod_toAdd_permAut (σ : Equiv.Perm (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) :
    ∏ i, toAdd (permAut σ f i) = ∏ i, toAdd (f i) := by
  have h : (fun i => toAdd (permAut σ f i)) = fun i => toAdd (f (σ⁻¹ i)) := by
    funext i
    rw [permAut_apply, Function.comp_apply]
  rw [h]
  exact Equiv.prod_comp σ⁻¹ (fun i => toAdd (f i))

private theorem prod_toAdd_of_isSignedPerm {u : MulAut (Fin n → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (f : Fin n → Multiplicative (ZMod p)) :
    ∏ i, toAdd (u f i) = (∏ i, ε i) * ∏ i, toAdd (f i) := by
  rw [← Equiv.prod_comp π (fun i => toAdd (u f i))]
  rw [show ∏ i, toAdd (u f (π i)) = ∏ i, ε i * toAdd (f i) from
    Finset.prod_congr rfl fun i _ => hu f i]
  exact Finset.prod_mul_distrib

@[expose] def coordProdStab (n p : ℕ) : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) where
  carrier := {u | ∀ f, ∏ i, toAdd (u f i) = ∏ i, toAdd (f i)}
  mul_mem' := by
    intro u v hu hv f
    change (∏ i, toAdd (u (v f) i)) = ∏ i, toAdd (f i)
    rw [hu (v f), hv f]
  one_mem' := by
    intro f
    rfl
  inv_mem' := by
    intro u hu f
    simpa [MulAut.apply_inv_self] using (hu (u⁻¹ f)).symm

private theorem permAut_swap_mem_coordProdStab (a b : Fin n) :
    permAut (Equiv.swap a b) ∈ coordProdStab n p := by
  intro f
  exact prod_toAdd_permAut (Equiv.swap a b) f

private theorem negTrans_mem_coordProdStab (a b : Fin n) :
    sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ ∈ coordProdStab n p := by
  have h2 : (sgnAut a : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut a = 1 := by
    simpa [sq] using sgnAut_sq a
  have hinv : (sgnAut a : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = sgnAut a :=
    inv_eq_of_mul_eq_one_right h2
  intro f
  rw [MulAut.mul_apply, MulAut.mul_apply, prod_toAdd_sgnAut, prod_toAdd_permAut, hinv,
    prod_toAdd_sgnAut]
  ring

theorem aPermutationFull_le_coordProdStab :
    aPermutationFull n p ≤ coordProdStab n p := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨a, b, _, rfl⟩
  exact permAut_swap_mem_coordProdStab a b

private theorem map_bCoordinateBlock_le_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (j : Fin n) :
    (bCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom ≤
      bCoordinateBlock n p (π j) := by
  rw [bCoordinateBlock, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨g, (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩), rfl⟩
  · rw [conj_toMonoidHom_apply u (sgnAut i), conj_sgnAut_eq hu i]
    exact Subgroup.subset_closure (Or.inl ⟨π i, fun h => hi (π.injective h), rfl⟩)
  · have hcd : π a ≠ π b := fun h => hab (π.injective h)
    have hca : π a ≠ π j := fun h => ha (π.injective h)
    have hcb : π b ≠ π j := fun h => hb (π.injective h)
    rw [conj_toMonoidHom_apply u (permAut (Equiv.swap a b))]
    by_cases hs : ε a * ε b = 1
    · rw [conj_permAut_swap_eq_of_mul_eq_one hε hu hs]
      exact Subgroup.subset_closure (Or.inr ⟨π a, π b, hcd, hca, hcb, rfl⟩)
    · have hsneg : ε a * ε b = -1 := by
        rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp_all
      rw [conj_permAut_swap_eq_of_mul_eq_neg_one hε hu hab hsneg]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inl ⟨π a, hca, rfl⟩))
        (Subgroup.subset_closure (Or.inr ⟨π a, π b, hcd, hca, hcb, rfl⟩)))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl ⟨π a, hca, rfl⟩)))

private theorem map_bCoordinateBlock_perm_le_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {j c d : Fin n}
    (hcd : c ≠ d) (hc : c ≠ π j) (hd : d ≠ π j) :
    permAut (Equiv.swap c d) ∈
      (bCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
  let a : Fin n := π⁻¹ c
  let b : Fin n := π⁻¹ d
  have hca : π a = c := by simp [a]
  have hcb : π b = d := by simp [b]
  have hab : a ≠ b := fun h => hcd (by rw [← hca, ← hcb, h])
  have ha : a ≠ j := fun h => hc (by rw [← hca, h])
  have hb : b ≠ j := fun h => hd (by rw [← hcb, h])
  have hgen : permAut (Equiv.swap a b) ∈ bCoordinateBlock n p j :=
    Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)
  by_cases hs : ε a * ε b = 1
  · refine Subgroup.mem_map.mpr ⟨permAut (Equiv.swap a b), hgen, ?_⟩
    rw [conj_toMonoidHom_apply, conj_permAut_swap_eq_of_mul_eq_one hε hu hs, hca, hcb]
  · have hsneg : ε a * ε b = -1 := by
      rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp_all
    have hN : sgnAut c * permAut (Equiv.swap c d) * (sgnAut c)⁻¹ ∈
        (bCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨permAut (Equiv.swap a b), hgen, ?_⟩
      rw [conj_toMonoidHom_apply, conj_permAut_swap_eq_of_mul_eq_neg_one hε hu hab hsneg,
        hca, hcb]
    have hcH : sgnAut c ∈
        (bCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨sgnAut a,
        Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩), ?_⟩
      rw [conj_toMonoidHom_apply, conj_sgnAut_eq hu a, hca]
    have hs2 : (sgnAut c : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut c = 1 := by
      simpa [sq] using sgnAut_sq c
    have hinv : (sgnAut c : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = sgnAut c :=
      inv_eq_of_mul_eq_one_right hs2
    have hP : permAut (p := p) (Equiv.swap c d) =
        sgnAut c * (sgnAut c * permAut (p := p) (Equiv.swap c d) *
          (sgnAut c)⁻¹) * sgnAut c := by
      rw [hinv]
      exact (sgnAut_conj_self c (permAut (p := p) (Equiv.swap c d))).symm
    rw [hP]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH hN) hcH

private theorem bCoordinateBlock_le_map_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (j : Fin n) :
    bCoordinateBlock n p (π j) ≤
      (bCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r (⟨c, hc, rfl⟩ | ⟨c, d, hcd, hc, hd, rfl⟩)
  · let i : Fin n := π⁻¹ c
    have hi : i ≠ j := by
      intro h
      have hcπ : c = π j := by
        calc c = π i := (Equiv.apply_symm_apply π c).symm
          _ = π j := by rw [h]
      exact hc hcπ
    refine Subgroup.mem_map.mpr ⟨sgnAut i,
      Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩), ?_⟩
    rw [conj_toMonoidHom_apply, conj_sgnAut_eq hu i]
    simp [i]
  · exact map_bCoordinateBlock_perm_le_of_isSignedPerm hε hu hcd hc hd

private theorem map_dCoordinateBlock_le_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (j : Fin n) :
    (dCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom ≤
      dCoordinateBlock n p (π j) := by
  rw [dCoordinateBlock, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨g, (⟨a, b, hab, ha, hb, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩), rfl⟩
  · have hcd : π a ≠ π b := fun h => hab (π.injective h)
    have hca : π a ≠ π j := fun h => ha (π.injective h)
    have hcb : π b ≠ π j := fun h => hb (π.injective h)
    rw [conj_toMonoidHom_apply u (permAut (Equiv.swap a b))]
    by_cases hs : ε a * ε b = 1
    · rw [conj_permAut_swap_eq_of_mul_eq_one hε hu hs]
      exact Subgroup.subset_closure (Or.inl ⟨π a, π b, hcd, hca, hcb, rfl⟩)
    · have hsneg : ε a * ε b = -1 := by
        rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp_all
      rw [conj_permAut_swap_eq_of_mul_eq_neg_one hε hu hab hsneg]
      exact Subgroup.subset_closure (Or.inr ⟨π a, π b, hcd, hca, hcb, rfl⟩)
  · have hcd : π a ≠ π b := fun h => hab (π.injective h)
    have hca : π a ≠ π j := fun h => ha (π.injective h)
    have hcb : π b ≠ π j := fun h => hb (π.injective h)
    rw [conj_toMonoidHom_apply u
      (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹)]
    by_cases hs : ε a * ε b = 1
    · rw [conj_negTrans_eq_of_mul_eq_one hε hu hs]
      exact Subgroup.subset_closure (Or.inr ⟨π a, π b, hcd, hca, hcb, rfl⟩)
    · have hsneg : ε a * ε b = -1 := by
        rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp_all
      rw [conj_negTrans_eq_of_mul_eq_neg_one hε hu hab hsneg]
      exact Subgroup.subset_closure (Or.inl ⟨π a, π b, hcd, hca, hcb, rfl⟩)

private theorem map_dCoordinateBlock_transposition_le_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {j c d : Fin n}
    (hcd : c ≠ d) (hc : c ≠ π j) (hd : d ≠ π j) :
    permAut (Equiv.swap c d) ∈
      (dCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
  let a : Fin n := π⁻¹ c
  let b : Fin n := π⁻¹ d
  have hca : π a = c := by simp [a]
  have hcb : π b = d := by simp [b]
  have hab : a ≠ b := fun h => hcd (by rw [← hca, ← hcb, h])
  have ha : a ≠ j := fun h => hc (by rw [← hca, h])
  have hb : b ≠ j := fun h => hd (by rw [← hcb, h])
  have hPgen : permAut (Equiv.swap a b) ∈ dCoordinateBlock n p j :=
    Subgroup.subset_closure (Or.inl ⟨a, b, hab, ha, hb, rfl⟩)
  have hNgen : sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ ∈
      dCoordinateBlock n p j :=
    Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)
  by_cases hs : ε a * ε b = 1
  · refine Subgroup.mem_map.mpr ⟨permAut (Equiv.swap a b), hPgen, ?_⟩
    rw [conj_toMonoidHom_apply, conj_permAut_swap_eq_of_mul_eq_one hε hu hs, hca, hcb]
  · have hsneg : ε a * ε b = -1 := by
      rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp_all
    refine Subgroup.mem_map.mpr
      ⟨sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹, hNgen, ?_⟩
    rw [conj_toMonoidHom_apply, conj_negTrans_eq_of_mul_eq_neg_one hε hu hab hsneg, hca,
      hcb]

private theorem map_dCoordinateBlock_negTrans_le_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) {j c d : Fin n}
    (hcd : c ≠ d) (hc : c ≠ π j) (hd : d ≠ π j) :
    sgnAut c * permAut (Equiv.swap c d) * (sgnAut c)⁻¹ ∈
      (dCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
  let a : Fin n := π⁻¹ c
  let b : Fin n := π⁻¹ d
  have hca : π a = c := by simp [a]
  have hcb : π b = d := by simp [b]
  have hab : a ≠ b := fun h => hcd (by rw [← hca, ← hcb, h])
  have ha : a ≠ j := fun h => hc (by rw [← hca, h])
  have hb : b ≠ j := fun h => hd (by rw [← hcb, h])
  have hPgen : permAut (Equiv.swap a b) ∈ dCoordinateBlock n p j :=
    Subgroup.subset_closure (Or.inl ⟨a, b, hab, ha, hb, rfl⟩)
  have hNgen : sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ ∈
      dCoordinateBlock n p j :=
    Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)
  by_cases hs : ε a * ε b = 1
  · refine Subgroup.mem_map.mpr
      ⟨sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹, hNgen, ?_⟩
    rw [conj_toMonoidHom_apply, conj_negTrans_eq_of_mul_eq_one hε hu hs, hca, hcb]
  · have hsneg : ε a * ε b = -1 := by
      rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp_all
    refine Subgroup.mem_map.mpr ⟨permAut (Equiv.swap a b), hPgen, ?_⟩
    rw [conj_toMonoidHom_apply, conj_permAut_swap_eq_of_mul_eq_neg_one hε hu hab hsneg, hca,
      hcb]

private theorem dCoordinateBlock_le_map_of_isSignedPerm
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (j : Fin n) :
    dCoordinateBlock n p (π j) ≤
      (dCoordinateBlock n p j).map (MulAut.conj u).toMonoidHom := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r (⟨c, d, hcd, hc, hd, rfl⟩ | ⟨c, d, hcd, hc, hd, rfl⟩)
  · exact map_dCoordinateBlock_transposition_le_of_isSignedPerm hε hu hcd hc hd
  · exact map_dCoordinateBlock_negTrans_le_of_isSignedPerm hε hu hcd hc hd

theorem exists_map_conj_bCoordinateBlock
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ : δ ∈ bSignedFull n p) (j : Fin n) :
    ∃ j' : Fin n, (bCoordinateBlock n p j).map (MulAut.conj δ).toMonoidHom =
      bCoordinateBlock n p j' := by
  obtain ⟨π, ε, hε, hu⟩ := isSignedPerm_of_mem_bSignedFull hδ
  exact ⟨π j, le_antisymm (map_bCoordinateBlock_le_of_isSignedPerm hε hu j)
    (bCoordinateBlock_le_map_of_isSignedPerm hε hu j)⟩

theorem exists_map_conj_dCoordinateBlock
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ : δ ∈ bSignedFull n p) (j : Fin n) :
    ∃ j' : Fin n, (dCoordinateBlock n p j).map (MulAut.conj δ).toMonoidHom =
      dCoordinateBlock n p j' := by
  obtain ⟨π, ε, hε, hu⟩ := isSignedPerm_of_mem_bSignedFull hδ
  exact ⟨π j, le_antisymm (map_dCoordinateBlock_le_of_isSignedPerm hε hu j)
    (dCoordinateBlock_le_map_of_isSignedPerm hε hu j)⟩

theorem exists_signs_apply_const {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ : δ ∈ bSignedFull n p) :
    ∃ ε : Fin n → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ (c : ZMod p) (i : Fin n), toAdd (δ (fun _ => ofAdd c) i) = ε i * c := by
  obtain ⟨π, ε, hε, hu⟩ := isSignedPerm_of_mem_bSignedFull hδ
  refine ⟨fun k => ε (π⁻¹ k), fun k => hε _, fun c i => ?_⟩
  have h := hu (fun _ => ofAdd c) (π⁻¹ i)
  have hπ : π (π⁻¹ i) = i := by
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rwa [hπ, toAdd_ofAdd] at h

private theorem eq_permAut_of_isSignedPerm_all_one
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (h1 : ∀ i, ε i = 1) : u = permAut (p := p) π := by
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
  rw [hu f i, h1 i, one_mul, permAut_apply, Function.comp_apply]
  simp

private theorem eq_permAut_mul_negAut_of_isSignedPerm_all_neg
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod p} (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (hm1 : ∀ i, ε i = -1) :
    u = permAut (p := p) π * OrthExcEven.negAut (p := p) (k := n) := by
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
  rw [hu f i, hm1 i, neg_one_mul, MulAut.mul_apply, permAut_apply, Function.comp_apply,
    OrthExcEven.negAut_apply]
  simp only [Pi.inv_apply, toAdd_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem aPermutationFull_map_conj_eq_of_apply_one {δ δ' : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ : δ ∈ bSignedFull n p) (hδ' : δ' ∈ bSignedFull n p)
    (h : δ (fun _ => ofAdd (1 : ZMod p)) = δ' (fun _ => ofAdd 1) ∨
      δ (fun _ => ofAdd (1 : ZMod p)) = (δ' (fun _ => ofAdd 1))⁻¹) :
    (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ').toMonoidHom := by
  let ψ : MulAut (Fin n → Multiplicative (ZMod p)) := δ'⁻¹ * δ
  let v : Fin n → Multiplicative (ZMod p) := fun _ => ofAdd (1 : ZMod p)
  have hψmem : ψ ∈ bSignedFull n p := Subgroup.mul_mem _ (Subgroup.inv_mem _ hδ') hδ
  obtain ⟨π, ε, hε, hψ⟩ := isSignedPerm_of_mem_bSignedFull hψmem
  have hψ1 : ψ v = v ∨ ψ v = v⁻¹ := by
    rcases h with h | h
    · left
      change δ'⁻¹ (δ v) = v
      rw [h, MulAut.inv_apply_self]
    · right
      change δ'⁻¹ (δ v) = v⁻¹
      rw [h, map_inv, MulAut.inv_apply_self]
  have hsigns : (∀ i, ε i = 1) ∨ (∀ i, ε i = -1) := by
    rcases hψ1 with h1 | h1
    · left
      intro i
      have hcoord := congrArg (fun g : Fin n → Multiplicative (ZMod p) =>
        toAdd (g (π i))) h1
      rw [hψ v i] at hcoord
      simpa [v] using hcoord
    · right
      intro i
      have hcoord := congrArg (fun g : Fin n → Multiplicative (ZMod p) =>
        toAdd (g (π i))) h1
      rw [hψ v i] at hcoord
      simpa [v] using hcoord
  have hmapψ : (aPermutationFull n p).map (MulAut.conj ψ).toMonoidHom =
      aPermutationFull n p := by
    rcases hsigns with h1 | hm1
    · rw [eq_permAut_of_isSignedPerm_all_one hψ h1, map_conj_permAut]
    · rw [eq_permAut_mul_negAut_of_isSignedPerm_all_neg hψ hm1,
        ← conj_mul_map (aPermutationFull n p) (permAut (p := p) π)
          (OrthExcEven.negAut (p := p) (k := n))]
      rw [map_conj_negAut, map_conj_permAut]
  have hδeq : δ = δ' * ψ := by
    change δ = δ' * (δ'⁻¹ * δ)
    group
  calc
    (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom
        = (aPermutationFull n p).map (MulAut.conj (δ' * ψ)).toMonoidHom := by rw [hδeq]
    _ = ((aPermutationFull n p).map (MulAut.conj ψ).toMonoidHom).map
          (MulAut.conj δ').toMonoidHom := (conj_mul_map (aPermutationFull n p) δ' ψ).symm
    _ = (aPermutationFull n p).map (MulAut.conj δ').toMonoidHom := by rw [hmapψ]

theorem dCoordinateBlock_le_coordProdStab (j : Fin n) :
    dCoordinateBlock n p j ≤ coordProdStab n p := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r (⟨a, b, _, _, _, rfl⟩ | ⟨a, b, _, _, _, rfl⟩)
  · exact permAut_swap_mem_coordProdStab a b
  · exact negTrans_mem_coordProdStab a b

theorem aPermutationFull_map_conj_le_coordProdStab {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ : δ ∈ bSignedFull n p) :
    (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom ≤ coordProdStab n p := by
  obtain ⟨π, ε, hε, hu⟩ := isSignedPerm_of_mem_bSignedFull hδ
  set s : ZMod p := ∏ i, ε i with hsdef
  have hss : s * s = 1 := by
    rw [hsdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => coord_sign_mul_self (hε i)
  rintro v hv f
  obtain ⟨u, huS, rfl⟩ := Subgroup.mem_map.mp hv
  have huProd : ∏ i, toAdd (u (δ⁻¹ f) i) = ∏ i, toAdd ((δ⁻¹ f) i) :=
    aPermutationFull_le_coordProdStab huS (δ⁻¹ f)
  have hδprod := prod_toAdd_of_isSignedPerm (u := δ) (π := π) (ε := ε) hu (δ⁻¹ f)
  rw [show δ (δ⁻¹ f) = f by rw [MulAut.apply_inv_self]] at hδprod
  have hQ : ∏ i, toAdd ((δ⁻¹ f) i) = s * ∏ i, toAdd (f i) := by
    calc ∏ i, toAdd ((δ⁻¹ f) i) = 1 * ∏ i, toAdd ((δ⁻¹ f) i) := by rw [one_mul]
      _ = (s * s) * ∏ i, toAdd ((δ⁻¹ f) i) := by rw [hss]
      _ = s * (s * ∏ i, toAdd ((δ⁻¹ f) i)) := by ring
      _ = s * ∏ i, toAdd (f i) := by rw [← hδprod]
  calc
    ∏ i, toAdd ((δ * u * δ⁻¹) f i)
        = s * ∏ i, toAdd (u (δ⁻¹ f) i) :=
          prod_toAdd_of_isSignedPerm (u := δ) (π := π) (ε := ε) hu (u (δ⁻¹ f))
    _ = s * ∏ i, toAdd ((δ⁻¹ f) i) := by rw [huProd]
    _ = s * (s * ∏ i, toAdd (f i)) := by rw [hQ]
    _ = ∏ i, toAdd (f i) := by rw [← mul_assoc, hss, one_mul]

theorem sgnAut_not_mem_coordProdStab (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin n) :
    sgnAut i ∉ coordProdStab n p := by
  intro h
  have h1 := h (fun _ : Fin n => (ofAdd 1 : Multiplicative (ZMod p)))
  have hleft : ∏ j, toAdd (sgnAut i (fun _ => ofAdd 1) j) = (-1 : ZMod p) := by
    rw [prod_toAdd_sgnAut]
    simp
  have hright : ∏ j : Fin n,
      toAdd ((fun _ : Fin n => (ofAdd 1 : Multiplicative (ZMod p))) j) = (1 : ZMod p) := by
    simp
  rw [hleft, hright] at h1
  have h2 : (2 : ZMod p) = 0 := by
    have h1' : (1 : ZMod p) = -1 := h1.symm
    linear_combination h1'
  exact coord_two_ne_zero hp hp2 h2

end CFSG.StandardType

end
