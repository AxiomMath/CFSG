module

public import CFSG.Sporadic.Fi22.Simple

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def D : Set J := {x | IsConj a x}

theorem orderOf_conj'
    (g x : J) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm

theorem mem_D_iff {x : J} : x ∈ D ↔ ∃ k < 3510, x = conjPt k := by
  have h : x ∈ D ↔ x ∈ MulAction.orbit (ConjAct J) a := by
    rw [ConjAct.mem_orbit_conjAct]
    exact ⟨IsConj.symm, IsConj.symm⟩
  rw [h, orbit_eq, orb_size]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem a_mem_D : a ∈ D := IsConj.refl a

theorem orderOf_of_mem_D {x : J} (hx : x ∈ D) : orderOf x = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  rw [orderOf_conj', orderOf_a]

theorem productChecks_parts :
    canonM 77 (mul 77 matA orb.keys[1]!) = true ∧
    canonM 77 (mul 77 matA orb.keys[subRoot]!) = true ∧
    eqM 77 (powM 77 (mul 77 matA orb.keys[1]!) 3) (idM 77) = true ∧
    eqM 77 (mul 77 matA orb.keys[1]!) (idM 77) = false ∧
    eqM 77 (powM 77 (mul 77 matA orb.keys[subRoot]!) 2) (idM 77) = true ∧
    eqM 77 (mul 77 matA orb.keys[subRoot]!) (idM 77) = false := by
  have h := certificate_parts.2.2.2
  unfold productChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem one_lt_orb : 1 < orb.keys.size := by rw [orb_size]; norm_num

theorem subRoot_lt_orb : subRoot < orb.keys.size := by
  rw [orb_size]; exact treeFacts_two.r_lt

theorem mat_a_conjPt {k : ℕ} (hk : k < orb.keys.size) :
    mat (a * conjPt k) = toMat 77 (mul 77 matA orb.keys[k]!) := by
  rw [mat_mul, mat_a, conjPt_mat k hk,
    toMat_mul matA_size rowsWF_matA (RowsWF.of_canonM (conjFacts.canon k hk))]

theorem orderOf_a_conjPt_one : orderOf (a * conjPt 1) = 3 := by
  obtain ⟨hc1, -, hp1, hn1, -, -⟩ := productChecks_parts
  have hw : RowsWF (mul 77 matA orb.keys[1]!) :=
    RowsWF.mul _ 77 rowsWF_matA (RowsWF.of_canonM (conjFacts.canon 1 one_lt_orb))
  have hs : (mul 77 matA orb.keys[1]!).size = 77 := by rw [mul_size, matA_size]
  refine orderOf_eq_prime ?_ ?_
  · apply mat_injective
    rw [mat_pow, mat_a_conjPt one_lt_orb, mat_one, ← toMat_powM hw, toMat_eq_of_eqM hp1,
      toMat_idM]
  · intro h
    have := not_eqM_of_ne hs (idM_size 77) hn1 hc1 (canonM_idM 77)
    apply this
    rw [← mat_a_conjPt one_lt_orb, h, mat_one, toMat_idM]

theorem orderOf_a_conjPt_sub : orderOf (a * conjPt subRoot) = 2 := by
  obtain ⟨-, hc2, -, -, hp2, hn2⟩ := productChecks_parts
  have hw : RowsWF (mul 77 matA orb.keys[subRoot]!) :=
    RowsWF.mul _ 77 rowsWF_matA (RowsWF.of_canonM (conjFacts.canon _ subRoot_lt_orb))
  have hs : (mul 77 matA orb.keys[subRoot]!).size = 77 := by rw [mul_size, matA_size]
  refine orderOf_eq_prime ?_ ?_
  · apply mat_injective
    rw [mat_pow, mat_a_conjPt subRoot_lt_orb, mat_one, ← toMat_powM hw, toMat_eq_of_eqM hp2,
      toMat_idM]
  · intro h
    have := not_eqM_of_ne hs (idM_size 77) hn2 hc2 (canonM_idM 77)
    apply this
    rw [← mat_a_conjPt subRoot_lt_orb, h, mat_one, toMat_idM]

theorem conj_a_of_fix
    {h : J} (hh : h • root = root) : h * a * h⁻¹ = a := by
  have := conjPt_smul h root
  rw [hh] at this
  rw [← conjPt_zero]
  exact this.symm

theorem orderOf_a_conjPt {k : ℕ} (hk : k < 3510) :
    orderOf (a * conjPt k) = 1 ∨ orderOf (a * conjPt k) = 2 ∨ orderOf (a * conjPt k) = 3 := by
  set p : Fin 3510 := ⟨k, hk⟩
  have hcases : subLab p = 0 ∨ subLab p = 1 ∨ subLab p = 2 := by
    rcases subLab p with ⟨_ | _ | _ | n, hn⟩
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · omega
  have key : ∀ (r : Fin 3510) (h : J), h ∈ lvl 1 → h • r = p →
      orderOf (a * conjPt k) = orderOf (a * conjPt r.val) := by
    intro r h hh hr
    have e1 := conjPt_smul h r
    rw [hr] at e1
    have e2 := conj_a_of_fix (lvl_one_fix hh)
    show orderOf (a * conjPt p.val) = _
    have e3 : a * conjPt p.val = h * (a * conjPt r.val) * h⁻¹ := by
      rw [e1]
      calc a * (h * conjPt r.val * h⁻¹) = (h * a * h⁻¹) * (h * conjPt r.val * h⁻¹) := by rw [e2]
        _ = h * (a * conjPt r.val) * h⁻¹ := by group
    rw [e3, orderOf_conj']
  rcases hcases with h0 | h1 | h2
  · left
    have hp : p = root := subLab_eq_zero.1 h0
    have hk0 : k = 0 := congrArg Fin.val hp
    subst hk0
    rw [conjPt_zero, ← pow_two, a_sq, orderOf_one]
  · right; right
    obtain ⟨⟨h, hh⟩, hr⟩ := subLab_eq_one.1 h1
    rw [key _ h hh hr]
    exact orderOf_a_conjPt_one
  · right; left
    obtain ⟨⟨h, hh⟩, hr⟩ := two_mem_orbit h2
    rw [key _ h hh hr]
    exact orderOf_a_conjPt_sub

theorem orderOf_mul_mem_D {x y : J} (hx : x ∈ D) (hy : y ∈ D) :
    orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  have hy' : g⁻¹ * y * g ∈ D := by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    exact isConj_iff.2 ⟨g⁻¹ * c, by group⟩
  obtain ⟨k, hk, hke⟩ := mem_D_iff.1 hy'
  have e : g * a * g⁻¹ * y = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
  rw [e, orderOf_conj', hke]
  rcases orderOf_a_conjPt hk with h | h | h <;> simp [h]

theorem a_mul_conjPt_one_ne : a * conjPt 1 ≠ conjPt 1 * a := by
  intro h
  have hc : orderOf (conjPt 1) = 2 := orderOf_of_mem_D (mem_D_iff.2 ⟨1, by norm_num, rfl⟩)
  have hc2 : conjPt 1 ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one _
  have h2 : (a * conjPt 1) ^ 2 = 1 := by
    calc (a * conjPt 1) ^ 2 = a * (conjPt 1 * a) * conjPt 1 := by rw [pow_two]; group
      _ = a * (a * conjPt 1) * conjPt 1 := by rw [h]
      _ = a ^ 2 * conjPt 1 ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [a_sq, hc2, one_mul]
  have h3 : orderOf (a * conjPt 1) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_a_conjPt_one] at h3
  exact absurd h3 (by norm_num)

theorem closure_D : Subgroup.closure D = ⊤ := by
  have := isSimpleGroup_J
  have hD : D = Group.conjugatesOfSet {a} := by
    ext x
    simp [D, Group.conjugatesOfSet, conjugatesOf]
  have hn : (Subgroup.closure D).Normal := by
    rw [hD]; exact Subgroup.normalClosure_normal
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    have : a ∈ Subgroup.closure D := Subgroup.subset_closure a_mem_D
    rw [h, Subgroup.mem_bot] at this
    exact a_ne_one this
  · exact h

theorem center_eq_bot : Subgroup.center J = ⊥ := by
  have := isSimpleGroup_J
  rcases (Subgroup.center J).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply a_mul_conjPt_one_ne
    have : a ∈ Subgroup.center J := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 this (conjPt 1)).symm

theorem commutator_eq_top : commutator J = ⊤ := by
  have := isSimpleGroup_J
  have hn : (commutator J).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    apply a_mul_conjPt_one_ne
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h ▸ (commutator_def J).symm)
    have ha : a ∈ Subgroup.centralizer ((⊤ : Subgroup J) : Set J) := this (Subgroup.mem_top a)
    exact (Subgroup.mem_centralizer_iff.1 ha (conjPt 1) (Subgroup.mem_top _)).symm
  · exact h

end CFSG.Sporadic.Fi22
