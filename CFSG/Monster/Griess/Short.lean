module

public import CFSG.Monster.SpinLattice.Isometry
public import CFSG.Monster.Code.LatticeCount

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Subgroup

@[expose] def IsShortCoord (p : C × Cocode) : Prop := ∃ u ∈ minVecs, classOf u = phi0 p

@[expose] def IsShort (c : Q ⧸ center Q) : Prop :=
  ∃ u ∈ minVecs, classOf u = Multiplicative.toAdd (phi c)

@[expose] noncomputable def coordOf (r : Q) : C × Cocode :=
  ((spinEquiv.symm r).a, (spinEquiv.symm r).δ)

@[expose] noncomputable def centralCoord (r : Q) : ZMod 2 := (spinEquiv.symm r).s

theorem toAdd_phi_mk (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk r)) = phi0 (coordOf r) :=
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  (congrArg (fun g => Multiplicative.toAdd (phi (QuotientGroup.mk g))) hx.symm).trans
    (congrArg Multiplicative.toAdd (phi_mk_spinEquiv (spinEquiv.symm r)))

theorem isShort_mk_iff (r : Q) : IsShort (QuotientGroup.mk r) ↔ IsShortCoord (coordOf r) := by
  unfold IsShort IsShortCoord
  rw [toAdd_phi_mk]

abbrev ShortIdx : Type := {p : C × Cocode // IsShortCoord p}

noncomputable instance : Fintype ShortIdx := Fintype.ofFinite _

noncomputable instance : DecidableEq ShortIdx := Classical.decEq _

theorem card_shortIdx : Nat.card ShortIdx = 98280 := by
  have e : ShortIdx ≃ {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c} :=
    { toFun := fun p => ⟨phi0 p.1, p.2⟩
      invFun := fun c => ⟨phi0Equiv.symm c.1, by
        obtain ⟨u, hu, h⟩ := c.2
        exact ⟨u, hu, h.trans (phi0Equiv.apply_symm_apply c.1).symm⟩⟩
      left_inv := fun p => Subtype.ext (phi0Equiv.symm_apply_apply p.1)
      right_inv := fun c => Subtype.ext (phi0Equiv.apply_symm_apply c.1) }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, card_classes]

@[expose] noncomputable def rep (p : C × Cocode) : Q := spinEquiv ⟨0, p.1, p.2⟩

theorem coe_rep (p : C × Cocode) : ((rep p : Q) : GL SpinIdx ℚ) = TU p.1 * DU p.2 := by
  rw [rep, coe_spinEquiv, toGL_mk, ZMod.val_zero, pow_zero, one_mul]

theorem coordOf_rep (p : C × Cocode) : coordOf (rep p) = p := by
  rw [coordOf, rep, MulEquiv.symm_apply_apply]

theorem centralCoord_rep (p : C × Cocode) : centralCoord (rep p) = 0 := by
  rw [centralCoord, rep, MulEquiv.symm_apply_apply]

theorem eq_zQ_pow_mul_rep (r : Q) : r = zQ ^ (centralCoord r).val * rep (coordOf r) := by
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have h : spinEquiv.symm r = ⟨centralCoord r, 0, 0⟩ * ⟨0, (coordOf r).1, (coordOf r).2⟩ := by
    ext <;> simp [centralCoord, coordOf, SpinCoord.mul_s]
  calc r = spinEquiv (spinEquiv.symm r) := hx.symm
    _ = spinEquiv (⟨centralCoord r, 0, 0⟩ * ⟨0, (coordOf r).1, (coordOf r).2⟩) :=
        congrArg spinEquiv h
    _ = zQ ^ (centralCoord r).val * rep (coordOf r) := by
        rw [map_mul, ← zQ_pow_val]
        rfl

theorem qL_classOf_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : qL (classOf u) = 0 := by
  have hL := hu.1
  have h4 : normSq u = 32 := (mem_minVecs_iff.1 hu).2
  have hcl : classOf u = cls u hL := by
    unfold classOf
    exact dite_eq_left hL
  rw [hcl, qL_cls]
  have : hInt u u = 4 := by
    unfold hInt
    rw [show (∑ i, u i * u i) = normSq u from rfl, h4]
    rfl
  rw [this]
  rfl

theorem pair_eq_zero_of_isShortCoord {p : C × Cocode} (h : IsShortCoord p) : pair p.1 p.2 = 0 := by
  obtain ⟨u, hu, hcl⟩ := h
  rw [← qL_phi0, ← hcl, qL_classOf_minVecs hu]

theorem sq_eq_one_of_isShort {r : Q} (h : IsShortCoord (coordOf r)) : r ^ 2 = 1 := by
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have h0 : pair (coordOf r).1 (coordOf r).2 = 0 := pair_eq_zero_of_isShortCoord (p := coordOf r) h
  have hsq : spinEquiv.symm r ^ 2 = 1 := by
    rw [SpinCoord.sq_eq]
    exact SpinCoord.ext h0 rfl rfl
  calc r ^ 2 = spinEquiv (spinEquiv.symm r) ^ 2 := (congrArg (· ^ 2) hx).symm
    _ = spinEquiv (spinEquiv.symm r ^ 2) := (map_pow spinEquiv _ 2).symm
    _ = spinEquiv 1 := congrArg spinEquiv hsq
    _ = 1 := map_one spinEquiv

@[expose] def LexLE (u v : Fin 24 → ℤ) : Prop := toLex u ≤ toLex v

@[expose] noncomputable def uvec (c : ShortIdx) : Fin 24 → ℤ :=
  open Classical in
  if LexLE c.2.choose (-c.2.choose) then c.2.choose else -c.2.choose

theorem uvec_spec (c : ShortIdx) :
    uvec c ∈ minVecs ∧ classOf (uvec c) = phi0 c.1 ∧ LexLE (uvec c) (-uvec c) := by
  obtain ⟨hu, hcl⟩ := c.2.choose_spec
  unfold uvec
  split_ifs with h
  · exact ⟨hu, hcl, h⟩
  · refine ⟨neg_mem_minVecs hu, ?_, ?_⟩
    · exact ((classOf_eq_iff hu (neg_mem_minVecs hu)).2 (Or.inr rfl)).symm.trans hcl
    · rw [neg_neg]
      exact le_of_lt (lt_of_not_ge h)

theorem uvec_mem (c : ShortIdx) : uvec c ∈ minVecs := (uvec_spec c).1

theorem classOf_uvec (c : ShortIdx) : classOf (uvec c) = phi0 c.1 := (uvec_spec c).2.1

theorem eq_uvec {c : ShortIdx} {v : Fin 24 → ℤ} (hv : v ∈ minVecs)
    (hcl : classOf v = phi0 c.1) (hle : LexLE v (-v)) : v = uvec c := by
  obtain ⟨hu, hclu, hleu⟩ := uvec_spec c
  rcases (classOf_eq_iff hu hv).1 (hclu.trans hcl.symm) with h | h
  · exact h
  · exfalso
    subst h
    have h0 : uvec c ≠ 0 := minVecs_ne_zero hu
    have hne : -uvec c ≠ uvec c := fun h => h0 (by
      have h2 : uvec c + uvec c = 0 := by nth_rw 1 [← h]; exact neg_add_cancel _
      have : (2 : ℤ) • uvec c = 0 := by rw [two_smul]; exact h2
      exact (smul_eq_zero.1 this).resolve_left (by norm_num))
    rw [neg_neg] at hle
    exact hne (toLex.injective (le_antisymm hle hleu))

end CFSG.Monster.Griess
