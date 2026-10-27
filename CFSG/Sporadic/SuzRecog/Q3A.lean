module

public import CFSG.Sporadic.SuzRecog.ModelBase

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.Q3A

open Subgroup CFSG.Sporadic.SuzOddCore

@[expose] def base : Subgroup (Equiv.Perm (Fin 1782)) := zpowers Model.rho1

@[expose] def IsVtx (H : Subgroup (Equiv.Perm (Fin 1782))) : Prop :=
  ∃ g ∈ suzM, H = base.map (MulAut.conj g).toMonoidHom

abbrev Vtx : Type := {H : Subgroup (Equiv.Perm (Fin 1782)) // IsVtx H}

theorem map_conj_map_conj (g h : Equiv.Perm (Fin 1782)) (H : Subgroup (Equiv.Perm (Fin 1782))) :
    (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem isVtx_map {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzM) {H : Subgroup (Equiv.Perm (Fin 1782))}
    (hH : IsVtx H) : IsVtx (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨h, hh, rfl⟩ := hH
  exact ⟨g * h, mul_mem hg hh, map_conj_map_conj g h base⟩

instance instMulAction : MulAction ↥suzM Vtx where
  smul g x := ⟨x.1.map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom, isVtx_map g.2 x.2⟩
  one_smul x := Subtype.ext (by
    show x.1.map (MulAut.conj (1 : Equiv.Perm (Fin 1782))).toMonoidHom = x.1
    rw [map_one]
    exact Subgroup.map_id x.1)
  mul_smul g h x := Subtype.ext (by
    show x.1.map (MulAut.conj ((g : Equiv.Perm (Fin 1782)) * h)).toMonoidHom =
      (x.1.map (MulAut.conj (h : Equiv.Perm (Fin 1782))).toMonoidHom).map
        (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom
    rw [map_conj_map_conj])

theorem coe_smul (g : ↥suzM) (x : Vtx) :
    ((g • x : Vtx) : Subgroup (Equiv.Perm (Fin 1782))) =
      (x : Subgroup (Equiv.Perm (Fin 1782))).map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom :=
  rfl

theorem mem_smul_iff (g : ↥suzM) (x : Vtx) (a : Equiv.Perm (Fin 1782)) :
    a ∈ ((g • x : Vtx) : Subgroup (Equiv.Perm (Fin 1782))) ↔
      (g : Equiv.Perm (Fin 1782))⁻¹ * a * g ∈ (x : Subgroup (Equiv.Perm (Fin 1782))) := by
  rw [coe_smul, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

@[expose] def v0 : Vtx := ⟨base, 1, one_mem _, by rw [map_one]; exact (Subgroup.map_id base).symm⟩

theorem exists_smul (x : Vtx) : ∃ g : ↥suzM, g • v0 = x := by
  obtain ⟨g, hg, hx⟩ := x.2
  exact ⟨⟨g, hg⟩, Subtype.ext hx.symm⟩

theorem coe_smul_v0 (g : ↥suzM) :
    ((g • v0 : Vtx) : Subgroup (Equiv.Perm (Fin 1782))) =
      zpowers ((g : Equiv.Perm (Fin 1782)) * Model.rho1 * (g : Equiv.Perm (Fin 1782))⁻¹) := by
  rw [coe_smul]
  show (zpowers Model.rho1).map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  rfl

theorem smul_v0_eq_iff (g : ↥suzM) :
    g • v0 = v0 ↔ (g : Equiv.Perm (Fin 1782)) ∈ normalizer (base : Set (Equiv.Perm (Fin 1782))) := by
  constructor
  · intro h
    have h1 : base.map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom = base :=
      congrArg Subtype.val h
    refine mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩
    · have : (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom a ∈
          (base.map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom) := ⟨a, ha, rfl⟩
      rw [h1] at this
      exact this
    · have h2 : (g : Equiv.Perm (Fin 1782)) * a * (g : Equiv.Perm (Fin 1782))⁻¹ ∈
          base.map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom := by
        rw [h1]; exact ha
      obtain ⟨b, hb, hba⟩ := h2
      have : b = a := by
        have := hba
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        exact mul_right_cancel (mul_left_cancel this)
      rw [← this]
      exact hb
  · intro h
    apply Subtype.ext
    show base.map (MulAut.conj (g : Equiv.Perm (Fin 1782))).toMonoidHom = base
    ext a
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    have := (mem_normalizer_iff'' (H := base) (g := (g : Equiv.Perm (Fin 1782)))).mp h a
    rw [this]

theorem orderOf_conj' {G : Type*} [Group G] (g a : G) : orderOf (g * a * g⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  simpa using this

theorem orderOf_mul_comm' {G : Type*} [Group G] (a b : G) : orderOf (b * a) = orderOf (a * b) := by
  have : b * a = b * (a * b) * b⁻¹ := by group
  rw [this, orderOf_conj']

@[expose] def a4Graph : SimpleGraph Vtx where
  Adj x y := x ≠ y ∧ ∃ a ∈ (x : Subgroup (Equiv.Perm (Fin 1782))),
    ∃ b ∈ (y : Subgroup (Equiv.Perm (Fin 1782))), orderOf (a * b) = 2
  symm := ⟨fun _ _ ⟨hne, a, ha, b, hb, h⟩ => ⟨hne.symm, b, hb, a, ha, by rwa [orderOf_mul_comm']⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem a4Graph_adj {x y : Vtx} :
    a4Graph.Adj x y ↔ x ≠ y ∧ ∃ a ∈ (x : Subgroup (Equiv.Perm (Fin 1782))),
      ∃ b ∈ (y : Subgroup (Equiv.Perm (Fin 1782))), orderOf (a * b) = 2 :=
  Iff.rfl

theorem a4Graph_adj_smul (g : ↥suzM) {x y : Vtx} (h : a4Graph.Adj x y) :
    a4Graph.Adj (g • x) (g • y) := by
  obtain ⟨hne, a, ha, b, hb, hab⟩ := h
  refine ⟨fun e => hne (by simpa using congrArg (g⁻¹ • ·) e), ?_⟩
  refine ⟨(g : Equiv.Perm (Fin 1782)) * a * (g : Equiv.Perm (Fin 1782))⁻¹, ?_,
    (g : Equiv.Perm (Fin 1782)) * b * (g : Equiv.Perm (Fin 1782))⁻¹, ?_, ?_⟩
  · rw [mem_smul_iff]; simpa [mul_assoc] using ha
  · rw [mem_smul_iff]; simpa [mul_assoc] using hb
  · have : (g : Equiv.Perm (Fin 1782)) * a * (g : Equiv.Perm (Fin 1782))⁻¹ *
        ((g : Equiv.Perm (Fin 1782)) * b * (g : Equiv.Perm (Fin 1782))⁻¹) =
        (g : Equiv.Perm (Fin 1782)) * (a * b) * (g : Equiv.Perm (Fin 1782))⁻¹ := by group
    rw [this, orderOf_conj', hab]

theorem a4Graph_adj_smul_iff (g : ↥suzM) {x y : Vtx} :
    a4Graph.Adj (g • x) (g • y) ↔ a4Graph.Adj x y := by
  refine ⟨fun h => ?_, a4Graph_adj_smul g⟩
  have := a4Graph_adj_smul g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at this

@[expose] def conjIso (g : ↥suzM) : a4Graph ≃g a4Graph where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := a4Graph_adj_smul_iff g

theorem conjIso_apply (g : ↥suzM) (x : Vtx) : conjIso g x = g • x := rfl

@[expose] def fixSet (x : Vtx) : Set (Fin 1782) :=
  {p | ∀ a ∈ (x : Subgroup (Equiv.Perm (Fin 1782))), a p = p}

theorem fixSet_smul (g : ↥suzM) (x : Vtx) :
    fixSet (g • x) = (g : Equiv.Perm (Fin 1782)) '' fixSet x := by
  ext p
  constructor
  · intro hp
    refine ⟨((g : Equiv.Perm (Fin 1782))⁻¹ : Equiv.Perm (Fin 1782)) p, fun a ha => ?_, by simp⟩
    have h1 := hp ((g : Equiv.Perm (Fin 1782)) * a * (g : Equiv.Perm (Fin 1782))⁻¹)
      ((mem_smul_iff g x _).2 (by simpa [mul_assoc] using ha))
    have h2 := congrArg (((g : Equiv.Perm (Fin 1782))⁻¹ : Equiv.Perm (Fin 1782)) : Fin 1782 → Fin 1782) h1
    simpa [Equiv.Perm.mul_apply] using h2
  · rintro ⟨q, hq, rfl⟩ a ha
    have h1 := hq _ ((mem_smul_iff g x a).1 ha)
    have h2 := congrArg (g : Equiv.Perm (Fin 1782)) h1
    simpa [Equiv.Perm.mul_apply] using h2

theorem fixSet_zpowers {x : Vtx} {q : Equiv.Perm (Fin 1782)}
    (hx : (x : Subgroup (Equiv.Perm (Fin 1782))) = zpowers q) :
    fixSet x = {p | q p = p} := by
  ext p
  constructor
  · intro hp
    exact hp q (hx ▸ mem_zpowers q)
  · intro hp a ha
    rw [hx] at ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    have : (q ^ k) p = p := by
      have h1 : q ∈ MulAction.stabilizer (Equiv.Perm (Fin 1782)) p := hp
      exact (zpow_mem h1 k : q ^ k ∈ MulAction.stabilizer (Equiv.Perm (Fin 1782)) p)
    exact this

theorem adj_smul_v0_iff (h3 : Model.rho1 ^ 3 = 1) (g h : ↥suzM) :
    a4Graph.Adj (g • v0) (h • v0) ↔
      g • v0 ≠ h • v0 ∧ ∃ i ∈ ({1, 2} : Finset ℕ), ∃ j ∈ ({1, 2} : Finset ℕ),
        orderOf (((g : Equiv.Perm (Fin 1782)) * Model.rho1 * (g : Equiv.Perm (Fin 1782))⁻¹) ^ i *
          ((h : Equiv.Perm (Fin 1782)) * Model.rho1 * (h : Equiv.Perm (Fin 1782))⁻¹) ^ j) = 2 := by
  set q := (g : Equiv.Perm (Fin 1782)) * Model.rho1 * (g : Equiv.Perm (Fin 1782))⁻¹
  set r := (h : Equiv.Perm (Fin 1782)) * Model.rho1 * (h : Equiv.Perm (Fin 1782))⁻¹
  have hq3 : q ^ 3 = 1 := by rw [conj_pow, h3]; group
  have hr3 : r ^ 3 = 1 := by rw [conj_pow, h3]; group
  have hpow : ∀ {s : Equiv.Perm (Fin 1782)}, s ^ 3 = 1 → ∀ a ∈ zpowers s,
      ∃ i < 3, a = s ^ i := by
    intro s hs a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    refine ⟨(k % 3).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    rw [show ((s : Equiv.Perm (Fin 1782)) ^ (3 : ℤ)) = 1 by exact_mod_cast hs, one_zpow, mul_one]
  rw [a4Graph_adj, coe_smul_v0, coe_smul_v0]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨i, hi, rfl⟩ := hpow hq3 a ha
    obtain ⟨j, hj, rfl⟩ := hpow hr3 b hb
    have hne : i ≠ 0 ∧ j ≠ 0 := by
      constructor
      · rintro rfl
        rw [pow_zero, one_mul] at hab
        have := orderOf_dvd_of_pow_eq_one (show (r ^ j) ^ 3 = 1 by
          rw [← pow_mul, mul_comm, pow_mul, hr3, one_pow])
        rw [hab] at this
        omega
      · rintro rfl
        rw [pow_zero, mul_one] at hab
        have := orderOf_dvd_of_pow_eq_one (show (q ^ i) ^ 3 = 1 by
          rw [← pow_mul, mul_comm, pow_mul, hq3, one_pow])
        rw [hab] at this
        omega
    refine ⟨i, by simp; omega, j, by simp; omega, hab⟩
  · rintro ⟨i, -, j, -, hij⟩
    exact ⟨q ^ i, pow_mem (mem_zpowers q) i, r ^ j, pow_mem (mem_zpowers r) j, hij⟩

end CFSG.Sporadic.SuzRecog.Q3A
