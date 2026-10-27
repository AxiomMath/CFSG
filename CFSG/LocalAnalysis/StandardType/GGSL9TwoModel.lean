module

public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

open scoped Pointwise

section SL9Core

abbrev GGSL9V : Type := Fin 3 → GaloisField 2 3

@[expose] noncomputable def ggSL9Fun (i j : Fin 3) (n : ℕ) (μ : GaloisField 2 3) (v : GGSL9V) :
    GGSL9V :=
  v + Pi.single j (μ * v i ^ 2 ^ n)

theorem ggSL9Fun_apply_self {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (μ : GaloisField 2 3)
    (v : GGSL9V) : ggSL9Fun i j n μ v i = v i := by
  simp [ggSL9Fun, Pi.single_eq_of_ne hij]

theorem ggSL9Fun_invol {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (μ : GaloisField 2 3)
    (v : GGSL9V) : ggSL9Fun i j n μ (ggSL9Fun i j n μ v) = v := by
  unfold ggSL9Fun
  rw [show ((v + Pi.single j (μ * v i ^ 2 ^ n) : GGSL9V) i) = v i by
    simpa [ggSL9Fun] using ggSL9Fun_apply_self hij n μ v]
  rw [add_assoc, ← Pi.single_add, CharTwo.add_self_eq_zero]
  simp

theorem ggSL9Fun_add (i j : Fin 3) (n : ℕ) (μ : GaloisField 2 3) (v w : GGSL9V) :
    ggSL9Fun i j n μ (v + w) = ggSL9Fun i j n μ v + ggSL9Fun i j n μ w := by
  ext l
  by_cases hl : l = j
  · subst hl
    simp only [ggSL9Fun, Pi.add_apply, Pi.single_eq_same]
    rw [add_pow_char_pow, mul_add]
    abel
  · simp only [ggSL9Fun, Pi.add_apply, Pi.single_eq_of_ne hl]
    abel

@[expose] noncomputable def ggSL9Root (i j : Fin 3) (hij : i ≠ j) (n : ℕ) (μ : GaloisField 2 3) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  { AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk' (ggSL9Fun i j n μ) (ggSL9Fun_add i j n μ)) with
    invFun := ggSL9Fun i j n μ
    left_inv := ggSL9Fun_invol hij n μ
    right_inv := ggSL9Fun_invol hij n μ }

@[expose] def ggSL9RootSet (i j : Fin 3) (n : ℕ) : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  {g | ∃ (h : i ≠ j) (μ : GaloisField 2 3), g = ggSL9Root i j h n μ}

@[expose] noncomputable def ggSL9J (i j : Fin 3) (e : ZMod 3) :
    Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  Subgroup.closure (ggSL9RootSet i j e.val ∪ ggSL9RootSet j i (-e).val)

@[expose] def GGSL9Refl : Set (Fin 3 × Fin 3 × ZMod 3) := {t | t.1 < t.2.1}

theorem ggSL9Root_apply {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (μ : GaloisField 2 3) (v : GGSL9V) :
    ggSL9Root i j hij n μ v = ggSL9Fun i j n μ v :=
  rfl

theorem ggSL9Fun_comp {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (μ μ' : GaloisField 2 3)
    (v : GGSL9V) : ggSL9Fun i j n μ (ggSL9Fun i j n μ' v) = ggSL9Fun i j n (μ + μ') v := by
  have h := ggSL9Fun_apply_self hij n μ' v
  unfold ggSL9Fun at h ⊢
  rw [h, add_assoc, ← Pi.single_add, ← add_mul, add_comm μ']

@[expose] noncomputable def ggSL9RootHom (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    Multiplicative (GaloisField 2 3) →* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  MonoidHom.mk' (fun μ => ggSL9Root i j hij n (toAdd μ)) fun μ μ' => LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, ggSL9Root_apply, ggSL9Root_apply, ggSL9Root_apply,
      ggSL9Fun_comp hij, toAdd_mul]

theorem ggSL9RootHom_apply {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (μ : GaloisField 2 3) :
    ggSL9RootHom i j hij n (ofAdd μ) = ggSL9Root i j hij n μ :=
  rfl

end SL9Core

section Torus

@[expose] noncomputable def ggSL9DiagFun (t : Fin 3 → (GaloisField 2 3)ˣ) (v : GGSL9V) : GGSL9V :=
  fun i => (t i : GaloisField 2 3) * v i

theorem ggSL9DiagFun_add (t : Fin 3 → (GaloisField 2 3)ˣ) (v w : GGSL9V) :
    ggSL9DiagFun t (v + w) = ggSL9DiagFun t v + ggSL9DiagFun t w := by
  funext i
  simp only [ggSL9DiagFun, Pi.add_apply, mul_add]

theorem ggSL9DiagFun_mul (s t : Fin 3 → (GaloisField 2 3)ˣ) (v : GGSL9V) :
    ggSL9DiagFun s (ggSL9DiagFun t v) = ggSL9DiagFun (s * t) v := by
  funext i
  simp only [ggSL9DiagFun, Pi.mul_apply, Units.val_mul, mul_assoc]

theorem ggSL9DiagFun_one (v : GGSL9V) : ggSL9DiagFun 1 v = v := by
  funext i
  simp only [ggSL9DiagFun, Pi.one_apply, Units.val_one, one_mul]

theorem ggSL9DiagFun_inv_mul (t : Fin 3 → (GaloisField 2 3)ˣ) (v : GGSL9V) :
    ggSL9DiagFun t⁻¹ (ggSL9DiagFun t v) = v := by
  rw [ggSL9DiagFun_mul, inv_mul_cancel, ggSL9DiagFun_one]

theorem ggSL9DiagFun_mul_inv (t : Fin 3 → (GaloisField 2 3)ˣ) (v : GGSL9V) :
    ggSL9DiagFun t (ggSL9DiagFun t⁻¹ v) = v := by
  rw [ggSL9DiagFun_mul, mul_inv_cancel, ggSL9DiagFun_one]

@[expose] noncomputable def ggSL9Diag (t : Fin 3 → (GaloisField 2 3)ˣ) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  { AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' (ggSL9DiagFun t) (ggSL9DiagFun_add t)) with
    invFun := ggSL9DiagFun t⁻¹
    left_inv := ggSL9DiagFun_inv_mul t
    right_inv := ggSL9DiagFun_mul_inv t }

theorem ggSL9Diag_apply (t : Fin 3 → (GaloisField 2 3)ˣ) (v : GGSL9V) (i : Fin 3) :
    ggSL9Diag t v i = (t i : GaloisField 2 3) * v i :=
  rfl

@[expose] noncomputable def ggSL9DiagHom :
    (Fin 3 → (GaloisField 2 3)ˣ) →* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  MonoidHom.mk' ggSL9Diag fun s t => LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply]
    exact (ggSL9DiagFun_mul s t v).symm

theorem ggSL9DiagHom_apply (t : Fin 3 → (GaloisField 2 3)ˣ) : ggSL9DiagHom t = ggSL9Diag t :=
  rfl

@[expose] noncomputable def ggSL9Torus : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  ggSL9DiagHom.range

theorem card_units_ggSL9 : Nat.card (GaloisField 2 3)ˣ = 7 := by
  rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)] <;> norm_num

theorem ggSL9_units_pow_seven (u : (GaloisField 2 3)ˣ) : u ^ 7 = 1 := by
  rw [← card_units_ggSL9]
  exact pow_card_eq_one'

@[expose] noncomputable def ggSL9Zeta : (GaloisField 2 3)ˣ :=
  Classical.choose (IsCyclic.exists_generator (α := (GaloisField 2 3)ˣ))

theorem mem_zpowers_ggSL9Zeta (u : (GaloisField 2 3)ˣ) : u ∈ Subgroup.zpowers ggSL9Zeta :=
  Classical.choose_spec (IsCyclic.exists_generator (α := (GaloisField 2 3)ˣ)) u

theorem ggSL9_pow_val_add {M : Type*} [Monoid M] {x : M} (hx : x ^ 7 = 1)
    (a b : ZMod 7) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hx]

@[expose] noncomputable def ggSL9ZetaPow :
    Multiplicative (Fin 3 → ZMod 7) →* (Fin 3 → (GaloisField 2 3)ˣ) :=
  MonoidHom.mk' (fun f i => ggSL9Zeta ^ (toAdd f i).val) fun f g => funext fun i =>
    ggSL9_pow_val_add (ggSL9_units_pow_seven ggSL9Zeta) (toAdd f i) (toAdd g i)

theorem ggSL9ZetaPow_apply (f : Fin 3 → ZMod 7) (i : Fin 3) :
    ggSL9ZetaPow (ofAdd f) i = ggSL9Zeta ^ (f i).val :=
  rfl

@[expose] noncomputable def ggSL9TorusCoord :
    Multiplicative (Fin 3 → ZMod 7) →* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  ggSL9DiagHom.comp ggSL9ZetaPow

theorem ggSL9TorusCoord_apply (f : Fin 3 → ZMod 7) (v : GGSL9V) (i : Fin 3) :
    ggSL9TorusCoord (ofAdd f) v i = ((ggSL9Zeta ^ (f i).val : (GaloisField 2 3)ˣ) :
      GaloisField 2 3) * v i :=
  rfl

theorem orderOf_ggSL9Zeta : orderOf ggSL9Zeta = 7 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers mem_zpowers_ggSL9Zeta, card_units_ggSL9]

theorem ggSL9TorusCoord_injective : Function.Injective ggSL9TorusCoord := by
  rw [injective_iff_map_eq_one ggSL9TorusCoord]
  intro f hf
  have hg : toAdd f = 0 := by
    funext i
    have h1 : ((ggSL9Zeta ^ (toAdd f i).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) = 1 := by
      have h := congrArg (fun (g : GGSL9V ≃ₗ[ZMod 2] GGSL9V) =>
        g (Pi.single i (1 : GaloisField 2 3)) i) hf
      rw [show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm, ggSL9TorusCoord_apply] at h
      simpa using h
    have h2 : ggSL9Zeta ^ (toAdd f i).val = 1 := Units.val_eq_one.mp h1
    have h3 : (7 : ℕ) ∣ (toAdd f i).val := by
      have h := orderOf_dvd_of_pow_eq_one h2
      rwa [orderOf_ggSL9Zeta] at h
    have h4 : (toAdd f i).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt (toAdd f i))
    exact (ZMod.val_eq_zero (toAdd f i)).mp h4
  rw [show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm, hg]
  rfl

private theorem ggSL9ZetaPow_surjective : Function.Surjective ggSL9ZetaPow := by
  intro u
  choose m hm using fun i => (Submonoid.mem_powers_iff (u i) ggSL9Zeta).mp
    ((mem_powers_iff_mem_zpowers (x := ggSL9Zeta) (y := u i)).mpr (mem_zpowers_ggSL9Zeta (u i)))
  refine ⟨ofAdd (fun i => (m i : ZMod 7)), ?_⟩
  funext i
  rw [ggSL9ZetaPow_apply, ZMod.val_natCast, ← orderOf_ggSL9Zeta, pow_mod_orderOf]
  exact hm i

theorem range_ggSL9TorusCoord : ggSL9TorusCoord.range = ggSL9Torus := by
  have htop : ggSL9ZetaPow.range = ⊤ := MonoidHom.range_eq_top.mpr ggSL9ZetaPow_surjective
  unfold ggSL9Torus
  rw [ggSL9TorusCoord, MonoidHom.range_comp, htop, Subgroup.map_top]

theorem card_ggSL9Torus : Nat.card ggSL9Torus = 7 ^ 3 := by
  rw [← range_ggSL9TorusCoord,
    ← Nat.card_congr (MonoidHom.ofInjective ggSL9TorusCoord_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

private theorem mem_ggSL9Torus_iff (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V) :
    x ∈ ggSL9Torus ↔ ∃ t : Fin 3 → (GaloisField 2 3)ˣ, ggSL9DiagHom t = x := by
  unfold ggSL9Torus
  exact MonoidHom.mem_range

theorem isElemAbelian_ggSL9Torus : IsElemAbelian 7 ggSL9Torus := by
  constructor
  · refine isMulCommutative_iff.mpr ?_
    intro x y
    obtain ⟨s, hs⟩ := (mem_ggSL9Torus_iff (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V)).mp x.2
    obtain ⟨t, ht⟩ := (mem_ggSL9Torus_iff (y : GGSL9V ≃ₗ[ZMod 2] GGSL9V)).mp y.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hs, ← ht, ← map_mul, ← map_mul, mul_comm s t]
  · intro x hx
    obtain ⟨t, ht⟩ := (mem_ggSL9Torus_iff x).mp hx
    rw [← ht, ← map_pow]
    have ht7 : t ^ 7 = 1 := funext fun i => ggSL9_units_pow_seven (t i)
    rw [ht7, map_one]

private theorem ggSL9Diag_inv (t : Fin 3 → (GaloisField 2 3)ˣ) :
    (ggSL9Diag t)⁻¹ = ggSL9Diag t⁻¹ :=
  LinearEquiv.ext fun _ => rfl

private theorem ggSL9_unit_mul_inv_mul (u : (GaloisField 2 3)ˣ) (x : GaloisField 2 3) :
    (u : GaloisField 2 3) * (((u⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) * x) = x := by
  rw [← mul_assoc, Units.mul_inv, one_mul]

theorem ggSL9Diag_conj_root (t : Fin 3 → (GaloisField 2 3)ˣ) {i j : Fin 3} (hij : i ≠ j) (n : ℕ)
    (μ : GaloisField 2 3) :
    ggSL9Diag t * ggSL9Root i j hij n μ * (ggSL9Diag t)⁻¹ =
      ggSL9Root i j hij n ((t j : GaloisField 2 3) *
        (((t i)⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ 2 ^ n * μ) := by
  apply LinearEquiv.ext
  intro v
  funext l
  simp only [LinearEquiv.mul_apply, ggSL9Root_apply, ggSL9Fun, ggSL9Diag_apply, ggSL9Diag_inv,
    ggSL9DiagFun, Pi.add_apply, Pi.inv_apply]
  by_cases hl : l = j
  · subst hl
    rw [Pi.single_eq_same, Pi.single_eq_same, mul_add, ggSL9_unit_mul_inv_mul, mul_pow]
    ring
  · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, add_zero, add_zero]
    rw [ggSL9_unit_mul_inv_mul]

theorem ggSL9RootHom_injective {i j : Fin 3} (hij : i ≠ j) (n : ℕ) :
    Function.Injective (ggSL9RootHom i j hij n) := by
  intro μ ν h
  rw [← ofAdd_toAdd μ, ← ofAdd_toAdd ν] at h
  have h' : toAdd μ = toAdd ν := by
    have h1 := congrArg (fun (g : GGSL9V ≃ₗ[ZMod 2] GGSL9V) =>
      g (Pi.single i (1 : GaloisField 2 3)) j) h
    rw [ggSL9RootHom_apply, ggSL9RootHom_apply, ggSL9Root_apply, ggSL9Root_apply] at h1
    simpa [ggSL9Fun, Pi.single_eq_of_ne (Ne.symm hij)] using h1
  exact toAdd.injective h'

theorem card_range_ggSL9RootHom {i j : Fin 3} (hij : i ≠ j) (n : ℕ) :
    Nat.card (ggSL9RootHom i j hij n).range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (ggSL9RootHom_injective hij n)).toEquiv]
  show Nat.card (GaloisField 2 3) = 8
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem ggSL9Torus_le_normalizer_rootHom {i j : Fin 3} (hij : i ≠ j) (n : ℕ) :
    ggSL9Torus ≤ Subgroup.normalizer ((ggSL9RootHom i j hij n).range :
      Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_ggSL9Torus_iff x).mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨μ, rfl⟩ := MonoidHom.mem_range.mp hh
    refine MonoidHom.mem_range.mpr
      ⟨ofAdd ((t j : GaloisField 2 3) *
        (((t i)⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ 2 ^ n * toAdd μ), ?_⟩
    have hμ : ggSL9RootHom i j hij n μ = ggSL9Root i j hij n (toAdd μ) := by
      rw [show μ = ofAdd (toAdd μ) from (ofAdd_toAdd μ).symm, ggSL9RootHom_apply, toAdd_ofAdd]
    rw [ggSL9DiagHom_apply, hμ, ggSL9Diag_conj_root t hij n (toAdd μ), ggSL9RootHom_apply]
  · intro hh
    obtain ⟨ν, hν⟩ := MonoidHom.mem_range.mp hh
    have hν'' : ggSL9Root i j hij n (toAdd ν) = ggSL9Diag t * h * (ggSL9Diag t)⁻¹ := by
      rw [← ggSL9RootHom_apply hij n (toAdd ν), ofAdd_toAdd, hν, ggSL9DiagHom_apply]
    refine MonoidHom.mem_range.mpr
      ⟨ofAdd ((t⁻¹ j : GaloisField 2 3) *
        (((t⁻¹ i)⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ 2 ^ n * toAdd ν), ?_⟩
    have hconj : ggSL9Diag t⁻¹ * ggSL9Root i j hij n (toAdd ν) * (ggSL9Diag t⁻¹)⁻¹ = h := by
      rw [hν'', ← ggSL9Diag_inv t]
      group
    rw [ggSL9Diag_conj_root t⁻¹ hij n (toAdd ν), ← ggSL9RootHom_apply] at hconj
    exact hconj

end Torus

section Shift

theorem ggSL9_pow_eight (x : GaloisField 2 3) : x ^ 8 = x := by
  letI := Fintype.ofFinite (GaloisField 2 3)
  have h : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)] <;> norm_num
  rw [← h]
  exact FiniteField.pow_card x

@[expose] noncomputable def ggSL9ShiftFun (v : GGSL9V) : GGSL9V := ![v 2 ^ 2, v 0, v 1]

@[expose] noncomputable def ggSL9ShiftInvFun (v : GGSL9V) : GGSL9V := ![v 1, v 2, v 0 ^ 4]

theorem ggSL9ShiftFun_add (v w : GGSL9V) :
    ggSL9ShiftFun (v + w) = ggSL9ShiftFun v + ggSL9ShiftFun w := by
  funext i
  fin_cases i <;> simp [ggSL9ShiftFun, add_pow_char]

theorem ggSL9ShiftInvFun_shiftFun (v : GGSL9V) : ggSL9ShiftInvFun (ggSL9ShiftFun v) = v := by
  funext i
  fin_cases i <;> simp [ggSL9ShiftFun, ggSL9ShiftInvFun, ← pow_mul, ggSL9_pow_eight]

theorem ggSL9ShiftFun_shiftInvFun (v : GGSL9V) : ggSL9ShiftFun (ggSL9ShiftInvFun v) = v := by
  funext i
  fin_cases i <;> simp [ggSL9ShiftFun, ggSL9ShiftInvFun, ← pow_mul, ggSL9_pow_eight]

@[expose] noncomputable def ggSL9Shift : GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  { AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' ggSL9ShiftFun ggSL9ShiftFun_add) with
    invFun := ggSL9ShiftInvFun
    left_inv := ggSL9ShiftInvFun_shiftFun
    right_inv := ggSL9ShiftFun_shiftInvFun }

theorem ggSL9Shift_apply (v : GGSL9V) : ggSL9Shift v = ![v 2 ^ 2, v 0, v 1] :=
  rfl

@[expose] def ggSL9ShiftCoord : MulAut (Multiplicative (Fin 3 → ZMod 7)) where
  toFun f := ofAdd ![2 * toAdd f 2, toAdd f 0, toAdd f 1]
  invFun f := ofAdd ![toAdd f 1, toAdd f 2, 4 * toAdd f 0]
  left_inv f := by
    apply toAdd.injective
    funext i
    fin_cases i <;> simp
    rw [show (4 : ZMod 7) * (2 * toAdd f 2) = (8 : ZMod 7) * toAdd f 2 by ring,
      show (8 : ZMod 7) = 1 by decide, one_mul]
  right_inv f := by
    apply toAdd.injective
    funext i
    fin_cases i <;> simp
    rw [show (2 : ZMod 7) * (4 * toAdd f 0) = (8 : ZMod 7) * toAdd f 0 by ring,
      show (8 : ZMod 7) = 1 by decide, one_mul]
  map_mul' f g := by
    apply toAdd.injective
    funext i
    fin_cases i <;> simp
    ring

theorem ggSL9ShiftCoord_apply (f : Fin 3 → ZMod 7) :
    ggSL9ShiftCoord (ofAdd f) = ofAdd ![2 * f 2, f 0, f 1] :=
  rfl

private theorem ggSL9_shiftCoord_pow_seven (f : Multiplicative (Fin 3 → ZMod 7)) : f ^ 7 = 1 := by
  apply toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

private theorem ggSL9ShiftCoord_pow_three_ofAdd (g : Fin 3 → ZMod 7) :
    (ggSL9ShiftCoord ^ 3) (ofAdd g) = (ofAdd g) ^ 2 := by
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, ggSL9ShiftCoord_apply, toAdd_ofAdd]
  apply toAdd.injective
  funext i
  fin_cases i <;> simp
  · ring
  · ring
  · ring

private theorem ggSL9ShiftCoord_pow_three (f : Multiplicative (Fin 3 → ZMod 7)) :
    (ggSL9ShiftCoord ^ 3) f = f ^ 2 := by
  rw [show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm]
  exact ggSL9ShiftCoord_pow_three_ofAdd (toAdd f)

theorem orderOf_ggSL9ShiftCoord : orderOf ggSL9ShiftCoord = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hnot : ¬ ggSL9ShiftCoord ^ 3 ^ 1 = 1 := by
    rw [show (3 : ℕ) ^ 1 = 3 by norm_num]
    intro h
    have h1 := congrArg (fun (s : MulAut (Multiplicative (Fin 3 → ZMod 7))) =>
      s (ofAdd ![(1 : ZMod 7), 0, 0])) h
    rw [ggSL9ShiftCoord_pow_three, MulAut.one_apply] at h1
    have h3 : ((ofAdd ![(1 : ZMod 7), 0, 0] : Multiplicative (Fin 3 → ZMod 7)) ^ 2)
        = ofAdd ![2, 0, 0] := by
      rw [← ofAdd_nsmul]
      congr 1
      funext i
      fin_cases i <;> decide
    rw [h3] at h1
    have h2 := congrArg (fun (x : Multiplicative (Fin 3 → ZMod 7)) => toAdd x 0) h1
    simp only [toAdd_ofAdd, Matrix.cons_val_zero] at h2
    exact (by decide : (2 : ZMod 7) ≠ 1) h2
  have hfin : ggSL9ShiftCoord ^ 3 ^ (1 + 1) = 1 := by
    rw [show (3 : ℕ) ^ (1 + 1) = 9 by norm_num]
    apply MulEquiv.ext
    intro f
    rw [MulAut.one_apply]
    have h9 : ggSL9ShiftCoord ^ 9 = (ggSL9ShiftCoord ^ 3) ^ 3 := by
      rw [← pow_mul]
    have hiter : ∀ n (g : Multiplicative (Fin 3 → ZMod 7)),
        ((ggSL9ShiftCoord ^ 3) ^ n) g = g ^ (2 ^ n) := by
      intro n
      induction n with
      | zero => intro g; rw [pow_zero, MulAut.one_apply, pow_zero, pow_one]
      | succ n ih =>
          intro g
          rw [pow_succ, MulAut.mul_apply, ih, ggSL9ShiftCoord_pow_three, ← pow_mul]
          congr 1
          ring
    rw [h9, hiter 3, show (2 : ℕ) ^ 3 = 8 by norm_num,
      show (8 : ℕ) = 7 + 1 by norm_num, pow_add, ggSL9_shiftCoord_pow_seven, pow_one, one_mul]
  rw [orderOf_eq_prime_pow hnot hfin]
  norm_num

private theorem ggSL9Shift_inv_apply (v : GGSL9V) : ggSL9Shift⁻¹ v = ggSL9ShiftInvFun v := rfl

private theorem ggSL9Zeta_pow_two_val (x : ZMod 7) :
    ((ggSL9Zeta ^ x.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ 2 =
      ((ggSL9Zeta ^ (2 * x).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) := by
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  rw [show 2 * x = x + x by ring,
    ggSL9_pow_val_add (ggSL9_units_pow_seven ggSL9Zeta) x x, pow_two]

private theorem ggSL9TorusCoord_apply' (f : Multiplicative (Fin 3 → ZMod 7)) (v : GGSL9V)
    (i : Fin 3) : ggSL9TorusCoord f v i = ((ggSL9Zeta ^ (toAdd f i).val :
      (GaloisField 2 3)ˣ) : GaloisField 2 3) * v i := by
  conv_lhs => rw [show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm]
  rw [ggSL9TorusCoord_apply]

private theorem ggSL9ShiftCoord_apply' (f : Multiplicative (Fin 3 → ZMod 7)) :
    ggSL9ShiftCoord f = ofAdd ![2 * toAdd f 2, toAdd f 0, toAdd f 1] := by
  conv_lhs => rw [show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm]
  rw [ggSL9ShiftCoord_apply]

theorem ggSL9Shift_conj_torusCoord (f : Multiplicative (Fin 3 → ZMod 7)) :
    ggSL9Shift * ggSL9TorusCoord f * ggSL9Shift⁻¹ = ggSL9TorusCoord (ggSL9ShiftCoord f) := by
  apply LinearEquiv.ext
  intro v
  funext l
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggSL9Shift_apply, ggSL9Shift_inv_apply,
    ggSL9ShiftCoord_apply']
  fin_cases l <;> simp [ggSL9TorusCoord_apply', ggSL9ShiftInvFun]
  · rw [mul_pow]
    have hv : (v 0 ^ 4) ^ 2 = v 0 := by
      rw [← pow_mul, show (4 : ℕ) * 2 = 8 by norm_num, ggSL9_pow_eight]
    rw [hv, ← Units.val_pow_eq_pow_val, ggSL9Zeta_pow_two_val, Units.val_pow_eq_pow_val]

end Shift

section Sylow

theorem finrank_ggSL9V : Module.finrank (ZMod 2) GGSL9V = 9 := by
  rw [Module.finrank_pi_fintype, GaloisField.finrank 2 (by norm_num : (3 : ℕ) ≠ 0)]
  simp

@[expose] noncomputable def ggSL9GLEquiv :
    GL (Fin 9) (ZMod 2) ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  (Matrix.GeneralLinearGroup.toLin'
      (Module.finBasisOfFinrankEq (ZMod 2) GGSL9V finrank_ggSL9V)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) GGSL9V)

theorem card_ggSL9Group :
    Nat.card (GGSL9V ≃ₗ[ZMod 2] GGSL9V) = ∏ i : Fin 9, (2 ^ 9 - 2 ^ (i : ℕ)) := by
  rw [← Nat.card_congr ggSL9GLEquiv.toEquiv, Matrix.card_GL_field]
  congr 1

theorem not_seven_pow_four_dvd_card_ggSL9 :
    ¬ 7 ^ 4 ∣ Nat.card (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
  rw [card_ggSL9Group]
  decide

theorem exists_conj_eq_ggSL9Torus {E : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    (hE : IsElemAbelian 7 E) (h3 : 7 ^ 3 ≤ Nat.card E) :
    ∃ g : GGSL9V ≃ₗ[ZMod 2] GGSL9V, E = ggSL9Torus.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
    Finite.of_equiv (GL (Fin 9) (ZMod 2)) ggSL9GLEquiv.toEquiv
  have hEp : IsPGroup 7 ↥E := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx : x ^ 7 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V) x.2
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨n, hEn⟩ := (IsPGroup.iff_card (p := 7) (G := ↥E)).mp hEp
  have hn_le : n ≤ 3 := by
    by_contra h
    push Not at h
    exact not_seven_pow_four_dvd_card_ggSL9
      (dvd_trans (Nat.pow_dvd_pow 7 (Nat.succ_le_of_lt h))
        (by rw [← hEn]; exact Subgroup.card_subgroup_dvd_card E))
  have hcardE : Nat.card E = 7 ^ 3 := by
    refine le_antisymm ?_ h3
    rw [hEn]
    exact Nat.pow_le_pow_right (by norm_num) hn_le
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow hEp
  let Psub : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := P
  have hPp : IsPGroup 7 ↥Psub := Sylow.isPGroup' P
  obtain ⟨m, hPm⟩ := (IsPGroup.iff_card (p := 7) (G := ↥Psub)).mp hPp
  have hm_le : m ≤ 3 := by
    by_contra h
    push Not at h
    exact not_seven_pow_four_dvd_card_ggSL9
      (dvd_trans (Nat.pow_dvd_pow 7 (Nat.succ_le_of_lt h))
        (by rw [← hPm]; exact Subgroup.card_subgroup_dvd_card Psub))
  have hPcard : Nat.card Psub ≤ 7 ^ 3 := by
    rw [hPm]
    exact Nat.pow_le_pow_right (by norm_num) hm_le
  have hPeq : E = ↑P := Subgroup.eq_of_le_of_card_ge hEP (by rw [hcardE]; exact hPcard)
  have hTp : IsPGroup 7 ↥ggSL9Torus := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx : x ^ 7 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact isElemAbelian_ggSL9Torus.2 (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V) x.2
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨Q, hTQ⟩ := IsPGroup.exists_le_sylow hTp
  let Qsub : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := Q
  have hQp : IsPGroup 7 ↥Qsub := Sylow.isPGroup' Q
  obtain ⟨k, hQk⟩ := (IsPGroup.iff_card (p := 7) (G := ↥Qsub)).mp hQp
  have hk_le : k ≤ 3 := by
    by_contra h
    push Not at h
    exact not_seven_pow_four_dvd_card_ggSL9
      (dvd_trans (Nat.pow_dvd_pow 7 (Nat.succ_le_of_lt h))
        (by rw [← hQk]; exact Subgroup.card_subgroup_dvd_card Qsub))
  have hQcard : Nat.card Qsub ≤ 7 ^ 3 := by
    rw [hQk]
    exact Nat.pow_le_pow_right (by norm_num) hk_le
  have hQeq : ggSL9Torus = ↑Q :=
    Subgroup.eq_of_le_of_card_ge hTQ (by rw [card_ggSL9Torus]; exact hQcard)
  haveI : MulAction.IsPretransitive (GGSL9V ≃ₗ[ZMod 2] GGSL9V)
      (Sylow 7 (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GGSL9V ≃ₗ[ZMod 2] GGSL9V) Q P
  have hmap : (↑Q : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)).map (MulAut.conj g).toMonoidHom =
      MulAut.conj g • (↑Q : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hcoe : (↑(g • Q) : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) = ↑P :=
    congrArg (fun R : Sylow 7 (GGSL9V ≃ₗ[ZMod 2] GGSL9V) =>
      (R : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) hg
  rw [Sylow.coe_subgroup_smul, ← hmap] at hcoe
  refine ⟨g, ?_⟩
  rw [hPeq, hQeq]
  exact hcoe.symm

end Sylow

end CFSG.StandardType

end
