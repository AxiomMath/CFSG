module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section CentMod

variable {M : Type} [Group M]

@[expose] def centMod (U : Subgroup M) (α : MulAut M) : Subgroup M where
  carrier := {b | b ∈ Subgroup.normalizer (U : Set M) ∧ α b * b⁻¹ ∈ U}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [map_mul, show α a * α b * (a * b)⁻¹ = (α a * a⁻¹) * (a * (α b * b⁻¹) * a⁻¹) by group]
    exact mul_mem ha.2 ((Subgroup.mem_normalizer_iff.mp ha.1 _).mp hb.2)
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, ?_⟩
    rw [map_inv, inv_inv, show (α a)⁻¹ * a = (a⁻¹ * (α a * a⁻¹) * a⁻¹⁻¹)⁻¹ by group]
    exact inv_mem ((Subgroup.mem_normalizer_iff.mp (inv_mem ha.1) _).mp ha.2)

theorem mem_centMod {U : Subgroup M} {α : MulAut M} {b : M} :
    b ∈ centMod U α ↔ b ∈ Subgroup.normalizer (U : Set M) ∧ α b * b⁻¹ ∈ U :=
  Iff.rfl

theorem centMod_le_normalizer (U : Subgroup M) (α : MulAut M) :
    centMod U α ≤ Subgroup.normalizer (U : Set M) := fun _ h => h.1

theorem map_mem_normalizer {U : Subgroup M} {φ : MulAut M} (hφ : U.map φ.toMonoidHom = U)
    {b : M} (hb : b ∈ Subgroup.normalizer (U : Set M)) :
    φ b ∈ Subgroup.normalizer (U : Set M) := by
  have h := Subgroup.map_equiv_normalizer_eq U φ
  rw [hφ] at h
  rw [← h]
  exact ⟨b, hb, rfl⟩

theorem le_centMod {U : Subgroup M} {α : MulAut M} (hα : U.map α.toMonoidHom = U) :
    U ≤ centMod U α := by
  intro u hu
  have h : α u ∈ U.map α.toMonoidHom := ⟨u, hu, rfl⟩
  rw [hα] at h
  exact ⟨Subgroup.le_normalizer hu, mul_mem h (inv_mem hu)⟩

theorem centMod_mul_eq {U : Subgroup M} {ι φ : MulAut M} (hφ : U.map φ.toMonoidHom = U)
    (hι : ∀ b ∈ Subgroup.normalizer (U : Set M), ι b * b⁻¹ ∈ U) :
    centMod U (ι * φ) = centMod U φ := by
  ext b
  simp only [mem_centMod, MulAut.mul_apply]
  refine and_congr_right fun hb => ?_
  have h1 := hι (φ b) (map_mem_normalizer hφ hb)
  rw [show ι (φ b) * b⁻¹ = (ι (φ b) * (φ b)⁻¹) * (φ b * b⁻¹) by group]
  exact ⟨fun h => by simpa using mul_mem (inv_mem h1) h, fun h => mul_mem h1 h⟩

theorem conj_mul_inv_mem {U : Subgroup M}
    (hab : ∀ a ∈ Subgroup.normalizer (U : Set M), ∀ b ∈ Subgroup.normalizer (U : Set M),
      a * b * a⁻¹ * b⁻¹ ∈ U)
    {g : M} (hg : g ∈ Subgroup.normalizer (U : Set M)) :
    ∀ b ∈ Subgroup.normalizer (U : Set M), MulAut.conj g b * b⁻¹ ∈ U := fun b hb => by
  rw [MulAut.conj_apply]
  exact hab g hg b hb

theorem index_comap_le [Finite M] {T : Type} [Group T] (U : Subgroup M) (α : MulAut M)
    (d : T →* M) (hd : d.range ≤ Subgroup.normalizer (U : Set M)) :
    ((centMod U α).comap d).index ≤ (centMod U α).relIndex (Subgroup.normalizer (U : Set M)) := by
  rw [← Subgroup.relIndex_top_right, Subgroup.relIndex_comap, ← MonoidHom.range_eq_map]
  exact Subgroup.relIndex_le_of_le_right hd Subgroup.index_ne_zero_of_finite

theorem mul_mul_inv_mul_inv_mem_of_mem_mul {U H : Subgroup M}
    (hHU : H ≤ Subgroup.normalizer (U : Set M)) (hH : ∀ h ∈ H, ∀ h' ∈ H, h * h' = h' * h)
    {a b : M} (ha : a ∈ (H : Set M) * (U : Set M)) (hb : b ∈ (H : Set M) * (U : Set M)) :
    a * b * a⁻¹ * b⁻¹ ∈ U := by
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := ha
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := hb
  have hn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mp hu
  have e : h₁ * u₁ * (h₂ * u₂) * (h₁ * u₁)⁻¹ * (h₂ * u₂)⁻¹ =
      (h₁ * u₁ * h₁⁻¹) * ((h₁ * h₂) * (u₂ * u₁⁻¹) * (h₁ * h₂)⁻¹) *
        ((h₁ * h₂ * h₁⁻¹) * u₂⁻¹ * (h₁ * h₂ * h₁⁻¹)⁻¹) * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) := by group
  rw [e, show h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = 1 by rw [hH h₁ hh₁ h₂ hh₂]; group, mul_one]
  exact mul_mem (mul_mem (hn _ hh₁ _ hu₁)
    (hn _ (mul_mem hh₁ hh₂) _ (mul_mem hu₂ (inv_mem hu₁))))
    (hn _ (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) _ (inv_mem hu₂))

theorem mem_normalizer_of_map_conj_eq {U : Subgroup M} {g : M}
    (h : U.map (MulAut.conj g).toMonoidHom = U) : g ∈ Subgroup.normalizer (U : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : MulAut.conj g x ∈ U.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at h1
  · intro hx
    have h1 : g * x * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := by rw [h]; exact hx
    obtain ⟨x', hx', he⟩ := h1
    have he' : g * x' * g⁻¹ = g * x * g⁻¹ := he
    rw [mul_left_inj, mul_right_inj] at he'
    exact he' ▸ hx'

theorem centMod_conj_mul_eq {U : Subgroup M}
    (hab : ∀ a ∈ Subgroup.normalizer (U : Set M), ∀ b ∈ Subgroup.normalizer (U : Set M),
      a * b * a⁻¹ * b⁻¹ ∈ U)
    {g : M} {φ : MulAut M} (hφ : U.map φ.toMonoidHom = U)
    (h : U.map (MulAut.conj g * φ).toMonoidHom = U) :
    centMod U (MulAut.conj g * φ) = centMod U φ := by
  have hg : U.map (MulAut.conj g).toMonoidHom = U :=
    calc U.map (MulAut.conj g).toMonoidHom = (U.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom
          := by rw [hφ]
      _ = U.map (MulAut.conj g * φ).toMonoidHom := by rw [Subgroup.map_map]; rfl
      _ = U := h
  exact centMod_mul_eq hφ (conj_mul_inv_mem hab (mem_normalizer_of_map_conj_eq hg))

theorem mem_normalizer_subgroupOf_iff {G : Type*} [Group G] {U C : Subgroup G} (hUC : U ≤ C)
    (g : C) : g ∈ Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) ↔
      (g : G) ∈ Subgroup.normalizer (U : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h x
    constructor
    · intro hx
      exact (h ⟨x, hUC hx⟩).mp hx
    · intro hx
      have hxC : x ∈ C := by
        have h1 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) ∈ C :=
          mul_mem (mul_mem (inv_mem g.2) (hUC hx)) g.2
        rwa [show (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) = x by group] at h1
      exact (h ⟨x, hxC⟩).mpr hx
  · intro h y
    exact h y

theorem map_eq_of_forall_mem {U : Subgroup M} [Finite U] {φ : MulAut M}
    (h : ∀ u ∈ U, φ u ∈ U) : U.map φ.toMonoidHom = U :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨u, hu, rfl⟩; exact h u hu)
    (by rw [Subgroup.card_map_of_injective φ.injective])

theorem map_mul_eq {U : Subgroup M} {ι₁ ι₂ : MulAut M} (h₁ : U.map ι₁.toMonoidHom = U)
    (h₂ : U.map ι₂.toMonoidHom = U) : U.map (ι₁ * ι₂).toMonoidHom = U := by
  rw [show (ι₁ * ι₂).toMonoidHom = ι₁.toMonoidHom.comp ι₂.toMonoidHom from rfl,
    ← Subgroup.map_map, h₂, h₁]

theorem map_inv_eq {U : Subgroup M} {ι : MulAut M} (h : U.map ι.toMonoidHom = U) :
    U.map ι⁻¹.toMonoidHom = U := by
  conv_lhs => rw [← h]
  rw [Subgroup.map_map]
  convert Subgroup.map_id U
  ext x
  simp

theorem map_pow_eq {U : Subgroup M} {ι : MulAut M} (h : U.map ι.toMonoidHom = U) (k : ℕ) :
    U.map (ι ^ k).toMonoidHom = U := by
  induction k with
  | zero =>
    rw [pow_zero]
    convert Subgroup.map_id U
    ext x
    rfl
  | succ k ih => rw [pow_succ]; exact map_mul_eq ih h

theorem mul_inv_mem_of_mul {U : Subgroup M} {ι₁ ι₂ : MulAut M}
    (h₂U : U.map ι₂.toMonoidHom = U)
    (h₁ : ∀ b ∈ Subgroup.normalizer (U : Set M), ι₁ b * b⁻¹ ∈ U)
    (h₂ : ∀ b ∈ Subgroup.normalizer (U : Set M), ι₂ b * b⁻¹ ∈ U) :
    ∀ b ∈ Subgroup.normalizer (U : Set M), (ι₁ * ι₂) b * b⁻¹ ∈ U := fun b hb => by
  rw [MulAut.mul_apply, show ι₁ (ι₂ b) * b⁻¹ = (ι₁ (ι₂ b) * (ι₂ b)⁻¹) * (ι₂ b * b⁻¹) by group]
  exact mul_mem (h₁ _ (map_mem_normalizer h₂U hb)) (h₂ b hb)

theorem centMod_one (U : Subgroup M) : centMod U 1 = Subgroup.normalizer (U : Set M) := by
  ext b
  simp only [mem_centMod, MulAut.one_apply, mul_inv_cancel, one_mem, and_true]

end CentMod

section FieldIndex

variable {K : Type} [Field K]

@[expose] def unitsFix (σ : K ≃+* K) : Subgroup Kˣ where
  carrier := {t | σ (t : K) = t}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [ha]

theorem mem_unitsFix {σ : K ≃+* K} {t : Kˣ} : t ∈ unitsFix σ ↔ σ (t : K) = t :=
  Iff.rfl

theorem unitsFix_eq_top_iff {σ : K ≃+* K} : unitsFix σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    refine RingEquiv.ext fun x => ?_
    by_cases hx : x = 0
    · rw [hx, map_zero]
      rfl
    · have h1 : Units.mk0 x hx ∈ unitsFix σ := h ▸ Subgroup.mem_top _
      exact h1
  · rintro rfl
    exact eq_top_iff.mpr fun t _ => rfl

variable [Finite K]

theorem two_le_index_unitsFix {σ : K ≃+* K} (hσ : σ ≠ 1) : 2 ≤ (unitsFix σ).index := by
  have h1 : (unitsFix σ).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one, unitsFix_eq_top_iff]
    exact hσ
  have h0 : (unitsFix σ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem eq_one_of_index_pi_unitsFix_le_three {ι : Type} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    {σ : K ≃+* K} (h : (Subgroup.pi Set.univ fun _ : ι => unitsFix σ).index ≤ 3) : σ = 1 := by
  by_contra hσ
  rw [Subgroup.index_pi, Finset.prod_const, Finset.card_univ] at h
  have h2 := two_le_index_unitsFix hσ
  have h3 : 2 ^ 2 ≤ (unitsFix σ).index ^ Fintype.card ι :=
    (Nat.pow_le_pow_left h2 2).trans (Nat.pow_le_pow_right (by omega) hι)
  omega

omit [Finite K] in
theorem card_fixed_sq_le [Fintype K] [DecidableEq K] (σ : K ≃+* K) (hσ : σ ≠ 1) :
    (Finset.univ.filter (fun x => σ x = x)).card ^ 2 ≤ Fintype.card K := by
  obtain ⟨y, hy⟩ : ∃ y, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  set E := Finset.univ.filter (fun x => σ x = x)
  rw [pow_two, ← Finset.card_product, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => p.1 + p.2 * y) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, E, Finset.mem_filter,
    Finset.mem_univ, true_and] at hab hab'
  simp only at h
  by_cases hb : b = b'
  · subst hb
    simp only [Prod.mk.injEq, and_true]
    linear_combination h
  · exfalso
    have hb' : b - b' ≠ 0 := sub_ne_zero.mpr hb
    have hy' : y = (a' - a) / (b - b') := by
      field_simp
      linear_combination h
    apply hy
    rw [hy', map_div₀, map_sub, map_sub, hab.1, hab.2, hab'.1, hab'.2]

theorem eq_one_or_card_eq_four_of_index_unitsFix_le_three {σ : K ≃+* K}
    (h : (unitsFix σ).index ≤ 3) : σ = 1 ∨ Nat.card K = 4 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hσ, h4⟩ := hne
  have : Fintype K := Fintype.ofFinite K
  set E := Finset.univ.filter (fun x : K => σ x = x) with hE
  have hsq : E.card ^ 2 ≤ Fintype.card K := card_fixed_sq_le σ hσ
  have e1 : (unitsFix σ) ≃ {x : K // σ x = x ∧ x ≠ 0} :=
    { toFun := fun t => ⟨(t : Kˣ), t.2, (t : Kˣ).ne_zero⟩
      invFun := fun x => ⟨Units.mk0 x.1 x.2.2, x.2.1⟩
      left_inv := fun t => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }
  have hc1 : Nat.card (unitsFix σ) = (E.erase 0).card := by
    rw [Nat.card_congr e1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    exact and_comm
  have hc2 : (E.erase 0).card + 1 = E.card :=
    Finset.card_erase_add_one (by simp [hE])
  have hL := (unitsFix σ).card_mul_index
  have hq := Nat.card_eq_card_units_add_one K
  rw [Nat.card_eq_fintype_card] at hq h4
  have hpos : 0 < Nat.card (unitsFix σ) := Nat.card_pos
  set u := Nat.card (unitsFix σ)
  set i := (unitsFix σ).index
  set e := E.card
  set q := Fintype.card K
  have he : e = u + 1 := by rw [← hc2, ← hc1]
  have hqu : q = u * i + 1 := by rw [hq, ← hL]
  have hu : u ≤ 1 := by
    by_contra hu
    have : (u + 1) ^ 2 ≤ u * 3 + 1 := by
      rw [← he]
      calc e ^ 2 ≤ q := hsq
        _ = u * i + 1 := hqu
        _ ≤ u * 3 + 1 := by nlinarith
    nlinarith
  have hu1 : u = 1 := by omega
  rw [hu1] at hqu he
  rw [he] at hsq
  omega

theorem ringAut_pow_eq_one {n : ℕ} (hK : Nat.card K = 2 ^ n) (β : K ≃+* K) : β ^ n = 1 := by
  have hc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by
    rw [hc]
    rintro rfl
    rw [pow_zero] at hK
    exact (Finite.one_lt_card (α := K)).ne' hK)
  rw [← hc]
  exact pow_card_eq_one'

end FieldIndex

@[expose] def ExcLie (M : Type) [Group M] : Prop :=
  IsPSL 2 2 2 M ∨ IsPSU 3 2 3 M ∨ IsPSL 3 2 2 M

@[expose] def N2At (M : Type) [Group M] (U : Subgroup M) : Prop :=
  ∀ α : MulAut M, (∃ k : ℕ, α ^ 2 ^ k = 1) → U.map α.toMonoidHom = U →
    (centMod U α).relIndex (Subgroup.normalizer (U : Set M)) = 3 → ExcLie M

@[expose] def N4At (M : Type) [Group M] (U : Subgroup M) : Prop :=
  ∀ α : MulAut M, (∃ k : ℕ, α ^ 2 ^ k = 1) → U.map α.toMonoidHom = U →
    Subgroup.normalizer (U : Set M) ≤ centMod U α →
      α ∈ (MulAut.conj : M →* MulAut M).range ∨ IsPSL 3 2 2 M

@[expose] def N3At (M : Type) [Group M] (U : Subgroup M) : Prop :=
  ∀ α β : MulAut M, (∃ k : ℕ, α ^ 2 ^ k = 1) → β ^ 3 = 1 → U.map α.toMonoidHom = U →
    U.map β.toMonoidHom = U → α * β * α⁻¹ = β⁻¹ →
    Subgroup.normalizer (U : Set M) ≤ centMod U α →
    Subgroup.normalizer (U : Set M) ≤ centMod U β →
      β ∈ (MulAut.conj : M →* MulAut M).range ∨ IsPSL 3 2 2 M

@[expose] def N2Model (M : Type) [Group M] : Prop :=
  ∀ U : Subgroup M, IsSylowTwoOf U ⊤ → N2At M U

@[expose] def N4Model (M : Type) [Group M] : Prop :=
  ∀ U : Subgroup M, IsSylowTwoOf U ⊤ → N4At M U

@[expose] def N3Model (M : Type) [Group M] : Prop :=
  ∀ U : Subgroup M, IsSylowTwoOf U ⊤ → N3At M U

section Transport

variable {M M' : Type} [Group M] [Group M']

theorem ExcLie.map (e : M ≃* M') (h : ExcLie M) : ExcLie M' := by
  rcases h with h | h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e h))

theorem isPSL34_map (e : M ≃* M') (h : IsPSL 3 2 2 M) : IsPSL 3 2 2 M' :=
  CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e h

theorem congr_symm_apply (e : M ≃* M') (α' : MulAut M') (m : M) :
    (MulAut.congr e).symm α' m = e.symm (α' (e m)) :=
  rfl

theorem map_congr_symm_eq (e : M ≃* M') {U : Subgroup M} {α' : MulAut M'}
    (h : (U.map e.toMonoidHom).map α'.toMonoidHom = U.map e.toMonoidHom) :
    U.map ((MulAut.congr e).symm α').toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h1 : α' (e u) ∈ (U.map e.toMonoidHom).map α'.toMonoidHom := ⟨e u, ⟨u, hu, rfl⟩, rfl⟩
    rw [h] at h1
    obtain ⟨v, hv, hve⟩ := h1
    change e.symm (α' (e u)) ∈ U
    rw [← hve]
    change e.symm (e v) ∈ U
    rwa [MulEquiv.symm_apply_apply]
  · intro hx
    have h1 : e x ∈ (U.map e.toMonoidHom).map α'.toMonoidHom := by
      rw [h]
      exact ⟨x, hx, rfl⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := h1
    refine ⟨u, hu, ?_⟩
    change e.symm (α' (e u)) = x
    have hue' : α' (e u) = e x := hue
    rw [hue', MulEquiv.symm_apply_apply]

theorem normalizer_map (e : M ≃* M') (U : Subgroup M) :
    Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup M') : Set M') =
      (Subgroup.normalizer (U : Set M)).map e.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq U e).symm

theorem centMod_map (e : M ≃* M') (U : Subgroup M) (α' : MulAut M') :
    centMod (U.map e.toMonoidHom) α' =
      (centMod U ((MulAut.congr e).symm α')).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_centMod, mem_centMod, normalizer_map, Subgroup.mem_map_equiv,
    Subgroup.mem_map_equiv, congr_symm_apply, MulEquiv.apply_symm_apply, map_mul, map_inv]

theorem pow_two_pow_congr (e : M ≃* M') {α' : MulAut M'} (h : ∃ k : ℕ, α' ^ 2 ^ k = 1) :
    ∃ k : ℕ, (MulAut.congr e).symm α' ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem mem_range_conj_congr (e : M ≃* M') {α : MulAut M}
    (h : α ∈ (MulAut.conj : M →* MulAut M).range) :
    MulAut.congr e α ∈ (MulAut.conj : M' →* MulAut M').range := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨e m, MulEquiv.ext fun x => ?_⟩
  change e m * x * (e m)⁻¹ = e (m * e.symm x * m⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem N2At.map (e : M ≃* M') {U : Subgroup M} (h : N2At M U) :
    N2At M' (U.map e.toMonoidHom) := by
  intro α' hα hαU hidx
  refine ExcLie.map e (h _ (pow_two_pow_congr e hα) (map_congr_symm_eq e hαU) ?_)
  rw [centMod_map, normalizer_map, Subgroup.relIndex_map_map_of_injective _ _ e.injective] at hidx
  exact hidx

theorem N4At.map (e : M ≃* M') {U : Subgroup M} (h : N4At M U) :
    N4At M' (U.map e.toMonoidHom) := by
  intro α' hα hαU hle
  rw [centMod_map, normalizer_map,
    Subgroup.map_le_map_iff_of_injective e.injective] at hle
  rcases h _ (pow_two_pow_congr e hα) (map_congr_symm_eq e hαU) hle with hi | hi
  · left
    have := mem_range_conj_congr e hi
    rwa [MulEquiv.apply_symm_apply] at this
  · exact Or.inr (isPSL34_map e hi)

end Transport

section Sylow

variable {M : Type} [Group M] [Finite M]

theorem isSylowTwoOf_sylow (P : Sylow 2 M) : IsSylowTwoOf (P : Subgroup M) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup M).subgroupOf ⊤).index = (P : Subgroup M).index from
    Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

theorem exists_map_conj_eq {U U' : Subgroup M} (hU : IsSylowTwoOf U ⊤) (hU' : IsSylowTwoOf U' ⊤) :
    ∃ g : M, U.map (MulAut.conj g).toMonoidHom = U' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup M, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := fun S hS => by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (hU.2.1.toSylow (hidx U hU))
    (hU'.2.1.toSylow (hidx U' hU'))
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 M => (T : Subgroup M)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem N2Model.of_at {U : Subgroup M} (hU : IsSylowTwoOf U ⊤) (h : N2At M U) : N2Model M := by
  intro U' hU'
  obtain ⟨g, rfl⟩ := exists_map_conj_eq hU hU'
  exact h.map (MulAut.conj g)

theorem N4Model.of_at {U : Subgroup M} (hU : IsSylowTwoOf U ⊤) (h : N4At M U) : N4Model M := by
  intro U' hU'
  obtain ⟨g, rfl⟩ := exists_map_conj_eq hU hU'
  exact h.map (MulAut.conj g)

variable {M' : Type} [Group M']

omit [Finite M] in
theorem isSylowTwoOf_map_symm (e : M ≃* M') {U' : Subgroup M'} (h : IsSylowTwoOf U' ⊤) :
    IsSylowTwoOf (U'.map e.symm.toMonoidHom) ⊤ := by
  refine ⟨le_top, h.2.1.map _, ?_⟩
  have h2 := h.2.2
  rw [show (U'.subgroupOf ⊤).index = U'.index from Subgroup.relIndex_top_right U'] at h2
  rw [show ((U'.map e.symm.toMonoidHom).subgroupOf ⊤).index = (U'.map e.symm.toMonoidHom).index
    from Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective e.symm.bijective]
  exact h2

omit [Finite M] in
theorem map_map_symm (e : M ≃* M') (U' : Subgroup M') :
    (U'.map e.symm.toMonoidHom).map e.toMonoidHom = U' := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]

omit [Finite M] in
theorem N2Model.of_mulEquiv (e : M ≃* M') (h : N2Model M) : N2Model M' := fun U' hU' => by
  have := (h _ (isSylowTwoOf_map_symm e hU')).map e
  rwa [map_map_symm] at this

omit [Finite M] in
theorem N4Model.of_mulEquiv (e : M ≃* M') (h : N4Model M) : N4Model M' := fun U' hU' => by
  have := (h _ (isSylowTwoOf_map_symm e hU')).map e
  rwa [map_map_symm] at this

end Sylow

section TwoInner

variable {M : Type} [Group M]

theorem mul_conj_mul_inv (φ : MulAut M) (x : M) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem mem_range_conj_of_pow_two_pow {Γ : Type*} [Group Γ] (F : Γ →* MulAut M)
    (hNF : ∀ α : MulAut M, ∃ (x : M) (β : Γ), α = MulAut.conj x * F β)
    (hF : ∀ β : Γ, F β ∈ (MulAut.conj : M →* MulAut M).range → β = 1)
    {f : ℕ} (hf : Odd f) (hpow : ∀ β : Γ, β ^ f = 1)
    {α : MulAut M} (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) : α ∈ (MulAut.conj : M →* MulAut M).range := by
  obtain ⟨k, hk⟩ := hα
  obtain ⟨x, β, rfl⟩ := hNF α
  have hm : ∀ m : ℕ, ∃ y : M, (MulAut.conj x * F β) ^ m = MulAut.conj y * F (β ^ m) := by
    intro m
    induction m with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, mul_one]⟩
    | succ m ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨y * F (β ^ m) x, ?_⟩
      rw [pow_succ, hy, pow_succ, map_mul F, map_mul MulAut.conj,
        show MulAut.conj y * F (β ^ m) * (MulAut.conj x * F β) =
          MulAut.conj y * (F (β ^ m) * MulAut.conj x * (F (β ^ m))⁻¹) * (F (β ^ m) * F β) by
          group, mul_conj_mul_inv, mul_assoc]
  obtain ⟨y, hy⟩ := hm (2 ^ k)
  rw [hk] at hy
  have h1 : F (β ^ 2 ^ k) ∈ (MulAut.conj : M →* MulAut M).range :=
    ⟨y⁻¹, by rw [map_inv, eq_inv_of_mul_eq_one_right hy.symm]⟩
  have h2 := hF _ h1
  have h3 : orderOf β ∣ Nat.gcd (2 ^ k) f :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (hpow β))
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hf)),
    Nat.dvd_one, orderOf_eq_one_iff] at h3
  rw [h3, map_one, mul_one]
  exact ⟨x, rfl⟩

theorem normalizer_le_centMod_of_inner (hZ : Subgroup.center M = ⊥) {U : Subgroup M}
    (hU : IsSylowTwoOf U ⊤) {α : MulAut M} (hα : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hαU : U.map α.toMonoidHom = U) (hinn : α ∈ (MulAut.conj : M →* MulAut M).range) :
    Subgroup.normalizer (U : Set M) ≤ centMod U α := by
  obtain ⟨g, rfl⟩ := hinn
  obtain ⟨k, hk⟩ := hα
  have hgN := mem_normalizer_of_map_conj_eq hαU
  have hg2 : g ^ 2 ^ k = 1 := by
    have h1 : g ^ 2 ^ k ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h2 := congrArg (fun φ : MulAut M => φ b) hk
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h2
      calc b * g ^ 2 ^ k = g ^ 2 ^ k * b * (g ^ 2 ^ k)⁻¹ * g ^ 2 ^ k := by rw [h2]
        _ = g ^ 2 ^ k * b := by group
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have hgU : g ∈ U := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hidx : ¬ 2 ∣ U.index := by
      have := hU.2.2
      rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
    set Q : Sylow 2 M := hU.2.1.toSylow hidx
    have hQ : (Q : Subgroup M) = U := IsPGroup.toSylow_coe hU.2.1 hidx
    have hP : IsPGroup 2 (Subgroup.zpowers g) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg2)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have h1 : g ∈ Subgroup.zpowers g ⊓ Subgroup.normalizer (Q : Set M) := by
      refine ⟨Subgroup.mem_zpowers _, ?_⟩
      show g ∈ Subgroup.normalizer ((Q : Subgroup M) : Set M)
      rw [hQ]
      exact hgN
    rw [hP.inf_normalizer_sylow Q, hQ] at h1
    exact h1.2
  intro b hb
  refine ⟨hb, ?_⟩
  rw [MulAut.conj_apply, show g * b * g⁻¹ * b⁻¹ = g * (b * g⁻¹ * b⁻¹) by group]
  exact mul_mem hgU ((Subgroup.mem_normalizer_iff.mp hb _).mp (inv_mem hgU))

theorem n2Model_n4Model_of_two_inner (hZ : Subgroup.center M = ⊥)
    (h : ∀ α : MulAut M, (∃ k : ℕ, α ^ 2 ^ k = 1) → α ∈ (MulAut.conj : M →* MulAut M).range) :
    N2Model M ∧ N4Model M := by
  refine ⟨fun U hU α hα hαU hidx => ?_, fun U _ α hα _ _ => Or.inl (h α hα)⟩
  exfalso
  have hle := normalizer_le_centMod_of_inner hZ hU hα hαU (h α hα)
  rw [le_antisymm (centMod_le_normalizer U α) hle, Subgroup.relIndex_self] at hidx
  omega

end TwoInner

end CFSG.Quasithin.H13.L32A.C.SkPf
