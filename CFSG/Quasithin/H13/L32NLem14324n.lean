module

public import CFSG.Quasithin.EmptyFaithful.SzPS8A8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S8Five

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth
  CFSG.Quasithin.SzPS8 CFSG.QuasithinUnique

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure Model5 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) where
  ι : V ≃ₗ[ZMod 2] p4insporth_V8
  K : Subgroup Perm8
  hK : K = alternatingGroup (Fin 8) ∨ K = ⊤
  hΓ : Γ.map (p4insporth_cg ι).toMonoidHom = K.map p4insporth_perm8Hom

theorem exists_model5 [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) (hC5 : G112Concl5 B Γ) : Nonempty (Model5 Γ) := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨hdim, q, hq, -, ⟨W, hW3, hWq⟩, hΓO, hrel⟩ := hC5
  have hf : IsSymplectic B := ⟨halt, hnd⟩
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad hq) :=
    ⟨W, by rw [hW3, hdim], fun x hx => hWq x hx⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff (n := 3)
    (p4insporth_nondegenerate_quad hf hq)
    (p4insporth_nondegenerate_quad p4insporth_symplectic8 p4insporth_q8_add)
    hdim p4insporth_finrank8 (iff_of_true hplus p4insporth_plus8)
  have hι : ∀ x, p4insporth_q8 (e.toLinearEquiv x) = q x := fun x => e.map_app x
  set ι := e.toLinearEquiv with hιdef
  set c := p4insporth_cg ι with hcdef
  have hOeq : orthogonalSubgroupOf q = orthSub q := by
    ext g
    exact Iff.rfl
  rw [hOeq] at hΓO hrel
  have hmapO : (orthSub q).map c.toMonoidHom = orthSub p4insporth_q8 :=
    p4insporth_map_cg_orthSub ι hι
  set Γ' := Γ.map c.toMonoidHom with hΓ'def
  have hΓ'le : Γ' ≤ p4insporth_perm8Hom.range := by
    rw [p4insporth_range_perm8, ← hmapO]
    exact Subgroup.map_mono hΓO
  set K := Γ'.comap p4insporth_perm8Hom with hKdef
  have hΓ'K : Γ' = K.map p4insporth_perm8Hom := by
    rw [hKdef, Subgroup.map_comap_eq, inf_eq_right.2 hΓ'le]
  have hKindex : K.index ≤ 2 := by
    have h1 := Subgroup.relIndex_map_map_of_injective Γ (orthSub q) (f := c.toMonoidHom)
      c.injective
    rw [hmapO, ← p4insporth_range_perm8] at h1
    rw [← hΓ'def, hΓ'K, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective K ⊤ p4insporth_perm8Hom_injective,
      Subgroup.relIndex_top_right] at h1
    exact h1.trans_le hrel
  have hK : K = alternatingGroup (Fin 8) ∨ K = ⊤ := by
    have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : K.index = 1 ∨ K.index = 2) with h | h
    · exact Or.inr (Subgroup.index_eq_one.1 h)
    · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h)
  exact ⟨⟨ι, K, hK, hΓ'K⟩⟩

@[expose] def a9 : Perm8 := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def b9 : Perm8 := Equiv.swap 4 5 * Equiv.swap 5 6

@[expose] def n1 : Perm8 := Equiv.swap 0 1 * Equiv.swap 3 7

@[expose] def n2 : Perm8 := Equiv.swap 4 5 * Equiv.swap 3 7

theorem e9_facts : a9 ^ 3 = 1 ∧ b9 ^ 3 = 1 ∧ a9 * b9 = b9 * a9 ∧
    Equiv.Perm.sign a9 = 1 ∧ Equiv.Perm.sign b9 = 1 ∧ Equiv.Perm.sign n1 = 1 ∧
    Equiv.Perm.sign n2 = 1 ∧ n1 * a9 * n1⁻¹ = a9⁻¹ ∧ n1 * b9 * n1⁻¹ = b9 ∧
    n2 * a9 * n2⁻¹ = a9 ∧ n2 * b9 * n2⁻¹ = b9⁻¹ ∧ a9 ≠ 1 ∧ b9 ≠ 1 ∧
    (∀ i j : Fin 3, a9 ^ (i : ℕ) * b9 ^ (j : ℕ) = 1 → i = 0 ∧ j = 0) := by
  decide

theorem e9_mul_pow : ∀ i j i' j' : Fin 3,
    a9 ^ ((i + i' : Fin 3) : ℕ) * b9 ^ ((j + j' : Fin 3) : ℕ) =
      a9 ^ (i : ℕ) * b9 ^ (j : ℕ) * (a9 ^ (i' : ℕ) * b9 ^ (j' : ℕ)) := by
  decide

theorem e9_inv_pow : ∀ i j : Fin 3,
    a9 ^ ((-i : Fin 3) : ℕ) * b9 ^ ((-j : Fin 3) : ℕ) = (a9 ^ (i : ℕ) * b9 ^ (j : ℕ))⁻¹ := by
  decide

theorem e9_inj : ∀ i j i' j' : Fin 3, a9 ^ (i : ℕ) * b9 ^ (j : ℕ) = a9 ^ (i' : ℕ) * b9 ^ (j' : ℕ) →
    i = i' ∧ j = j' := by
  decide

theorem e9_comm : ∀ i j i' j' : Fin 3,
    a9 ^ (i : ℕ) * b9 ^ (j : ℕ) * (a9 ^ (i' : ℕ) * b9 ^ (j' : ℕ)) =
      a9 ^ (i' : ℕ) * b9 ^ (j' : ℕ) * (a9 ^ (i : ℕ) * b9 ^ (j : ℕ)) := by
  decide

theorem e9_cube : ∀ i j : Fin 3, (a9 ^ (i : ℕ) * b9 ^ (j : ℕ)) ^ 3 = 1 := by
  decide

theorem e9_sign : ∀ i j : Fin 3, Equiv.Perm.sign (a9 ^ (i : ℕ) * b9 ^ (j : ℕ)) = 1 := by
  decide

@[expose] def E9 : Subgroup Perm8 where
  carrier := {x | ∃ i j : Fin 3, a9 ^ (i : ℕ) * b9 ^ (j : ℕ) = x}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    exact ⟨i + i', j + j', e9_mul_pow i j i' j'⟩
  one_mem' := ⟨0, 0, by decide⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact ⟨-i, -j, e9_inv_pow i j⟩

theorem card_E9 : Nat.card E9 = 9 := by
  let f : Fin 3 × Fin 3 → E9 := fun p => ⟨a9 ^ (p.1 : ℕ) * b9 ^ (p.2 : ℕ), p.1, p.2, rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨i', j'⟩ h
      obtain ⟨h1, h2⟩ := e9_inj i j i' j' (congrArg Subtype.val h)
      rw [h1, h2]
    · rintro ⟨x, i, j, rfl⟩
      exact ⟨(i, j), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  simp

theorem E9_comm : ∀ x ∈ E9, ∀ y ∈ E9, x * y = y * x := by
  rintro _ ⟨i, j, rfl⟩ _ ⟨i', j', rfl⟩
  exact e9_comm i j i' j'

theorem E9_cube : ∀ x ∈ E9, x ^ 3 = 1 := by
  rintro _ ⟨i, j, rfl⟩
  exact e9_cube i j

theorem E9_le_alt : E9 ≤ alternatingGroup (Fin 8) := by
  rintro _ ⟨i, j, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr (e9_sign i j)

theorem e9_fix : p4insporth_perm8Hom a9 w8 = w8 ∧ p4insporth_perm8Hom b9 w8 = w8 := by
  constructor
  · rw [w8, p4insporth_perm8Hom_mk, mk_eq_iff]
    exact Or.inl (by decide : ∀ i : Fin 8, (![1, 1, 1, 1, 0, 0, 0, 0] : Fin 8 → ZMod 2)
      (a9⁻¹ i) = ![1, 1, 1, 1, 0, 0, 0, 0] i)
  · rw [w8, p4insporth_perm8Hom_mk, mk_eq_iff]
    exact Or.inl (by decide : ∀ i : Fin 8, (![1, 1, 1, 1, 0, 0, 0, 0] : Fin 8 → ZMod 2)
      (b9⁻¹ i) = ![1, 1, 1, 1, 0, 0, 0, 0] i)

namespace Model5

variable {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (M : Model5 Γ)

@[expose] noncomputable def ψ : Perm8 →* (V ≃ₗ[ZMod 2] V) :=
  (p4insporth_cg M.ι).symm.toMonoidHom.comp p4insporth_perm8Hom

theorem ψ_apply (σ : Perm8) (v : V) : M.ψ σ v = M.ι.symm (p4insporth_perm8Hom σ (M.ι v)) := rfl

theorem ψ_injective : Function.Injective M.ψ :=
  (p4insporth_cg M.ι).symm.injective.comp p4insporth_perm8Hom_injective

theorem eq_map : Γ = M.K.map M.ψ := by
  have h := congrArg (Subgroup.map (p4insporth_cg M.ι).symm.toMonoidHom) M.hΓ
  rw [Subgroup.map_map, Subgroup.map_map] at h
  have e : (p4insporth_cg M.ι).symm.toMonoidHom.comp (p4insporth_cg M.ι).toMonoidHom =
      MonoidHom.id _ := by
    ext g v
    simp
  rw [e, Subgroup.map_id] at h
  exact h

theorem mem_iff (γ : V ≃ₗ[ZMod 2] V) : γ ∈ Γ ↔ ∃ σ ∈ M.K, M.ψ σ = γ := by
  have h := M.eq_map
  constructor
  · intro hγ
    rw [h] at hγ
    exact Subgroup.mem_map.mp hγ
  · intro hσ
    have := Subgroup.mem_map.mpr hσ
    rw [← h] at this
    exact this

@[expose] noncomputable def A : Subgroup (V ≃ₗ[ZMod 2] V) := (alternatingGroup (Fin 8)).map M.ψ

theorem alt_le_K : alternatingGroup (Fin 8) ≤ M.K := by
  rcases M.hK with h | h <;> rw [h]
  exact le_top

theorem A_le : M.A ≤ Γ := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact (M.mem_iff _).mpr ⟨σ, M.alt_le_K hσ, rfl⟩

theorem card_A : Nat.card M.A = 20160 := by
  rw [A, Subgroup.card_map_of_injective M.ψ_injective, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem alt_le_of_normal {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (hN1 : N ≠ ⊥) : M.A ≤ N := by
  set N' := N.comap M.ψ with hN'
  have hN'K : N' ≤ M.K := by
    intro σ hσ
    obtain ⟨τ, hτ, he⟩ := (M.mem_iff _).mp (hNΓ hσ)
    rw [← M.ψ_injective he]
    exact hτ
  have hN'n : ∀ k ∈ M.K, ∀ n ∈ N', k * n * k⁻¹ ∈ N' := by
    intro k hk n hn
    show M.ψ (k * n * k⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hN _ ((M.mem_iff _).mpr ⟨k, hk, rfl⟩) _ hn
  have hN'1 : N' ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨σ, -, rfl⟩ := (M.mem_iff _).mp (hNΓ hx)
    have : σ ∈ N' := hx
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact one_mem _
  have h := SzPS8.alt_le_of_normal M.hK hN'K hN'n hN'1
  rintro _ ⟨σ, hσ, rfl⟩
  exact h hσ

theorem A_normal {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ M.A) :
    γ * a * γ⁻¹ ∈ M.A := by
  obtain ⟨σ, -, rfl⟩ := (M.mem_iff _).mp hγ
  obtain ⟨τ, hτ, rfl⟩ := ha
  refine ⟨σ * τ * σ⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (alternatingGroup.normal : (alternatingGroup (Fin 8)).Normal).conj_mem τ hτ σ

theorem isSimpleGroup_A : IsSimpleGroup ↥M.A := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  exact (Subgroup.equivMapOfInjective _ _ M.ψ_injective).symm.isSimpleGroup

theorem mem_A_of_pow_three {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) (h3 : γ ^ 3 = 1) : γ ∈ M.A := by
  obtain ⟨σ, -, rfl⟩ := (M.mem_iff _).mp hγ
  have hσ3 : σ ^ 3 = 1 := M.ψ_injective (by rw [map_pow, h3, map_one])
  refine ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr ?_, rfl⟩
  have h1 : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact h
  · rw [h] at h1
    exact absurd h1 (by decide)

theorem exists_e9 [Finite V] {S : Subgroup (V ≃ₗ[ZMod 2] V)} (hS : IsSylowTwoOf S Γ) {v : V}
    (hv : v ≠ 0) (hfix : ∀ s ∈ S, s v = v) :
    ∃ σ ∈ M.K, M.ψ (σ * a9 * σ⁻¹) v = v ∧ M.ψ (σ * b9 * σ⁻¹) v = v := by
  have hAK : alternatingGroup (Fin 8) ≤ M.K := M.alt_le_K
  have hT8K : IsSylowTwoOf (T8 ⊓ M.K) M.K := by
    rcases M.hK with h | h <;> rw [h]
    · exact isSylowTwoOf_T8_inf
    · rw [inf_top_eq]
      exact isSylowTwoOf_T8_top
  have hT' : IsSylowTwoOf ((T8 ⊓ M.K).map p4insporth_perm8Hom) (M.K.map p4insporth_perm8Hom) :=
    isSylowTwoOf_map_of_injective p4insporth_perm8Hom_injective hT8K
  have hS' : IsSylowTwoOf (S.map (p4insporth_cg M.ι).toMonoidHom)
      (M.K.map p4insporth_perm8Hom) := by
    rw [← M.hΓ]
    exact isSylowTwoOf_map_of_injective (p4insporth_cg M.ι).injective hS
  obtain ⟨γ, hγ, hγT⟩ := exists_conj_eq_of_isSylowTwoOf hS' hT'
  obtain ⟨g, hgK, rfl⟩ := hγ
  set w := p4insporth_perm8Hom g (M.ι v) with hw
  have hw0 : w ≠ 0 := fun h0 => hv (M.ι.injective (by
    rw [map_zero]
    exact (map_eq_zero_iff (p4insporth_perm8Hom g) (p4insporth_perm8Hom g).injective).mp h0))
  have hwfix : ∀ s ∈ T8 ⊓ alternatingGroup (Fin 8), p4insporth_perm8Hom s w = w := by
    intro s hs
    have hs' : p4insporth_perm8Hom s ∈ (T8 ⊓ M.K).map p4insporth_perm8Hom :=
      ⟨s, ⟨hs.1, hAK hs.2⟩, rfl⟩
    obtain ⟨y, ⟨t, ht, rfl⟩, hys⟩ := (hγT _).mp hs'
    rw [hys, hw]
    simp only [LinearEquiv.mul_apply, MulEquiv.coe_toMonoidHom, p4insporth_cg_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    rw [hfix t ht]
  have hww := fixed_class8 w hw0 hwfix
  refine ⟨g⁻¹, M.K.inv_mem hgK, ?_, ?_⟩
  all_goals
    rw [ψ_apply, inv_inv, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ← hw, hww]
  · rw [e9_fix.1, ← hww, hw, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      LinearEquiv.coe_one, id, LinearEquiv.symm_apply_apply]
  · rw [e9_fix.2, ← hww, hw, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      LinearEquiv.coe_one, id, LinearEquiv.symm_apply_apply]

theorem exists_E9 [Finite V] {S : Subgroup (V ≃ₗ[ZMod 2] V)} (hS : IsSylowTwoOf S Γ) {v : V}
    (hv : v ≠ 0) (hfix : ∀ s ∈ S, s v = v) :
    ∃ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≤ M.A ∧ Nat.card P = 9 ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ 3 = 1) ∧ ∀ x ∈ P, x v = v := by
  obtain ⟨σ, -, hα, hβ⟩ := M.exists_e9 hS hv hfix
  set c : Perm8 →* Perm8 := (MulAut.conj σ).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj σ).injective
  set P := (E9.map c).map M.ψ with hP
  have hmem : ∀ x ∈ P, ∃ i j : Fin 3, x = M.ψ (σ * a9 * σ⁻¹) ^ (i : ℕ) *
      M.ψ (σ * b9 * σ⁻¹) ^ (j : ℕ) := by
    rintro _ ⟨_, ⟨_, ⟨i, j, rfl⟩, rfl⟩, rfl⟩
    refine ⟨i, j, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, conj_pow, conj_pow]
    congr 1
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hpow : ∀ (x : V ≃ₗ[ZMod 2] V), x v = v → ∀ n : ℕ, (x ^ n) v = v := by
    intro x hx n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hx, ih]
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨c x, ?_, rfl⟩
    exact (alternatingGroup.normal : (alternatingGroup (Fin 8)).Normal).conj_mem x
      (E9_le_alt hx) σ
  · rw [hP, Subgroup.card_map_of_injective M.ψ_injective,
      Subgroup.card_map_of_injective hcinj, card_E9]
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, E9_comm x hx y hy]
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow, E9_cube x hx, map_one, map_one]
  · intro x hx
    obtain ⟨i, j, rfl⟩ := hmem x hx
    rw [LinearEquiv.mul_apply, hpow _ hβ, hpow _ hα]

end Model5

end CFSG.Quasithin.H13.S8Five
