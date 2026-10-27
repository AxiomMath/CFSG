module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.A5F

open Equiv

@[expose] def E0list : List (Perm (Fin 5)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem a5_norm : ∀ c : Perm (Fin 5), c ≠ 1 → c ^ 3 = 1 → Perm.sign c = 1 →
    (∀ e ∈ E0list, ∃ i : Fin 3, ∃ e' ∈ E0list, e * c = c ^ (i : ℕ) * e') →
    ∀ e ∈ E0list, c * e * c⁻¹ ∈ E0list := by
  decide +kernel

@[expose] def InvCond (c ℓ : Perm (Fin 5)) : Prop :=
  c ≠ 1 ∧ c ^ 3 = 1 ∧ (∀ e ∈ E0list, c * e * c⁻¹ ∈ E0list) ∧
    (∀ e ∈ E0list, ℓ * e * ℓ⁻¹ ∈ E0list) ∧ ℓ * c * ℓ⁻¹ = c⁻¹

instance (c ℓ : Perm (Fin 5)) : Decidable (InvCond c ℓ) := by unfold InvCond; infer_instance

theorem a5_inv : ∀ c ℓ : Perm (Fin 5), InvCond c ℓ → Perm.sign ℓ ≠ 1 := by
  decide +kernel

theorem E0_sign : ∀ e ∈ E0list, Perm.sign e = 1 := by decide +kernel

theorem E0_mul : ∀ a ∈ E0list, ∀ b ∈ E0list, a * b ∈ E0list := by decide +kernel

theorem E0_sq : ∀ a ∈ E0list, a * a = 1 := by decide +kernel

@[expose] def E0 : Subgroup ↥(alternatingGroup (Fin 5)) where
  carrier := {x | (x : Perm (Fin 5)) ∈ E0list}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => E0_mul _ ha _ hb
  inv_mem' := fun {a} ha => by
    have h : a⁻¹ = a := by
      rw [inv_eq_iff_mul_eq_one]
      exact Subtype.ext (E0_sq _ ha)
    rw [h]
    exact ha

theorem card_E0 : Nat.card E0 = 4 := by
  let f : ↥E0 → {x : Perm (Fin 5) // x ∈ E0list} := fun x =>
    ⟨(x : ↥(alternatingGroup (Fin 5))), x.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => ?_, ?_⟩
    · have h' := congrArg (fun z : {x : Perm (Fin 5) // x ∈ E0list} => (z : Perm (Fin 5))) h
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨x, hx⟩
      exact ⟨⟨⟨x, Perm.mem_alternatingGroup.mpr (E0_sign x hx)⟩, hx⟩, rfl⟩
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_A5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_conj_E0 {E : Subgroup ↥(alternatingGroup (Fin 5))} (hE : Nat.card E = 4) :
    ∃ g : ↥(alternatingGroup (Fin 5)), E.map (MulAut.conj g).toMonoidHom = E0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ H : Subgroup ↥(alternatingGroup (Fin 5)), Nat.card H = 4 → ¬ 2 ∣ H.index := by
    intro H hH h2
    have h := H.card_mul_index
    rw [hH, card_A5] at h
    omega
  have hp : ∀ H : Subgroup ↥(alternatingGroup (Fin 5)), Nat.card H = 4 → IsPGroup 2 H := fun H hH =>
    IsPGroup.of_card (n := 2) (by rw [hH]; norm_num)
  let R : Sylow 2 ↥(alternatingGroup (Fin 5)) := (hp E hE).toSylow (hidx E hE)
  let Q : Sylow 2 ↥(alternatingGroup (Fin 5)) := (hp E0 card_E0).toSylow (hidx E0 card_E0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(alternatingGroup (Fin 5)) R Q
  refine ⟨g, ?_⟩
  have hQ : ((g • R : Sylow 2 _) : Subgroup ↥(alternatingGroup (Fin 5))) = E0 := by rw [hg]; rfl
  rw [Sylow.coe_subgroup_smul] at hQ
  ext x
  rw [← hQ]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) _).mp hx
    exact ⟨y, hy, hyx⟩

theorem a5_false {A : Type} [Group A] (φ : A ≃* ↥(alternatingGroup (Fin 5))) {E : Subgroup A}
    (hE : Nat.card E = 4) {c ℓ : A} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hEc : ∀ e ∈ E, ∃ i : ℕ, ∃ e' ∈ E, e * c = c ^ i * e')
    (hℓ : ℓ ∈ Subgroup.normalizer (E : Set A)) (hℓc : ℓ * c * ℓ⁻¹ = c⁻¹) : False := by
  set E' := E.map φ.toMonoidHom with hE'
  have hE'4 : Nat.card E' = 4 := by rw [hE', Subgroup.card_map_of_injective φ.injective, hE]
  obtain ⟨g, hg⟩ := exists_conj_E0 hE'4
  set κ : A →* ↥(alternatingGroup (Fin 5)) := (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom
    with hκ
  have hκb : Function.Bijective κ :=
    ⟨(MulAut.conj g).injective.comp φ.injective, (MulAut.conj g).surjective.comp φ.surjective⟩
  set ψ : A →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp κ with hψ
  have hψinj : Function.Injective ψ := (Subgroup.subtype_injective _).comp hκb.1
  have hmemE : ∀ x : A, x ∈ E ↔ ψ x ∈ E0list := by
    intro x
    change x ∈ E ↔ κ x ∈ E0
    rw [← hg]
    constructor
    · intro hx
      exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
      have : κ z = κ x := hyx
      rwa [← hκb.1 this]
  have hsurjE : ∀ e ∈ E0list, ∃ x ∈ E, ψ x = e := by
    intro e he
    obtain ⟨x, hx⟩ := hκb.2 ⟨e, Perm.mem_alternatingGroup.mpr (E0_sign e he)⟩
    have hψx : ψ x = e := by rw [hψ, MonoidHom.comp_apply, hx]; rfl
    exact ⟨x, (hmemE x).mpr (hψx ▸ he), hψx⟩
  have hsign : ∀ x : A, Perm.sign (ψ x) = 1 := fun x =>
    Perm.mem_alternatingGroup.mp (κ x).2
  have hc1' : ψ c ≠ 1 := fun h => hc1 (hψinj (h.trans (map_one ψ).symm))
  have hc3' : ψ c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hEc' : ∀ e ∈ E0list, ∃ i : Fin 3, ∃ e' ∈ E0list, e * ψ c = ψ c ^ (i : ℕ) * e' := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := hsurjE e he
    obtain ⟨i, e'', he'', hxc⟩ := hEc x hx
    refine ⟨⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ψ e'', (hmemE e'').mp he'', ?_⟩
    have hmod : ψ c ^ i = ψ c ^ (i % 3) := by
      conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hc3', one_pow, one_mul]
    rw [← map_mul, hxc, map_mul, map_pow, hmod]
  have hnorm := a5_norm (ψ c) hc1' hc3' (hsign c) hEc'
  have hℓnorm : ∀ e ∈ E0list, ψ ℓ * e * (ψ ℓ)⁻¹ ∈ E0list := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := hsurjE e he
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (hmemE _).mp ((Subgroup.mem_normalizer_iff.mp hℓ x).mp hx)
  have hℓc' : ψ ℓ * ψ c * (ψ ℓ)⁻¹ = (ψ c)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hℓc, map_inv]
  exact a5_inv (ψ c) (ψ ℓ) ⟨hc1', hc3', hnorm, hℓnorm, hℓc'⟩ (hsign ℓ)

end CFSG.Quasithin.H13.A5F
