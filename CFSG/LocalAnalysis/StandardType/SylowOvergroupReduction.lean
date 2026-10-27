module

public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.StandardType.SylowOvergroup

theorem exists_conj_ge_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {X : Subgroup G} (hX : ¬ p ∣ X.index) :
    ∃ g : G, (P : Subgroup G) ≤ X.map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨Q⟩ : Nonempty (Sylow p X) := inferInstance
  have hp : IsPGroup p ((Q : Subgroup X).map X.subtype) := Q.isPGroup'.map X.subtype
  have hidx : ¬ p ∣ ((Q : Subgroup X).map X.subtype).index := by
    have h1 : ((Q : Subgroup X).map X.subtype).relIndex X * X.index =
        ((Q : Subgroup X).map X.subtype).index :=
      Subgroup.relIndex_mul_index (Subgroup.map_subtype_le _)
    have h2 : ((Q : Subgroup X).map X.subtype).relIndex X = (Q : Subgroup X).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [← h1, h2]
    intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).mp hd with h | h
    · exact Q.not_dvd_index h
    · exact hX h
  let S : Sylow p G := hp.toSylow hidx
  have hS : (S : Subgroup G) = (Q : Subgroup X).map X.subtype := IsPGroup.toSylow_coe _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨g, fun x hx => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have h2 : g⁻¹ * x * g ∈ (S : Subgroup G) := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hx
  rw [hS] at h2
  obtain ⟨y, -, hy⟩ := h2
  refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
  · rw [← hy]
    exact y.2
  · simp [MulAut.conj_apply, mul_assoc]

theorem forall_of_sylow_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (Q : Subgroup G → Prop)
    (hQ : ∀ (g : G) (Y : Subgroup G), Q (Y.map (MulAut.conj g).toMonoidHom) → Q Y)
    (h : ∀ Y : Subgroup G, (P : Subgroup G) ≤ Y → Y ≠ ⊤ → Q Y)
    {X : Subgroup G} (hX1 : X ≠ ⊤) (hX : ¬ p ∣ X.index) : Q X := by
  obtain ⟨g, hg⟩ := exists_conj_ge_sylow P hX
  refine hQ g X (h _ hg fun htop => hX1 ?_)
  have hX' : X = (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rw [this]
      exact hy
  rw [hX', htop, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective]

theorem isSolvable_of_coprime {Y : Type*} [Group Y] [Finite Y] {a b m : ℕ}
    (hdvd : Nat.card Y ∣ 2 ^ a * 3 ^ b * m) (hcop : Nat.Coprime (Nat.card Y) m) :
    Group.IsSolvable Y := by
  have h : Nat.card Y ∣ 2 ^ a * 3 ^ b := hcop.dvd_of_dvd_mul_right hdvd
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  let := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hyz.symm)

theorem isSolvable_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Group.IsSolvable B) : Group.IsSolvable A := by
  haveI := h
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem forall_isSolvable_of_mulEquiv {K G : Type*} [Group K] [Group G] [Finite K] {p : ℕ}
    (e : K ≃* G)
    (h : ∀ X : Subgroup G, X ≠ ⊤ → ¬ p ∣ X.index → Group.IsSolvable ↥X) :
    ∀ X : Subgroup K, X ≠ ⊤ → ¬ p ∣ X.index → Group.IsSolvable ↥X := by
  intro X hX1 hX
  have hidx : (X.map e.toMonoidHom).index = X.index := Subgroup.index_map_of_bijective e.bijective X
  refine isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective)
    (h _ ?_ (by rwa [hidx]))
  rw [ne_eq, ← Subgroup.index_eq_one, hidx, Subgroup.index_eq_one]
  exact hX1

theorem forall_of_mulEquiv {K G : Type} [Group K] [Group G] [Finite K] {p : ℕ} (e : K ≃* G)
    (P : ∀ (A : Type) [Group A], Prop)
    (hP : ∀ (A B : Type) [Group A] [Group B], (A ≃* B) → P A → P B)
    (h : ∀ X : Subgroup G, X ≠ ⊤ → ¬ p ∣ X.index → P ↥X) :
    ∀ X : Subgroup K, X ≠ ⊤ → ¬ p ∣ X.index → P ↥X := by
  intro X hX1 hX
  have hidx : (X.map e.toMonoidHom).index = X.index := Subgroup.index_map_of_bijective e.bijective X
  refine hP _ _ (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective).symm
    (h _ ?_ (by rwa [hidx]))
  rw [ne_eq, ← Subgroup.index_eq_one, hidx, Subgroup.index_eq_one]
  exact hX1

section Commutator

variable {A B : Type*} [Group A] [Group B]

theorem map_commutator_mulEquiv (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

@[expose] noncomputable def commutatorEquiv (e : A ≃* B) : commutator A ≃* commutator B :=
  ((commutator A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_commutator_mulEquiv e))

end Commutator

end CFSG.StandardType.SylowOvergroup
