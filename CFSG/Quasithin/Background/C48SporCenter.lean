module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open

theorem eq_one_of_commute_of_orbit {α : Type*} {c σ : Equiv.Perm α} {x₀ : α} {p m : ℕ}
    (horb : ∀ x, ∃ i : ℕ, (c ^ i) x₀ = x) (hcp : c ^ p = 1) (hcomm : Commute σ c)
    (h2 : σ ^ (2 ^ m) = 1) (hp : Nat.Coprime (2 ^ m) p) : σ = 1 := by
  obtain ⟨k, hk⟩ := horb (σ x₀)
  have hσ : σ = c ^ k := by
    ext x
    obtain ⟨i, rfl⟩ := horb x
    have h1 : σ ((c ^ i) x₀) = (c ^ i) (σ x₀) := by
      have := (hcomm.pow_right i).eq
      exact congrArg (fun f : Equiv.Perm α => f x₀) this
    rw [h1, ← hk]
    change (c ^ i * c ^ k) x₀ = (c ^ k * c ^ i) x₀
    rw [← pow_add, ← pow_add, add_comm]
  have hp' : σ ^ p = 1 := by rw [hσ, ← pow_mul, mul_comm, pow_mul, hcp, one_pow]
  have := pow_gcd_eq_one.mpr ⟨h2, hp'⟩
  rwa [hp, pow_one] at this

@[expose] def m23c : Equiv.Perm (Fin 23) :=
  (List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]) *
  (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16])

theorem m23c_mem : m23c ∈ CFSG.Blueprint.NativeSporadic.M23 :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem m23c_pow : m23c ^ 23 = 1 := by decide +kernel

theorem m23c_orbit : ∀ x : Fin 23, ∃ i : Fin 23, (m23c ^ (i : ℕ)) 0 = x := by decide +kernel

theorem center_eq_bot_m23 {K : Type*} [Group K]
    (e : K ≃* ↥CFSG.Blueprint.NativeSporadic.M23) (hZ : IsPGroup 2 ↥(Subgroup.center K)) :
    Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨m, hm⟩ := hZ ⟨z, hz⟩
  have hc : Commute ((e z : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) m23c := by
    have hez : e z ∈ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M23 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz k)]
    have := Subgroup.mem_center_iff.mp hez ⟨m23c, m23c_mem⟩
    exact (congrArg Subtype.val this).symm
  have h2 : ((e z : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) ^ (2 ^ m) = 1 := by
    have : (e z) ^ (2 ^ m) = 1 := by
      rw [← map_pow]
      have : z ^ (2 ^ m) = 1 := congrArg Subtype.val hm
      rw [this, map_one]
    exact congrArg Subtype.val this
  have h1 := eq_one_of_commute_of_orbit (x₀ := 0)
    (fun x => by obtain ⟨i, hi⟩ := m23c_orbit x; exact ⟨i, hi⟩) m23c_pow hc h2
    (Nat.Coprime.pow_left _ (by norm_num))
  have : e z = 1 := Subtype.ext h1
  rw [Subgroup.mem_bot]
  exact e.injective (this.trans (map_one e).symm)

theorem eq_one_of_commute_of_orbit_fix {α : Type*} {c σ : Equiv.Perm α} {x₀ x₁ : α} {p m : ℕ}
    (hfix : ∀ x, c x = x → x = x₁) (hc₁ : c x₁ = x₁)
    (horb : ∀ x, x ≠ x₁ → ∃ i : ℕ, (c ^ i) x₀ = x) (hx₀ : x₀ ≠ x₁)
    (hcp : c ^ p = 1) (hcomm : Commute σ c) (h2 : σ ^ (2 ^ m) = 1) (hp : Nat.Coprime (2 ^ m) p) :
    σ = 1 := by
  have hcomm' : ∀ i : ℕ, ∀ y, σ ((c ^ i) y) = (c ^ i) (σ y) := fun i y =>
    congrArg (fun f : Equiv.Perm α => f y) (hcomm.pow_right i).eq
  have hσ₁ : σ x₁ = x₁ := hfix _ (by
    have := hcomm' 1 x₁
    simp only [pow_one, hc₁] at this
    exact this.symm)
  have hσ₀ : σ x₀ ≠ x₁ := fun h => hx₀ (σ.injective (h.trans hσ₁.symm))
  obtain ⟨k, hk⟩ := horb (σ x₀) hσ₀
  have hck : ∀ i : ℕ, (c ^ i) x₁ = x₁ := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, Equiv.Perm.mul_apply, hc₁, ih]
  have hσ : σ = c ^ k := by
    ext x
    by_cases hx : x = x₁
    · rw [hx, hσ₁, hck]
    obtain ⟨i, rfl⟩ := horb x hx
    rw [hcomm' i x₀, ← hk]
    change (c ^ i * c ^ k) x₀ = (c ^ k * c ^ i) x₀
    rw [← pow_add, ← pow_add, add_comm]
  have hp' : σ ^ p = 1 := by rw [hσ, ← pow_mul, mul_comm, pow_mul, hcp, one_pow]
  have := pow_gcd_eq_one.mpr ⟨h2, hp'⟩
  rwa [hp, pow_one] at this

@[expose] def m24c : Equiv.Perm (Fin 24) :=
  (List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
    List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
    List.formPerm [19, 23] * List.formPerm [21, 22]) *
  (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22])

theorem m24c_mem : m24c ∈ CFSG.Blueprint.NativeSporadic.M24 :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem m24c_pow : m24c ^ 23 = 1 := by decide +kernel

theorem m24c_fix : ∀ x : Fin 24, m24c x = x → x = 0 := by decide +kernel

theorem m24c_fix0 : m24c 0 = 0 := by decide +kernel

theorem m24c_orbit : ∀ x : Fin 24, x ≠ 0 → ∃ i : Fin 23, (m24c ^ (i : ℕ)) 1 = x := by decide +kernel

theorem center_eq_bot_m24 {K : Type*} [Group K]
    (e : K ≃* ↥CFSG.Blueprint.NativeSporadic.M24) (hZ : IsPGroup 2 ↥(Subgroup.center K)) :
    Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨m, hm⟩ := hZ ⟨z, hz⟩
  have hc : Commute ((e z : ↥CFSG.Blueprint.NativeSporadic.M24) : Equiv.Perm (Fin 24)) m24c := by
    have hez : e z ∈ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M24 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz k)]
    have := Subgroup.mem_center_iff.mp hez ⟨m24c, m24c_mem⟩
    exact (congrArg Subtype.val this).symm
  have h2 : ((e z : ↥CFSG.Blueprint.NativeSporadic.M24) : Equiv.Perm (Fin 24)) ^ (2 ^ m) = 1 := by
    have : (e z) ^ (2 ^ m) = 1 := by
      rw [← map_pow]
      have : z ^ (2 ^ m) = 1 := congrArg Subtype.val hm
      rw [this, map_one]
    exact congrArg Subtype.val this
  have h1 := eq_one_of_commute_of_orbit_fix (x₀ := 1) (x₁ := 0) m24c_fix m24c_fix0
    (fun x hx => by obtain ⟨i, hi⟩ := m24c_orbit x hx; exact ⟨i, hi⟩) (by decide) m24c_pow hc h2
    (Nat.Coprime.pow_left _ (by norm_num))
  have : e z = 1 := Subtype.ext h1
  rw [Subgroup.mem_bot]
  exact e.injective (this.trans (map_one e).symm)

theorem center_eq_bot_of_simple {K X : Type*} [Group K] [Group X] [IsSimpleGroup X]
    (e : K ≃* X) (hK : CFSG.Open.IsQuasisimple K) : Subgroup.center K = ⊥ := by
  have : IsSimpleGroup K := MulEquiv.isSimpleGroup e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hcomm : commutator K = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer, ← h]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x)) y)
    have htop : (⊤ : Subgroup K) = ⊥ := hK.1.symm.trans hcomm
    obtain ⟨a, b, hab⟩ := (inferInstance : IsSimpleGroup K).toNontrivial
    apply hab
    have ha : a ∈ (⊥ : Subgroup K) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup K) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

theorem center_eq_bot_j4 {X : Type} [Group X]
    (h : IsSporadic .J4 X) (hX : CFSG.Open.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.isSimpleGroup_J4
  exact center_eq_bot_of_simple e hX

theorem center_eq_bot_he {X : Type} [Group X]
    (h : IsSporadic .He X) (hX : CFSG.Open.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  exact center_eq_bot_of_simple e hX

end CFSG.Quasithin.C48Spor
