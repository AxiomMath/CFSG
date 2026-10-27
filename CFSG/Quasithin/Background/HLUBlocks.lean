module

public import CFSG.Quasithin.Background.HModChk

public section

namespace CFSG.Quasithin.H.LU

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

theorem mul_card_le_of_cosets {G : Type*} [Group G] {H K : Subgroup G} [Finite ↥K] (hHK : H ≤ K)
    {m : ℕ} (w : Fin m → G) (hw : ∀ i, w i ∈ K) (hd : ∀ i j, (w i)⁻¹ * w j ∈ H → i = j) :
    m * Nat.card ↥H ≤ Nat.card ↥K := by
  set H' := H.subgroupOf K
  have hinj : Function.Injective
      fun i : Fin m => (QuotientGroup.mk (⟨w i, hw i⟩ : ↥K) : ↥K ⧸ H') := by
    intro i j h
    have h1 := QuotientGroup.eq.1 h
    exact hd i j (Subgroup.mem_subgroupOf.1 h1)
  have : Finite (↥K ⧸ H') := Finite.of_surjective _ (QuotientGroup.mk_surjective)
  have h1 : m ≤ H'.index := by
    rw [Subgroup.index]
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 := Subgroup.card_mul_index H'
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at h2
  rw [← h2, mul_comm]
  exact Nat.mul_le_mul_left _ h1

theorem perm_apply_inv (σ : Equiv.Perm (Fin 24)) (x : Fin 24) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

theorem perm_inv_apply (σ : Equiv.Perm (Fin 24)) (x : Fin 24) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

variable {k : ℕ} (lab : Fin 24 → Fin k)

@[expose] def blockP : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | ∀ x y, lab (σ x) = lab (σ y) ↔ lab x = lab y}
  one_mem' _ _ := Iff.rfl
  mul_mem' {a b} ha hb x y := (ha (b x) (b y)).trans (hb x y)
  inv_mem' {a} ha x y := by
    have h := ha (a⁻¹ x) (a⁻¹ y)
    rw [perm_apply_inv, perm_apply_inv] at h
    exact h.symm

@[expose] def block0 : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | ∀ x, lab (σ x) = lab x}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb x := (ha (b x)).trans (hb x)
  inv_mem' {a} ha x := by
    have h := ha (a⁻¹ x)
    rw [perm_apply_inv] at h
    exact h.symm

theorem block0_le : block0 lab ≤ blockP lab := fun σ hσ x y => by
  show lab (σ x) = lab (σ y) ↔ lab x = lab y
  rw [hσ x, hσ y]

variable {lab} {rep : Fin k → Fin 24} (hrep : ∀ i, lab (rep i) = i)

include hrep in
theorem lab_of_mem {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ blockP lab) (x : Fin 24) :
    lab (σ x) = lab (σ (rep (lab x))) :=
  (hσ x (rep (lab x))).2 (hrep _).symm

@[expose] def blockFun (rep : Fin k → Fin 24) (σ : Equiv.Perm (Fin 24)) (i : Fin k) : Fin k :=
  lab (σ (rep i))

include hrep in
theorem blockFun_lab {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ blockP lab) (x : Fin 24) :
    lab (σ x) = blockFun (lab := lab) rep σ (lab x) :=
  lab_of_mem hrep hσ x

@[expose] def blockHom : ↥(blockP lab) →* Equiv.Perm (Fin k) where
  toFun σ :=
    { toFun := blockFun (lab := lab) rep σ
      invFun := blockFun (lab := lab) rep (σ⁻¹ : ↥(blockP lab))
      left_inv := fun i => by
        show lab ((σ : Equiv.Perm (Fin 24))⁻¹
          (rep (lab ((σ : Equiv.Perm (Fin 24)) (rep i))))) = i
        rw [← lab_of_mem hrep ((blockP lab).inv_mem σ.2), perm_inv_apply, hrep]
      right_inv := fun i => by
        show lab ((σ : Equiv.Perm (Fin 24))
          (rep (lab ((σ : Equiv.Perm (Fin 24))⁻¹ (rep i))))) = i
        rw [← lab_of_mem hrep σ.2, perm_apply_inv, hrep] }
  map_one' := Equiv.ext fun i => hrep i
  map_mul' σ τ := Equiv.ext fun i =>
    blockFun_lab hrep σ.2 ((τ : Equiv.Perm (Fin 24)) (rep i))

theorem blockHom_apply (σ : ↥(blockP lab)) (i : Fin k) :
    blockHom hrep σ i = lab ((σ : Equiv.Perm (Fin 24)) (rep i)) := rfl

include hrep in
theorem perfectCore_blockP_le (hk : k ≤ 4) : perfectCore (blockP lab) ≤ block0 lab := by
  have hS : Group.IsSolvable (Equiv.Perm (Fin k)) := Equiv.Perm.isSolvable (by simpa using hk)
  have h1 : perfectCore (⊤ : Subgroup ↥(blockP lab)) ≤ (blockHom hrep).ker := by
    have h2 : (perfectCore (⊤ : Subgroup ↥(blockP lab))).map (blockHom hrep) = ⊥ := by
      rw [map_perfectCore, ← (isSolvable_iff_perfectCore_eq_bot _).1]
      infer_instance
    rwa [Subgroup.map_eq_bot_iff] at h2
  have h3 : perfectCore (blockP lab) =
      (perfectCore (⊤ : Subgroup ↥(blockP lab))).map (blockP lab).subtype := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h3]
  rintro _ ⟨σ, hσ, rfl⟩ x
  have hk' : blockHom hrep σ = 1 := h1 hσ
  show lab ((σ : Equiv.Perm (Fin 24)) x) = lab x
  rw [blockFun_lab hrep σ.2 x]
  exact congrArg (fun π : Equiv.Perm (Fin k) => π (lab x)) hk'

@[expose] def blockEven : Subgroup (Equiv.Perm (Fin 24)) :=
  ((Equiv.Perm.sign.comp (blockHom hrep)).ker).map (blockP lab).subtype

theorem mem_blockEven {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ blockP lab)
    (h : Equiv.Perm.sign (blockHom hrep ⟨σ, hσ⟩) = 1) : σ ∈ blockEven hrep :=
  ⟨⟨σ, hσ⟩, h, rfl⟩

theorem not_mem_blockEven {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ blockP lab)
    (h : Equiv.Perm.sign (blockHom hrep ⟨σ, hσ⟩) ≠ 1) : σ ∉ blockEven hrep := by
  rintro ⟨τ, hτ, rfl⟩
  exact h hτ

variable (labL : List ℕ) (hlab : ∀ x : Fin 24, ((lab x : Fin k) : ℕ) = labL.getD x 0)

include hlab in
theorem mem_blockP_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (h : ∀ x y : Fin 24, (labL.getD a[(x : ℕ)]! 0 = labL.getD a[(y : ℕ)]! 0 ↔
      labL.getD x 0 = labL.getD y 0)) : σ ∈ blockP lab := fun x y => by
  rw [Fin.ext_iff, Fin.ext_iff, hlab, hlab, hlab, hlab, ha, ha]
  exact h x y

include hlab in
theorem mem_block0_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (h : ∀ x : Fin 24, labL.getD a[(x : ℕ)]! 0 = labL.getD x 0) : σ ∈ block0 lab := fun x => by
  rw [Fin.ext_iff, hlab, hlab, ha]
  exact h x

include hlab in
theorem eq_of_inv_mul_mem_block0 {σ τ : Equiv.Perm (Fin 24)} (hσ : σ ∈ blockP lab)
    (h : σ⁻¹ * τ ∈ block0 lab) (x : Fin 24) : labL.getD (τ x) 0 = labL.getD (σ x) 0 := by
  have h1 : lab (σ ((σ⁻¹ * τ) x)) = lab (σ x) := (hσ _ _).2 (h x)
  rw [Equiv.Perm.mul_apply, perm_apply_inv] at h1
  rw [← hlab, ← hlab, h1]

end CFSG.Quasithin.H.LU
