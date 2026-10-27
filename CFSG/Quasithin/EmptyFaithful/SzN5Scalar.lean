module

public import CFSG.Quasithin.EmptyFaithful.SzN4Local

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Scalar

variable {G : Type} [Group G]

theorem szN5_scalar_action {L : Subgroup G} {F : Type} [Field F]
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L)
    (β : ↥(blockU L) →* Multiplicative (Fin 2 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβc : ∀ ℓ : ↥L, ∀ u v : ↥(blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {c : G} (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) :
    ∃ a : F, ∀ u : ↥(blockU L), ∀ hu' : c * (u : G) * c⁻¹ ∈ blockU L,
      Multiplicative.toAdd (β ⟨c * (u : G) * c⁻¹, hu'⟩) = a • Multiplicative.toAdd (β u) := by
  have hcU : ∀ u ∈ blockU L, c * u * c⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hcN) u).mp hu
  let φ : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun u => ⟨c * u * c⁻¹, hcU u u.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hker : β.ker ≤ (β.comp φ).ker := by
    intro u hu
    rw [hβk] at hu
    have hu' : (u : G) ∈ blockZ L := Subgroup.mem_subgroupOf.mp hu
    rw [MonoidHom.mem_ker]
    show β (φ u) = 1
    have : φ u ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact ⟨hcU u u.2, szN4_conj_mem_centralizer hcN hu'.2⟩
    exact MonoidHom.mem_ker.mp this
  let Θ' : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
    (MonoidHom.liftOfRightInverse β (Function.surjInv hβs) (Function.rightInverse_surjInv hβs))
      ⟨β.comp φ, hker⟩
  have hΘ'β : ∀ u : ↥(blockU L), Θ' (β u) = β (φ u) := fun u => by
    simp [Θ', MonoidHom.liftOfRightInverse_comp_apply]
  let Θ : (Fin 2 → F) → (Fin 2 → F) := fun v => Multiplicative.toAdd (Θ' (Multiplicative.ofAdd v))
  have hΘ : ∀ u : ↥(blockU L),
      Θ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (φ u)) := by
    intro u
    simp only [Θ, ofAdd_toAdd]
    rw [hΘ'β]
  have hadd : ∀ v w, Θ (v + w) = Θ v + Θ w := by
    intro v w
    simp only [Θ]
    rw [ofAdd_add, map_mul, toAdd_mul]
  have hcomm : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∀ v : Fin 2 → F,
      Θ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A : Matrix (Fin 2) (Fin 2) F).mulVec (Θ v) := by
    intro A v
    obtain ⟨ℓ, rfl⟩ := hαs A
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ℓ.2
    have hu'mem : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hℓN) u).mp u.2
    let u' : ↥(blockU L) := ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hu'mem⟩
    have h1 : Multiplicative.toAdd (β u') = (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec v := by
      rw [hβc ℓ u u' rfl, hu]; simp
    have hℓ'L : c * (ℓ : G) * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcN (ℓ : G)).mp ℓ.2
    let ℓ' : ↥L := ⟨c * (ℓ : G) * c⁻¹, hℓ'L⟩
    have hαℓ' : α ℓ' = α ℓ := by
      have hmem : ℓ' * ℓ⁻¹ ∈ α.ker := by
        rw [hαk, szN4_mem_pCore_iff]
        exact hcQ (ℓ : G) ℓ.2
      have := MonoidHom.mem_ker.mp hmem
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    have h2 : Multiplicative.toAdd (β (φ u')) =
        (α ℓ' : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β (φ u))) := by
      refine hβc ℓ' (φ u) (φ u') ?_
      show c * ((ℓ : G) * u * (ℓ : G)⁻¹) * c⁻¹ =
        (c * (ℓ : G) * c⁻¹) * (c * (u : G) * c⁻¹) * (c * (ℓ : G) * c⁻¹)⁻¹
      group
    calc Θ ((α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec v) = Θ (Multiplicative.toAdd (β u')) := by
          rw [h1]
      _ = Multiplicative.toAdd (β (φ u')) := hΘ u'
      _ = (α ℓ' : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β (φ u))) := h2
      _ = (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Θ v) := by
          rw [hαℓ', ← hΘ u, hu]; simp
  obtain ⟨a, ha⟩ := szN4_scalar_of_commute Θ hadd hcomm
  refine ⟨a, fun u hu' => ?_⟩
  have h := hΘ u
  rw [ha] at h
  exact h.symm

end Scalar

end CFSG.Quasithin
