module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.StandardType.AltSix

noncomputable def permSixOfMem {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j) (m : ↥M) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (fun i => Classical.choose (hstab m m.2 i))
    (by
      have hinj : Function.Injective (fun i => Classical.choose (hstab m m.2 i)) := by
        intro i j h
        change Classical.choose (hstab m m.2 i) = Classical.choose (hstab m m.2 j) at h
        have hi : (m : Equiv.Perm α) (o i) = o (Classical.choose (hstab m m.2 i)) :=
          Classical.choose_spec (hstab m m.2 i)
        have hj : (m : Equiv.Perm α) (o j) = o (Classical.choose (hstab m m.2 j)) :=
          Classical.choose_spec (hstab m m.2 j)
        exact ho ((m : Equiv.Perm α).injective (by rw [hi, h, ← hj]))
      exact hinj.bijective_of_finite)

theorem permSixOfMem_apply {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j) (m : ↥M) (i : Fin 6) :
    (m : Equiv.Perm α) (o i) = o (permSixOfMem M o ho hstab m i) :=
  Classical.choose_spec (hstab m m.2 i)

theorem permSixOfMem_one {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j) :
    permSixOfMem M o ho hstab 1 = 1 := by
  refine Equiv.ext (fun i => ho ?_)
  simp [← permSixOfMem_apply, Equiv.Perm.one_apply]

theorem permSixOfMem_mul {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j) (m m' : ↥M) :
    permSixOfMem M o ho hstab (m * m') =
      permSixOfMem M o ho hstab m * permSixOfMem M o ho hstab m' := by
  refine Equiv.ext (fun i => ho ?_)
  simp [← permSixOfMem_apply, Equiv.Perm.mul_apply]

noncomputable def permSixHom {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j) : ↥M →* Equiv.Perm (Fin 6) where
  toFun := permSixOfMem M o ho hstab
  map_one' := permSixOfMem_one M o ho hstab
  map_mul' := permSixOfMem_mul M o ho hstab

theorem permSixHom_injective {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j)
    (hfaith : ∀ m ∈ M, (∀ i, m (o i) = o i) → m = 1) :
    Function.Injective (permSixHom M o ho hstab) := by
  intro m n hmn
  have hfix : ∀ i, ((m * n⁻¹ : ↥M) : Equiv.Perm α) (o i) = o i := by
    intro i
    have hker : permSixHom M o ho hstab (m * n⁻¹) = 1 := by
      rw [map_mul, hmn, map_inv, mul_inv_cancel]
    have hpoint : permSixOfMem M o ho hstab (m * n⁻¹) i = i := by
      have hker' : permSixOfMem M o ho hstab (m * n⁻¹) = 1 := hker
      have := congrArg (fun f : Equiv.Perm (Fin 6) => f i) hker'
      simpa using this
    rw [permSixOfMem_apply M o ho hstab (m * n⁻¹) i, hpoint]
  have h1 : (m * n⁻¹ : ↥M) = 1 :=
    Subtype.ext (by
      simpa using hfaith ((m * n⁻¹ : ↥M) : Equiv.Perm α) (m * n⁻¹).2 hfix)
  have hmn' : m = n := by
    rw [← mul_one m, ← inv_mul_cancel n, ← mul_assoc, h1, one_mul]
  exact hmn'

theorem permSixHom_mem_alternatingGroup {α : Type} (M : Subgroup (Equiv.Perm α))
    (o : Fin 6 → α) (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j)
    (hperf : commutator ↥M = ⊤) (m : ↥M) :
    permSixHom M o ho hstab m ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  haveI : IsMulCommutative ℤˣ :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  have hle := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign.comp (permSixHom M o ho hstab))
  rw [hperf] at hle
  have hm : (Equiv.Perm.sign.comp (permSixHom M o ho hstab)) m = 1 := by
    simpa [MonoidHom.mem_ker] using hle (Subgroup.mem_top m)
  simpa using hm

noncomputable def permSixAltHom {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j)
    (hperf : commutator ↥M = ⊤) : ↥M →* alternatingGroup (Fin 6) :=
  (permSixHom M o ho hstab).codRestrict (alternatingGroup (Fin 6))
    (permSixHom_mem_alternatingGroup M o ho hstab hperf)

theorem permSixAltHom_injective {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j)
    (hfaith : ∀ m ∈ M, (∀ i, m (o i) = o i) → m = 1)
    (hperf : commutator ↥M = ⊤) :
    Function.Injective (permSixAltHom M o ho hstab hperf) := by
  have h := (MonoidHom.injective_codRestrict (permSixHom M o ho hstab)
      (alternatingGroup (Fin 6))
      (permSixHom_mem_alternatingGroup M o ho hstab hperf)).mpr
      (permSixHom_injective M o ho hstab hfaith)
  simpa [permSixAltHom] using h

theorem permSixAltHom_bijective {α : Type} (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α)
    (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j)
    (hfaith : ∀ m ∈ M, (∀ i, m (o i) = o i) → m = 1)
    (hperf : commutator ↥M = ⊤) (hcard : Nat.card ↥M = 360) :
    Function.Bijective (permSixAltHom M o ho hstab hperf) := by
  refine (permSixAltHom_injective M o ho hstab hfaith hperf).bijective_of_nat_card_le ?_
  rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem nonempty_mulEquiv_alternatingGroup_fin_six {α : Type} [DecidableEq α]
    (M : Subgroup (Equiv.Perm α)) (o : Fin 6 → α) (ho : Function.Injective o)
    (hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j)
    (hfaith : ∀ m ∈ M, (∀ i, m (o i) = o i) → m = 1)
    (hperf : commutator ↥M = ⊤) (hcard : Nat.card ↥M = 360) :
    Nonempty (↥M ≃* alternatingGroup (Fin 6)) :=
  ⟨MulEquiv.ofBijective (permSixAltHom M o ho hstab hperf)
    (permSixAltHom_bijective M o ho hstab hfaith hperf hcard)⟩

end CFSG.StandardType.AltSix
