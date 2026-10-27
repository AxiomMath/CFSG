module

public import CFSG.RankThree.GroupTheory.SteinbergCECentralThetaQuasisimple

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank

theorem map_inSubgroup_aschbacherSolvableCore_mulEquiv {G G' : Type*} [Group G] [Group G']
    [Finite G] {p : ℕ} (hp : p.Prime) (φ : G ≃* G') (X : Subgroup G) :
    (inSubgroup (aschbacherSolvableCore p) X).map φ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore p) (X.map φ.toMonoidHom) := by
  rw [inSubgroup, inSubgroup,
    ← aschbacherSolvableCore_map_mulEquiv hp (X.equivMapOfInjective φ.toMonoidHom φ.injective),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem mulAut_conj_apply_eq {C : Type*} [Group C] (β : MulAut C) (d : C) :
    MulAut.conj (β d) = β * MulAut.conj d * β⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem automorphism_centralizer_trivial_theta_core_fixed_components {C : Type*} [Group C]
    [Finite C] {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut C)}
    (hInn : (MulAut.conj : C →* MulAut C).range ≤ B) (α : MulAut C)
    (hθ : aschbacherSolvableCore p
      (B ⊓ Subgroup.centralizer ({α} : Set (MulAut C)) : Subgroup (MulAut C)) = ⊥) :
    inSubgroup (aschbacherSolvableCore p) (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id C)) ≤
        Subgroup.center C ∧
      ∀ L ∈ thetaComponents p (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id C)),
        IsQuasisimple L := by
  set Hc := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id C) with hHc
  set Q : Subgroup (MulAut C) := B ⊓ Subgroup.centralizer ({α} : Set (MulAut C)) with hQ
  set D := inSubgroup (aschbacherSolvableCore p) Hc with hD
  have hmemHc : ∀ x : C, x ∈ Hc ↔ α x = x := fun _ => Iff.rfl
  have hDα : ∀ d ∈ D, α d = d := fun d hd => (hmemHc d).mp (Subgroup.map_subtype_le _ hd)
  have hcore := solvable_prime_complement_core_characterization (H := Hc) hp
  have hconjQ : D.map (MulAut.conj : C →* MulAut C) ≤ Q := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨hInn ⟨d, rfl⟩, ?_⟩
    show MulAut.conj d ∈ Subgroup.centralizer ({α} : Set (MulAut C))
    rw [Subgroup.mem_centralizer_singleton_iff]
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hDα d hd]
  have hβD : ∀ β ∈ Q, ∀ d ∈ D, β d ∈ D := by
    intro β hβ d hd
    have hβα : β * α = α * β := Subgroup.mem_centralizer_singleton_iff.mp hβ.2
    have hHβ : Hc.map β.toMonoidHom = Hc := by
      ext x
      rw [Subgroup.mem_map_equiv, hmemHc, hmemHc]
      have hc : α (β.symm x) = β.symm (α x) := by
        have h := congrArg (fun γ : MulAut C => γ (β.symm x)) hβα
        simp only [MulAut.mul_apply, MulEquiv.apply_symm_apply] at h
        apply β.injective
        rw [MulEquiv.apply_symm_apply, ← h]
      rw [hc]
      exact ⟨fun h => by simpa using congrArg β h, fun h => by rw [h]⟩
    have h := map_inSubgroup_aschbacherSolvableCore_mulEquiv hp β Hc
    rw [hHβ] at h
    have h' : D.map β.toMonoidHom = D := h
    rw [← h']
    exact Subgroup.mem_map_of_mem β.toMonoidHom hd
  set D₀ : Subgroup Q := (D.map (MulAut.conj : C →* MulAut C)).subgroupOf Q with hD₀
  have hD₀n : D₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨d, hd, hdn⟩ := hn
    change ((g * n * g⁻¹ : Q) : MulAut C) ∈ D.map (MulAut.conj : C →* MulAut C)
    refine ⟨(g : MulAut C) d, hβD g g.2 d hd, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mulAut_conj_apply_eq]
    exact congrArg (fun γ => (g : MulAut C) * γ * (g : MulAut C)⁻¹) hdn
  have hDs : Group.IsSolvable D := by
    have := hcore.1
    exact Group.isSolvable_of_surjective (Hc.subtype.subgroupMap_surjective _)
  have hD₀s : Group.IsSolvable D₀ := by
    have : Group.IsSolvable (D.map (MulAut.conj : C →* MulAut C)) :=
      Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ D)
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hconjQ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hconjQ).symm.surjective
  have hD₀p : ¬ p ∣ Nat.card D₀ := by
    intro h
    apply hcore.2.2.1
    have h1 : Nat.card D₀ = Nat.card (D.map (MulAut.conj : C →* MulAut C)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconjQ).toEquiv
    have h2 : Nat.card D = Nat.card (aschbacherSolvableCore p Hc) :=
      Subgroup.card_map_of_injective Hc.subtype_injective
    rw [h1] at h
    exact h2 ▸ h.trans (Subgroup.card_map_dvd _ _)
  have hD₀bot : D₀ ≤ ⊥ := by
    have := (solvable_prime_complement_core_characterization (H := Q) hp).2.2.2.1 D₀ hD₀n hD₀s
      hD₀p
    rwa [hθ] at this
  have hDZ : D ≤ Subgroup.center C := by
    intro d hd
    have hmem : (⟨MulAut.conj d, hconjQ ⟨d, hd, rfl⟩⟩ : Q) ∈ D₀ := ⟨d, hd, rfl⟩
    have h1 := hD₀bot hmem
    rw [Subgroup.mem_bot] at h1
    have h2 : MulAut.conj d = 1 := congrArg Subtype.val h1
    rw [Subgroup.mem_center_iff]
    intro x
    have h3 := congrArg (fun γ : MulAut C => γ x) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc x * d = d * x * d⁻¹ * d := by rw [h3]
      _ = d * x := by group
  refine ⟨hDZ, central_theta_core_components_quasisimple hp fun y hy => ?_⟩
  have hyZ := hDZ (Subgroup.mem_map_of_mem Hc.subtype hy)
  exact Subgroup.mem_center_iff.mpr fun z => Subtype.ext (Subgroup.mem_center_iff.mp hyZ z)

end CFSG.RankThree.GroupTheory.SteinbergBY
