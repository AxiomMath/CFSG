module

public import CFSG.Quasithin.Vol2.Ch10SecBCoord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Vol2.Ch10SecC8V1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

theorem exists_L3Data_twist {V : Type*} [CommGroup V] {Gm : Subgroup (MulAut V)}
    {U Z : Subgroup V} (D : L3Data Gm U Z) (γ0 : L3.Γ) :
    ∃ D' : L3Data Gm U Z, ∀ γ, D'.π γ = D.π (γ0 * γ * γ0⁻¹) := by
  let f : Multiplicative L3.Vec →* Multiplicative L3.Vec :=
    { toFun := fun v => Multiplicative.ofAdd (L3.act γ0⁻¹ (Multiplicative.toAdd v))
      map_one' := by
        change Multiplicative.ofAdd (L3.act γ0⁻¹ 0) = 1
        rw [L3.act_zero]
        rfl
      map_mul' := fun a b => by
        change Multiplicative.ofAdd
          (L3.act γ0⁻¹ (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
        rw [L3.act_add]
        rfl }
  refine ⟨{ π := D.π.comp (MulAut.conj γ0).toMonoidHom
            β := f.comp D.β
            π_surj := D.π_surj.comp (MulAut.conj γ0).surjective
            β_surj := fun y => ?_
            ker_β := fun u => ?_
            Z_le := D.Z_le
            inv_U := D.inv_U
            inv_Z := D.inv_Z
            equi := fun γ u hu => ?_ }, fun γ => rfl⟩
  · obtain ⟨x, hx⟩ := D.β_surj (Multiplicative.ofAdd (L3.act γ0 (Multiplicative.toAdd y)))
    refine ⟨x, ?_⟩
    change Multiplicative.ofAdd (L3.act γ0⁻¹ (Multiplicative.toAdd (D.β x))) = y
    rw [hx, toAdd_ofAdd, L3.act_inv_act]
    rfl
  · rw [← D.ker_β u]
    change Multiplicative.ofAdd (L3.act γ0⁻¹ (Multiplicative.toAdd (D.β u))) = 1 ↔ D.β u = 1
    constructor
    · intro h
      have h1 : L3.act γ0⁻¹ (Multiplicative.toAdd (D.β u)) = 0 := congrArg Multiplicative.toAdd h
      have h2 := congrArg (L3.act γ0) h1
      rw [L3.act_act_inv, L3.act_zero] at h2
      exact congrArg Multiplicative.ofAdd h2
    · intro h
      rw [h]
      change Multiplicative.ofAdd (L3.act γ0⁻¹ 0) = 1
      rw [L3.act_zero]
      rfl
  · change Multiplicative.ofAdd (L3.act γ0⁻¹ (Multiplicative.toAdd
        (D.β ⟨((D.π (γ0 * γ * γ0⁻¹) : ↥Gm) : MulAut V) (u : V), hu⟩))) =
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd
        (Multiplicative.ofAdd (L3.act γ0⁻¹ (Multiplicative.toAdd (D.β u))))))
    rw [D.equi (γ0 * γ * γ0⁻¹) u hu, toAdd_ofAdd, toAdd_ofAdd, ← L3.act_mul, ← L3.act_mul,
      show γ0⁻¹ * (γ0 * γ * γ0⁻¹) = γ * γ0⁻¹ by group]

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_L3Data_U3 (hyp : Hyp10 G T L I) [IsMulCommutative ↥(fsuUL T L I)]
    (D0 : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I)) :
    ∃ D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I), ∀ γ,
      ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
        autOn (T ⊓ L) (fsuUL T L I) ↔ γ ∈ SecB.L32.U3 := by
  have hP : QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) (fsuUL T L I))
      (autOn L (fsuUL T L I)) :=
    QuasithinUnique.Setup.isSylowTwoOf_autOn (SecA.isSylowTwoOf_inf hyp.fsu.maximal.1)
      (le_normalizer_fsuUL T L I)
  let e : ↥(autOn L (fsuUL T L I)) ≃* L3.Γ :=
    (MulEquiv.ofBijective D0.π ⟨D0.π_injective, D0.π_surj⟩).symm
  have hS := SecB.isSylowTwoOf_map_of_surjective hP e.toMonoidHom e.surjective
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf SecB.isSylowTwoOf_U3 hS
  obtain ⟨D, hD⟩ := exists_L3Data_twist D0 g
  refine ⟨D, fun γ => ?_⟩
  rw [hD γ]
  have h1 := hg (g * γ * g⁻¹)
  have e1 : g⁻¹ * (g * γ * g⁻¹) * g = γ := by group
  rw [e1] at h1
  rw [← h1, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨D0.π (g * γ * g⁻¹), Subgroup.mem_subgroupOf.mpr h, ?_⟩
    change (MulEquiv.ofBijective D0.π ⟨D0.π_injective, D0.π_surj⟩).symm _ = _
    rw [MulEquiv.symm_apply_eq]
    rfl
  · rintro ⟨a, ha, hae⟩
    have h2 : a = D0.π (g * γ * g⁻¹) := by
      rw [← hae]
      change a = (MulEquiv.ofBijective D0.π ⟨D0.π_injective, D0.π_surj⟩)
        ((MulEquiv.ofBijective D0.π ⟨D0.π_injective, D0.π_surj⟩).symm a)
      rw [MulEquiv.apply_symm_apply]
    rw [← h2]
    exact Subgroup.mem_subgroupOf.mp ha

end CFSG.Quasithin.Vol2.Ch10.SecC
