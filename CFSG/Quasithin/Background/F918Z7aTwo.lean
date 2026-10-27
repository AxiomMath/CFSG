module

public import CFSG.Quasithin.Background.F918Z6Symm
public import CFSG.Quasithin.Background.F918Z4e
public import CFSG.Quasithin.Background.F918Z5B2

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace Z7a

theorem isPerfect_of_simple_nonab {G : Type} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h0 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h1

theorem nonab_subtype {V : Type} [CommGroup V] {D : Subgroup (MulAut V)}
    (h : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a) : ∃ a b : ↥D, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

end Z7a

theorem z37_dim_ne_one {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}
    {s : MulAut V} (hZ : Z37 D X G T' s) {F : Type} [Field F]
    (β : V ≃* Multiplicative (Matrix (Fin 1) (Fin 1) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 1) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin 1) F) (hM : IsMatModel D X β ρ σ) : False := by
  obtain ⟨a, ha, b, hb, hab⟩ := hZ.nonab
  apply hab
  have hcomm : ρ ⟨a, ha⟩ * ρ ⟨b, hb⟩ = ρ ⟨b, hb⟩ * ρ ⟨a, ha⟩ := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  rw [← map_mul, ← map_mul] at hcomm
  exact congrArg Subtype.val (hM.rho_injective hcomm)

theorem z37Concl_of_sqModel_two
    {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
    (hZ : Z37 D X G T' s) {F : Type} [Field F] [Finite F] [CharP F 2]
    (β : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 2) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) (hM : IsMatModel D X β ρ σ) :
    Z37Concl D X := by
  have hZX : Z37 X D G T' s := hZ.symm
  have : IsSimpleGroup ↥D := hZ.simple
  have : IsSimpleGroup ↥X := hZX.simple
  obtain ⟨n, hn⟩ := exists_psl2_of_faithful_two hZ.typeD (Z7a.nonab_subtype hZ.nonab) ρ
    hM.rho_injective
  have : Group.IsPerfect ↥D := Z7a.isPerfect_of_simple_nonab (Z7a.nonab_subtype hZ.nonab)
  have : Group.IsPerfect ↥X := Z7a.isPerfect_of_simple_nonab (Z7a.nonab_subtype hZX.nonab)
  exact Or.inl (omega4Plus_of_sqModel_two hZ.comm β ρ σ hM inferInstance inferInstance hn
    ⟨conjEquivOfEq hZ.swapDX⟩)

end CFSG.Quasithin
