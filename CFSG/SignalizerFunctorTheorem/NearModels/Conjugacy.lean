module

public import CFSG.Open.SignalizerFunctorDefs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.NearModels

private theorem apply_eq_of_mem_zpowers {X : Type*} [Group X] {a b : MulAut X}
    (hb : b ∈ Subgroup.zpowers a) {x : X} (hx : a x = x) : b x = x := by
  have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut X) x := by
    rw [Subgroup.zpowers_le]
    exact hx
  exact hle hb

private theorem exists_sylow_eq_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hbound : ∀ P : Subgroup G, IsPGroup p P → Nat.card P ∣ p) {g : G} (hg : orderOf g = p) :
    ∃ S : Sylow p G, (S : Subgroup G) = Subgroup.zpowers g := by
  have hzp : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
  have h1 : Nat.card (S : Subgroup G) ≤ p :=
    Nat.le_of_dvd (Fact.out : p.Prime).pos (hbound _ S.isPGroup')
  rwa [Nat.card_zpowers, hg]

theorem signalizerFixedSubgroup_mulEquiv_of_orderOf_eq {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hbound : ∀ P : Subgroup (MulAut X), IsPGroup p P → Nat.card P ∣ p)
    {f φ : MulAut X} (hf : orderOf f = p) (hφ : orderOf φ = p) :
    Nonempty (signalizerFixedSubgroup f ≃* signalizerFixedSubgroup φ) := by
  obtain ⟨Sf, hSf⟩ := exists_sylow_eq_zpowers hbound hf
  obtain ⟨Sφ, hSφ⟩ := exists_sylow_eq_zpowers hbound hφ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut X) Sφ Sf
  have hconj : ∀ y : MulAut X, y ∈ Subgroup.zpowers f ↔ g⁻¹ * y * g ∈ Subgroup.zpowers φ := by
    intro y
    rw [← hSf, ← hSφ, ← hg, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have key : ∀ x : X, f x = x ↔ φ (g.symm x) = g.symm x := by
    intro x
    constructor
    · intro hx
      have hmem : g * φ * g⁻¹ ∈ Subgroup.zpowers f := by
        rw [hconj, show g⁻¹ * (g * φ * g⁻¹) * g = φ by group]
        exact Subgroup.mem_zpowers φ
      have h : g (φ (g.symm x)) = x := apply_eq_of_mem_zpowers hmem hx
      simpa using congrArg g.symm h
    · intro hx
      have hmem : g⁻¹ * f * g ∈ Subgroup.zpowers φ := (hconj f).mp (Subgroup.mem_zpowers f)
      have h : g.symm (f (g (g.symm x))) = g.symm x := apply_eq_of_mem_zpowers hmem hx
      simpa using h
  have hmap : (signalizerFixedSubgroup f).map g.symm.toMonoidHom = signalizerFixedSubgroup φ := by
    ext y
    rw [Subgroup.mem_map_equiv]
    change f (g y) = g y ↔ φ y = y
    simpa using key (g y)
  exact ⟨(g.symm.subgroupMap (signalizerFixedSubgroup f)).trans (MulEquiv.subgroupCongr hmap)⟩

end CFSG.SignalizerFunctorTheorem.NearModels
