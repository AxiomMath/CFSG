module

public import CFSG.Quasithin.Vol2.KGFact12617L52b
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module

section Conj

variable {Γ : Type} [Group Γ]

private def leafOuterConj (K : Subgroup Γ) {y : Γ} (hy : y ∈ Subgroup.normalizer (K : Set Γ)) :
    ↥K ≃* ↥K where
  toFun k := ⟨y * (k : Γ) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy (k : Γ)).mp k.2⟩
  invFun k := ⟨y⁻¹ * (k : Γ) * y, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) (k : Γ)).mp k.2
    rw [inv_inv] at h
    exact h⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

end Conj

theorem leafOuter_holds : LeafOuter := by
  intro Γ _ _ F _ _ hF Y K hKY hYN hYC e U _hUK hne y hyY hyU
  have hyK : y ∈ Subgroup.normalizer (K : Set Γ) := hYN hyY
  let c := leafOuterConj K hyK
  let β : MulAut ↥(StatedSL 5 F) := (e.symm.trans c).trans e
  have hβ : ∀ g, β g = e (c (e.symm g)) := fun g => rfl
  have hβU : ((U.subgroupOf K).map e.toMonoidHom).map β.toMonoidHom =
      (U.subgroupOf K).map e.toMonoidHom := by
    ext g
    constructor
    · intro hg
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg'
      refine Subgroup.mem_map.mpr ⟨c u, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hyU (u : Γ)).mp (Subgroup.mem_subgroupOf.mp hu)
      · show e (c u) = β (e u)
        rw [hβ, MulEquiv.symm_apply_apply]
    · intro hg
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_map.mpr ⟨e (c.symm v), Subgroup.mem_map.mpr ⟨c.symm v, ?_, rfl⟩, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr ?_
        show y⁻¹ * (v : Γ) * y ∈ U
        refine (Subgroup.mem_normalizer_iff.mp hyU (y⁻¹ * (v : Γ) * y)).mpr ?_
        rw [show y * (y⁻¹ * (v : Γ) * y) * y⁻¹ = (v : Γ) by group]
        exact Subgroup.mem_subgroupOf.mp hv
      · show β (e (c.symm v)) = e v
        rw [hβ, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply c v]
  obtain ⟨a, ha⟩ := exists_inner_of_map_eq hF β hβU hne
  obtain ⟨k₀, rfl⟩ := e.surjective a
  have key : ∀ k : ↥K, c k = k₀ * k * k₀⁻¹ := by
    intro k
    have h := ha (e k)
    rw [hβ, MulEquiv.symm_apply_apply] at h
    apply e.injective
    rw [h, map_mul, map_mul, map_inv]
  have hz : (k₀ : Γ)⁻¹ * y ∈ Y ⊓ Subgroup.centralizer (K : Set Γ) := by
    refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.inv_mem (hKY k₀.2)) hyY, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hk' : y * h * y⁻¹ = (k₀ : Γ) * h * (k₀ : Γ)⁻¹ :=
      congrArg Subtype.val (key ⟨h, hh⟩)
    have h1 : y * h = (k₀ : Γ) * h * (k₀ : Γ)⁻¹ * y := by
      rw [← hk']
      group
    calc h * ((k₀ : Γ)⁻¹ * y) = (k₀ : Γ)⁻¹ * ((k₀ : Γ) * h * (k₀ : Γ)⁻¹ * y) := by group
      _ = (k₀ : Γ)⁻¹ * (y * h) := by rw [h1]
      _ = (k₀ : Γ)⁻¹ * y * h := by simp only [mul_assoc]
  rw [hYC, Subgroup.mem_bot] at hz
  have hy : y = (k₀ : Γ) := by
    calc y = (k₀ : Γ) * ((k₀ : Γ)⁻¹ * y) := by group
      _ = (k₀ : Γ) := by rw [hz, mul_one]
  rw [hy]
  exact k₀.2

end CFSG.Quasithin.H13.KG12617L52
