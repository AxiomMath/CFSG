module

public import CFSG.Quasithin.Recognition.St84.Gen.LinSemidirectIso
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.QuasithinUnique

theorem mem_normalizer_iff_of_mulEquiv {G Y : Type*} [Group G] [Group Y]
    {P S : Subgroup G} {M U : Subgroup Y} (ψ : ↥P ≃* ↥M) (hSP : S ≤ P) (hUM : U ≤ M)
    (hψ : ∀ x : ↥P, (x : G) ∈ S ↔ ((ψ x : ↥M) : Y) ∈ U) (x : ↥P) :
    (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y) := by
  have hmap : (S.subgroupOf P).map ψ.toMonoidHom = U.subgroupOf M := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hψ (ψ.symm y)
  have hleft : (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      x ∈ Subgroup.normalizer (S.subgroupOf P) := by
    rw [← Subgroup.mem_subgroupOf (H := Subgroup.normalizer (S : Set G)) (K := P),
      Subgroup.subgroupOf_normalizer_eq hSP]
  have hright : ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y) ↔
      ψ x ∈ Subgroup.normalizer (U.subgroupOf M) := by
    rw [← Subgroup.mem_subgroupOf (H := Subgroup.normalizer (U : Set Y)) (K := M),
      Subgroup.subgroupOf_normalizer_eq hUM]
  rw [hleft, hright, ← hmap, ← Subgroup.map_equiv_normalizer_eq]
  rw [Subgroup.mem_map_equiv]
  simp

theorem exists_mulEquiv_sylow {G Y : Type*} [Group G] [Group Y] [Finite Y]
    {P Q S : Subgroup G} {M V U : Subgroup Y} (ψ₀ : ↥P ≃* ↥M)
    (hψ₀ : ∀ x : ↥P, (x : G) ∈ Q ↔ ((ψ₀ x : ↥M) : Y) ∈ V)
    (hV : M ≤ Subgroup.normalizer (V : Set Y)) (hS : IsSylowTwoOf S P)
    (hU : IsSylowTwoOf U M) :
    ∃ ψ : ↥P ≃* ↥M, (∀ x : ↥P, (x : G) ∈ Q ↔ ((ψ x : ↥M) : Y) ∈ V) ∧
      (∀ x : ↥P, (x : G) ∈ S ↔ ((ψ x : ↥M) : Y) ∈ U) ∧
      ∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y) := by
  let S₁ : Subgroup ↥M := (S.subgroupOf P).map ψ₀.toMonoidHom
  let S₂ : Subgroup Y := S₁.map M.subtype
  have hStop : IsSylowTwoOf (S.subgroupOf P) ⊤ := by
    refine ⟨le_top, hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm, ?_⟩
    have h := Subgroup.index_map_subtype (H := (⊤ : Subgroup ↥P))
      (K := (S.subgroupOf P).subgroupOf ⊤)
    rw [Subgroup.map_subgroupOf_eq_of_le le_top, Subgroup.index_top, mul_one] at h
    rw [← h]
    exact hS.2.2
  have hS₁ : IsSylowTwoOf S₁ ⊤ := by
    have h := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv ψ₀
      (X := S.subgroupOf P) (Y := (⊤ : Subgroup ↥P))).2 hStop
    simpa [S₁] using h
  have hS₂ : IsSylowTwoOf S₂ M := by
    refine ⟨Subgroup.map_subtype_le S₁, hS₁.isPGroup.map M.subtype, ?_⟩
    have htop : (⊤ : Subgroup ↥M).map M.subtype = M := by
      simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
    have hrel := Subgroup.relIndex_map_map_of_injective (f := M.subtype) S₁ ⊤
      M.subtype_injective
    rw [htop] at hrel
    show ¬ 2 ∣ (S₂.subgroupOf M).index
    rw [show (S₂.subgroupOf M).index = (S₁.subgroupOf ⊤).index from hrel]
    exact hS₁.2.2
  obtain ⟨g, hg, hconj⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hS₂ hU
  let gM : ↥M := ⟨g, hg⟩
  let ψ : ↥P ≃* ↥M := ψ₀.trans (MulAut.conj gM)
  have hψ_apply : ∀ x : ↥P, ((ψ x : ↥M) : Y) = g * ((ψ₀ x : ↥M) : Y) * g⁻¹ := by
    intro x
    simp [ψ, gM, MulAut.conj_apply]
  have hS₂_mem : ∀ x : ↥P, ((ψ₀ x : ↥M) : Y) ∈ S₂ ↔ (x : G) ∈ S := by
    intro x
    have h1 : ((ψ₀ x : ↥M) : Y) ∈ S₂ ↔ (ψ₀ x : ↥M) ∈ S₁ :=
      Subgroup.mem_map_iff_mem M.subtype_injective
    have h2 : (ψ₀ x : ↥M) ∈ S₁ ↔ (x : G) ∈ S := by
      change ψ₀.toMonoidHom x ∈ (S.subgroupOf P).map ψ₀.toMonoidHom ↔ (x : G) ∈ S
      rw [Subgroup.mem_map_iff_mem (f := ψ₀.toMonoidHom) ψ₀.injective]
      exact Subgroup.mem_subgroupOf
    exact h1.trans h2
  have hU_mem : ∀ v : Y, g * v * g⁻¹ ∈ U ↔ v ∈ S₂ := by
    intro v
    rw [hconj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    rw [h]
  have hSmap : ∀ x : ↥P, (x : G) ∈ S ↔ ((ψ x : ↥M) : Y) ∈ U := by
    intro x
    rw [hψ_apply x, hU_mem]
    exact (hS₂_mem x).symm
  have hQ : ∀ x : ↥P, (x : G) ∈ Q ↔ ((ψ x : ↥M) : Y) ∈ V := by
    intro x
    have hmem : ∀ v : Y, v ∈ V ↔ g * v * g⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff (H := V) (g := g)).1 (hV hg)
    rw [hψ_apply x]
    exact (hψ₀ x).trans (hmem _)
  exact ⟨ψ, hQ, hSmap, fun x => mem_normalizer_iff_of_mulEquiv ψ hS.le hU.le hSmap x⟩

theorem IsLinSemidirect.exists_mulEquiv_sylow {G Y : Type*} [Group G] [Group Y] [Finite Y]
    {P Q S : Subgroup G} {M V U : Subgroup Y} {F : Type*} [Field F] {n : ℕ}
    {Γ : Subgroup (GL (Fin n) F)}
    (h : IsLinSemidirect P Q Γ) (h' : IsLinSemidirect M V Γ)
    (hS : IsSylowTwoOf S P) (hU : IsSylowTwoOf U M) :
    ∃ ψ : ↥P ≃* ↥M, (∀ x : ↥P, (x : G) ∈ Q ↔ ((ψ x : ↥M) : Y) ∈ V) ∧
      (∀ x : ↥P, (x : G) ∈ S ↔ ((ψ x : ↥M) : Y) ∈ U) ∧
      ∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y) := by
  obtain ⟨ψ₀, hψ₀⟩ := h.exists_mulEquiv h'
  exact CFSG.Quasithin.F112R.St84.exists_mulEquiv_sylow ψ₀ hψ₀ h'.normal hS hU

end CFSG.Quasithin.F112R.St84
