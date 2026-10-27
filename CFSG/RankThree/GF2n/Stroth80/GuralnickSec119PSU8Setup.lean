module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form
import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.mem_movedSpace_cmCommAct_of_a2 {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hb : b ∈ cmComm M Q Z B K γ M₀ φ) (s : ↥(XbarH M Q Z B))
    (hsL : ((s : ↥(H0 M Z)) : G) ∈ LB M Q B)
    (hsA : IsA2 Q Z ((s : ↥(H0 M Z)) : G)) :
    (⟨b, hb⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈
      CFSG.HardMathSupport.Kantor79.movedSpace (cmCommAct hc φ s) := by
  have hbimg : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  have hBle : B ≤ ⁅Q, Subgroup.zpowers ((s : ↥(H0 M Z)) : G)⁆ ⊔ Z :=
    hc.B_le_commutator_of_a2 hsL hsA
  have hbimg' : b ∈ M₀.img (⁅Q, Subgroup.zpowers ((s : ↥(H0 M Z)) : G)⁆ ⊔ Z) :=
    M₀.img_mono hBle hbimg
  have ha2 : ((s : ↥(H0 M Z)) : G) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hsL
  have hT : (⟨((s : ↥(H0 M Z)) : G), (s : ↥(H0 M Z)).2⟩ : ↥(H0 M Z)) = (s : ↥(H0 M Z)) := rfl
  have hbrange : b ∈ LinearMap.range
      (((φ (⟨((s : ↥(H0 M Z)) : G), (s : ↥(H0 M Z)).2⟩ : ↥(H0 M Z)) :
        M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) :=
    (hc.mem_img_zpowers_sup_iff φ hφπ (s : ↥(H0 M Z)).2 ha2 b).mp hbimg'
  rw [hT] at hbrange
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hbrange
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe] at hy
  have hsup : y ∈ cmComm M Q Z B K γ M₀ φ ⊔
      M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
    rw [(hc.isCompl_cmComm_orthogonal hD φ hφπ).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hsup
  have hfix : φ (s : ↥(H0 M Z)) y₂ = y₂ :=
    hc.action_fixes_orthogonal_of_mem_XbarH hD φ hφπ s hy₂
  refine LinearMap.mem_range.mpr ⟨⟨y₁, hy₁⟩, ?_⟩
  apply Subtype.ext
  change ((cmCommAct hc φ s) ⟨y₁, hy₁⟩ : M₀.E) - y₁ = b
  rw [coe_cmCommAct]
  show φ (s : ↥(H0 M Z)) y₁ - y₁ = b
  have h2 : φ (s : ↥(H0 M Z)) (y₁ + y₂) - (y₁ + y₂) = φ (s : ↥(H0 M Z)) y₁ - y₁ := by
    rw [map_add, hfix]
    abel
  rw [← h2]
  exact hy

end CFSG.RankThree.GF2n.Stroth80

end
