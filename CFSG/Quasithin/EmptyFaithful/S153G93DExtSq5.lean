module

public import CFSG.Quasithin.EmptyFaithful.S153G93DExtSq5Core
public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.F918T1
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.F918T2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.S153G93D.ExtSq5

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem exists_coord {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {π : ↥(StatedSL 5 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.extSq (ZMod 2) 5).RealizesVia K ⊤ ⊥ π) :
    ∃ Φ : W ≃* Multiplicative ↥(altMat 5), ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (w : W),
      Φ (((π γ : ↥K) : MulAut W) w) = altMulAct γ (Φ w) := by
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.extSq (ZMod 2) 5) rfl hπ
  obtain ⟨Ψ, hΨ⟩ := extSq5_equiv_alt
  exact ⟨(E.trans Subgroup.topEquiv).trans Ψ, fun γ w => (congrArg Ψ (hE γ w)).trans (hΨ γ _)⟩

theorem oneExtSq5_holds : OneExtSq5 := by
  intro W _ _ G₀ K S a z hC hGK hExt
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 5 (ZMod 2)) →* ↥K,
      (FFModel.extSq (ZMod 2) 5).RealizesVia K ⊤ ⊥ π := hExt
  obtain ⟨Φ, hΦ⟩ := exists_coord hπ
  have haK : a ∈ K := by
    rw [← hGK]
    exact hC.a_mem
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 5 (ZMod 2)), π γ = ⟨a, haK⟩ := hπ.1 ⟨a, haK⟩
  have hγa : ((π γ : ↥K) : MulAut W) = a := congrArg Subtype.val hγ
  have hγ1 : γ ≠ 1 := by
    intro h
    apply hC.a1
    have h1 : ((π γ : ↥K) : MulAut W) = 1 := by
      rw [h, map_one]
      rfl
    rw [← hγa]
    exact h1
  have hγ2 : γ * γ = 1 := by
    refine altMulAct_faithful fun B => ?_
    obtain ⟨v, rfl⟩ := Φ.surjective B
    have hπ2 : ((π (γ * γ) : ↥K) : MulAut W) = 1 := by
      rw [map_mul, Subgroup.coe_mul, hγa, ← pow_two]
      exact hC.a2
    rw [← hΦ, hπ2]
    rfl
  obtain ⟨B₁, B₂, B₃, hind⟩ := exists_indep3 hγ1 hγ2
  have hcomm : ∀ B : Multiplicative ↥(altMat 5),
      Φ (a (Φ.symm B) * (Φ.symm B)⁻¹) = altAct γ B * B⁻¹ := by
    intro B
    rw [map_mul, map_inv, ← hγa, hΦ, MulEquiv.apply_symm_apply]
    rfl
  have hmem : ∀ B : Multiplicative ↥(altMat 5),
      a (Φ.symm B) * (Φ.symm B)⁻¹ ∈ commV (Subgroup.zpowers a) := fun B =>
    Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, Φ.symm B, rfl⟩
  have hi : Indep3 (a (Φ.symm B₁) * (Φ.symm B₁)⁻¹) (a (Φ.symm B₂) * (Φ.symm B₂)⁻¹)
      (a (Φ.symm B₃) * (Φ.symm B₃)⁻¹) := by
    refine Indep3.of_map Φ.toMonoidHom ?_
    simp only [MulEquiv.coe_toMonoidHom, hcomm]
    exact hind
  have hX : ∀ w : W, w * w = 1 := fun w => by
    rw [← pow_two]
    exact hC.exp w
  have hcard : Nat.card ↥(commV (Subgroup.zpowers a)) = 4 := by
    rw [hC.rk]
    norm_num
  exact Indep3.false_of_card_eq_four hX hcard (hmem B₁) (hmem B₂) (hmem B₃) hi

end CFSG.Quasithin.S153G93D.ExtSq5
