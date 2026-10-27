module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsRee
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoEndNode
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Facts
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

namespace TableBF4TwoInputs

section Aut

variable {C : Type*} [Group C]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center C = ⊥) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [← hZ, Subgroup.mem_center_iff]
  intro x
  have h1 := congrArg (fun φ : MulAut C => φ x) hg
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc x * g = g * x * g⁻¹ * g := by rw [h1]
    _ = g * x := by group

theorem centralizer_range_conj_eq_bot (hZ : Subgroup.center C = ⊥) :
    Subgroup.centralizer ((MulAut.conj : C →* MulAut C).range : Set (MulAut C)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff] at hφ
  rw [Subgroup.mem_bot]
  ext g
  have h1 := hφ (MulAut.conj g) ⟨g, rfl⟩
  have h2 : MulAut.conj (φ g) = MulAut.conj g := by
    ext x
    have h3 := congrArg (fun χ : MulAut C => χ (φ.symm x)) h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h3
    simp only [MulAut.conj_apply]
    exact h3.symm
  exact conj_injective_of_center_eq_bot hZ h2

theorem mul_conj_mul_inv (α : MulAut C) (g : C) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem mem_normalizer_range_conj (α : MulAut C) :
    α ∈ Subgroup.normalizer ((MulAut.conj : C →* MulAut C).range : Set (MulAut C)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨α g, (mul_conj_mul_inv α g).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨α⁻¹ g, ?_⟩
    rw [← mul_conj_mul_inv, hg]
    group

theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    (hA : IsElemAbelian p A) : IsPGroup p A := CFSG.Open.IsElemAbelian.isPGroup hA

end Aut

section Main

set_option linter.unusedSectionVars false


theorem card_lt_of_outer_adjoint {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) {τ : MulAut (adjointGroup ReeTag.F4.tag K)}
    (hτ : τ ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut _).range) (hτ2 : τ ^ 2 = 1)
    {A : Subgroup (adjointGroup ReeTag.F4.tag K)} (hA : IsElemAbelian 3 A)
    (hcomm : ∀ a ∈ A, MulAut.conj a * τ = τ * MulAut.conj a) : Nat.card A < 3 ^ 3 := by
  have hZ : Subgroup.center (adjointGroup ReeTag.F4.tag K) = ⊥ := center_adjointGroup_eq_bot
  have hψ : Function.Injective
      (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut (adjointGroup ReeTag.F4.tag K)) :=
    conj_injective_of_center_eq_bot hZ
  have hs2 : orderOf τ = 2 := by
    refine orderOf_eq_prime hτ2 ?_
    intro h1
    exact hτ ⟨1, by rw [map_one, h1]⟩
  obtain ⟨h, hh⟩ := ggF4_exists_ree_conj (m := 0) (by rw [hK]; norm_num) hψ
    (centralizer_range_conj_eq_bot hZ) (mem_normalizer_range_conj τ) hτ hs2
  have hAΓ : A.map (MulAut.conj h⁻¹).toMonoidHom ≤ reeFixed ReeTag.F4 K 0 := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem : MulAut.conj a ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut _).range ⊓
        Subgroup.centralizer {τ} :=
      ⟨⟨a, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha)⟩
    rw [← hh] at hmem
    obtain ⟨r, hr, hre⟩ := hmem
    have hre' : h * r * h⁻¹ = a := hψ (by simpa [MulAut.conj_apply] using hre)
    have hx : (MulAut.conj h⁻¹).toMonoidHom a = r := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← hre']
      group
    rw [hx]
    exact hr
  have hcard : Nat.card (A.map (MulAut.conj h⁻¹).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
  have hEp : IsPGroup 3 (A.map (MulAut.conj h⁻¹).toMonoidHom) :=
    (isPGroup_of_isElemAbelian hA).map _
  have hEc : ∀ x ∈ A.map (MulAut.conj h⁻¹).toMonoidHom,
      ∀ y ∈ A.map (MulAut.conj h⁻¹).toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hab]
  rw [← hcard]
  exact card_lt_of_le_reeFixed hK hAΓ hEp hEc

theorem ggF4TwoOuterRankInput_holds : TableBF4Two.GGF4TwoOuterRankInput := by
  intro K _ _ _ hK τ hτ hτ2 A hA hcomm
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  let e : TableBF4.RecipeGroup K ≃* adjointGroup ReeTag.F4.tag K := TableBF4.recipeEquiv K
  have hconj : ∀ g, MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) :=
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e
  have hτ' : MulAut.congr e τ ∉
      (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut _).range := by
    rintro ⟨c, hc⟩
    apply hτ
    refine ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [hconj, MulEquiv.apply_symm_apply]
    exact hc
  have hτ2' : MulAut.congr e τ ^ 2 = 1 := by
    rw [← map_pow, hτ2, map_one]
  have hA' : IsElemAbelian 3 (A.map e.toMonoidHom) := TableB.isElemAbelian_map hA _
  have hcomm' : ∀ a ∈ A.map e.toMonoidHom,
      MulAut.conj a * MulAut.congr e τ = MulAut.congr e τ * MulAut.conj a := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := congrArg (MulAut.congr e) (hcomm a ha)
    rwa [map_mul, map_mul, hconj] at h1
  have h := card_lt_of_outer_adjoint hK hτ' hτ2' hA' hcomm'
  rwa [Subgroup.card_map_of_injective e.injective] at h

end Main

end TableBF4TwoInputs

end CFSG.StandardType
