module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R856G2MovedAbelian
public import CFSG.RankThree.PartOne.SEITZRF.Rank1
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LieType.Ree.LargeReeInvolution


theorem exists_moved_abelian_of_twistedF4_field
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) (hσ : orderOf σ = 3) :
    ∃ A : Subgroup (F4.reeGamma K a), IsPGroup 3 A ∧ IsMulCommutative A ∧
      (∀ x ∈ A, F4.reeGammaFieldAut K a σ x ∈ A) ∧
      ∃ x ∈ A, F4.reeGammaFieldAut K a σ x ≠ x := by
  let ρ : Matrix.SpecialLinearGroup (Fin 2) K →* F4.reeGamma K a :=
    (largeReeA1Hom K a).codRestrict (F4.reeGamma K a)
      (CFSG.RankThree.PartTwo.KFacts.KS14.largeReeA1Hom_mem_reeGamma a hK)
  have hρ : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
      (ρ M : ModGL F4.tag K) = largeReeA1Hom K a M := fun _ => rfl
  have hi : Function.Injective ρ := by
    intro A B h
    exact largeReeA1Hom_injective (congrArg Subtype.val h)
  have heq : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
      F4.reeGammaFieldAut K a σ (ρ M) = ρ (Matrix.SpecialLinearGroup.map σ.toRingHom M) := by
    intro M
    apply Subtype.ext
    rw [ReeTag.coe_reeGammaFieldAut, hρ, hρ]
    exact CFSG.RankThree.PartOne.SEITZRF.units_map_entrywiseHom_largeReeA1Hom
      (K := K) (a := a) σ M
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K F4.prime]; decide
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 4 ≤ 2 ^ 3).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨S, hSab, hstable, x, hx, hmoved⟩ := exists_moved_abelian_of_sl2_field hK3 hK4 σ hσ
  let A := (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map ρ
  have hAp : IsPGroup 3 A := S.isPGroup'.map ρ
  have hAab : IsMulCommutative A := by
    let : IsMulCommutative (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) := hSab
    exact Subgroup.map_isMulCommutative (S : Subgroup _) ρ
  refine ⟨A, hAp, hAab, ?_, ρ x, Subgroup.mem_map_of_mem ρ hx, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [heq]
    exact Subgroup.mem_map_of_mem ρ (hstable y hy)
  · rw [heq]
    exact fun h => hmoved (hi h)

theorem exists_moved_abelian_of_twistedF4_outer
    {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hY : CFSG.Blueprint.LieModel Y .twistedF4 0 2 f)
    (α : MulAut Y) (hα3 : α ^ 3 = 1)
    (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner Y) :
    ∃ A : Subgroup Y, IsPGroup 3 A ∧ IsMulCommutative A ∧
      (∀ a ∈ A, α a ∈ A) ∧ ∃ a ∈ A, α a ≠ a := by
  classical
  have hR := (hY.reeTitsModel (by decide)).2
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  let β : MulAut (F4.reeGamma K a) := MulAut.congr e α
  have hβ3 : β ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma K a) := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext y
    apply e.injective
    have h := congrArg (fun δ : MulAut (F4.reeGamma K a) => δ (e y)) hx
    simpa [β, MulAut.congr_apply, MulAut.conj_apply] using h
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field
      ha hK Nat.prime_three hβ3 hβ1 with ⟨x, hx, -, -⟩ | ⟨σ, x, hσ, hx⟩
  · exact (hβout ⟨x, hx.symm⟩).elim
  obtain ⟨A, hAp, hAab, hstable, y, hy, hmoved⟩ :=
    exists_moved_abelian_of_twistedF4_field ha hK σ hσ
  let θ : F4.reeGamma K a ≃* Y := (MulAut.conj x).trans e.symm
  have heq : ∀ z : F4.reeGamma K a, α (θ z) = θ (F4.reeGammaFieldAut K a σ z) := by
    intro z
    apply e.injective
    change e (α (e.symm (MulAut.conj x z))) = e (e.symm (MulAut.conj x (F4.reeGammaFieldAut K a σ z)))
    rw [e.apply_symm_apply]
    change β (MulAut.conj x z) = _
    rw [hx, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  let B := A.map θ.toMonoidHom
  have hBp : IsPGroup 3 B := hAp.map θ.toMonoidHom
  have hBab : IsMulCommutative B := by
    let : IsMulCommutative A := hAab
    exact Subgroup.map_isMulCommutative A θ.toMonoidHom
  refine ⟨B, hBp, hBab, ?_, θ y, Subgroup.mem_map_of_mem θ.toMonoidHom hy, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change α (θ z) ∈ B
    rw [heq]
    exact Subgroup.mem_map_of_mem θ.toMonoidHom (hstable z hz)
  · rw [heq]
    exact fun h => hmoved (θ.injective h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
