module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.GF2n.Smith81.S81U6Basic
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.Open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Module

private theorem scalar_pow_three_of_det_one {F : Type} [Field F] [CharP F 2] {h : GL (Fin 6) F}
    (hdet : (h : Matrix (Fin 6) (Fin 6) F).det = 1) (c : Fˣ)
    (hc : h = Matrix.GeneralLinearGroup.scalar (Fin 6) c) : h ^ 3 = 1 := by
  have hmat : (h : Matrix (Fin 6) (Fin 6) F) = (c : F) • 1 := by
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have h6 : (c : F) ^ 6 = 1 := by
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : ((c : F) ^ 3 - 1) ^ 2 = 0 := by
    linear_combination h6 + (1 - (c : F) ^ 3) * h2
  have hc3 : (c : F) ^ 3 = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have hcu : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  rw [hc, ← map_pow, hcu, map_one]

theorem exists_ThetaU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {X : Type} [Group X]
    (θ : X ≃* StatedProj (StatedSU 6 (2 ^ f) F)) :
    ∃ Θ : ↥(SUid (unitaryInvolution F 2 f) 6) →* X, Function.Surjective Θ ∧
      (∀ n ∈ Θ.ker, n ^ 3 = 1) ∧
      (∀ n ∈ Θ.ker, ∀ x : ↥(SUid (unitaryInvolution F 2 f) 6), n * x = x * n) := by
  let incl : ↥(SUid (unitaryInvolution F 2 f) 6) →* ↥(StatedSU 6 (2 ^ f) F) :=
    Subgroup.inclusion (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 6).le
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ↥(SUid (unitaryInvolution F 2 f) 6) →* X, ∀ n, Θ n =
      θ.symm (QuotientGroup.mk'
        ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F)) (incl n)) :=
    ⟨θ.symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F))).comp incl),
      fun n => rfl⟩
  have hker : ∀ n ∈ Θ.ker, ∃ c : Fˣ,
      ((n : ↥(SUid (unitaryInvolution F 2 f) 6)) : GL (Fin 6) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    intro n hn
    rw [MonoidHom.mem_ker, hΘ] at hn
    have h1 := θ.symm.map_eq_one_iff.mp hn
    rw [QuotientGroup.mk'_apply] at h1
    have h2 : incl n ∈ (StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((incl n : ↥(StatedSU 6 (2 ^ f) F)) : GL (Fin 6) F) ∈ StatedScalars (Fin 6) F :=
      Subgroup.mem_subgroupOf.mp h2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h3
    exact ⟨c, hc.symm⟩
  refine ⟨Θ, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F)) (θ x)
    have hmem : (g : GL (Fin 6) F) ∈ SUid (unitaryInvolution F 2 f) 6 :=
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 6).ge g.2
    refine ⟨⟨(g : GL (Fin 6) F), hmem⟩, ?_⟩
    rw [hΘ]
    have hincl : incl ⟨(g : GL (Fin 6) F), hmem⟩ = g := rfl
    rw [hincl, hg]
    exact θ.symm_apply_apply x
  · intro n hn
    obtain ⟨c, hc⟩ := hker n hn
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact scalar_pow_three_of_det_one
      (CFSG.LieType.Universal.Unitary.mem_SUid.mp n.2).1 c hc
  · intro n hn x
    obtain ⟨c, hc⟩ := hker n hn
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Subgroup.center (GL (Fin 6) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (Subgroup.mem_center_iff.mp hz (x : GL (Fin 6) F)).symm

end CFSG.RankThree.GF2n.Smith81.S81V
