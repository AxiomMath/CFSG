module

public import CFSG.RankThree.PartTwo.Sec15.Read148PerfProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofSeven

public section

namespace CFSG.RankThree.PartTwo.Sec15.Read148Perf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem pow_three_mem_projImage_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (x : ↥(projImage (glPi π 3 (p ^ f) K))) :
    ((x ^ 3 : ↥(projImage (glPi π 3 (p ^ f) K))) : ProjGenLinGroup (Fin 3) K) ∈
      projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨_, g, hg, rfl⟩ := x
  rw [Subgroup.coe_pow, ← map_pow]
  refine Sec14.Item148Res6.mk_mem_projImage_slPi_of_detPow hK hq (pow_mem hg 3) ?_
  have hd := (mem_rootsOfUnity _ _).mp (det_mem_rootsOfUnity hK hg)
  rw [map_pow, ← pow_mul, Nat.mul_div_cancel' (Sec14.Item148Res6.three_dvd_qSubPi hq), hd]

theorem cubeComm_of_isZ3PGLThreeAt {P : Type} [Group P] {p f : ℕ}
    (h : Sec14.IsZ3PGLThreeAt P p f) (hq2 : 2 < p ^ f) :
    CubeComm P ∧ Group.IsPerfect ↥(commutator P) := by
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := h
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hSG : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (slPi_le_glPi hπ)
  have hcomm := Sec13.commutator_projImage_glPi hK hq2
  refine ⟨CubeComm.of_mulEquiv (CubeComm.prod (fun z => ?_) (fun x => ?_)) ψ, ?_⟩
  · have h1 : z ^ 3 = 1 := by
      have h0 := pow_card_eq_one' (x := z)
      rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h0
    rw [h1]
    exact one_mem _
  · rw [hcomm, Subgroup.mem_subgroupOf]
    exact pow_three_mem_projImage_slPi hK hq x
  · obtain ⟨e'⟩ := Y4Core.nonempty_commutator_equiv ψ
    have eS : ↥(commutator ↥(projImage (glPi π 3 (p ^ f) K))) ≃*
        ↥(projImage (slPi π 3 (p ^ f) K)) :=
      (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSG)
    have := Sec13.isPerfect_projImage_slPi hK hq2
    exact Group.IsPerfect.ofSurjective (f := (e'.trans eS).symm.toMonoidHom)
      (MulEquiv.surjective _)

theorem pow_three_mem_commutator_of_isZ3PGLThreeAt {Γ : Type} [Group Γ] {X J B : Subgroup Γ}
    (hJX : J ≤ X) (hB : IsMulCommutative ↥B) (hBX : B ≤ Subgroup.normalizer (X : Set Γ))
    {p f : ℕ} (hZ : Sec14.IsZ3PGLThreeAt ↥(J ⊔ B) p f) (hq2 : 2 < p ^ f) {y : Γ}
    (hy : y ∈ J ⊔ B) : y ^ 3 ∈ ⁅X, X⁆ := by
  obtain ⟨hcube, hperf⟩ := cubeComm_of_isZ3PGLThreeAt hZ hq2
  have hCX : ⁅J ⊔ B, J ⊔ B⁆ ≤ X :=
    (Subgroup.commutator_mono (sup_le_sup_right hJX B) (sup_le_sup_right hJX B)).trans
      (Sec14.commutator_sup_le_of_le_normalizer hB hBX)
  have eC : ↥(commutator ↥(J ⊔ B)) ≃* ↥⁅J ⊔ B, J ⊔ B⁆ :=
    ((commutator ↥(J ⊔ B)).equivMapOfInjective (J ⊔ B).subtype (J ⊔ B).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_commutator (J ⊔ B)))
  have hCp : Group.IsPerfect ↥⁅J ⊔ B, J ⊔ B⁆ :=
    Group.IsPerfect.ofSurjective (f := eC.toMonoidHom) eC.surjective
  have hCC : ⁅⁅J ⊔ B, J ⊔ B⁆, ⁅J ⊔ B, J ⊔ B⁆⁆ = ⁅J ⊔ B, J ⊔ B⁆ := Subgroup.isPerfect_iff.mp hCp
  have hy3 : y ^ 3 ∈ ⁅J ⊔ B, J ⊔ B⁆ := cubeComm_subgroup_iff.mp hcube y hy
  rw [← hCC] at hy3
  exact Subgroup.commutator_mono hCX hCX hy3

theorem cube_mem_of_case7 {Γ : Type} [Group Γ] {X J₁ J₂ B : Subgroup Γ} (hsup : J₁ ⊔ J₂ = X)
    (hcomm : ⁅J₁, J₂⁆ = ⊥) (hB : IsMulCommutative ↥B)
    (hBX : B ≤ Subgroup.normalizer (X : Set Γ)) {p₁ f₁ p₂ f₂ : ℕ}
    (hZ₁ : Sec14.IsZ3PGLThreeAt ↥(J₁ ⊔ B) p₁ f₁) (hZ₂ : Sec14.IsZ3PGLThreeAt ↥(J₂ ⊔ B) p₂ f₂)
    (hq₁ : 2 < p₁ ^ f₁) (hq₂ : 2 < p₂ ^ f₂) : ∀ x ∈ X, x ^ 3 ∈ ⁅X, X⁆ := by
  intro x hx
  have hJX₁ : J₁ ≤ X := hsup ▸ le_sup_left
  have hJX₂ : J₂ ≤ X := hsup ▸ le_sup_right
  obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hx)
  rw [(commute_of_commutator_eq_bot hcomm hj₁ hj₂).mul_pow]
  exact mul_mem
    (pow_three_mem_commutator_of_isZ3PGLThreeAt hJX₁ hB hBX hZ₁ hq₁ (Subgroup.mem_sup_left hj₁))
    (pow_three_mem_commutator_of_isZ3PGLThreeAt hJX₂ hB hBX hZ₂ hq₂ (Subgroup.mem_sup_left hj₂))

end CFSG.RankThree.PartTwo.Sec15.Read148Perf
