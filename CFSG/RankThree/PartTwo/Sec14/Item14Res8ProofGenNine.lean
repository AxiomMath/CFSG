module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofGenL3
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open Res8Hess

@[expose] def KS142L3HessGenNineModel : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], PiField π p f K → ModThree π (p ^ f) →
    (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) → ¬ (p = 2 ∧ f = 3) →
    ∀ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 → ∀ dM cM : projImage (slPi π 3 (p ^ f) K),
      (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ) →
      (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) →
      ⨆ (b : projImage (slPi π 3 (p ^ f) K)) (_ : b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM)
        (_ : b ≠ 1), thetaC b = ⊤

theorem ks142L3HessGenNine_of_model (hM : KS142L3HessGenNineModel) : KS142L3HessGenNine := by
  intro X _ _ p e _ he hiso hperf hmod hU38 E hEe hE9 htr
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, -, -, -, -, Φ, hΦE⟩ :=
    exists_hessian_equiv he hiso hEe hE9 htr
  have hne : ¬ (p = 2 ∧ e = 3) := by
    intro h
    obtain ⟨hp, he3⟩ := h
    subst hp
    subst he3
    exact hU38 hiso
  have hgen := hM π p e K hK hq hmod hne τ hτ hτ1 dM cM hdM hcM
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hΦE' : ∀ w ∈ Ê, Φ w ∈ E := fun w hw => hΦE ▸ ⟨w, hw, rfl⟩
  rw [eq_top_iff]
  have hle : ∀ b ∈ Ê, b ≠ 1 → (thetaC b).map Φ.toMonoidHom ≤
      sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} := by
    intro b hb hb1
    refine le_sSup ⟨?_, ?_⟩
    · rw [Subgroup.card_map_of_injective Φ.injective]
      exact not_dvd_card_inSubgroup_theta _
    · rw [thetaC_map_equiv]
      refine le_trans (fun x hx => ?_)
        (CFSG.RankThree.PartOne.Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore 3 _)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨Φ b, hΦE' b hb⟩)
  calc (⊤ : Subgroup X) = (⊤ : Subgroup (projImage (slPi π 3 (p ^ e) K))).map Φ.toMonoidHom := by
        rw [Subgroup.map_top_of_surjective _ Φ.surjective]
    _ = (⨆ (b : projImage (slPi π 3 (p ^ e) K)) (_ : b ∈ Ê) (_ : b ≠ 1), thetaC b).map
          Φ.toMonoidHom := by rw [hgen]
    _ ≤ _ := by
        rw [Subgroup.map_iSup]
        refine iSup_le fun b => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun hb => ?_
        rw [Subgroup.map_iSup]
        exact iSup_le fun hb1 => hle b hb hb1

end CFSG.RankThree.PartTwo.Sec14
