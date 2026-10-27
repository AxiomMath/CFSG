module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem hom_eq_one_of_commute_values {K H : Type*} [Group K] [Group.IsPerfect K]
    [Group H] (f : K →* H) (hf : ∀ a b : K, f a * f b = f b * f a) : f = 1 := by
  have hker : commutator K ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf a b
  rw [Group.IsPerfect.commutator_eq_top] at hker
  ext k
  exact hker (Subgroup.mem_top k)

theorem res1340_mulAut_eq_one_of_fixes_generalizedFitting {L : Type*} [Group L]
    [Group.IsPerfect L] {S : Type*} [Group S] [Finite S] (φ : L →* MulAut S)
    (hF : ∀ l : L, ∀ s ∈ CFSG.generalizedFitting S, φ l s = s) : φ = 1 := by
  have hFn : (CFSG.generalizedFitting S).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := S)).2
  have hcen : ∀ (l : L) (s : S), s⁻¹ * φ l s ∈
      Subgroup.centralizer (CFSG.generalizedFitting S : Set S) := by
    intro l s
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : φ l (s * g * s⁻¹) = s * g * s⁻¹ := hF l _ (hFn.conj_mem g hg s)
    rw [map_mul, map_mul, map_inv, hF l g hg] at h1
    calc g * (s⁻¹ * φ l s) = s⁻¹ * (s * g * s⁻¹) * φ l s := by group
      _ = s⁻¹ * (φ l s * g * (φ l s)⁻¹) * φ l s := by rw [h1]
      _ = s⁻¹ * φ l s * g := by group
  have hmem : ∀ (l : L) (s : S), s⁻¹ * φ l s ∈ CFSG.generalizedFitting S := fun l s =>
    CFSG.centralizer_generalizedFitting_le S (hcen l s)
  refine MonoidHom.ext fun l => MulEquiv.ext fun s => ?_
  let d : L →* S :=
    { toFun := fun l => s⁻¹ * φ l s
      map_one' := by simp
      map_mul' := fun a b => by
        have hb : φ a (s⁻¹ * φ b s) = s⁻¹ * φ b s := hF a _ (hmem b s)
        have hb' : φ a (φ b s) = φ a s * (s⁻¹ * φ b s) := by
          rw [← hb, ← map_mul, mul_inv_cancel_left]
        simp only [map_mul, MulAut.mul_apply]
        rw [hb']
        group }
  have hd : d = 1 := by
    refine hom_eq_one_of_commute_values d fun a b => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hcen a s) _ (hmem b s)).symm
  have h := DFunLike.congr_fun hd l
  change s⁻¹ * φ l s = 1 at h
  rw [inv_mul_eq_one] at h
  exact h.symm

theorem res1340_fixes_fittingSubgroup {L : Type*} [Group L] {S : Type*} [Group S] [Finite S]
    (φ : L →* MulAut S)
    (hp : ∀ p : ℕ, p.Prime → ∀ l : L, ∀ s ∈ CFSG.pCore p S, φ l s = s) :
    ∀ l : L, ∀ s ∈ CFSG.fittingSubgroup S, φ l s = s := by
  intro l
  have hle : CFSG.fittingSubgroup S ≤ (φ l).toMonoidHom.eqLocus (MonoidHom.id S) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_le fun p s hs => hp p (Nat.prime_of_mem_primeFactors p.2) l s hs
  exact fun s hs => hle hs

theorem res1340_fixes_generalizedFitting {L : Type*} [Group L] {S : Type*} [Group S]
    (φ : L →* MulAut S) (hF : ∀ l : L, ∀ s ∈ CFSG.fittingSubgroup S, φ l s = s)
    (hE : ∀ l : L, ∀ s ∈ CFSG.layer S, φ l s = s) :
    ∀ l : L, ∀ s ∈ CFSG.generalizedFitting S, φ l s = s := by
  intro l
  have hle : CFSG.generalizedFitting S ≤ (φ l).toMonoidHom.eqLocus (MonoidHom.id S) := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact sup_le (fun s hs => hF l s hs) fun s hs => hE l s hs
  exact fun s hs => hle hs

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
