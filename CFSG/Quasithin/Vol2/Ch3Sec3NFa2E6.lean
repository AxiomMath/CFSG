module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Blueprint
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.G2_le_centralizer_Z (h36 : A36ForSQTK) (c : A2Cfg G T M L D H K q) :
    a2G2 K T ≤ Subgroup.centralizer (a2Z T : Set G) :=
  sup_le (nf_conjClosure_le_centralizer_Z h36 c.nf.hyp c.nf.inH_H₀ c.nf.K_comp c.nf.nonfaithful)
    (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T)

theorem leaf_E6i (h36 : A36ForSQTK) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      CaseAFacts G T M L D H K q → E6iConcl L K T H := by
  intro G _ _ T M L D H K q facts g hg
  have c := facts.cfg
  have hyp := facts.amalgam
  have hV0 := facts.V_ne
  obtain ⟨-, he1⟩ := facts.e1
  intro hcomm
  apply hg.critical.not_le
  have hVst : a2V L T ≤ stab (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) :=
    V_le_stab_of_dist_le hyp hV0 hg.critical.dist_eq.le
  have hst : stab (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) = conjSub (g : G) (a2G2 K T) := by
    rw [stab_smul, stab_γ₁ hyp.le₂]
  rw [hst] at hVst
  have hbs : ballStab 1 (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) =
      conjSub (g : G) (a2TC K T) := by
    rw [ballStab_smul, (ballStab_one_γ₁ hyp.gen).1, he1]
  rw [hbs, ← facts.e5b, conjSub_centralizerMod]
  intro v hv
  have hvG := hVst hv
  have hGZ : conjSub (g : G) (a2G2 K T) ≤ Subgroup.normalizer (conjSub (g : G) (a2Z T) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [conjSub_centralizer]
    exact conjSub_mono _ (c.G2_le_centralizer_Z h36)
  refine ⟨hvG, hGZ hvG, fun u hu => ?_⟩
  have h1 : ⁅u, v⁆ ∈ conjSub (g : G) (a2Z T) :=
    hcomm (Subgroup.commutator_mem_commutator hu hv)
  have e : v * u * v⁻¹ * u⁻¹ = ⁅u, v⁆⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact (conjSub (g : G) (a2Z T)).inv_mem h1

end CFSG.Quasithin.H13.NFa2
