module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPair
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUAssembly
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section DualPairDeg

theorem false_of_fieldExt_of_model_PSL
    {X : Type} [Group X] {J : Subgroup X} {g r : ℕ} (hr : 3 ≤ r)
    (hmodel : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL r 2 (2 * (g + 1)))
    (hF : GGSixLSevenFieldExtCase J .PSU (g + 1)) : False := by
  obtain ⟨t', m', f', -, hmod', hne⟩ := hF
  obtain ⟨ht, -, hf⟩ := CFSG.SeitzReduction.LinearPilot.slmEvenTypeDetAt hr
    (↥J ⧸ Subgroup.center ↥J) (2 * (g + 1)) t' m' f' hmodel hmod'.admissible hmod'
  exact hne ⟨ht, hf, Or.inl rfl⟩

theorem lieModel_PSL_map_of_isQuasisimple {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) {J' : Subgroup U}
    (hJ' : CFSG.Assembly.IsQuasisimple ↥J') {k f : ℕ}
    (h : CFSG.Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL k 2 f) :
    CFSG.Blueprint.LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL k 2 f := by
  have : Group.IsPerfect ↥J' := ⟨hJ'.1⟩
  let φ : ↥J' →* ↥(J'.map ψ) := ψ.subgroupMap J'
  have hsurj : Function.Surjective φ := ψ.subgroupMap_surjective J'
  have hφker : φ.ker ≤ Subgroup.center ↥J' := by
    intro u hu
    have hu' : (u : U) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker] at hu ⊢
      have := congrArg Subtype.val hu
      exact this
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hu')) w.1)
  exact blueprintLieModel_PSL_of_mulEquiv
    (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence φ hsurj hφker) h

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem PSUBlock.two_le_blockDegree_of_dualPair
    [Finite X] (hH : PSULiftHyp n g ψ p B)
    {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hb : PSUBlock ψ B S ε e) (hpair : e ≠ ε) {D J : Subgroup X} (hDcard : Nat.card D = p ^ 2)
    (hjc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'g : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆)
    (hJ'm : J'.map ψ = J) (hF : GGSixLSevenFieldExtCase J .PSU (g + 1)) :
    2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e := by
  by_contra hlt
  push Not at hlt
  have hblock := hb.three_mul_blockDegree_le_rank hH hDcard hjc hJ'g hJ'm
  have hpos := (exists_blockDegree_mul_eq_rank (hb.S_comm hH) (hb.S_odd hH) hb.e_prim).1
  have hr3 : 3 ≤ Matrix.rank e := by omega
  obtain ⟨-, hpair', hε⟩ := hb.cases.resolve_left hpair
  have hSU : ∀ s ∈ S, s ∈ GUsub (PSUσ g) n := fun s hs => (hb.subE s hs).1
  rw [hε] at hJ'g
  obtain ⟨P, Q, R, W, hD, hM, -, -, hmodel⟩ :=
    exists_blockModel_dualPair_PSU_explicit n g S hSU (hb.S_comm hH) hb.e_prim hpair' hlt hJ'g
  have hmodelJ := lieModel_PSL_map_of_isQuasisimple ψ hH.ker hJ'g.2.2 hmodel
  rw [hJ'm] at hmodelJ
  exact false_of_fieldExt_of_model_PSL hr3 hmodelJ hF

end DualPairDeg

end CFSG.StandardType.TableCRes
