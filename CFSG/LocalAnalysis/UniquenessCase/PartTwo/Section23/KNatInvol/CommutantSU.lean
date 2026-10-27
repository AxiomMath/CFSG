module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatInvol.Commutant
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.TorusSU
import CFSG.ClassicalGroups.Unitary.Transitivity
import CFSG.ClassicalGroups.Unitary.Hyperbolic
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LieType.Universal.Unitary.Comparison
import Mathlib.Algebra.CharP.Two
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private abbrev vec (K : Type) [Field K] (i : Fin 4) (c : K) : Fin 4 → K := Pi.single i c

private abbrev e0 (K : Type) [Field K] : Fin 4 → K := vec K 0 1 + vec K 1 1

private abbrev orbitSpan (K : Type) [Field K] (a : ℕ) : Submodule K (Fin 4 → K) :=
  Submodule.span K (Set.range fun γ : ↥(CFSG.Open.StatedSU 4 (2 ^ a) K) =>
    ((γ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ e0 K)

private theorem herm_e0 {σ : K ≃+* K} : herm σ (e0 K) (e0 K) = 0 := by
  simp only [e0, vec]
  rw [herm_single_add_single (by decide : (0 : Fin 4) ≠ 1)]
  rw [map_one, one_mul]
  exact CharTwo.add_self_eq_zero 1

private theorem e0_ne_zero : (e0 K : Fin 4 → K) ≠ 0 := by
  intro h
  have h' := congrFun h 0
  simp [e0, vec] at h'

private theorem vec_add_vec_ne_zero {i j : Fin 4} (hij : i ≠ j) (t : K) :
    vec K i 1 + vec K j t ≠ 0 := by
  intro h
  have h' := congrFun h i
  simp [vec, hij] at h'

private theorem mem_orbitSpan_of_iso {a : ℕ} {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hSU : ∀ g : SUid σ 4, (g : GL (Fin 4) K) ∈ CFSG.Open.StatedSU 4 (2 ^ a) K)
    {v : Fin 4 → K} (hv0 : v ≠ 0) (hv : herm σ v v = 0) : v ∈ orbitSpan K a := by
  obtain ⟨t, -, htv⟩ := exists_mem_T_smul_eq_of_iso hσ (by norm_num : 3 ≤ 4)
    e0_ne_zero herm_e0 hv0 hv
  refine Submodule.subset_span ⟨⟨(t : GL (Fin 4) K), hSU t⟩, ?_⟩
  simpa only [smul_def] using htv

private theorem single_mem_orbitSpan {a : ℕ} {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hSU : ∀ g : SUid σ 4, (g : GL (Fin 4) K) ∈ CFSG.Open.StatedSU 4 (2 ^ a) K)
    (j : Fin 4) : vec K j 1 ∈ orbitSpan K a := by
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  obtain ⟨i, hij⟩ : ∃ i : Fin 4, i ≠ j := by
    by_cases hj : j = 0
    · exact ⟨1, by rw [hj]; decide⟩
    · exact ⟨0, Ne.symm hj⟩
  have h1 : vec K i 1 + vec K j 1 ∈ orbitSpan K a := by
    refine mem_orbitSpan_of_iso hσ hSU (vec_add_vec_ne_zero hij 1) ?_
    simp only [vec, herm_single_add_single hij, map_one, one_mul]
    exact CharTwo.add_self_eq_zero 1
  have h2 : vec K i 1 + vec K j ω ∈ orbitSpan K a := by
    refine mem_orbitSpan_of_iso hσ hSU (vec_add_vec_ne_zero hij ω) ?_
    simp only [vec, herm_single_add_single hij, hω]
    exact CharTwo.add_self_eq_zero 1
  have hdiff : (vec K i 1 + vec K j ω) - (vec K i 1 + vec K j 1) = (ω - 1) • vec K j 1 := by
    simp only [vec]
    rw [add_sub_add_left_eq_sub, ← Pi.single_sub, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hmem : (ω - 1) • vec K j 1 ∈ orbitSpan K a := by
    rw [← hdiff]
    exact (orbitSpan K a).sub_mem h2 h1
  have hω0 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  have hmul : vec K j 1 = (ω - 1)⁻¹ • ((ω - 1) • vec K j 1) := by
    rw [inv_smul_smul₀ hω0]
  rw [hmul]
  exact (orbitSpan K a).smul_mem ((ω - 1)⁻¹) hmem

theorem span_orbit_statedSU_four {a : ℕ} (hK : Nat.card K = (2 ^ a) ^ 2) :
    Submodule.span K (Set.range fun γ : ↥(CFSG.Open.StatedSU 4 (2 ^ a) K) =>
      ((γ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K)) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let σ := CFSG.LieType.BorelTits.unitaryInvolution K 2 a
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hK
  have hSU : ∀ g : SUid σ 4, (g : GL (Fin 4) K) ∈ CFSG.Open.StatedSU 4 (2 ^ a) K := by
    intro g
    rw [← SUid_eq_statedSU hK 4]
    exact g.2
  change orbitSpan K a = ⊤
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = ∑ j : Fin 4, x j • vec K j 1 := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [vec]
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ =>
    (orbitSpan K a).smul_mem (x j) (single_mem_orbitSpan hσ hSU j)

theorem addCommutantScalar_statedSU_four {a : ℕ} (hK : Nat.card K = (2 ^ a) ^ 2) :
    CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar (CFSG.Open.StatedSU 4 (2 ^ a) K) :=
  addCommutantScalar_of_sylowFixedLine (KGenProof.sylowFixedLine_statedSU_four hK)
    (AutZC.lineTorus_statedSU_four hK) (span_orbit_statedSU_four hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol
