module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI.1.8(ii)

An irreducible character takes its degree at exactly the elements in the
kernel of its representation.
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u v

private lemma rootOfUnity_norm_eq_one
    {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    ‖z‖ = 1 := by
  have hpow : ‖z‖ ^ n = (1 : ℝ) := by
    simpa [hz] using (norm_pow z n).symm
  have habs_pow : |(‖z‖ : ℝ) ^ n| = 1 := by simp [hpow]
  have habs : |(‖z‖ : ℝ)| = 1 := (abs_pow_eq_one ‖z‖ hn).mp habs_pow
  simpa [abs_of_nonneg (norm_nonneg z)] using habs

private lemma rootOfUnity_eq_one_of_one_le_re
    {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) (hre : 1 ≤ z.re) :
    z = 1 := by
  have hnorm : ‖z‖ = 1 := rootOfUnity_norm_eq_one hn hz
  have hre_eq : z.re = 1 :=
    le_antisymm (by simpa [hnorm] using Complex.re_le_norm z) hre
  have hnormSq : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hnorm] at h
    norm_num at h
    exact h
  have him : z.im = 0 := by
    have : z.im * z.im = 0 := by nlinarith
    exact mul_self_eq_zero.mp this
  exact Complex.ext (by simp [hre_eq]) (by simp [him])

private lemma eigenspace_finrank_pos
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (mu : f.Eigenvalues) :
    0 < Module.finrank ℂ (f.eigenspace (mu : ℂ)) := by
  have hmu : f.HasEigenvalue (mu : ℂ) :=
    Module.End.hasEigenvalue_of_hasGenEigenvalue mu.property
  rcases hmu.exists_hasEigenvector with ⟨w, hw⟩
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨w, ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    exact hw.apply_eq_smul
  · intro hzero
    apply hw.2
    simpa using congrArg Subtype.val hzero

private theorem finiteOrderEnd_eq_one_of_trace_eq_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (htrace : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) :
    f = 1 := by
  classical
  let mult : f.Eigenvalues → ℝ := fun mu =>
    (Module.finrank ℂ (f.eigenspace (mu : ℂ)) : ℝ)
  have htrace_one :
      LinearMap.trace ℂ V f =
        ∑ mu : f.Eigenvalues, (mu : ℂ) * (mult mu : ℂ) := by
    simpa [mult] using
      (Section1.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ mu : f.Eigenvalues, (mult mu : ℂ) := by
    have hzero :=
      Section1.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 0) hn hpow
    simpa [mult, LinearMap.trace_id] using hzero
  have hsum_real :
      ∑ mu : f.Eigenvalues, (mu : ℂ).re * mult mu =
        ∑ mu : f.Eigenvalues, (1 : ℝ) * mult mu := by
    have hsum_complex :
        ∑ mu : f.Eigenvalues, (mu : ℂ) * (mult mu : ℂ) =
          ∑ mu : f.Eigenvalues, (1 : ℂ) * (mult mu : ℂ) := by
      rw [← htrace_one, htrace, htrace_zero]
      simp
    simpa [Complex.re_sum, Complex.re_mul_ofReal] using congrArg Complex.re hsum_complex
  have hle : ∀ mu ∈ (Finset.univ : Finset f.Eigenvalues),
      (mu : ℂ).re * mult mu ≤ (1 : ℝ) * mult mu := by
    intro mu _
    have hmupow : (mu : ℂ) ^ n = 1 :=
      Section1.eigenvalue_pow_eq_one_of_pow_eq_one hpow mu.property
    have hnorm : ‖(mu : ℂ)‖ = 1 := rootOfUnity_norm_eq_one hn hmupow
    have hre : (mu : ℂ).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (mu : ℂ)
    exact mul_le_mul_of_nonneg_right hre (by positivity : 0 ≤ mult mu)
  have heq_each : ∀ mu : f.Eigenvalues,
      (mu : ℂ).re * mult mu = (1 : ℝ) * mult mu := by
    intro mu
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by simpa using hsum_real) mu
      (Finset.mem_univ mu)
  have heigen_eq_one : ∀ mu : f.Eigenvalues, (mu : ℂ) = 1 := by
    intro mu
    have hpos : 0 < mult mu := by
      dsimp [mult]
      exact_mod_cast eigenspace_finrank_pos mu
    have hre : (mu : ℂ).re = 1 := by
      have h := heq_each mu
      nlinarith
    have hmupow : (mu : ℂ) ^ n = 1 :=
      Section1.eigenvalue_pow_eq_one_of_pow_eq_one hpow mu.property
    exact rootOfUnity_eq_one_of_one_le_re hn hmupow (by linarith)
  have htop : f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple :=
      Section1.end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup := Section1.eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro mu
    simp [heigen_eq_one mu]
  ext w
  have hw : w ∈ f.eigenspace (1 : ℂ) := by simp [htop]
  rw [Module.End.mem_eigenspace_iff] at hw
  simpa using hw

/-- Suzuki, *Group Theory II*, Chapter 6, (1.8)(ii). -/
public theorem suzuki_ch6_theorem_1_8_ii
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (x : G) :
    rho.character x = rho.character 1 ↔ x ∈ rho.ker := by
  constructor
  · intro hx
    rw [MonoidHom.mem_ker]
    apply finiteOrderEnd_eq_one_of_trace_eq_finrank (rho x)
    · exact Nat.ne_of_gt (orderOf_pos x)
    · rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
    · simpa [Representation.character] using hx
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    simp [Representation.character, hx]

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
