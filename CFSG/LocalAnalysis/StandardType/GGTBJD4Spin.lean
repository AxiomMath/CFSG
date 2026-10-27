module

public import CFSG.LocalAnalysis.StandardType.GGTBJD4Iso
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmFrame
public import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGTBJD4Block
import CFSG.LocalAnalysis.StandardType.GGTBJD4Fixed
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDich
import CFSG.LocalAnalysis.StandardType.GGA8NbrOmFrameCore
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3OrthMinusBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitCent
import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  Polynomial
open CFSG.StandardType.KGCentOm (kgcDiag)

theorem ggTBJD4_spin {p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f - 1)
    {u : spinGroup (quadPlus 4 F)} (hu : u ∈ ggTorus (plusDatum 4 F (by norm_num)))
    (hup : u ^ p = 1) (hu1 : u ≠ 1) {J : Subgroup (spinGroup (quadPlus 4 F))}
    (hJ : IsComponentOf J (Subgroup.centralizer ({u} : Set (spinGroup (quadPlus 4 F)))))
    (hcount : Set.ncard {h | h ∈ ggTorus (plusDatum 4 F (by norm_num)) ∧ h ^ p = 1 ∧
      h ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F)))} ≤ p)
    {H : Type} [Group H] (e : H ≃* ↥J) :
    StatedClassicalModel (H ⧸ Subgroup.center H) .PSL 4 2 f := by
  have hpq : p ∣ Nat.card F - 1 := hF ▸ hpf
  have h2f : 1 < 2 ^ f := hF ▸ Finite.one_lt_card
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hple : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by omega) hpf
  have hf : 2 ≤ f := by
    by_contra hf
    have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn3 : 3 ≤ 4 := by norm_num
  have hrange : (spinAction (quadPlus 4 F)).range = orthDerived (quadPlus 4 F) :=
    range_spinAction_quadPlus_eq_commutator hn3
  have hxΩ : spinAction (quadPlus 4 F) u ∈ orthDerived (quadPlus 4 F) := hrange ▸ ⟨u, rfl⟩
  have hxp : (⟨_, hxΩ⟩ : ↥(orthDerived (quadPlus 4 F))) ^ p = 1 := by
    apply Subtype.ext
    change spinAction (quadPlus 4 F) u ^ p = 1
    rw [← map_pow, hup, map_one]
  have hx := LocalAnalysis.GLTheoremA.CanonU3.OrthMinus.oddOrderIsometry_of_pow_eq_one hp
    (by rw [ringChar.eq F 2]; exact hp2) (nondegenerate_polarBilin_quadPlus 4 F) _ hxp
  have huJ : u ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F))) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hz)
  obtain ⟨T, hT, hcase⟩ := jcoreOm_dichotomy le_rfl hp hp2 hup hJ
  rcases hcase with ⟨h, hh, hne1, hq, rfl⟩ | ⟨hL, hTq, hTle, hTn⟩
  · obtain ⟨μ, -, rfl⟩ := LocalAnalysis.GLTheoremA.T173S.exists_eq_X_sub_C_of_mem_primaryFactors
      hp hpq hx.pow_eq_one hh
    have hμ : μ ≠ 1 := by
      rintro rfl
      exact hne1 (by rw [Units.val_one, C_1])
    have hm := ggTBJD4_block_mult hp hpq hu hup huJ hμ hh
      (fun z hz => specialBlock_le_supportedBlock _ ((hT z).mp hz)) hcount
    have hne : X - C (μ : F) ≠ reciprocalPolynomial (X - C (μ : F)) := by
      rw [A8Coord.omf_reciprocalPolynomial_X_sub_C μ.ne_zero, Ne, sub_right_inj, C_inj]
      intro h'
      have h3 : (μ : F) ^ 2 = 1 ^ 2 := by
        rw [one_pow, sq]
        nth_rewrite 2 [h']
        exact mul_inv_cancel₀ μ.ne_zero
      exact hμ (Units.ext (by rw [Units.val_one]; exact CharTwo.sq_injective h3))
    have hle : specialBlock (quadPlus 4 F) (spinAction (quadPlus 4 F) u) (X - C (μ : F)) ≤
        orthDerived (quadPlus 4 F) :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer _).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    obtain ⟨eJ⟩ := ggTBJD4_nonempty_mulEquiv hn3 hT hle
    exact ggTBJD4_model_specialBlock hx hh hne hm hF hf (e.trans eJ)
  · obtain ⟨hd, rfl, hT3⟩ := ggTBJD4_fixed_shape hp hpq hu hu1 hx hT hL hTq hTle hTn hcount
    obtain ⟨eJ⟩ := ggTBJD4_nonempty_mulEquiv hn3 hT hx.supportedFixedDerived_le_orthDerived
    exact ggTBJD4_model_fixed hx hd hT3 hF hf (e.trans eJ)

end CFSG.StandardType

end
