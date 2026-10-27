module

public import CFSG.RankThree.GF2n.Stroth80.Sec7ModelAlg
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec7_conj_mem_of_proportional {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
    [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E))
    {Z0 : Subgroup G} (hQZ0 : Q ≤ Z0) {t m : G} (htM : t ∈ M) (hm : m ∈ M)
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hψ : ∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd e - e)
    (hinj : ∀ a a' : Mbar M Q, (∀ e, (ρ a).toAdd e = (ρ a').toAdd e) → a = a')
    (hA : ∀ c : K, ∃ a ∈ bar M Q Z0, ∀ e, (ρ a).toAdd e = e + c • ψ e)
    (μ : K) (hμ : μ ≠ 0)
    (hprop : ∀ e, ψ e = μ • (ρ (QuotientGroup.mk (⟨m, hm⟩ : ↥M))).toAdd
      (ψ ((ρ (QuotientGroup.mk (⟨m, hm⟩ : ↥M))).toAdd.symm e))) :
    m * t * m⁻¹ ∈ Z0 := by
  have hm' : m * t * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm htM) (M.inv_mem hm)
  obtain ⟨g, hg⟩ : ∃ g : Mbar M Q, g = QuotientGroup.mk (⟨t, htM⟩ : ↥M) := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : Mbar M Q, g' = QuotientGroup.mk (⟨m, hm⟩ : ↥M) := ⟨_, rfl⟩
  rw [← hg] at hψ
  rw [← hg'] at hprop
  have hmk : (QuotientGroup.mk (⟨m * t * m⁻¹, hm'⟩ : ↥M) : Mbar M Q) = g' * g * g'⁻¹ := by
    rw [hg, hg', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] <;> rfl
  have hprop' : ∀ e, (ρ g').toAdd (ψ ((ρ g').toAdd.symm e)) = μ⁻¹ • ψ e := by
    intro e
    rw [hprop e, inv_smul_smul₀ hμ]
  have hback : ∀ e, (ρ g).toAdd ((ρ g').toAdd.symm e) - (ρ g').toAdd.symm e =
      ψ ((ρ g').toAdd.symm e) := fun e => (hψ _).symm
  have hact : ∀ e, (ρ (QuotientGroup.mk (⟨m * t * m⁻¹, hm'⟩ : ↥M))).toAdd e =
      e + μ⁻¹ • ψ e := by
    intro e
    rw [hmk, ← sub_eq_iff_eq_add', sec7_psi_conj ρ g g' e, hback, hprop']
  obtain ⟨a, ha, hae⟩ := hA μ⁻¹
  have haeq : a = QuotientGroup.mk (⟨m * t * m⁻¹, hm'⟩ : ↥M) :=
    hinj a (QuotientGroup.mk (⟨m * t * m⁻¹, hm'⟩ : ↥M)) fun e => by rw [hae e, hact e]
  rw [haeq] at ha
  exact (Tim37.mk_mem_bar_iff' hQZ0 ⟨m * t * m⁻¹, hm'⟩).mp ha

end CFSG.RankThree.GF2n.Stroth80
