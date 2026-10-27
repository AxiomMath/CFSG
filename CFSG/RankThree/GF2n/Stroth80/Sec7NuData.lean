module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorGlue
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec7_nu_data {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {m : G} (hm : m ∈ M) :
    ∃ (σ : K ≃+* K) (a : K), a ≠ 0 ∧
      (∀ (c : K) (e : M₀.E), (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (c • e) =
        σ c • (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e) ∧
      (∀ e e' : M₀.E, M₀.B ((ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e)
        ((ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e') = a * σ (M₀.B e e')) := by
  obtain ⟨σ, a, T, hT1, hT2, -, hT4⟩ := hS.model.act m hm
  have hρ : ∀ e : M₀.E, (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e = T e := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have h1 : M₀.π (m * x * m⁻¹) = (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (M₀.π x) :=
      hS.conj ⟨m, hm⟩ x hxQ
    exact h1.symm.trans (hT2 x hxQ)
  refine ⟨σ, (a : K), a.ne_zero, fun c e => ?_, fun e e' => ?_⟩
  · rw [hρ, hρ]
    exact hT1 c e
  · have h1 := M₀.Qf_add (T e) (T e')
    have hsum : M₀.Qf (T e + T e') = (a : K) * σ (M₀.Qf (e + e')) := by
      rw [← map_add T e e', hT4]
    have hσ : σ (M₀.Qf (e + e')) = σ (M₀.Qf e) + σ (M₀.Qf e') + σ (M₀.B e e') := by
      rw [M₀.Qf_add e e', map_add, map_add]
    rw [hρ, hρ]
    linear_combination -h1 + hsum - hT4 e - hT4 e' + (a : K) * hσ

theorem sec7_nu_img {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {m : G} (hm : m ∈ M) {S : Subgroup G}
    (hZS : Z ≤ S) (hSQ : S ≤ Q) (hmS : conjSubgroup m S = S) (e : M₀.E) :
    e ∈ M₀.img S ↔ (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e ∈ M₀.img S := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  have hmxQ : m * x * m⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hm).1 x hxQ
  have h1 : M₀.π (m * x * m⁻¹) = (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (M₀.π x) :=
    hS.conj ⟨m, hm⟩ x hxQ
  have h2 : m * x * m⁻¹ ∈ S ↔ x ∈ S := by
    have h := CFSG.CGT.Timmesfeld75.mem_conjSubgroup (g := m) (T := S) (x := m * x * m⁻¹)
    rw [hmS, show m⁻¹ * (m * x * m⁻¹) * m = x by group] at h
    exact h
  rw [← h1]
  exact (Tim79.QuadModel.mem_img_iff M₀ hZS hxQ).trans
    (h2.symm.trans (Tim79.QuadModel.mem_img_iff M₀ hZS hmxQ).symm)

end CFSG.RankThree.GF2n.Stroth80
