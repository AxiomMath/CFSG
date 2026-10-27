module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec34Model
public import CFSG.RankThree.GF2n.Stroth80.Sec5Model
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Q_le_CN' (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) : Q ≤ hc.CN t := fun y hy =>
  Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hy, fun v hv => hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩

theorem Ctx.Q_le_H0' (hc : Ctx M Q Z B) : Q ≤ H0 M Z := fun y hy =>
  ⟨hc.hyp.Q_normal.1 hy, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    hc.hyp.toHyp79.V_central hz hy⟩

theorem Ut_mul_Q (hc : Ctx M Q Z B) {x q : G} (hx : x ∈ H0 M Z) (hq : q ∈ Q) :
    Ut Q Z (q * x) = Ut Q Z x := by
  obtain ⟨K, fK, finK, -, γ, M₀, hG⟩ := stroth_globalModelData hc.hyp
  have hxc : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hx.2 z hz
    rw [← this]; group
  obtain ⟨T, hT, -, -⟩ := hG.linear_of_centralizes hx.1 hxc
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := hQn x hx.1
  have hxQ' : ∀ y ∈ Q, x⁻¹ * y * x ∈ Q := fun y hy => by
    have := hQn x⁻¹ (M.inv_mem hx.1) y hy
    simpa using this
  have hqx : q * x ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hq) hx.1
  have hqQ : ∀ y ∈ Q, (q * x) * y * (q * x)⁻¹ ∈ Q := hQn _ hqx
  have hqQ' : ∀ y ∈ Q, (q * x)⁻¹ * y * (q * x) ∈ Q := fun y hy => by
    have := hQn _ (M.inv_mem hqx) y hy
    simpa using this
  have hTq : ∀ y ∈ Q, M₀.π ((q * x) * y * (q * x)⁻¹) = T (M₀.π y) := by
    intro y hy
    have e : (q * x) * y * (q * x)⁻¹ = q * (x * y * x⁻¹) * q⁻¹ := by group
    rw [e, Tim79.QuadModel.pi_conj_self hq (hxQ y hy), hT y hy]
  have hUQ : ∀ {a : G}, a ∈ M → Ut Q Z a ≤ Q := fun ha => hc.Ut_le_Q ha
  ext y
  constructor
  · intro hy
    have hyQ : y ∈ Q := hUQ hqx hy
    have h1 : M₀.π y ∈ M₀.img (Ut Q Z (q * x)) := M₀.pi_mem_img hy hyQ
    have h2 := (mem_img_comm_zpowers_sup_iff M₀ hG.reg T hqQ hqQ' hTq _).mp h1
    exact (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z x) hyQ).mp
      ((mem_img_comm_zpowers_sup_iff M₀ hG.reg T hxQ hxQ' hT _).mpr h2)
  · intro hy
    have hyQ : y ∈ Q := hUQ hx.1 hy
    have h1 : M₀.π y ∈ M₀.img (Ut Q Z x) := M₀.pi_mem_img hy hyQ
    have h2 := (mem_img_comm_zpowers_sup_iff M₀ hG.reg T hxQ hxQ' hT _).mp h1
    exact (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z (q * x)) hyQ).mp
      ((mem_img_comm_zpowers_sup_iff M₀ hG.reg T hqQ hqQ' hTq _).mpr h2)

end CFSG.RankThree.GF2n.Stroth80
