module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2Producer
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2Center
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117Module
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2Short
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2Gen
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportHom
public import CFSG.RankThree.GF2n.Stroth80.HeringSec11Action
import CFSG.RankThree.GF2n.Stroth80.Sec3Action
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalGroups.Symplectic.TransvectionCentralizer
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.RankThree.GF2n.Smith81.Lin31Back
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMIsometry
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate3008
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

theorem Ctx.exists_g2_cmComm_action {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {x : ℕ}
    (hLie : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .G2 0 2 x)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (h : ↥(H0 M Z)) (q : G), q ∈ Q → M₀.π ((h : G) * q * (h : G)⁻¹) = φ h (M₀.π q))
    (hφk : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (hφQ : ∀ (h : ↥(H0 M Z)) e, M₀.Qf (φ h e) = M₀.Qf e) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2), Nat.card K' = 2 ^ x ∧
      ∃ ρV : ↥(adjointGroup .G2 K') →*
          (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)),
        Function.Injective ρV ∧ (∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v) ∧
        commutatorSpace ρV.range = ⊤ ∧
        ∃ t₀, IsLongRootElement (cmCommQf B φ) (ρV t₀) := by
  obtain ⟨-, K', _, _, _, hK', ⟨ψ₀⟩⟩ := hc.exists_mulEquiv_adjointGroup_g2 hLie
  set Θ : ↥(XbarH M Q Z B) →* ↥(adjointGroup .G2 K') :=
    ψ₀.toMonoidHom.comp (xbarHToXbar M Q Z B) with hΘ
  have hΘs : Function.Surjective Θ := ψ₀.surjective.comp (xbarHToXbar_surjective hc)
  have hΘk : ∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q := fun s => by
    rw [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      xbarHToXbar_eq_one_iff]
  obtain ⟨ρV, hρV⟩ := hc.exists_rho_factor_group φ Θ hΘs
    (fun s hs => (hφk (s : ↥(H0 M Z))).mpr ((hΘk s).mp hs))
  obtain ⟨-, hiso, -, hcomm, hsieg⟩ := hc.cmComm_kantor_instance ha2 hD φ hφπ hφQ
  have hρQ : ∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v := fun g v => by
    obtain ⟨s, rfl⟩ := hΘs g
    rw [hρV s]
    exact hiso s v
  have hρinj : Function.Injective ρV := by
    refine (injective_iff_map_eq_one ρV).mpr fun g hg => ?_
    obtain ⟨s, rfl⟩ := hΘs g
    rw [hρV s] at hg
    exact (hΘk s).mpr (hc.mem_Q_of_cmCommAct_eq_one hD φ hφπ hφk hφQ hg)
  have hrange : ρV.range = (cmCommAct hc φ).range := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨s, rfl⟩ := hΘs g
      exact ⟨s, (hρV s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Θ s, hρV s⟩
  obtain ⟨a, haL, haA⟩ := ha2
  obtain ⟨s₀, hs₀a, -⟩ := hc.exists_lift_a2 (a := ⟨a, hc.LB_le_M haL⟩) (h := ⟨haL, haA⟩)
  refine ⟨K', inferInstance, inferInstance, inferInstance, hK', ρV, hρinj, hρQ,
    by rw [hrange]; exact hcomm, Θ s₀, ?_⟩
  rw [hρV s₀]
  exact hsieg s₀ (hs₀a ▸ haL) (hs₀a ▸ haA)

end CFSG.RankThree.GF2n.Stroth80
