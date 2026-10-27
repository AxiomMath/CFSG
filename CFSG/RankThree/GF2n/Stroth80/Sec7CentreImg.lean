module

public import CFSG.RankThree.GF2n.Stroth80.Sec7CentralizerQBW
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_mem_centre_of_img_le [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hZc : Sec7CentreMpStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {y : G} (hyL : y ∈ LB M Q B) {K : Type}
    [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    (hH : ∀ e : M₀.E, (ρ (QuotientGroup.mk (⟨y, hc.LB_le_M hyL⟩ : ↥M))).toAdd e - e ∈
      M₀.img ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)) :
    y ∈ Z0 := by
  classical
  have hs5 := hs.toSec5
  refine sec7_centralizer_QB_Wt h34 hRoot hZc hZcard hc hs hZ0 hyL fun x hx => ?_
  have hyM : y ∈ M := hc.LB_le_M hyL
  have hxQ : x ∈ Q := hx.2.1
  have hQn : ∀ m ∈ M, ∀ z ∈ Q, m * z * m⁻¹ ∈ Q := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) z).mp hz
  have hreg := hS.model.reg
  have hζH : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.mpr
      ⟨hyM, Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (mul_inv_eq_iff_eq_mul.mp (hc.LB_centralizes_Z hyL z hz)).symm⟩, rfl⟩
  have hiso := hS.iso _ hζH
  have hy2 : y ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hyL
  have hsq : ∀ e, (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd
      ((ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e) = e := by
    intro e
    have h1 : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨y, hyM⟩ : ↥M) = 1 := by
      rw [← QuotientGroup.mk_mul]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [pow_two] using hy2
    rw [← act_mul_apply ρ, h1, map_one]
    rfl
  have hperp : ∀ e : M₀.E, M₀.B (M₀.π x)
      ((ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e - e) = 0 := by
    intro e
    obtain ⟨z, hz', hzQ, hzπ⟩ := M₀.mem_img.mp (hH e)
    have hnorm : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
        Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ ha.2.2
    obtain ⟨α, hα, c, hc', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hz'
    have hαQ : α ∈ Q := hα.2.1
    have hcQ : c ∈ Q := hc.Vt_le_Q t hc'
    rw [← hzπ, M₀.π_mul _ hαQ _ hcQ, map_add]
    have h1 : M₀.B (M₀.π x) (M₀.π α) = 0 := by
      refine (M₀.comm_iff_B hreg hxQ hαQ).mp ?_
      have hc1 := hc.inf_QB_elemAbelian.1.is_comm
      exact congrArg Subtype.val (hc1.comm ⟨x, hxQ, hx.1⟩ ⟨α, hαQ, hα.1⟩)
    have h2 : M₀.B (M₀.π x) (M₀.π c) = 0 := by
      refine (M₀.comm_iff_B hreg hxQ hcQ).mp ?_
      exact (Subgroup.mem_centralizer_iff.mp hx.2.2 c hc').symm
    rw [h1, h2, add_zero]
  have hfix : (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd (M₀.π x) = M₀.π x := by
    refine sub_eq_zero.mp (M₀.nondeg _ fun e' => ?_)
    have h1 := hiso (M₀.π x) ((ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e')
    rw [hsq e'] at h1
    rw [map_sub, LinearMap.sub_apply, h1, ← map_sub (M₀.B (M₀.π x))]
    exact hperp e'
  have hyx : y * x * y⁻¹ ∈ Q := hQn y hyM x hxQ
  exact (M₀.comm_mem_iff hxQ hyx).mpr (by rw [hS.conj ⟨y, hyM⟩ x hxQ]; exact hfix)

end CFSG.RankThree.GF2n.Stroth80
