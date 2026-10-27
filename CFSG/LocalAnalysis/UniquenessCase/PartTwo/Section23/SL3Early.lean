module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx2311.V_le_K {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) : c.V ≤ c.K := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (h12 h1930 c)
  have hVN : c.V ≤ Subgroup.normalizer (c.K : Set G) :=
    ((c.V_le_T h4 h1930).trans D.sylowM.le).trans hMN
  have hcomm : ⁅c.V, c.K⁆ ≤ c.K := by
    refine (Subgroup.commutator_le).2 ?_
    intro v hv k hk
    have hvk : v * k * v⁻¹ ∈ c.K :=
      (Subgroup.mem_normalizer_iff.mp (hVN hv) k).mp hk
    simpa [commutatorElement_def] using c.K.mul_mem hvk (c.K.inv_mem hk)
  rw [← hN8]
  exact hcomm

theorem Ctx2311.V_le_pCoreOf_M {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) : c.V ≤ CFSG.Open.pCoreOf 2 D.M := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (h12 h1930 c)
  have hKNV : c.K ≤ Subgroup.normalizer (c.V : Set G) :=
    ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right).trans
      ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
        (Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L))
  have hVK : c.V ≤ c.K := Ctx2311.V_le_K c h1930 h4 h12 hN8
  have hV2 : IsPGroup 2 ↥c.V :=
    CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_V h4 h1930)
  have hVcore : c.V ≤ CFSG.Open.pCoreOf 2 c.K :=
    uc22main1_le_pCoreOf hVK hV2 fun k hk x hx =>
      (Subgroup.mem_normalizer_iff.mp (hKNV hk) x).mp hx
  exact hVcore.trans
    (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hKM hMN)

theorem Ctx2311.E_le_pCoreOf_M {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) : c.E ≤ CFSG.Open.pCoreOf 2 D.M := by
  have hV : c.V ≤ CFSG.Open.pCoreOf 2 D.M :=
    Ctx2311.V_le_pCoreOf_M c h1930 h4 h12 hN8
  rw [Ctx23L.E]
  exact uc22p22v_conjClosure_le
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M) hV

theorem Ctx2311.isPGroup_E {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) : IsPGroup 2 ↥c.E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le
    (Ctx2311.E_le_pCoreOf_M c h1930 h4 h12 hN8)

theorem Ctx2311.E_le_K {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) : c.E ≤ c.K := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (h12 h1930 c)
  have hVK : c.V ≤ c.K := Ctx2311.V_le_K c h1930 h4 h12 hN8
  rw [Ctx23L.E]
  exact uc22p22v_conjClosure_le hMN hVK

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
