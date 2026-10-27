module

public import CFSG.Quasithin.MS93.S4A441W
public import CFSG.Quasithin.MS93.S4A441N
public import CFSG.Quasithin.MS93.S4A441B6
public import CFSG.Quasithin.MS93.S4A441B7
public import CFSG.Quasithin.MS93.S4A441Main
import CFSG.Quasithin.MS93.S4A44Nabla
import CFSG.Quasithin.MS93.ML3Pair

public section

namespace CFSG.Quasithin.MS93.S4A.X441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem exists_not_le_normalizer_of_not_mem_bloc (hb : 4 < critDist 𝔛) {α α' μ : Vtx 𝔛}
    (hc : IsCritical 𝔛 α α') (hμ : IsMVtx 𝔛 μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist α μ = 2) {x : 𝔘}
    (hx : x ∈ ⁅ZM 𝔛 μ, Qv 𝔛 α⁆) (hxB : x ∉ Bloc h.le L α) :
    ∃ k ∈ stab 𝔛 α, ¬ ZM 𝔛 α' ≤ Subgroup.normalizer
      ((⁅ZM 𝔛 (k • μ), Qv 𝔛 α⁆ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
  by_contra hcon
  push Not at hcon
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hα : IsMVtx 𝔛 α := hc.1
  have hZμV : ZM 𝔛 μ ≤ Vv 𝔛 α := by
    have := zv_le_vv h (α := α) (ρ := μ) hdμ.le
    rwa [zv_of_isMVtx _ hμ] at this
  have hXV : ⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α ≤ Vv 𝔛 α :=
    sup_le ((Subgroup.commutator_mono hZμV le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((qv_le_stab _ α).trans (stab_le_normalizer_vv h α)))) (zm_le_vv h hα)
  apply hxB
  rw [mem_bloc_iff h (by omega) hα]
  refine ⟨hXV (Subgroup.mem_sup_left hx), fun l hl => ?_⟩
  rw [← commutatorElement_inv]
  exact inv_mem (W441.commutator_mem_zm h hφ hb hα (W441.ltil_le_normalizer h hfull hc hcon)
    le_sup_right hXV (W441.relIndex_le h hφ (by omega) hα hμ hdμ) hl (Subgroup.mem_sup_left hx))

theorem not_zm_le_qv_of_not_le_normalizer (hb : 4 < critDist 𝔛) {α α' μ : Vtx 𝔛}
    (hc : IsCritical 𝔛 α α') (hμ : IsMVtx 𝔛 μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist α μ = 2)
    (hN : ¬ ZM 𝔛 α' ≤ Subgroup.normalizer
      ((⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘)) :
    ¬ ZM 𝔛 μ ≤ Qv 𝔛 (geo 𝔛 α' α 2) := by
  intro hμQ
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 h.centHyp hc
  have hα : IsMVtx 𝔛 α := hc.1
  have hρν : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
  have hν : IsMVtx 𝔛 (geo 𝔛 α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hμρ : ZM 𝔛 μ ≤ Qv 𝔛 (geo 𝔛 α' α 1) := hμQ.trans (qv_le_qv _ h20 hν hρν.symm)
  have hB : ⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ≤ ZM 𝔛 μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_dist_le_two _ h20 hα hdμ.le).trans (stab_le_normalizer_zm _ μ))
  have hZn : ZM 𝔛 α' ≤ Subgroup.normalizer (ZM 𝔛 α : Set 𝔘) :=
    (zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ α)
  have hBZ : ¬ ⁅⁅ZM 𝔛 μ, Qv 𝔛 α⁆, ZM 𝔛 α'⁆ ≤ ZM 𝔛 α := fun hle =>
    hN (le_normalizer_sup_of_commutator_le hZn (hle.trans le_sup_right))
  have h1 : ⁅ZM 𝔛 μ, ZM 𝔛 α'⁆ ≤ Usup 𝔛 α' (geo 𝔛 α' α 1) := by
    rw [Subgroup.commutator_comm, Usup, zv_of_isMVtx _ hc'.1]
    exact Subgroup.commutator_mono le_rfl hμρ
  have hcomm := h1.trans (N441.usup_le_commutator_sup h hφ hb hc (hB.trans hμρ) hBZ)
  exact hN (ms21_vi _ h20 hb0 hc hdμ (zm_le_qv_of_dist_lt _ hμ (by rw [tdist_comm, hdμ]; omega))
    hcomm).2

theorem exists_smul_not_le_qv_of_fail (hH : Hyp40 h φ) (hb : 4 < critDist 𝔛)
    (hdual : S441C1Dual)
    (hV : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → ¬ Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 δ' δ 2))
    {x x' : Vtx 𝔛} (hc : IsCritical 𝔛 x x')
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • geo 𝔛 x x' 2) (g • x))
    {y : Vtx 𝔛} (hcy : IsCritical 𝔛 (geo 𝔛 x x' 2) y) (hy : geo 𝔛 (geo 𝔛 x x' 2) y 2 = x) :
    ∃ k ∈ stab 𝔛 x, ¬ ZM 𝔛 (k • geo 𝔛 x x' 2) ≤ Qv 𝔛 (geo 𝔛 x' x 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hd : (puAmalgam h.le).treeGraph.dist x x' = critDist 𝔛 := hc.2.1
  have hx : IsMVtx 𝔛 x := hc.1
  have ha : IsMVtx 𝔛 (geo 𝔛 x x' 2) := isMVtx_geo_two _ h20 hb0 hc
  have hda : (puAmalgam h.le).treeGraph.dist x (geo 𝔛 x x' 2) = 2 := dist_geo _ (by omega)
  have hH0 : ¬ ⁅ZM 𝔛 (geo 𝔛 x x' 2), Qv 𝔛 x⁆ ≤ Dloc h.le L x := by
    intro hle
    apply hfail 1
    rw [one_smul, one_smul]
    intro hn
    exact absurd hle hn
  by_cases hB : ⁅ZM 𝔛 (geo 𝔛 x x' 2), Qv 𝔛 x⁆ ≤ Bloc h.le L x
  ·
    have hQUD := C441.commutator_zm_qv_le_of_le_bloc h hφ (by omega) hx hda hB hH0
    have hmu := geo_two_mem_nablaSet h hfull hC (by omega) hV hc
    obtain ⟨u, hu, huD⟩ := Set.not_subset.mp hH0
    rcases C441.exists_good_conj_or_secD h hφ hC hb hc hmu hQUD hu huD with
      ⟨k, hk, -, hkZ⟩ | ⟨ψ, dual, C, hψs, hψ, hUC, hCG, hWQ, hWC, hCK⟩
    · exact ⟨k, hk, hkZ⟩
    · exfalso
      have hda' : (puAmalgam h.le).treeGraph.dist (geo 𝔛 x x' 2) x = 2 := by
        rw [tdist_comm]
        exact hda
      have hab : 𝔄 (geo 𝔛 x x' 2) (geo 𝔛 (geo 𝔛 x x' 2) x 1) := adj_geo_one _ (by omega)
      have hbx : 𝔄 (geo 𝔛 (geo 𝔛 x x' 2) x 1) x := by
        have := adj_geo _ (u := geo 𝔛 x x' 2) (w := x) (i := 1) (by omega)
        rwa [show geo 𝔛 (geo 𝔛 x x' 2) x (1 + 1) = x from geo_of_le _ (by omega)] at this
      cases dual
      · apply hfail 1
        rw [one_smul, one_smul]
        exact L441.concl441_of_secD h hfull ms17i_holds hb hφ ha hx hab hbx hψs hψ
          ⟨hUC, hCG, hWQ, hWC, hCK⟩
      · have key : ∀ γ' : Vtx 𝔛, geo 𝔛 (geo 𝔛 x x' 2) y 2 = γ' →
            ∀ ψ' : ↥(stab 𝔛 γ') →* ↥(StatedSL 3 F), Function.Surjective ψ' →
              IsSumOfNaturalModulesVia (stab 𝔛 γ') (Uloc h.le L γ') ⊥ ψ' false 1 →
              ∀ C' : Subgroup 𝔘, ¬ L441.IsSecD h.le L γ' ψ' true
                (conjCl (stab 𝔛 γ') (ZM 𝔛 (geo 𝔛 x x' 2))) C' := by
          intro γ' hγ'
          subst hγ'
          refine hdual G M T L h F inferInstance inferInstance φ hH hb _ y hcy ?_
          intro g
          rw [hy]
          exact hfail g
        exact key x hy ψ hψs hψ C ⟨hUC, hCG, hWQ, hWC, hCK⟩
  ·
    obtain ⟨u, hu, huB⟩ := Set.not_subset.mp hB
    obtain ⟨k, hk, hN⟩ := exists_not_le_normalizer_of_not_mem_bloc h hφ hb hc ha hda hu huB
    have hka : IsMVtx 𝔛 (k • geo 𝔛 x x' 2) := (isMVtx_smul _ k _).mpr ha
    have hdka : (puAmalgam h.le).treeGraph.dist x (k • geo 𝔛 x x' 2) = 2 := by
      have := dist_smul _ k x (geo 𝔛 x x' 2)
      rwa [(mem_stab _).mp hk, hda] at this
    exact ⟨k, hk, not_zm_le_qv_of_not_le_normalizer h hφ hb hc hka hdka hN⟩

end Vertex

end CFSG.Quasithin.MS93.S4A.X441
