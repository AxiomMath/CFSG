module

public import CFSG.Quasithin.MS93.S4A441Main
public import CFSG.Quasithin.MS93.S4A44FcWStmt
import CFSG.Quasithin.MS93.S4A44Lin
import CFSG.Quasithin.MS93.S46Ker
import CFSG.Quasithin.MS93.S46I464Lin
import CFSG.Quasithin.MS93.S4A432I
import CFSG.Quasithin.MS93.S4A441N

public section

namespace CFSG.Quasithin.MS93.S4A.L441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

section Grp

variable {G : Type*} [Group G]

private def commSub (H Y N : Subgroup G) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup G where
  carrier := {v | v ∈ H ∧ ∀ y ∈ Y, ⁅v, y⁆ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHN ha) _).mp (hb' y hy)) (ha' y hy)
  one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha)) _).mp (N.inv_mem (ha' y hy))

theorem commutator_iSup₂_le {ι : Type*} {s : Set ι} {A : ι → Subgroup G} {Y N H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hAH : ∀ i ∈ s, A i ≤ H)
    (hA : ∀ i ∈ s, ⁅A i, Y⁆ ≤ N) : ⁅⨆ i ∈ s, A i, Y⁆ ≤ N := by
  have hK : (⨆ i ∈ s, A i) ≤ commSub H Y N hHN := iSup₂_le fun i hi v hv =>
    ⟨hAH i hi hv, fun y hy => hA i hi (Subgroup.commutator_mem_commutator hv hy)⟩
  rw [Subgroup.commutator_le]
  intro v hv y hy
  exact (hK hv).2 y hy

theorem commutator_sup_le_of {A B Y N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hA : ⁅A, Y⁆ ≤ N) (hB : ⁅B, Y⁆ ≤ N) : ⁅A ⊔ B, Y⁆ ≤ N := by
  have hK : A ⊔ B ≤ commSub (A ⊔ B) Y N (sup_le hAN hBN) := by
    refine sup_le (fun v hv => ⟨Subgroup.mem_sup_left hv, fun y hy =>
      hA (Subgroup.commutator_mem_commutator hv hy)⟩) (fun v hv => ⟨Subgroup.mem_sup_right hv,
      fun y hy => hB (Subgroup.commutator_mem_commutator hv hy)⟩)
  rw [Subgroup.commutator_le]
  intro v hv y hy
  exact (hK hv).2 y hy

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem commutator_vv_qv_le_vv_of_le_bloc (hb : 4 < critDist 𝔛) {ν σ : Vtx 𝔛}
    (hν : IsMVtx 𝔛 ν) (hνσ : 𝔄 ν σ) (hB : ⁅Vv 𝔛 ν, Qv 𝔛 ν⁆ ≤ Bloc h.le L ν) :
    ⁅Vv 𝔛 ν, Qv 𝔛 ν⁆ ≤ Vv 𝔛 σ := by
  have h20 := h.hyp20
  have hQs : Qv 𝔛 ν ≤ stab 𝔛 ν := qv_le_stab _ ν
  have hQνσ : Qv 𝔛 ν ≤ stab 𝔛 σ := (qv_le_qv _ h20 hν hνσ).trans (qv_le_stab _ σ)
  have hQσν : Qv 𝔛 σ ≤ stab 𝔛 ν := qv_le_stab_of_adj _ hνσ.symm
  have hVσν : Vv 𝔛 σ ≤ Vv 𝔛 ν := D432.vv_le_vv_of_adj h hν hνσ
  have hVs : Vv 𝔛 ν ≤ stab 𝔛 ν := (vv_le_qv h (by omega) hν).trans hQs
  have hZn := stab_le_normalizer_zm 𝔛 ν
  set N := ⁅Vv 𝔛 σ, Qv 𝔛 ν⁆ ⊔ ZM 𝔛 ν with hN
  have hcB : ⁅Vv 𝔛 σ, Qv 𝔛 ν⁆ ≤ Bloc h.le L ν :=
    (Subgroup.commutator_mono hVσν le_rfl).trans hB
  have hLN : Ltil h.le L ν ≤ Subgroup.normalizer (N : Set 𝔘) := by
    refine le_normalizer_of_map_conj_le fun l hl => ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hxB := hcB hx
      rw [mem_bloc_iff h (by omega) hν] at hxB
      have h1 := hxB.2 l hl
      have e : (MulAut.conj l).toMonoidHom x = ⁅x, l⁆⁻¹ * x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
        (Subgroup.mem_sup_left hx)
    · rintro _ ⟨z, hz, rfl⟩
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hZn (ltil_le_stab h ν hl)) z).mp hz)
  have hQσN : Qv 𝔛 σ ≤ Subgroup.normalizer (N : Set 𝔘) :=
    (le_inf (le_normalizer_commutator ((qv_le_stab _ σ).trans (stab_le_normalizer_vv h σ))
      (hQσν.trans (stab_le_normalizer_qv _ ν))) (hQσν.trans hZn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hNn : stab 𝔛 ν ≤ Subgroup.normalizer (N : Set 𝔘) := by
    rw [stab_eq_ltil_sup_qv_adj h hfull hν hνσ]
    exact sup_le hLN hQσN
  have hNV : N ≤ Vv 𝔛 σ := by
    refine sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQνσ.trans (stab_le_normalizer_vv h σ))) ?_
    have := zv_le_vv h (α := σ) (ρ := ν) (by rw [dist_eq_one_of_adj _ hνσ.symm]; omega)
    rwa [zv_of_isMVtx _ hν] at this
  refine le_trans ?_ hNV
  rw [S46.vv_eq_iSup_vv hν]
  refine commutator_iSup₂_le hNn (fun ρ hρ => (D432.vv_le_vv_of_adj h hν hρ).trans hVs)
    fun ρ hρ => ?_
  obtain ⟨g, hg, rfl⟩ := exists_mem_stab_smul _ hνσ hρ
  have hVg : Vv 𝔛 (g • σ) = (Vv 𝔛 σ).map (MulAut.conj g).toMonoidHom := by
    rw [show Vv 𝔛 (g • σ) = Vi 𝔛 (g • σ) 2 from rfl, vi_smul]
  rw [hVg, ← map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ ν hg),
    ← Subgroup.map_commutator]
  exact (Subgroup.map_mono le_sup_left).trans (map_conj_eq_of_mem_normalizer (hNn hg)).le

theorem lt_relIndex_vv_of_not_isC1 (hFFcW : S4CFFcW) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ) (hC : CentHyp 𝔛) (hb : 4 < critDist 𝔛)
    {μ δ : Vtx 𝔛} (hc : IsCritical 𝔛 μ δ) {lam lam' : Vtx 𝔛} (hc' : IsCritical 𝔛 lam lam')
    (hlam : geo 𝔛 lam lam' 2 = δ)
    (h3 : ⁅ZM 𝔛 μ, Vv 𝔛 δ ⊓ Qv 𝔛 (geo 𝔛 μ δ 2)⁆ ≤ ZM 𝔛 δ)
    (hnot : ¬ IsC1 h.le L (Fintype.card F) δ (conjCl (stab 𝔛 δ) (ZM 𝔛 lam)) (ZM 𝔛 δ)) :
    Fintype.card F < (Qv 𝔛 (geo 𝔛 μ δ 2)).relIndex (Vv 𝔛 δ) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hδ : IsMVtx 𝔛 δ := hc.isMVtx_right _ h20
  have hlamM : IsMVtx 𝔛 lam := hc'.1
  have hdl : (puAmalgam h.le).treeGraph.dist lam δ = 2 := by
    rw [← hlam]
    exact dist_geo _ (by rw [hc'.2.1]; omega)
  have hdl' : (puAmalgam h.le).treeGraph.dist δ lam = 2 := by rw [tdist_comm]; exact hdl
  have hZlV : ZM 𝔛 lam ≤ Vv 𝔛 δ := by
    have := zv_le_vv h (α := δ) (ρ := lam) hdl'.le
    rwa [zv_of_isMVtx _ hlamM] at this
  have hWV : conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ≤ Vv 𝔛 δ :=
    conjCl_le_of_le_normalizer' hZlV (stab_le_normalizer_vv h δ)
  have hWn : stab 𝔛 δ ≤ Subgroup.normalizer (conjCl (stab 𝔛 δ) (ZM 𝔛 lam) : Set 𝔘) :=
    le_normalizer_conjCl _ _
  have hZW : ZM 𝔛 δ ≤ conjCl (stab 𝔛 δ) (ZM 𝔛 lam) := zm_le_conjCl_zm h hdl'
  have hQs : Qv 𝔛 δ ≤ stab 𝔛 δ := qv_le_stab _ δ
  have hVs : Vv 𝔛 δ ≤ stab 𝔛 δ := (vv_le_qv h (by omega) hδ).trans hQs
  have hWs : conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ≤ stab 𝔛 δ := hWV.trans hVs
  have hZμs : ZM 𝔛 μ ≤ stab 𝔛 δ :=
    zm_le_stab_of_isCritical _ h20 hb0 (ms22_iii _ h20 hb0 hC hc)
  have : Finite ↥(stab 𝔛 δ) := finite_stab h hδ
  have hfinV : Finite ↥(Vv 𝔛 δ) := Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  have hfinW : Finite ↥(conjCl (stab 𝔛 δ) (ZM 𝔛 lam)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hWs)
  by_contra hle
  push Not at hle
  apply hnot
  refine hFFcW G M T L h F inferInstance inferInstance φ hH μ δ hc ?_ _ hWn hZW hWV ?_
    ((conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ⊓ Qv 𝔛 (geo 𝔛 μ δ 2)) ⊔ ZM 𝔛 δ) le_sup_right
    (sup_le inf_le_left hZW) ?_ ?_
  · rw [vv_comm_eq_bot h hb hδ]
    exact bot_le
  ·
    intro hLle
    have hlρ : 𝔄 lam (geo 𝔛 lam lam' 1) := adj_geo_one_of_isCritical _ hb0 hc'
    have hρδ : 𝔄 (geo 𝔛 lam lam' 1) δ := by
      have := adj_geo _ (u := lam) (w := lam') (i := 1) (by rw [hc'.2.1]; omega)
      rwa [hlam] at this
    have hρH : ¬ IsMVtx 𝔛 (geo 𝔛 lam lam' 1) := by
      rw [← isMVtx_iff_of_adj _ hlρ]
      exact hlamM
    have hQρl : Qv 𝔛 (geo 𝔛 lam lam' 1) ≤ stab 𝔛 lam := qv_le_stab_of_adj _ hlρ.symm
    have hQρδ : Qv 𝔛 (geo 𝔛 lam lam' 1) ≤ stab 𝔛 δ := qv_le_stab_of_adj _ hρδ
    have hQδρ : Qv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 lam lam' 1) := qv_le_qv _ h20 hδ hρδ.symm
    have hBn : Qv 𝔛 (geo 𝔛 lam lam' 1) ≤ Subgroup.normalizer
        (((ZM 𝔛 lam ⊔ ZM 𝔛 δ) ⊔ ⁅conjCl (stab 𝔛 δ) (ZM 𝔛 lam), Qv 𝔛 δ⁆ : Subgroup 𝔘) :
          Set 𝔘) :=
      (le_inf ((le_inf (hQρl.trans (stab_le_normalizer_zm _ lam))
        (hQρδ.trans (stab_le_normalizer_zm _ δ))).trans
          (Subgroup.inf_normalizer_le_normalizer_sup _ _))
        (hQρδ.trans (le_normalizer_commutator hWn (stab_le_normalizer_qv _ δ)))).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have hLB : ∀ l ∈ Ltil h.le L δ, ∀ z ∈ ZM 𝔛 lam,
        l * z * l⁻¹ ∈ (ZM 𝔛 lam ⊔ ZM 𝔛 δ) ⊔ ⁅conjCl (stab 𝔛 δ) (ZM 𝔛 lam), Qv 𝔛 δ⁆ := by
      intro l hl z hz
      have hzW : z ∈ conjCl (stab 𝔛 δ) (ZM 𝔛 lam) := le_conjCl _ _ hz
      have h1 : ⁅z⁻¹, l⁆ ∈ ⁅conjCl (stab 𝔛 δ) (ZM 𝔛 lam), Qv 𝔛 δ⁆ ⊔ ZM 𝔛 δ :=
        hLle (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hzW) hl)
      have e : l * z * l⁻¹ = z * ⁅z⁻¹, l⁆ := by simp only [commutatorElement_def]; group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)) ?_
      exact (sup_le le_sup_right (le_sup_right.trans le_sup_left) :
        ⁅conjCl (stab 𝔛 δ) (ZM 𝔛 lam), Qv 𝔛 δ⁆ ⊔ ZM 𝔛 δ ≤
          (ZM 𝔛 lam ⊔ ZM 𝔛 δ) ⊔ ⁅conjCl (stab 𝔛 δ) (ZM 𝔛 lam), Qv 𝔛 δ⁆) h1
    have hWB : conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ≤
        (ZM 𝔛 lam ⊔ ZM 𝔛 δ) ⊔ ⁅conjCl (stab 𝔛 δ) (ZM 𝔛 lam), Qv 𝔛 δ⁆ := by
      refine iSup₂_le fun g hg => ?_
      rintro _ ⟨z, hz, rfl⟩
      have hg' : g ∈ ((Qv 𝔛 (geo 𝔛 lam lam' 1) ⊔ Ltil h.le L δ : Subgroup 𝔘) : Set 𝔘) := by
        rw [sup_comm, ← stab_eq_ltil_sup_qv_adj h hfull hδ hρδ.symm]
        exact hg
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hQρδ.trans (stab_le_normalizer_ltil h δ)), Set.mem_mul] at hg'
      obtain ⟨t, ht, l, hl, rfl⟩ := hg'
      have e : (MulAut.conj (t * l)).toMonoidHom z = t * (l * z * l⁻¹) * t⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hBn ht) _).mp (hLB l hl z hz)
    have hfinρ := finite_qv _ h20 hρH
    have hnil : Group.IsNilpotent ↥(Qv 𝔛 (geo 𝔛 lam lam' 1)) :=
      (isPGroup_qv _ h20 hρH).isNilpotent
    have hAρ : ZM 𝔛 lam ⊔ ZM 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 lam lam' 1) :=
      sup_le ((zm_le_qv_self _ hlamM hb0).trans (qv_le_qv _ h20 hlamM hlρ))
        ((zm_le_qv_self _ hδ hb0).trans hQδρ)
    have hWρ : conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ≤ Qv 𝔛 (geo 𝔛 lam lam' 1) :=
      (hWV.trans (vv_le_qv h (by omega) hδ)).trans hQδρ
    have hQA : Qv 𝔛 δ ≤ Subgroup.normalizer ((ZM 𝔛 lam ⊔ ZM 𝔛 δ : Subgroup 𝔘) : Set 𝔘) :=
      (le_inf (hQδρ.trans (hQρl.trans (stab_le_normalizer_zm _ lam)))
        (hQs.trans (stab_le_normalizer_zm _ δ))).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have hAW : ZM 𝔛 lam ⊔ ZM 𝔛 δ ≤ conjCl (stab 𝔛 δ) (ZM 𝔛 lam) :=
      sup_le (le_conjCl _ _) hZW
    have hWA := eq_of_le_sup_commutator hnil hAρ hWρ hQδρ hQA hAW hWB
    apply ms22_iv _ h20 hb0 hC hc'
    rw [hlam, xm_eq_zm h hfull hδ, ← hWA]
    exact hWn
  ·
    refine commutator_sup_le_of (inf_le_left.trans (hWs.trans (stab_le_normalizer_zm _ δ)))
      Subgroup.le_normalizer ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl (inf_le_inf_right _ hWV)).trans h3
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hZμs.trans (stab_le_normalizer_zm _ δ))
  ·
    have hne : ∀ H' : Subgroup 𝔘, H'.relIndex (conjCl (stab 𝔛 δ) (ZM 𝔛 lam)) ≠ 0 :=
      fun H' => Subgroup.index_ne_zero_of_finite
    have hne' : ∀ H' : Subgroup 𝔘, H'.relIndex (Vv 𝔛 δ) ≠ 0 :=
      fun H' => Subgroup.index_ne_zero_of_finite
    calc ((conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ⊓ Qv 𝔛 (geo 𝔛 μ δ 2)) ⊔ ZM 𝔛 δ).relIndex
          (conjCl (stab 𝔛 δ) (ZM 𝔛 lam))
        ≤ (conjCl (stab 𝔛 δ) (ZM 𝔛 lam) ⊓ Qv 𝔛 (geo 𝔛 μ δ 2)).relIndex
          (conjCl (stab 𝔛 δ) (ZM 𝔛 lam)) := Subgroup.relIndex_le_of_le_left le_sup_left (hne _)
      _ = (Qv 𝔛 (geo 𝔛 μ δ 2)).relIndex (conjCl (stab 𝔛 δ) (ZM 𝔛 lam)) := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
      _ ≤ (Qv 𝔛 (geo 𝔛 μ δ 2)).relIndex (Vv 𝔛 δ) :=
        Subgroup.relIndex_le_of_le_right hWV (hne' _)
      _ ≤ Fintype.card F := hle

omit hfull in
theorem commutator_uloc_eq_usup_of_lt {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) (hC : CentHyp 𝔛)
    (hb : 4 < critDist 𝔛) {μ σ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμσ : 𝔄 μ σ) {X : Subgroup 𝔘}
    (hXQ : X ≤ Qv 𝔛 σ) (hXc : Usup 𝔛 μ σ ≤ Subgroup.centralizer (X : Set 𝔘))
    (hlt : Fintype.card F < (Qv 𝔛 μ).relIndex X) :
    ⁅Uloc h.le L μ, X⁆ = Usup 𝔛 μ σ := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
  have hXs : X ≤ stab 𝔛 μ := hXQ.trans (qv_le_stab_of_adj _ hμσ.symm)
  have hUn : stab 𝔛 μ ≤ Subgroup.normalizer (Uloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hfix := commN_le_fixN_of_le_centralizer h hφ hμ hμσ hψ hXs hXc
  have hk2 := finrank_commN_qv h hφ hC hb hμ hμσ hψ
  have hcle : commN (natImage ψ X) ≤ commN (natImage ψ (Qv 𝔛 σ)) :=
    commN_mono (natImage_mono hXQ)
  have h2 : 2 ≤ Module.finrank F (fixN (natImage ψ X)) := hk2 ▸ Submodule.finrank_mono hfix
  have hcomm : commN (natImage ψ X) = commN (natImage ψ (Qv 𝔛 σ)) := by
    by_contra hne
    have hlt' : commN (natImage ψ X) < commN (natImage ψ (Qv 𝔛 σ)) := lt_of_le_of_ne hcle hne
    have h1 : Module.finrank F (commN (natImage ψ X)) ≤ 1 := by
      have := Submodule.finrank_lt_finrank_of_lt hlt'
      omega
    have hcard := S46.I464.card_le_of_finrank h2 h1
    rw [S46.card_natImage_eq_relIndex h hφ hμ hψ hXs, Nat.card_eq_fintype_card] at hcard
    omega
  have hUX : ⁅Uloc h.le L μ, X⁆ ≤ Uloc h.le L μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hXs.trans hUn)
  apply le_antisymm
  · intro u hu
    have huU : u ∈ Uloc h.le L μ := hUX hu
    have h1 := (mem_commutator_iff_natVec hψ hXs ⟨u, huU⟩).mp hu
    rw [hcomm] at h1
    exact (mem_usup_iff_natVec h hφ hμ hμσ hψ ⟨u, huU⟩).mpr h1
  · intro u hu
    have huU : u ∈ Uloc h.le L μ := usup_le_uloc h hφ hμ hμσ hu
    have h1 := (mem_usup_iff_natVec h hφ hμ hμσ hψ ⟨u, huU⟩).mp hu
    rw [← hcomm] at h1
    exact (mem_commutator_iff_natVec hψ hXs ⟨u, huU⟩).mpr h1

end Vertex

section EndA

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ)
include h hH

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem false_of_le_bloc (h32 : S32) (h2c : C441.S441C2Cent) (hFFcW : S4CFFcW)
    (hb : 4 < critDist 𝔛) {α α' : Vtx 𝔛} (hc : IsCritical 𝔛 α α')
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • α) (g • geo 𝔛 α α' 2))
    (hc1 : ∀ g : 𝔘, ¬ IsC1 h.le L (Fintype.card F) (g • geo 𝔛 α α' 2)
      (conjCl (stab 𝔛 (g • geo 𝔛 α α' 2)) (ZM 𝔛 (g • α))) (ZM 𝔛 (g • geo 𝔛 α α' 2)))
    (hA : ⁅Vv 𝔛 α, Qv 𝔛 α⁆ ≤ Bloc h.le L α) : False := by
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_S32 h32 h
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα : IsMVtx 𝔛 α := hc.1
  have hα' : IsMVtx 𝔛 α' := hc.isMVtx_right _ h20
  have hbe : Even (critDist 𝔛) := by
    rw [← hc.2.1]
    exact (even_dist_iff _ α α').mpr ⟨fun _ => hα', fun _ => hα⟩
  obtain ⟨k, hk⟩ := hbe
  have hb6 : 6 ≤ critDist 𝔛 := by omega
  obtain ⟨μ, ⟨g, hgμ, hgα⟩, hcμ, hgeoμ, h2⟩ := C441.claim2_of h hH C441.s441C2Wlog_holds
    C441.s441C2NonCrit_holds h2c hb hc hfail hc1
  set α2 := geo 𝔛 α' α 2 with hα2
  have hμ : IsMVtx 𝔛 μ := hcμ.1
  have hα2M : IsMVtx 𝔛 α2 := hcμ.isMVtx_right _ h20
  have hdμ : (puAmalgam h.le).treeGraph.dist μ α2 = critDist 𝔛 := hcμ.2.1
  have hdα'α2 : (puAmalgam h.le).treeGraph.dist α2 α' = 2 := by
    rw [tdist_comm]
    exact dist_geo _ (by rw [tdist_comm, hc.2.1]; omega)
  have e1 : ∀ g' : 𝔘, g' • μ = (g' * g⁻¹) • α := fun g' => by
    rw [mul_smul, ← hgμ, inv_smul_smul]
  have e2 : ∀ g' : 𝔘, g' • α = (g' * g⁻¹) • geo 𝔛 α α' 2 := fun g' => by
    rw [mul_smul, ← hgα, inv_smul_smul]
  have hfailμ : ∀ g' : 𝔘, ¬ Concl441 h.le L (g' • μ) (g' • geo 𝔛 μ α2 2) := by
    intro g'
    rw [hgeoμ, e2 g', e1 g']
    exact hfail (g' * g⁻¹)
  have hc1μ : ∀ g' : 𝔘, ¬ IsC1 h.le L (Fintype.card F) (g' • geo 𝔛 μ α2 2)
      (conjCl (stab 𝔛 (g' • geo 𝔛 μ α2 2)) (ZM 𝔛 (g' • μ))) (ZM 𝔛 (g' • geo 𝔛 μ α2 2)) := by
    intro g'
    rw [hgeoμ, e2 g', e1 g']
    exact hc1 (g' * g⁻¹)
  have h2' : ⁅⁅ZM 𝔛 μ, Qv 𝔛 (geo 𝔛 μ α2 2)⁆, ZM 𝔛 α'⁆ ≠ ⊥ := by rwa [hgeoμ]
  have h3μ := C441.commutator_zm_vv_inf_qv_eq h hφ hC hb hcμ hdα'α2 h2'
  rw [hgeoμ] at h3μ
  obtain ⟨μ₂, -, hcμ₂, hgeoμ₂, h2μ⟩ := C441.claim2_of h hH C441.s441C2Wlog_holds
    C441.s441C2NonCrit_holds h2c hb hcμ hfailμ hc1μ
  set α4 := geo 𝔛 α2 μ 2 with hα4
  have hα4M : IsMVtx 𝔛 α4 := hcμ₂.isMVtx_right _ h20
  have hdα2α4 : (puAmalgam h.le).treeGraph.dist α4 α2 = 2 := by
    rw [tdist_comm]
    exact dist_geo _ (by rw [tdist_comm, hdμ]; omega)
  have h2μ' : ⁅⁅ZM 𝔛 μ₂, Qv 𝔛 (geo 𝔛 μ₂ α4 2)⁆, ZM 𝔛 α2⁆ ≠ ⊥ := by rwa [hgeoμ₂]
  have h3μ₂ := C441.commutator_zm_vv_inf_qv_eq h hφ hC hb hcμ₂ hdα2α4 h2μ'
  obtain ⟨g₄, hg₄⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_geo_two _ h20 hb0 hc) hα4M
  have hE2 : Fintype.card F < (Qv 𝔛 (geo 𝔛 μ₂ α4 2)).relIndex (Vv 𝔛 α4) := by
    refine lt_relIndex_vv_of_not_isC1 h hfull hFFcW hH hC hb hcμ₂
      ((isCritical_smul _ g₄ α α').mpr hc) (by rw [geo_smul, hg₄]) ?_ ?_
    · rw [h3μ₂, Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((zm_le_stab_of_isCritical _ h20 hb0 (ms22_iii _ h20 hb0 hC hcμ₂)).trans
          (stab_le_normalizer_zm _ α4))
    · have := hc1 g₄
      rwa [hg₄] at this
  rw [hgeoμ₂] at hE2
  have hm₁ : 𝔄 μ (geo 𝔛 μ α2 1) := adj_geo_one_of_isCritical _ hb0 hcμ
  have hm₁H : ¬ IsMVtx 𝔛 (geo 𝔛 μ α2 1) := by rw [← isMVtx_iff_of_adj _ hm₁]; exact hμ
  have hα4e : α4 = geo 𝔛 μ α2 (critDist 𝔛 - 2) := by
    have := geo_symm (puAmalgam h.le) (u := α2) (w := μ) (i := 2) (by rw [tdist_comm, hdμ]; omega)
    rw [tdist_comm, hdμ] at this
    rw [hα4, ← this]
  have hp3 : 𝔄 α (geo 𝔛 μ α2 3) := by
    have := adj_geo _ (u := μ) (w := α2) (i := 2) (by omega)
    rwa [hgeoμ] at this
  have hd34 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 μ α2 3) α4 = critDist 𝔛 - 5 := by
    rw [hα4e, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hdm₁4 : (puAmalgam h.le).treeGraph.dist α4 (geo 𝔛 μ α2 1) = critDist 𝔛 - 3 := by
    rw [tdist_comm, hα4e, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hdμ4 : (puAmalgam h.le).treeGraph.dist μ α4 = critDist 𝔛 - 2 := by
    rw [hα4e]
    exact dist_geo _ (by omega)
  have hQαm : Qv 𝔛 α ≤ Qv 𝔛 (geo 𝔛 μ α2 1) := by
    have hadj : 𝔄 (geo 𝔛 μ α2 1) α := by
      have := adj_geo _ (u := μ) (w := α2) (i := 1) (by omega)
      rwa [hgeoμ] at this
    exact qv_le_qv _ h20 hα hadj.symm
  have hm₁s : Qv 𝔛 (geo 𝔛 μ α2 1) ≤ stab 𝔛 μ := qv_le_stab_of_adj _ hm₁.symm
  have hZα2m : ZM 𝔛 α2 ≤ Qv 𝔛 (geo 𝔛 μ α2 1) := zm_le_qv_geo_one _ h20 hb0 hcμ
  have hZα2α : ZM 𝔛 α2 ≤ Qv 𝔛 α := zm_le_qv_of_dist_lt _ hα2M (by
    rw [tdist_comm, ← hgeoμ, dist_geo_right _ (by omega), hdμ]; omega)
  have hZeq : ⁅ZM 𝔛 μ, Qv 𝔛 α⁆ = Usup 𝔛 μ (geo 𝔛 μ α2 1) := by
    rw [commutator_zm_eq_uloc h hfull hμ (hQαm.trans hm₁s), usup_eq_commutator_uloc h hfull hμ hm₁]
    set R' := ⁅Uloc h.le L μ, ZM 𝔛 α2⁆ with hR'
    have hRZ : R' ≤ ⁅Uloc h.le L μ, Qv 𝔛 α⁆ := Subgroup.commutator_mono le_rfl hZα2α
    have hRne : R' ≠ ⊥ := by
      rw [hR', ← commutator_zm_eq_uloc h hfull hμ (hZα2m.trans hm₁s)]
      exact ms22_ii _ h20 hb0 hC hcμ
    have hZs : ZM 𝔛 μ ≤ stab 𝔛 α2 := zm_le_stab_of_isCritical _ h20 hb0 (ms22_iii _ h20 hb0 hC hcμ)
    have hRZne : R' ≠ ⁅Uloc h.le L μ, Qv 𝔛 α⁆ := by
      intro he
      apply h2
      rw [commutator_zm_eq_uloc h hfull hμ (hQαm.trans hm₁s), ← he,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      have hRZ' : R' ≤ ZM 𝔛 α2 := by
        rw [hR', Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp
          (((uloc_le_zm h hfull hμ).trans hZs).trans (stab_le_normalizer_zm _ α2))
      exact (hRZ'.trans (zm_le_vv h hα2M)).trans
        (vv_le_centralizer_zm _ h20 hα' (by rw [tdist_comm, hdα'α2]; omega))
    obtain ⟨d₁, hd₁, hc₁⟩ := S46.card_commutator_uloc_le h hφ hμ hm₁ hZα2m
    obtain ⟨d₂, hd₂, hc₂⟩ := S46.card_commutator_uloc_le h hφ hμ hm₁ hQαm
    have hq : 2 ≤ Fintype.card F := by
      rw [← Nat.card_eq_fintype_card]
      exact Finite.one_lt_card
    have hfinZ : Finite ↥⁅Uloc h.le L μ, Qv 𝔛 α⁆ :=
      Nat.finite_of_card_ne_zero (by rw [hc₂]; positivity)
    have h1 : 1 ≤ d₁ := by
      by_contra h0
      apply hRne
      rw [← Subgroup.card_eq_one, hc₁, show d₁ = 0 by omega, pow_zero]
    have h12 : d₁ < d₂ := by
      have hle : Fintype.card F ^ d₁ ≤ Fintype.card F ^ d₂ := by
        rw [← hc₁, ← hc₂]
        exact Subgroup.card_le_of_le hRZ
      have hle' : d₁ ≤ d₂ := (Nat.pow_le_pow_iff_right (by omega)).mp hle
      rcases hle'.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        exact hRZne (Subgroup.eq_of_le_of_card_ge hRZ (by rw [hc₁, hc₂, heq]))
    have hcZ : Nat.card ↥⁅Uloc h.le L μ, Qv 𝔛 α⁆ = Fintype.card F ^ 2 := by
      rw [hc₂, show d₂ = 2 by omega]
    have hle : ⁅Uloc h.le L μ, Qv 𝔛 α⁆ ≤ ⁅Uloc h.le L μ, Qv 𝔛 (geo 𝔛 μ α2 1)⁆ :=
      Subgroup.commutator_mono le_rfl hQαm
    have hU2 := card_usup_le_sq h hfull hφ hμ hm₁
    rw [usup_eq_commutator_uloc h hfull hμ hm₁] at hU2
    have : Finite ↥(stab 𝔛 μ) := finite_stab h hμ
    have hUs : ⁅Uloc h.le L μ, Qv 𝔛 (geo 𝔛 μ α2 1)⁆ ≤ stab 𝔛 μ :=
      commutator_le_of_le ((uloc_le_zm h hfull hμ).trans
        ((zm_le_qv_self _ hμ hb0).trans (qv_le_stab _ μ))) hm₁s
    have : Finite ↥⁅Uloc h.le L μ, Qv 𝔛 (geo 𝔛 μ α2 1)⁆ :=
      Finite.of_injective _ (Subgroup.inclusion_injective hUs)
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hZμV : ZM 𝔛 μ ≤ Vv 𝔛 α := by
    have hd2 : (puAmalgam h.le).treeGraph.dist α μ ≤ 2 := by
      rw [tdist_comm, ← hgeoμ, dist_geo _ (by omega)]
    have := zv_le_vv h (α := α) (ρ := μ) hd2
    rwa [zv_of_isMVtx _ hμ] at this
  have hZV3 : ⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ≤ Vv 𝔛 (geo 𝔛 μ α2 3) :=
    (Subgroup.commutator_mono hZμV le_rfl).trans
      (commutator_vv_qv_le_vv_of_le_bloc h hfull hb hα hp3 hA)
  have hp3H : ¬ IsMVtx 𝔛 (geo 𝔛 μ α2 3) := by rw [← isMVtx_iff_of_adj _ hp3]; exact hα
  have hV3c : Vv 𝔛 (geo 𝔛 μ α2 3) ≤ Subgroup.centralizer (Vv 𝔛 α4 : Set 𝔘) := by
    rw [S46.vv_eq_iSup_of_not_isMVtx hp3H]
    refine iSup₂_le fun δ hδ => ?_
    have hδM : IsMVtx 𝔛 δ := by
      by_contra hδM
      exact hp3H ((isMVtx_iff_of_adj _ hδ).mpr hδM)
    have hdδ : (puAmalgam h.le).treeGraph.dist δ α4 + 2 < critDist 𝔛 := by
      have := dist_triangle (puAmalgam h.le) δ (geo 𝔛 μ α2 3) α4
      rw [tdist_comm _ δ (geo 𝔛 μ α2 3), dist_eq_one_of_adj _ hδ, hd34] at this
      omega
    exact Subgroup.le_centralizer_iff.mp (vv_le_centralizer_zm _ h20 hδM hdδ)
  have hXQ : Vv 𝔛 α4 ≤ Qv 𝔛 (geo 𝔛 μ α2 1) :=
    vv_le_qv_of_dist h hα4M (by rw [hdm₁4]; omega)
  have hXc : Usup 𝔛 μ (geo 𝔛 μ α2 1) ≤ Subgroup.centralizer (Vv 𝔛 α4 : Set 𝔘) :=
    (hZeq ▸ hZV3).trans hV3c
  have hZU := commutator_uloc_eq_usup_of_lt h hφ hC hb hμ hm₁ hXQ hXc hE2
  have hZμQ : ZM 𝔛 μ ≤ Qv 𝔛 α4 := zm_le_qv_of_dist_lt _ hμ (by rw [hdμ4]; omega)
  have hA4 : ⁅Vv 𝔛 α4, Qv 𝔛 α4⁆ ≤ Bloc h.le L α4 := by
    obtain ⟨g₅, hg₅⟩ := exists_smul_eq_of_isMVtx _ hα hα4M
    rw [← hg₅, show Vv 𝔛 (g₅ • α) = Vi 𝔛 (g₅ • α) 2 from rfl, vi_smul, qv_smul, bloc_smul h,
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono hA
  have hdα4α' : 0 < (puAmalgam h.le).treeGraph.dist α4 α' := by
    by_contra h0
    have he : α4 = α' := (dist_eq_zero_iff _).mp (by omega)
    have hdαα4 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 μ α2 2) (geo 𝔛 μ α2 (critDist 𝔛 - 2)) =
        critDist 𝔛 - 4 := by
      rw [dist_geo_geo _ (by omega) (by omega)]
      omega
    rw [hgeoμ, ← hα4e, he, hc.2.1] at hdαα4
    omega
  have hσ' : 𝔄 α4 (geo 𝔛 α4 α' 1) := adj_geo_one _ hdα4α'
  have hZσ : ⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ≤ Vv 𝔛 (geo 𝔛 α4 α' 1) := by
    rw [hZeq, ← hZU]
    refine (Subgroup.commutator_mono ((uloc_le_zm h hfull hμ).trans hZμQ) le_rfl).trans ?_
    rw [Subgroup.commutator_comm]
    exact commutator_vv_qv_le_vv_of_le_bloc h hfull hb hα4M hσ' hA4
  have hdσα' : (puAmalgam h.le).treeGraph.dist α' (geo 𝔛 α4 α' 1) + 2 < critDist 𝔛 := by
    have h1 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α4 α' 1) α' =
        (puAmalgam h.le).treeGraph.dist α4 α' - 1 := dist_geo_right _ (by omega)
    have h2 := dist_triangle (puAmalgam h.le) α4 α2 α'
    rw [hdα2α4, hdα'α2] at h2
    rw [tdist_comm, h1]
    omega
  apply h2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hZσ.trans (vv_le_centralizer_zm _ h20 hα' hdσα')

end EndA

end CFSG.Quasithin.MS93.S4A.L441

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S441EndB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
          (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
            (ZM (puAmalgam h.le) (g • α)))
          (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) →
      ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α

theorem s441End_of (h32 : S32) (h2c : C441.S441C2Cent) (hFFcW : S4CFFcW) (hB : S441EndB) :
    S441End := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hfail hc1
  exact L441.false_of_le_bloc h hH h32 h2c hFFcW hb hc hfail hc1
    (hB G M T L h F inferInstance inferInstance φ hH hb α α' hc hfail hc1)

end CFSG.Quasithin.MS93.S4A
