module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.FF81.CentACentralizer
import CFSG.LocalAnalysis.StandardType.FF81.CentAFusion83
import CFSG.LocalAnalysis.StandardType.FF81.CentAIdent
import CFSG.LocalAnalysis.StandardType.FF81.CentARadical

public section

namespace CFSG.StandardType.FF81.CentA

theorem centralizerA_holds : CentralizerA := by
  intro G _ _ _ _ hchar n b L hA K t hup hYd hlab
  obtain ⟨z, hP2, hFS⟩ := hup
  have hK0 : K 0 ≤ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    le_iSup (fun i : Fin (n + 2) => K (i : ℕ)) ⟨0, by omega⟩
  have hbY : b ∈ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    hK0 (hFS.K0 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have htY : t ∈ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    hK0 (hFS.K0 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  obtain ⟨S, hS, htS, -, hSt⟩ := hYd.syl
  obtain ⟨φ, hφt, hφb, hφL⟩ := exists_blockModel hA.n_cases hlab hA.model htY hbY hYd.le hA.ord
    hFS.ord_t hFS.inv_b hYd.cen_b ⟨S, hS, htS, hSt⟩
  obtain ⟨R, hRY, hRodd, hrad⟩ := exists_odd_radical hA hP2.loc hFS hYd
  have hset : CentASetting (n + 1) (⨆ i : Fin (n + 2), K (i : ℕ)) L R b t φ :=
    { m_cases := by rcases hA.n_cases with rfl | rfl <;> simp
      t_mem := htY
      b_mem := hbY
      L_le := hYd.le
      φ_t := hφt
      φ_b := hφb
      φ_L := hφL
      nor := hA.nor
      rad_le := hRY
      rad_odd := hRodd
      rad := hrad }
  exact centralizer_le_of_setting hchar hset (centAFus_of_afterProp2 hA hP2 hset)

end CFSG.StandardType.FF81.CentA

end
