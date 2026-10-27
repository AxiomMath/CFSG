module

public import CFSG.RankThree.GF2n.Stroth80.Sec37Geom
public import CFSG.RankThree.GF2n.Stroth80.Sec41
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

namespace Mn37

theorem exists_mul_ne_mul_SL2 (K : Type) [Field K] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩
  have h00 : (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end Mn37

theorem stroth37Statement_of_geom (h34 : Stroth34Statement)
    (hGeom : Geom37Statement) (hCom : Stroth37CommutingStatement) : Stroth37Statement := by
  intro G _ _ M Q Z B hQM hc n hw hn hno hgen hTI
  obtain ⟨h4, k, hk, hsimple, ⟨e⟩⟩ :=
    hGeom G M Q Z B hc n hw hn hno hgen (hCom G M Q Z B hc n hw hn hno hgen hTI)
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  have hnab : ∃ a b : ↥(bar M Q (Lgen M (LB M Q B))), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Mn37.exists_mul_ne_mul_SL2 (GaloisField 2 (k * 3))
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h
  haveI := hsimple
  have hq : IsQuasisimple ↥(bar M Q (Lgen M (LB M Q B))) :=
    (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  haveI hN0 : (bar M Q (Lgen M (LB M Q B))).Normal := normal_bar_Lgen (LB M Q B)
  have hcomp : IsComponent (bar M Q (Lgen M (LB M Q B))) := ⟨hq, hN0.isSubnormal⟩
  have hlayer : bar M Q (Lgen M (LB M Q B)) = layer (Mbar M Q) := by
    rw [layer.eq_sSup]
    refine le_antisymm (le_sSup hcomp) (sSup_le fun C hC => ?_)
    rcases LocalCores.component_normal_subgroup hC hN0 with h | h
    · exact h
    · exfalso
      have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      refine hc.false_of_comm h35 C hC.1 fun x hx t ht => ?_
      have hmem : (QuotientGroup.mk t : Mbar M Q) ∈ bar M Q (Lgen M (LB M Q B)) :=
        ⟨t, Subgroup.mem_subgroupOf.mpr (le_Lgen_self M (LB M Q B) ht), rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp (hcen hx) _ hmem).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := hc.hyp.q4
    rw [hk] at this
    norm_num at this
  refine ⟨h4, hlayer, GaloisField 2 (k * 3), inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · rw [GaloisField.card 2 (k * 3) (by omega), hk, ← pow_mul]
  · exact (MulEquiv.subgroupCongr hlayer.symm).trans
      (e.trans (specialLinearGroupEquivStatedSL 2 _))

end CFSG.RankThree.GF2n.Stroth80
