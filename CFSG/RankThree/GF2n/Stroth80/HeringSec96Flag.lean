module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec96Stmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

open HS9


theorem sec96Flag_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    HS9.Sec96FlagStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs X Y hsplit
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hYR : Y ≤ Rt M (LB M Q B) t := hsplit.1.2.2.2.1
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hflag, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  have hfac := sec97_factor h34 h311a hc hs hsplit hK φ hrange hker
  have hHY : ∀ h, h ∈ (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  obtain ⟨Φ, w₀, hA, hw₀, hu⟩ := natural_module_data hfac hdet hu0
  have hdetH : ∀ h ∈ (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ),
      ∀ X : Matrix (Fin 2) (Fin 2) K, (h X).det = X.det := by
    intro h hh X
    rcases hfac with hf | hf <;> rw [hf] at hh
    · obtain ⟨A, rfl⟩ := hh
      show (rho' K (A, 1) X).det = X.det
      rw [rho'_inl_apply, Matrix.det_mul, A.det_coe, one_mul]
    · obtain ⟨B', rfl⟩ := hh
      show (rho' K (1, B') X).det = X.det
      rw [rho'_inr_apply, Matrix.det_mul, (B'⁻¹).det_coe, mul_one]
  have hdetΦ : ∀ w, (Φ w).det = 0 := by
    intro w
    by_cases hw : w = 0
    · rw [hw, map_zero]
      simp
    · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw₀ hw
      obtain ⟨h, hh, hact⟩ := hA.lift g
      have hΦw : Φ w = h (Φ w₀) := by rw [hact, hg]
      rw [hΦw, hdetH h ((hHY h).mpr hh) (Φ w₀), ← hu]
      exact hdet
  have hQdet : ∀ v, quadPlus 2 K v = (toMat K v).det := fun v =>
    (congrFun (coe_quadPlus 2 K) v).trans (det_toMat K v).symm
  intro x hx
  obtain ⟨hxV, w', hw'⟩ :=
    (uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY hA hw₀ hu x).mp hx
  have hx' : toMat K (secVec ψ ⟨x, hxV⟩) = Φ w' := hw'.symm
  have hpolar : polar (quadPlus 2 K) u (secVec ψ ⟨x, hxV⟩) = 0 := by
    show quadPlus 2 K (u + secVec ψ ⟨x, hxV⟩) - quadPlus 2 K u -
      quadPlus 2 K (secVec ψ ⟨x, hxV⟩) = 0
    rw [hQdet, hQdet, hQdet, map_add, hu, hx', ← map_add, hdetΦ, hdetΦ, hdetΦ]
    simp
  obtain ⟨w, hwmem, hwsv⟩ := (hflag _).mpr hpolar
  have hz : x * (w : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨x, hxV⟩ w).mp hwsv.symm
  have hxe : x = (x * (w : G)⁻¹) * (w : G) := by group
  rw [hxe, sup_comm]
  exact Subgroup.mul_mem_sup hz hwmem

end CFSG.RankThree.GF2n.Stroth80
