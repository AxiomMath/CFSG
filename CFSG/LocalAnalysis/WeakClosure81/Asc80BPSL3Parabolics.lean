module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.WeakClosure81.FiveCoatom
import CFSG.RankThree.PartTwo.Sec19.KF1923L3Par

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Late Matrix

theorem mem_maximalParabolics_subgroupOf {Q : Type} [Group Q] [Finite Q] {L R : Subgroup Q}
    (hR : IsMaxParabolicMod ⊥ L R) : R.subgroupOf L ∈ maximalParabolics (↥L) 2 := by
  obtain ⟨-, hRL, hmax, S, -, hSL, hpow, hidx, hN⟩ := hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    intro s
    obtain ⟨k, hk⟩ := hpow s s.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hSyl : IsSylowIn 2 S L := ⟨hSL, hS2, hidx⟩
  refine ⟨isCoatom_subgroupOf ⟨hRL, hmax⟩, ?_⟩
  refine ⟨normalizer ((hSyl.toSylow : Subgroup ↥L) : Set ↥L), ⟨hSyl.toSylow, rfl⟩, ?_⟩
  rw [hSyl.coe_toSylow, ← Subgroup.subgroupOf_normalizer_eq hSL]
  intro x hx
  exact hN ⟨x.2, hx⟩

theorem graphExponent_eq_one_of_actsOnDynkinMod {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    {K : Type} [Field K] [Finite K] [CharP K 2] (e : ↥L ≃* projectiveSL 3 K) {a : Q}
    (α : MulAut ↥L) (hα : ∀ x : ↥L, (α x : Q) = a * (x : Q) * a⁻¹)
    (haD : ActsOnDynkinMod ⊥ L a) (D : GL (Fin 3) K) (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    (hstd : MulAut.congr e α = conjAut 3 K D * fieldAut 3 K σ * dualAut 3 K ^ ε) : ε = 1 := by
  by_contra hε1
  have hε0 : ε = 0 := by omega
  obtain ⟨-, R, hR, hconj⟩ := haD
  have hRmem : R.subgroupOf L ∈ maximalParabolics (↥L) 2 :=
    mem_maximalParabolics_subgroupOf hR
  have hRpar : CFSG.RankThree.PartTwo.Sec18.IsMaxParabolicRankTwo (R.subgroupOf L) := by
    obtain ⟨hc, B₀, hB₀, hle⟩ := hRmem
    obtain ⟨T, rfl⟩ := hB₀
    exact ⟨hc, T, hle⟩
  obtain ⟨W, -, hRW⟩ := kfl3_stab_of_isMax_map e hRpar
  rw [hε0, pow_zero, mul_one] at hstd
  set U : Submodule K (Fin 3 → K) :=
    (coordImage σ W).map (mulVecLin (D : Matrix (Fin 3) (Fin 3) K)) with hU
  have hfinU : Module.finrank K W = Module.finrank K U := by
    rw [hU, kfl3_finrank_map, CFSG.RankThree.PartTwo.Sec20.Res7.finrank_coordImage]
  obtain ⟨y, hy⟩ := kfl3_stab_conj_of_finrank hfinU
  have hstep : (projStabilizer W).map
      (MulEquiv.toMonoidHom (conjAut 3 K D * fieldAut 3 K σ)) = projStabilizer U := by
    rw [hU, show MulEquiv.toMonoidHom (conjAut 3 K D * fieldAut 3 K σ) =
        (MulEquiv.toMonoidHom (conjAut 3 K D)).comp
          (MulEquiv.toMonoidHom (fieldAut 3 K σ)) from rfl,
      ← Subgroup.map_map,
      show MulEquiv.toMonoidHom (fieldAut 3 K σ) =
        (↑(fieldAut 3 K σ) : projectiveSL 3 K →* projectiveSL 3 K) from rfl,
      kfl3_tr_field,
      show MulEquiv.toMonoidHom (conjAut 3 K D) =
        (↑(conjAut 3 K D) : projectiveSL 3 K →* projectiveSL 3 K) from rfl,
      kfl3_tr_conj]
  have hkey2 : ((R.subgroupOf L).map α.toMonoidHom).map e.toMonoidHom = projStabilizer U := by
    calc ((R.subgroupOf L).map α.toMonoidHom).map e.toMonoidHom
        = ((R.subgroupOf L).map e.toMonoidHom).map
            (MulEquiv.toMonoidHom (MulAut.congr e α)) :=
          (kfl3_map_congr e α (R.subgroupOf L)).symm
      _ = ((R.subgroupOf L).map e.toMonoidHom).map
            (MulEquiv.toMonoidHom (conjAut 3 K D * fieldAut 3 K σ)) := by rw [hstd]
      _ = (projStabilizer W).map
            (MulEquiv.toMonoidHom (conjAut 3 K D * fieldAut 3 K σ)) := by rw [hRW]
      _ = projStabilizer U := hstep
  have hkey3 : ((R.subgroupOf L).map (MulAut.conj (e.symm y)).toMonoidHom).map
      e.toMonoidHom = projStabilizer U := by
    rw [kfl3_map_conj_map e (R.subgroupOf L) (e.symm y), hRW, MulEquiv.apply_symm_apply]
    exact hy.symm
  have hαeq : (R.subgroupOf L).map α.toMonoidHom =
      (R.subgroupOf L).map (MulAut.conj (e.symm y)).toMonoidHom :=
    Subgroup.map_injective (f := e.toMonoidHom) e.injective (hkey2.trans hkey3.symm)
  have hcomp_a : L.subtype.comp α.toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp L.subtype := by
    ext x
    simpa [MulAut.conj_apply] using hα x
  have hLa : ((R.subgroupOf L).map α.toMonoidHom).map L.subtype =
      R.map (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.map_map, hcomp_a, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hR.2.1.le]
  have hcomp_l : L.subtype.comp (MulAut.conj (e.symm y)).toMonoidHom =
      (MulAut.conj ((e.symm y : ↥L) : Q)).toMonoidHom.comp L.subtype := by
    ext x
    simp [MulAut.conj_apply]
  have hLl : ((R.subgroupOf L).map (MulAut.conj (e.symm y)).toMonoidHom).map L.subtype =
      R.map (MulAut.conj (((e.symm y : ↥L) : Q))).toMonoidHom := by
    rw [Subgroup.map_map, hcomp_l, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hR.2.1.le]
  have hRmap : R.map (MulAut.conj a).toMonoidHom =
      R.map (MulAut.conj (((e.symm y : ↥L) : Q))).toMonoidHom := by
    rw [← hLa, ← hLl, hαeq]
  have hconj_eq : conjSubgroup R a⁻¹ = conjSubgroup R (((e.symm y : ↥L) : Q))⁻¹ := by
    simp only [conjSubgroup, inv_inv]
    exact hRmap
  have hfinal : conjSubgroup R (a⁻¹ * ((e.symm y : ↥L) : Q)) = R := by
    rw [← conjSubgroup_conjSubgroup R a⁻¹ (((e.symm y : ↥L) : Q)), hconj_eq,
      conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  exact hconj ((e.symm y : ↥L) : Q) (e.symm y).2 hfinal

end CFSG.LocalAnalysis.WeakClosure81

end
