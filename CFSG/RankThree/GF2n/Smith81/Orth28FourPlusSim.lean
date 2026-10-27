module

public import CFSG.RankThree.GF2n.Smith81.Orth28FourPlusAct
public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIPBot

public section

namespace CFSG.RankThree.GF2n.Smith81.FourPlus

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.RankThree.GF2n.Smith81.OrthTN CFSG.RankThree.GF2n.Smith81.D2
open scoped Matrix MatrixGroups

theorem relIndex_map_ker_le {G : Type} [Group G] {H : Subgroup G}
    (f : ↥H →* Equiv.Perm (Fin 3)) : (f.ker.map H.subtype).relIndex H ≤ 6 := by
  rw [Subgroup.relIndex]
  have : (f.ker.map H.subtype).subgroupOf H = f.ker := by
    rw [Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  rw [this, Subgroup.index_ker]
  calc Nat.card f.range ≤ Nat.card (Equiv.Perm (Fin 3)) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 6 := by rw [Nat.card_perm]; simp [Nat.factorial]

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem tensorFactor_of_permHom_eq_one (F : Data M Q Z B) (m : ↥(H0 M Z))
    (hm : permHom F m = 1) : OrthCaseI.TensorFactor F.C (m : G) := by
  obtain ⟨h, hu, hh⟩ := exists_kron_of_permHom_eq_one F m hm
  obtain ⟨c, s, hc0, hs, hks⟩ := exists_scalar_sl h hu
  have hs3 : ![s 0, s 1, s 2] = s := by
    funext i
    fin_cases i <;> rfl
  have hupd : (Function.update ![s 0, s 1, s 2] 0 (c • ![s 0, s 1, s 2] 0) :
      Fin 3 → Mat2 F.C.K) = ![c • s 0, s 1, s 2] := by
    funext i
    fin_cases i <;> simp
  refine ⟨c • s 0, swEquiv F.μ ⟨s 1, hs 1⟩ ⟨s 2, hs 2⟩, 1, ?_, one_ne_zero, ?_, ?_⟩
  · rw [Matrix.det_smul, hs 0, Fintype.card_fin]
    simpa using hc0
  · intro v
    rw [one_mul]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (swEquiv_mem_orthogonalGroup F.det_eq ⟨s 1, hs 1⟩ ⟨s 2, hs 2⟩) v
  · have hcoe : ⇑(swEquiv F.μ ⟨s 1, hs 1⟩ ⟨s 2, hs 2⟩) = swL F.μ (s 1) (s 2) :=
      coe_swEquiv F.μ ⟨s 1, hs 1⟩ ⟨s 2, hs 2⟩
    rw [hcoe]
    refine (actsAsTensor_swL_iff F m _ _ _).mpr fun v => ?_
    rw [hh v, hks, ← hupd, kronMap_smul_apply, hs3]
    rfl

theorem orthSimFourPlus_of (hT : OrthTacitStatement) : OrthSimFourPlusStatement := by
  intro G _ _ M Q Z B hc C h4 hTSP
  let F := Data.ofFrame hc (noA2_of_tacit hT hc) C h4 hTSP
  refine ⟨(permHom F).ker.map (H0 M Z).subtype, Subgroup.map_subtype_le _,
    relIndex_map_ker_le (permHom F), ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  exact tensorFactor_of_permHom_eq_one F m hm

end CFSG.RankThree.GF2n.Smith81.FourPlus

