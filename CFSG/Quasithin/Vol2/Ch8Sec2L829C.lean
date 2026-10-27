module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829B
public import CFSG.Quasithin.Vol2.Ch8Sec2L829A
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L829C

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem nontrivial_star_82 {X : Type} [Group X] {k : ℕ}
    (hcases : (k = 1 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧ Nonempty (X ≃* DihedralGroup m)) ∨
      IsPSL 2 2 k X ∨ IsSz k X) : Nontrivial X := by
  rcases hcases with ⟨-, m, -, hm, ⟨e⟩⟩ | hP | hS
  · have : Nontrivial (DihedralGroup m) := by
      refine ⟨⟨DihedralGroup.r 1, 1, fun h => ?_⟩⟩
      have h1 : DihedralGroup.r (1 : ZMod m) = DihedralGroup.r 0 := h
      have h2 : (1 : ZMod m) = 0 := DihedralGroup.r.inj h1
      have : Fact (1 < m) := ⟨hm⟩
      exact one_ne_zero h2
    exact e.toEquiv.nontrivial
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 k hP).1
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 k hS).1

theorem concl829_of_82 (hE214 : AS_E_2_14)
    (hmod : StmtFSUModule) (hyp : Hyp7_0_2 G T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k) (hk2 : k ≤ 2)
    (hTO : T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G)) :
    Concl829 T I H h := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨-, hhI, hIC, hZ1, -, -, hMIeq, hker, -, hcases, -, -, -, -, -, -, -, -, h28, hchar,
    hTI⟩ := hC
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hnt := nontrivial_star_82 hcases
  have hIN := not_le_normalizer_ch82I_82 hV hhI hker hnt
  refine ⟨hTO, eq_ch82I_sup_82 hyp.fsu.sylow hH hIC.1 hMIeq hIN, ?_⟩
  have hP := e214P_eq_kerIn_82 hE214 hhI hIC hZ1 h28 hchar hTI hk2 hcases
  rw [hker] at hP
  exact le_normalizer_sup_ch82A_82 hTV hP hTO

end L829C

end CFSG.Quasithin.H13
