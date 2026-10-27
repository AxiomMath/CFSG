module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A23
public import CFSG.Quasithin.Vol2.Ch10SecFObl
public import CFSG.Quasithin.Vol2.Ch10SecQ4A17
public import CFSG.Quasithin.Vol2.Ch10SecQ4A18
public import CFSG.Quasithin.Vol2.Ch10SecQ4A19
public import CFSG.Quasithin.Vol2.Ch10SecQ4A22

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.QuasithinUnique.C1
open C10E4

theorem obl10_2_1E4A314_of (hF1 : FactA314NoSL25Block) (hF2 : FactA314B45)
    (hNq : Obl10_2_1E4Nonquasi) (hΔ : NoDelta5Statement) (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hA7 : Ch11.SecA.FactA7Cent) : Obl10_2_1E4A314 := by
  intro G _ _ T L I hyp h2 K hK hKs hKa X J hXs hsyl hJ hKJ hT1J
  have hJX := le_of_mem_cComp hJ
  have hTK := T1_le_normalizer_of_isLi h37 h38 hyp hK
  have hQT : pCoreOf 2 J ≤ Ch10.T1 T L := by
    have hTJ := A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hJ) hsyl
    exact (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTJ).trans inf_le_left
  have hQK := hQT.trans hTK
  have hTs := isSylowTwoOf_sup hsyl (hKJ.le.trans hJX)
  have hZ := blockZ_eq_bot_of_c113 h113 hTs hTK hKs hKa
  obtain ⟨hQeq, hcases⟩ := blockQ_eq_sup_of_c113 h113 hTs hTK hKs hKa
  rcases blockU_inf_pCoreOf hKs hZ hKJ.le with hUQ | hUQ
  · exact (false_of_blockU_inf_eq_bot h36' hF1 hΔ h113 hXs hsyl hJ hKJ hTK hQK hKs hKa
      hUQ).elim
  refine ⟨(commutator_fsuVM_le_blockU h113 hyp h2 hK hKs hKa).trans hUQ, ?_⟩
  by_cases hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)
  · rcases a7_or_hat hF2 h113 hXs hsyl hJ hKJ hTK hQK hKs hKa hUQ hq with he | ⟨hhat, hZW⟩
    · left
      refine ⟨he, ?_⟩
      rcases a318_alt7 h318 h36' h38 hA7 hXs hJ hq (Or.inl he) with h1 | ⟨hhat', -⟩
      · exact eq_oPrimeResidualOf_of_subgroupOf hJX h1
      · exfalso
        obtain ⟨e⟩ := he
        have h3 := hhat'.2.1
        rw [← Subgroup.map_center_eq e.symm, Subgroup.card_map_of_injective e.symm.injective,
          center_alt7', Subgroup.card_bot] at h3
        exact absurd h3 (by norm_num)
    · right
      refine ⟨hhat, exists_center_three hKs hKJ.le hQK hUQ hKa hJ hhat hZW, fun x hx hx3 => ?_⟩
      rcases a318_alt7 h318 h36' h38 hA7 hXs hJ hq (Or.inr hhat) with h1 | ⟨-, hθ⟩
      · exact mem_of_orderOf_three hx hx3 (Or.inl h1)
      · exact mem_of_orderOf_three hx hx3 (Or.inr hθ)
  · exfalso
    by_cases hZQ : K ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 J
    · exact false_of_nonquasi_of_blockQ_le h36' hXs hJ hKJ.le hKa (hQeq ▸ sup_le hUQ hZQ) hq
    · obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.mp hZQ
      have hcard : Nat.card (Subgroup.center ↥K) = 2 := by
        rcases hcases with h | h
        · exfalso
          rw [h] at hzZ
          obtain rfl := Subgroup.mem_bot.mp hzZ
          exact hzQ (Subgroup.one_mem _)
        · exact h
      exact hNq G T L I hyp h2 K hK hKs hKa X J hXs hsyl hJ hKJ hT1J hcard hq hUQ z hzZ.1 hzZ.2
        hzQ

end CFSG.Quasithin.Vol2.Ch10.SecF
