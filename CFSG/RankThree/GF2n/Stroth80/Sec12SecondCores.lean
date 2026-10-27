module

public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondFalse
public import CFSG.RankThree.GF2n.Stroth80.Sec12SubWidth
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Sp

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth121SpCore_of_secondFalse (hZcard : Sec86ZCardStatement)
    (hirr : Sec86IrredStatement) (hS3 : SecondCfgFalse (IsSpModel 3) 4)
    (hS4 : SecondCfgFalse (IsSpModel 4) 8) : Stroth121SpCoreStatement := by
  intro G _ _ M Q Z B hc n h12 t ht htQ h83 hsub
  haveI := hc.normal_Q_in_M
  have h5 : Sec5Hyp hc n t := h12.toSec5 ht htQ
  have hsp : ∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m := by
    rcases h83 with ⟨-, hsp, -⟩ | ⟨-, hsp, -⟩
    · exact ⟨3, by norm_num, hsp⟩
    · exact ⟨4, by norm_num, hsp⟩
  have hs : Sec8Hyp hc n t := ⟨h5, hsp⟩
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hZN := sec8_Z0_le_CN hc hs hZ0
  have hcard := hZcard G M Q Z B hc n t hs Z0 hZ0
  have hI := hirr G M Q Z B hc n t hs Z0 hZ0
  rcases h83 with ⟨-, hsp3, hN⟩ | ⟨-, hsp4, hN⟩
  · exact hc.false_of_secondCfg ht hZ0 hZN hcard hI (k := 4) hN (P := IsSpModel 3)
      (fun q X Y _ _ e h => IsSpModel.congr e h) hsp3.quotSat (fun [_] => trivial) hsub hS3
  · exact hc.false_of_secondCfg ht hZ0 hZN hcard hI (k := 8) hN (P := IsSpModel 4)
      (fun q X Y _ _ e h => IsSpModel.congr e h) hsp4.quotSat (fun [_] => trivial) hsub hS4

theorem stroth121SpCore_of_4i (hZcard : Sec86ZCardStatement) (hirr : Sec86IrredStatement)
    (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement) : Stroth121SpCoreStatement :=
  stroth121SpCore_of_secondFalse hZcard hirr (secondCfgFalse_sp3 hgen hCi) secondCfgFalse_sp4

end Sp

section Omega

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth121OmegaCore_of_secondFalse (hZcard : Sec7ZCardStatement)
    (hSign : OmegaSignStatement) (hS1 : SecondCfgFalse (IsOmegaMinus 4) 8)
    (hS2 : SecondCfgFalse (IsOmegaPlus 5) 8) (hS3 : SecondCfgFalse (IsOmegaPlus 4) 4) :
    Stroth121OmegaCoreStatement := by
  intro G _ _ M Q Z B hc n h12 t ht htQ hex h79 hsub
  haveI := hc.normal_Q_in_M
  have h5 : Sec5Hyp hc n t := h12.toSec5 ht htQ
  have hlarge := h12.large t ht htQ
  have horth : ∃ m : ℕ, 2 ≤ m ∧ (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) := by
    rcases hex with ⟨hm | hm, -⟩ | ⟨hm, -, -⟩
    · exact ⟨4, by norm_num, Or.inr hm⟩
    · exact ⟨5, by norm_num, Or.inl hm⟩
    · exact ⟨4, by norm_num, Or.inl hm⟩
  have hnot : ¬ OmegaPlusNat hc t 2 := by
    rcases hex with ⟨hm | hm, -⟩ | ⟨hm, -, -⟩
    · exact not_omegaPlusNat_two_of (m := 4) (by norm_num) (Or.inr hm)
    · exact not_omegaPlusNat_two_of (m := 5) (by norm_num) (Or.inl hm)
    · exact not_omegaPlusNat_two_of (m := 4) (by norm_num) (Or.inl hm)
  have hs : Sec7Hyp hc n t := ⟨h5, hnot, horth, hlarge⟩
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hcard := hZcard G M Q Z B hc n t hs Z0 hZ0
  have hI : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 := by
    rcases h79 with ⟨Z1, hZ1, hirr⟩ | h3 | ⟨h4, hn16⟩
    · rw [← IsCentrePre.unique hZ0 hZ1]
      exact hirr
    · exfalso
      rcases hex with ⟨hm | hm, -⟩ | ⟨hm, -, -⟩
      · exact absurd (omegaPlusNat_eq_omegaMinusNat (by norm_num) h3 hm) (by norm_num)
      · exact absurd (h3.eq_of_plus hm) (by norm_num)
      · exact absurd (h3.eq_of_plus hm) (by norm_num)
    · exfalso
      rcases hex with ⟨hm | hm, -⟩ | ⟨hm, hn12, -⟩
      · exact hSign G M Q Z B hc t 4 (by norm_num) h4 hm
      · exact absurd (h4.eq_of_plus hm) (by norm_num)
      · omega
  rcases hex with ⟨hm | hm, hN⟩ | ⟨hm, hn, hN⟩
  · exact hc.false_of_secondCfg ht hZ0 hZN hcard hI (k := 8) hN (P := IsOmegaMinus 4)
      (fun q X Y _ _ e h => IsOmegaMinus.congr e h) hm.quotSat (fun [_] => trivial) hsub hS1
  · exact hc.false_of_secondCfg ht hZ0 hZN hcard hI (k := 8) hN (P := IsOmegaPlus 5)
      (fun q X Y _ _ e h => IsOmegaPlus.congr e h) hm.quotSat (fun [_] => trivial) hsub hS2
  · exact hc.false_of_secondCfg ht hZ0 hZN hcard hI (k := 4) hN (P := IsOmegaPlus 4)
      (fun q X Y _ _ e h => IsOmegaPlus.congr e h) hm.quotSat (fun [_] => trivial) hsub hS3

theorem stroth121OmegaCore_of_4i (hZcard : Sec7ZCardStatement) (hSign : OmegaSignStatement)
    (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement) : Stroth121OmegaCoreStatement :=
  stroth121OmegaCore_of_secondFalse hZcard hSign secondCfgFalse_omegaMinus4
    secondCfgFalse_omegaPlus5 (secondCfgFalse_omegaPlus4 hgen hCi)

theorem stroth12Omega6Minus_of_secondFalse (hZcard : Sec7ZCardStatement)
    (h78 : Stroth78Statement) (h79 : Stroth79Statement) (hSign : OmegaSignStatement)
    (hS : SecondCfgFalse (IsOmegaMinus 3) 4) : Stroth12Omega6MinusStatement := by
  intro G _ _ M Q Z B hc n h12 t ht htQ hm hsub
  haveI := hc.normal_Q_in_M
  have h5 : Sec5Hyp hc n t := h12.toSec5 ht htQ
  have hlarge := h12.large t ht htQ
  have hnot : ¬ OmegaPlusNat hc t 2 := not_omegaPlusNat_two_of (m := 3) le_rfl (Or.inr hm)
  have hs : Sec7Hyp hc n t := ⟨h5, hnot, ⟨3, by norm_num, Or.inr hm⟩, hlarge⟩
  have hC := h78 G M Q Z B hc n t h5 hlarge hnot 3 (by norm_num) (Or.inr hm)
  have hnN : n = 10 ∧ Nat.card (hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    unfold Conc78 at hC
    rcases hC with ⟨-, h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨h1, h2⟩
    all_goals omega
  have h79' := h79 G M Q Z B hc n t h5 hlarge hnot ⟨3, by norm_num, Or.inr hm⟩
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hcard := hZcard G M Q Z B hc n t hs Z0 hZ0
  have hI : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 := by
    rcases h79' with ⟨Z1, hZ1, hirr⟩ | h3 | ⟨h4, hn16⟩
    · rw [← IsCentrePre.unique hZ0 hZ1]
      exact hirr
    · exact (hSign G M Q Z B hc t 3 (by norm_num) h3 hm).elim
    · exact absurd (omegaPlusNat_eq_omegaMinusNat (by norm_num) h4 hm) (by norm_num)
  exact hc.false_of_secondCfg ht hZ0 hZN hcard hI (k := 4) hnN.2 (P := IsOmegaMinus 3)
    (fun q X Y _ _ e h => IsOmegaMinus.congr e h) hm.quotSat (fun [_] => trivial) hsub hS

theorem stroth12Omega6Minus_of_4i (hZcard : Sec7ZCardStatement) (h78 : Stroth78Statement)
    (h79 : Stroth79Statement) (hSign : OmegaSignStatement) (hgen : StrothGenByBStatement)
    (hCi : Stroth4iStatement) : Stroth12Omega6MinusStatement :=
  stroth12Omega6Minus_of_secondFalse hZcard h78 h79 hSign (secondCfgFalse_omegaMinus3 hgen hCi)

end Omega

end CFSG.RankThree.GF2n.Stroth80
