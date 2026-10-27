module

import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Sec16.Item166Res8ProofComm
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem exists_inverts_or_le_pPrimeCore_sup {Γ : Type} [Group Γ] [Finite Γ] {K Z S : Subgroup Γ}
    (hKn : K.Normal) (hZK : Z ≤ K) (hZ : Nat.card Z = 3)
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S K) (hZS : Z ≤ S)
    (hrk : CFSG.Open.pRank 3 K = 1) :
    (∃ n ∈ K, ∀ z ∈ Z, n * z * n⁻¹ = z⁻¹) ∨ K ≤ CFSG.pPrimeCore 3 Γ ⊔ S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSleK : S ≤ K := hS.le
  have hrankS : CFSG.Open.pRank 3 S ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hSleK).trans_eq hrk
  have hScyc : IsCyclic ↥S :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hS.isPGroup le_rfl hrankS
  have h3dvdZ : 3 ∣ Nat.card Z := by rw [hZ]
  obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 h3dvdZ
  let z0 : Γ := (z : Z)
  have hz0Z : z0 ∈ Z := z.2
  have hz0o : orderOf z0 = 3 := by
    rw [show z0 = (z : Γ) from rfl, Subgroup.orderOf_coe]
    exact hzo
  have hZzp : Z = Subgroup.zpowers z0 := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz0Z) ?_
    rw [Nat.card_zpowers, hz0o, hZ]
  have hz0K : z0 ∈ K := hZK hz0Z
  have hz0S : z0 ∈ S := hZS hz0Z
  obtain ⟨S', hS'⟩ := hS.exists_sylow_eq_subgroupOf
  have hS'cyc : IsCyclic ↥(S' : Subgroup ↥K) := by
    have hsubcyc : IsCyclic ↥(S.subgroupOf K) :=
      (Subgroup.subgroupOfEquivOfLe hS.le).isCyclic.mpr hScyc
    rwa [hS']
  let c : ↥K := ⟨z0, hz0K⟩
  have hcS' : c ∈ (S' : Subgroup ↥K) := by
    rw [hS', Subgroup.mem_subgroupOf]
    exact hz0S
  have hco : orderOf c = 3 := by
    rw [show c = (⟨z0, hz0K⟩ : ↥K) from rfl, Subgroup.orderOf_mk]
    exact hz0o
  rcases CFSG.RankThree.PartTwo.Sec17.Proof168Res8Comm.normalizer_le_centralizer_or_exists_inv
      S' hS'cyc hcS' hco with hNC | ⟨t, htN, htc⟩
  · set N' : Subgroup ↥K := (MonoidHom.transferSylow S' hNC).ker with hN'
    have hN'normal : N'.Normal := MonoidHom.normal_ker _
    have h3N' : ¬ 3 ∣ Nat.card N' := MonoidHom.not_dvd_card_ker_transferSylow S' hNC
    have hcopN' : Nat.Coprime 3 (Nat.card N') :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3N'
    have hN'core : N' ≤ CFSG.pPrimeCore 3 ↥K :=
      CFSG.le_pPrimeCore_of_normal_coprime hN'normal hcopN'
    have htop : CFSG.Open.GLAPPrimeCoreOf 3 (⊤ : Subgroup Γ) = CFSG.pPrimeCore 3 Γ := by
      change (CFSG.pPrimeCore 3 ↥(⊤ : Subgroup Γ)).map (⊤ : Subgroup Γ).subtype =
        CFSG.pPrimeCore 3 Γ
      rw [show (⊤ : Subgroup Γ).subtype =
          (Subgroup.topEquiv (G := Γ)).toMonoidHom from MonoidHom.ext fun _ => rfl]
      exact CFSG.pPrimeCore_map_iso 3 (Subgroup.topEquiv (G := Γ))
    have hKnormal : (K.subgroupOf (⊤ : Subgroup Γ)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : K ≤ ⊤)).mpr
        (Subgroup.le_normalizer_of_normal (H := K) (K := ⊤))
    have hmapcore : N'.map K.subtype ≤ CFSG.pPrimeCore 3 Γ := by
      have hle := CFSG.gLAPPrimeCoreOf_le_of_normal (G := Γ) (p := 3) (K := K)
        (H := ⊤) (by simp) hKnormal
      exact (Subgroup.map_mono hN'core).trans (hle.trans_eq htop)
    have hcompl := MonoidHom.ker_transferSylow_isComplement' S' hNC
    have hmap : K = N'.map K.subtype ⊔ S := by
      calc K = (⊤ : Subgroup ↥K).map K.subtype := by
              refine le_antisymm ?_ ?_
              · intro x hx
                exact Subgroup.mem_map_of_mem K.subtype
                  (Subgroup.mem_top (⟨x, hx⟩ : ↥K))
              · exact Subgroup.map_subtype_le (H := K) (⊤ : Subgroup ↥K)
        _ = (N' ⊔ (S' : Subgroup ↥K)).map K.subtype := by rw [hcompl.sup_eq_top]
        _ = N'.map K.subtype ⊔ (S' : Subgroup ↥K).map K.subtype :=
              Subgroup.map_sup N' (S' : Subgroup ↥K) K.subtype
        _ = N'.map K.subtype ⊔ S := by
              rw [hS', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSleK]
    right
    rw [hmap]
    exact sup_le_sup_right hmapcore S
  · refine Or.inl ⟨(t : Γ), t.2, ?_⟩
    have htcΓ : (t : Γ) * z0 * (t : Γ)⁻¹ = z0⁻¹ := by
      have := congrArg (fun x : ↥K => (x : Γ)) htc
      simpa [c] using this
    have hconj : MulAut.conj (t : Γ) z0 = z0⁻¹ := by
      simpa [MulAut.conj_apply] using htcΓ
    intro z hz
    have hzZ : z ∈ Subgroup.zpowers z0 := by
      rw [← hZzp]
      exact hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzZ
    calc (t : Γ) * z0 ^ k * (t : Γ)⁻¹ = MulAut.conj (t : Γ) (z0 ^ k) := by
            simp [MulAut.conj_apply]
      _ = (MulAut.conj (t : Γ) z0) ^ k := map_zpow _ _ _
      _ = (z0⁻¹) ^ k := by rw [hconj]
      _ = (z0 ^ k)⁻¹ := by rw [inv_zpow]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
