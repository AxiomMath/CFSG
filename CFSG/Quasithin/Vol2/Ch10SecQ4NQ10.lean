module

public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ9
public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

theorem obl10_2_1E4Nonquasi_of
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hshape : Stmt7_0_1_shape) (h113 : ASInputs.AS_C_1_13) :
    Obl10_2_1E4Nonquasi := by
  intro G _ _ T L I hyp h2 K hK hKs hKa X J hXs hsyl hJ hKJ _ hcard hq hUQ z hzK hzC hzQ
  have hs := hyp.fsu.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hz2 : z * z = 1 := by
    have hzc : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC k k.2)
    have h1 := orderOf_dvd_natCard (⟨⟨z, hzK⟩, hzc⟩ : ↥(Subgroup.center ↥K))
    rw [hcard, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  obtain ⟨D, hD1, hDodd, hD3, hDQ, hKD, hDD⟩ := C10P4F.exists_D h36 h113 h37 h38 hyp hK hKs hKa
    hXs hsyl hJ hKJ.le hq hUQ hzK hzC hzQ hz2
  have hVKU := C10E4.commutator_fsuVM_le_blockU h113 hyp h2 hK hKs hKa
  have hDV : D ≤ Subgroup.centralizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G) :=
    hDQ.trans (Subgroup.centralizer_le (hVKU.trans hUQ))
  have hL0T1 := C10P4F.le_normalizer_VK h37 h38 hyp hK
  have hH2 := C10P4F.pCoreOf_normalizer_VK_ne_bot hyp h2 hK
  have hS := C10P4F.isSylowTwoOf_normalizer_VK h311 h331 h37 h38 hshape hyp h2 hK
  have hKL0 : K ≤ fsuL0 T L := by
    rcases hK with rfl | ⟨t, ht, -, rfl⟩
    · exact SecA.le_fsuL0 T K
    · exact SecA.conjugate_le_fsuL0 ht
  obtain ⟨K1, hK1, hKK1, hK1n⟩ :=
    C10P4F.exists_K1 hLoc h37 h38 h39 hyp hK hH2 hS (hKL0.trans (le_sup_left.trans hL0T1))
  have hDH := hDV.trans (Subgroup.centralizer_le_normalizer _)
  have hDK1 := C10P4F.le_of_commutator_eq hDH hK1n (hKK1 hzK) hDD
  have hzQH := C10P4F.not_mem_pCoreOf_of_commutator_eq hDH hDodd hD1 hDD
  have hDM := C10P4F.le_fsuM_of_cComp hLoc h36 h331 h37 h38 hyp hL0T1 hH2 hS hK1 hK1n hKK1
    (C10E4.perfect_of_isAltType_five hKs hKa) (C10P4F.not_le_centralizer_VK hyp h2 hK) hDK1 hDV
    hDodd hD3 hD1 hDD hzK hz2 hzQH
  have hDK : D ⊓ K = ⊥ := by
    have hQK2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
    have hNodd : Odd (Nat.card (D ⊓ K : Subgroup G)) :=
      hDodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hbot := SecB.inf_eq_bot_of_two_odd hQK2 hNodd
    rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
      refine ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun o ho => ?_⟩
      have hoK := CFSG.LieType.BorelTits.pCoreOf_le 2 K ho
      have hc1 : ⁅o, x⁆ ∈ pCoreOf 2 K := by
        rw [commutatorElement_def]
        have h1 : x * o⁻¹ * x⁻¹ ∈ pCoreOf 2 K := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hx.2) _).mp (Subgroup.inv_mem _ ho)
        have e : o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ ho h1
      have hc2 : ⁅o, x⁆ ∈ D ⊓ K := by
        rw [commutatorElement_def]
        have h1 : o * x * o⁻¹ ∈ D ⊓ K :=
          ⟨(Subgroup.mem_normalizer_iff.mp (hKD hoK) x).mp hx.1, K.mul_mem (K.mul_mem hoK hx.2)
            (K.inv_mem hoK)⟩
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx)
      have hc : ⁅o, x⁆ = 1 := by
        have : ⁅o, x⁆ ∈ pCoreOf 2 K ⊓ (D ⊓ K) := ⟨hc1, hc2⟩
        rwa [hbot, Subgroup.mem_bot] at this
      exact (commutatorElement_eq_one_iff_mul_comm.mp hc)
    have : x ∈ pCoreOf 2 K ⊓ (D ⊓ K) := ⟨hKs.2.1 hxc, hx⟩
    rwa [hbot] at this
  apply hD1
  rw [← hDD, eq_bot_iff, Subgroup.commutator_le]
  intro d hd y hy
  have hdodd : Odd (orderOf d) := hDodd.of_dvd_nat (by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
    rwa [Subgroup.orderOf_mk] at this)
  have hdN := C10P4F.mem_normalizer_of_odd_of_isLi h37 h38 hyp hK (hDM hd) hdodd
  have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hzK) hy
  have h1 : ⁅d, y⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hdN y).mp hyK) (K.inv_mem hyK)
  have h2 : ⁅d, y⁆ ∈ D := by
    rw [commutatorElement_def]
    have h3 : y * d⁻¹ * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hKD hyK) _).mp (D.inv_mem hd)
    have e : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
    rw [e]
    exact D.mul_mem hd h3
  rw [← hDK]
  exact ⟨h2, h1⟩

end CFSG.Quasithin.Vol2.Ch10.SecF
