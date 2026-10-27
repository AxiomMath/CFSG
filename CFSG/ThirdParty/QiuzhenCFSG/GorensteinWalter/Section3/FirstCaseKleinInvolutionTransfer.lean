module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCentralizerSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinSylowTransfer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionExtraction
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
open scoped Pointwise
namespace CFSG.GorensteinWalter
noncomputable section
universe u

/-- Restriction (5) transfer: an outside involution inverting a nontrivial `U`-element can be replaced by one in `Ĥ \ V`. -/
public theorem firstCase_klein_involution_transfer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∀ {x y : G}, x ∈ c.U → x ≠ 1 → IsInvolution y →
      y ∉ c.Hhat → y * x * y⁻¹ = x⁻¹ →
      ∃ s : G, s ∈ c.Hhat ∧ IsInvolution s ∧
        s ∉ twoCoreOf c.Hhat ∧ s * x * s⁻¹ = x⁻¹ := by
  intro x y hxU hxne hy hyH hyInv
  let V : Subgroup G := twoCoreOf c.Hhat
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  obtain ⟨Q, hVQ, hQnorm⟩ :=
    firstCase_klein_centralizer_sylow_normalizer_le_Hhat hmin c hfirst hklein hxU
  have hQnorm' : Subgroup.normalizer
      (((Q : Subgroup C).map C.subtype : Subgroup G) : Set G) ≤ c.Hhat := by
    simpa [C] using hQnorm
  obtain ⟨n, hnQ, hnInv⟩ :=
    firstCase_klein_sylow_normalizer_inverter hy hyInv Q
  have hnH : n ∈ c.Hhat := hQnorm' hnQ
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    have h26 := theorem_2_6 hmin c
    rw [h26.1]
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
    have hcard : Nat.card (oddCoreOf c.Hhat) =
        Nat.card (pPrimeCore 2 c.Hhat) := by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
          c.Hhat.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hxInvNe : x⁻¹ ≠ x := by
    intro hxInvEq
    have hxSq : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := by rw [pow_two]
        _ = x * x⁻¹ := by rw [hxInvEq]
        _ = 1 := mul_inv_cancel x
    have hxOrd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hxSq
    have hxOrdU : orderOf x ∣ Nat.card c.U :=
      Subgroup.orderOf_dvd_natCard c.U hxU
    have hcopOrd : Nat.Coprime 2 (orderOf x) :=
      Nat.Coprime.of_dvd_right hxOrdU hUcop
    have hxOrd1 : orderOf x = 1 := hcopOrd.symm.eq_one_of_dvd hxOrd2
    exact hxne (orderOf_eq_one_iff.mp hxOrd1)
  let A := c.Hhat
  let VA : Subgroup A := pCore 2 A
  let SA : Sylow 2 A := c.S.subtype ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)
  have hSAcard : Nat.card (SA : Subgroup A) = 8 := by
    calc
      Nat.card (SA : Subgroup A) = Nat.card (c.S : Subgroup G) := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)).toEquiv
      _ = 8 := firstCase_klein_S_card hmin c hfirst hklein
  have hm2 : c.m = 2 := by
    have hScard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
      obtain ⟨e⟩ := c.dihedralEquiv
      simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    have hmPow : 2 ^ c.m = 4 := by
      have h8 := firstCase_klein_S_card hmin c hfirst hklein
      omega
    apply (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2))
    simpa using hmPow
  obtain ⟨eS0⟩ := c.dihedralEquiv
  let eSA : SA ≃* c.S := by
    change (c.S.subgroupOf c.Hhat) ≃* c.S
    exact Subgroup.subgroupOfEquivOfLe
      ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)
  have eS0' : c.S ≃* DihedralGroup 4 := by
    rw [hm2] at eS0
    exact eS0
  let eS : SA ≃* DihedralGroup 4 := by
    exact eSA.trans eS0'
  let φ : A →* MulAut G := MulAut.conj.comp A.subtype
  have hφVx : ∀ v : A, v ∈ VA → φ v x = x := by
    intro v hv
    have hvV : (v : G) ∈ V := by
      exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    have hcent : (v : G) * x = x * (v : G) := by
      exact (Subgroup.mem_centralizer_iff.mp (by
        have h26 := theorem_2_6 hmin c
        have hVC : V ≤ Subgroup.centralizer (c.U : Set G) := by
          simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
        exact hVC hvV) x hxU).symm
    change (v : G) * x * (v : G)⁻¹ = x
    rw [hcent]
    group
  obtain ⟨sA, hsAI, hsAnot, hsAinv⟩ :=
    firstCase_klein_extract_inverting_involution VA SA (by
      dsimp [VA]
      infer_instance) hklein hSAcard eS φ x hφVx (a := ⟨n, hnH⟩)
      (by simpa [φ, MulAut.conj_apply] using hnInv) hxInvNe
  let s : G := sA
  have hsH : s ∈ c.Hhat := sA.2
  have hsI : IsInvolution s := by
    refine ⟨?_, ?_⟩
    · intro hs1
      apply hsAI.1
      exact Subtype.ext hs1
    · exact congrArg Subtype.val hsAI.2
  have hsV : s ∉ V := by
    intro hs
    apply hsAnot
    rcases Subgroup.mem_map.mp hs with ⟨w, hw, hws⟩
    change sA ∈ pCore 2 A
    have hwsA : (w : A) = sA := by
      apply Subtype.ext
      exact hws
    rw [← hwsA]
    exact hw
  have hsInv : s * x * s⁻¹ = x⁻¹ := by
    simpa [s, φ, MulAut.conj_apply] using hsAinv
  exact ⟨s, hsH, hsI, hsV, hsInv⟩

end
end CFSG.GorensteinWalter
