module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involutions in the Klein-four-by-odd kernel
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In the Klein-four branch, every involution of `O₂(Ĥ) U` already belongs
to `O₂(Ĥ)`. -/
public theorem firstCase_klein_involution_mem_twoCore_of_mem_VU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {z : G} (hzVU : z ∈ twoCoreOf c.Hhat ⊔ c.U)
    (hzI : IsInvolution z) :
    z ∈ twoCoreOf c.Hhat := by
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVK : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hVcent : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVnorm : V ≤ Subgroup.normalizer (c.U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv u hu
    have hcomm : v * u = u * v :=
      (Subgroup.mem_centralizer_iff.mp (hVcent hv) u hu).symm
    simpa [hcomm] using hu
  have hVUset : ((V ⊔ c.U : Subgroup G) : Set G) =
      (V : Set G) * (c.U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right V c.U hVnorm
  have hzprod : z ∈ (V : Set G) * (c.U : Set G) := by
    rw [← hVUset]
    exact hzVU
  rcases Set.mem_mul.mp hzprod with ⟨v, hv, u, hu, hvuz⟩
  have hv2 : v * v = 1 := by
    simpa [pow_two] using congrArg Subtype.val (hVK.mul_self (⟨v, hv⟩ : V))
  have hcomm : v * u = u * v :=
    (Subgroup.mem_centralizer_iff.mp (hVcent hv) u hu).symm
  have hu2 : u ^ 2 = 1 := by
    calc
      u ^ 2 = (v * v) * (u * u) := by rw [pow_two, hv2]; simp
      _ = v * (v * u) * u := by group
      _ = v * (u * v) * u := by rw [hcomm]
      _ = (v * u) ^ 2 := by rw [pow_two]; group
      _ = z ^ 2 := by rw [← hvuz]
      _ = 1 := hzI.2
  have huord2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have huordU : orderOf u ∣ Nat.card c.U :=
    Subgroup.orderOf_dvd_natCard c.U hu
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    have h26 := theorem_2_6 hmin c
    rw [h26.1]
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
    rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
          c.Hhat.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have huordCop : Nat.Coprime 2 (orderOf u) :=
    Nat.Coprime.of_dvd_right huordU hUcop
  have huord1 : orderOf u = 1 := huordCop.symm.eq_one_of_dvd huord2
  have hu1 : u = 1 := orderOf_eq_one_iff.mp huord1
  rw [← hvuz, hu1]
  simpa using hv

end CFSG.GorensteinWalter
