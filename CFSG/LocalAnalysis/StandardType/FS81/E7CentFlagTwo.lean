module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.RankThree.PartTwo.Sec3.SectionModuleBound

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

private lemma fs81FlagTwo_odd_eq_one {X : Type} [Group X] {H Q C W Z N : Subgroup X}
    (hQ : IsPGroup 2 Q) (hZW : Z ≤ W) (hWC : W ≤ C) (hCQ : C ≤ Q) (hNH : N ≤ H)
    (hHCQ : H ⊓ Subgroup.centralizer (Q : Set X) ≤ Q)
    (hNQ : ∀ n ∈ N, ∀ q ∈ Q, ⁅n, q⁆ ∈ C)
    (hNC : ∀ n ∈ N, ∀ c ∈ C, ⁅n, c⁆ ∈ W)
    (hNW : ∀ n ∈ N, ∀ w ∈ W, ⁅n, w⁆ ∈ Z)
    (hNZ : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n)
    {n : X} (hn : n ∈ N) (hodd : Odd (orderOf n)) : n = 1 := by
  have hW2 : IsPGroup 2 W := hQ.to_le (hWC.trans hCQ)
  have hC2 : IsPGroup 2 C := hQ.to_le hCQ
  have hWcent : ∀ w ∈ W, n * w * n⁻¹ = w := by
    intro w hw
    exact CFSG.RankThree.PartTwo.Sec3.commute_of_odd_of_stabilizes hW2 hZW hodd
      (fun w hw => hNW n hn w hw) (fun z hz => by rw [hNZ n hn z hz]; group) hw
  have hCcent : ∀ c ∈ C, n * c * n⁻¹ = c := by
    intro c hc
    exact CFSG.RankThree.PartTwo.Sec3.commute_of_odd_of_stabilizes hC2 hWC hodd
      (fun c hc => hNC n hn c hc) hWcent hc
  have hQcent : ∀ q ∈ Q, q * n = n * q := by
    intro q hq
    have h := CFSG.RankThree.PartTwo.Sec3.commute_of_odd_of_stabilizes hQ hCQ hodd
      (fun q hq => hNQ n hn q hq) hCcent hq
    calc q * n = (n * q * n⁻¹) * n := by rw [h]
      _ = n * q := by group
  have hnQ : n ∈ Q :=
    hHCQ (Subgroup.mem_inf.mpr ⟨hNH hn, Subgroup.mem_centralizer_iff.mpr hQcent⟩)
  obtain ⟨k, hk⟩ := hQ.exists_orderOf_dvd_pow ⟨n, hnQ⟩
  rw [← Subgroup.orderOf_coe ⟨n, hnQ⟩] at hk
  have hcop : Nat.Coprime (orderOf n) (2 ^ k) := hodd.coprime_two_right.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hk)

theorem fs81FlagTwoGroup_holds : FS81FlagTwoGroup := by
  intro X _ _ H Q C W Z N hQ hZW hWC hCQ hNH hHCQ hNQ hNC hNW hNZ
  rw [IsPGroup.iff_orderOf]
  intro g
  have hn0 : orderOf (g : X) ≠ 0 :=
    orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite (g : X))
  obtain ⟨a, m, hm, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hpow : (g : X) ^ 2 ^ a ∈ N := N.pow_mem g.2 _
  have hdvd : orderOf ((g : X) ^ 2 ^ a) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hdecomp, pow_orderOf_eq_one]
  have hodd : Odd (orderOf ((g : X) ^ 2 ^ a)) := hm.of_dvd_nat hdvd
  have hone : (g : X) ^ 2 ^ a = 1 :=
    fs81FlagTwo_odd_eq_one hQ hZW hWC hCQ hNH hHCQ hNQ hNC hNW hNZ hpow hodd
  obtain ⟨k, hk⟩ :=
    (exists_orderOf_eq_prime_pow_iff (p := 2) (x := (g : X))).mpr ⟨a, hone⟩
  exact ⟨k, by rw [← Subgroup.orderOf_coe g]; exact hk⟩

end CFSG.StandardType.FrameRoute.FS81
