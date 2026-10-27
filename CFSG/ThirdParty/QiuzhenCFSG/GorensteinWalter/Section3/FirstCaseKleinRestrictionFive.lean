module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionTransfer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The nontrivial `V`-component in restriction (5)

In the Klein-four branch, write an element of `V U` as `v * u`.  If `v` is
nontrivial and an outside involution inverts `v * u`, then the odd order of
`U` lets us recover `v` as an odd power of `v * u`.  The outside involution
therefore centralizes `v`, contradicting the ambient centralizer bound.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem oddCore_card_eq_pPrimeCore_local
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (oddCoreOf H) = Nat.card (pPrimeCore 2 H) := by
  simpa [oddCoreOf] using
    (Subgroup.card_map_of_injective (K := pPrimeCore 2 H) H.subtype_injective)

private theorem firstCase_klein_U_coprime_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G) :
    Nat.Coprime 2 (Nat.card c.U) := by
  have h26 := theorem_2_6 hmin c
  rw [h26.1]
  change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
  rw [oddCore_card_eq_pPrimeCore_local]
  simpa using pPrimeCore_coprime_card (p := 2) (G := c.Hhat)

private theorem firstCase_klein_V_sq_one
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {v : G} (hv : v ∈ twoCoreOf c.Hhat) :
    v * v = 1 := by
  have hVK : IsKleinFour (twoCoreOf c.Hhat) :=
    firstCase_klein_V_klein c hklein
  simpa [pow_two] using
    congrArg Subtype.val (hVK.mul_self (⟨v, hv⟩ : twoCoreOf c.Hhat))

/-- A nontrivial `V`-component cannot occur in restriction (5). -/
public theorem firstCase_klein_restrictionFive_V_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y v u : G}
    (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hv : v ∈ twoCoreOf c.Hhat) (hvne : v ≠ 1)
    (hu : u ∈ c.U)
    (hcent : ∀ z : G, z ∈ twoCoreOf c.Hhat →
      ∀ w : G, w ∈ c.U → z * w = w * z)
    (hinv : y * (v * u) * y⁻¹ = (v * u)⁻¹) :
    False := by
  have hUcop : Nat.Coprime 2 (Nat.card c.U) :=
    firstCase_klein_U_coprime_two hmin c
  have hordU : orderOf u ∣ Nat.card c.U :=
    Subgroup.orderOf_dvd_natCard c.U hu
  have hcopord : Nat.Coprime 2 (orderOf u) :=
    Nat.Coprime.of_dvd_right hordU hUcop
  have hordOdd : Odd (orderOf u) := Nat.coprime_two_left.mp hcopord
  let m := orderOf u
  have hcomm : Commute v u := hcent v hv u hu
  have hpow : (v * u) ^ m = v ^ m * u ^ m := hcomm.mul_pow m
  have hum : u ^ m = 1 := pow_orderOf_eq_one u
  have hvm' : v ^ m = v := by
    rcases hordOdd with ⟨q, hq⟩
    calc
      v ^ m = v ^ (2 * q + 1) := by simpa [m] using congrArg (fun n : ℕ => v ^ n) hq
      _ = v ^ (2 * q) * v ^ 1 := by rw [pow_add]
      _ = (v ^ 2) ^ q * v := by rw [pow_mul]; simp
      _ = v := by
        have hv2 : v ^ 2 = 1 := by
          simpa [pow_two] using firstCase_klein_V_sq_one c hklein hv
        rw [hv2]
        simp
  have hvm : (v * u) ^ m = v := by rw [hpow, hvm', hum]; simp
  have hconjm : y * (v * u) ^ m * y⁻¹ = ((v * u) ^ m)⁻¹ := by
    calc
      y * (v * u) ^ m * y⁻¹ = (y * (v * u) * y⁻¹) ^ m := by
        rw [conj_pow]
      _ = ((v * u)⁻¹) ^ m := by rw [hinv]
      _ = ((v * u) ^ m)⁻¹ := by rw [inv_pow]
  have hvfix : y * v * y⁻¹ = v := by
    rw [hvm] at hconjm
    have hv_inv : v⁻¹ = v := by
      apply inv_eq_of_mul_eq_one_right
      exact firstCase_klein_V_sq_one c hklein hv
    rw [hv_inv] at hconjm
    exact hconjm
  have hyC : y ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hvfix)
  exact hyH (firstCase_klein_centralizer_twoCore_le_Hhat
    hmin c hklein v hv hvne hyC)

/-!
The remaining branch is isolated behind the exact transfer assertion used by
the source: a nontrivial `x ∈ U` inverted by an outside involution admits an
inverting involution in `Ĥ \ V`.  This premise is deliberately explicit until
the Sylow-2 centralizer transfer is landed.
-/

/-- Restriction (5), assuming the source's Sylow/Frattini transfer for the
`U`-component. -/
public theorem firstCase_klein_restrictionFive_of_transfer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (htransfer : ∀ {x y : G}, x ∈ c.U → x ≠ 1 → IsInvolution y →
      y ∉ c.Hhat → y * x * y⁻¹ = x⁻¹ →
      ∃ s : G, s ∈ c.Hhat ∧ IsInvolution s ∧
        s ∉ twoCoreOf c.Hhat ∧ s * x * s⁻¹ = x⁻¹)
    (y : G) (hy : IsInvolution y) (hyH : y ∉ c.Hhat) :
    Nat.card {x : G // x ∈ invertedElements
      (twoCoreOf c.Hhat ⊔ c.U) y} = 1 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVcent : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVnormU : V ≤ Subgroup.normalizer (c.U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv u hu
    have hcomm : v * u = u * v :=
      (Subgroup.mem_centralizer_iff.mp (hVcent hv) u hu).symm
    have hfix : v * u * v⁻¹ = u := by rw [hcomm]; group
    simpa [hfix] using hu
  have hVU : ((V ⊔ c.U : Subgroup G) : Set G) =
      (V : Set G) * (c.U : Set G) := by
    exact Subgroup.coe_mul_of_left_le_normalizer_right V c.U hVnormU
  obtain ⟨_d, K, hK, _hKne, hKall⟩ :=
    firstCase_klein_data_complete hmin c hfirst hklein
  have hOne : (1 : G) ∈ invertedElements (V ⊔ c.U) y := by
    constructor
    · exact (V ⊔ c.U).one_mem
    · simp
  apply (Nat.card_eq_one_iff_exists).2
  refine ⟨⟨1, hOne⟩, ?_⟩
  intro z
  apply Subtype.ext
  have hz := z.property
  change (z : G) ∈ V ⊔ c.U ∧
    y * (z : G) * y⁻¹ = (z : G)⁻¹ at hz
  rcases hz with ⟨hzVU, hzy⟩
  have hzVU' : (z : G) ∈ (V : Set G) * (c.U : Set G) := by
    rw [← hVU]
    exact hzVU
  rcases Set.mem_mul.mp hzVU' with ⟨v, hv, u, hu, hvueq⟩
  have hdecomp : (z : G) = v * u := hvueq.symm
  have hvinv : y * (v * u) * y⁻¹ = (v * u)⁻¹ := by
    simpa [hdecomp] using hzy
  have hvone : v = 1 := by
    by_contra hvne
    exact firstCase_klein_restrictionFive_V_component hmin c hklein
      hy hyH hv hvne hu
      (fun z hz w hw =>
        (Subgroup.mem_centralizer_iff.mp (hVcent hz) w hw).symm)
      hvinv
  have hzU : (z : G) ∈ c.U := by
    rw [hdecomp, hvone]
    simpa using hu
  by_cases hz1 : (z : G) = 1
  · exact hz1
  obtain ⟨s, hsH, hsI, hsV, hsInv⟩ :=
    htransfer hzU hz1 hy hyH (by simpa [hdecomp, hvone] using hvinv)
  have hsKs := hKall s hsH hsI hsV
  have hzK : (z : G) ∈ K := by
    change (z : G) ∈ (K : Set G)
    rw [hsKs.1]
    exact ⟨hzU, by simpa [hdecomp, hvone] using hsInv⟩
  let X : Subgroup G := Subgroup.zpowers (z : G)
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hz1' : (z : G) = 1 := by
      exact (Subgroup.eq_bot_iff_forall X).1 hbot
        (z : G) (Subgroup.mem_zpowers (z : G))
    exact hz1 hz1'
  have hXle : X ≤ c.FU :=
    (Subgroup.zpowers_le).2 (hK.1 hzK)
  have hXN : Subgroup.normalizer (X : Set G) ≤ c.Hhat :=
    hfirst.2 X hXne hXle
  have hyX : y ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rcases (Subgroup.mem_zpowers_iff.mp hw) with ⟨n, hn⟩
      rw [← hn]
      have heq : y * (z : G) ^ n * y⁻¹ = ((z : G)⁻¹) ^ n := by
        calc
          y * (z : G) ^ n * y⁻¹ =
              (y * (z : G) * y⁻¹) ^ n := by rw [conj_zpow]
          _ = ((z : G)⁻¹) ^ n := by
            rw [show y * (z : G) * y⁻¹ = (z : G)⁻¹ by
              simpa [hdecomp, hvone] using hzy]
      rw [heq]
      apply (Subgroup.mem_zpowers_iff).2
      refine ⟨-n, ?_⟩
      calc
        (z : G) ^ (-n) = ((z : G) ^ n)⁻¹ := by rw [zpow_neg]
        _ = w⁻¹ := by rw [hn]
        _ = ((z : G)⁻¹) ^ n := by
          rw [inv_zpow, hn]
    · intro hw
      rcases (Subgroup.mem_zpowers_iff.mp hw) with ⟨n, hn⟩
      have hwexpr : w = y * (z : G) ^ n * y⁻¹ := by
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        calc
          w = y * (y * w * y⁻¹) * y⁻¹ := by
            calc
              w = (y * y) * w * (y⁻¹ * y⁻¹) := by
                rw [hy2, hyinv, hy2]
                simp
              _ = y * (y * w * y⁻¹) * y⁻¹ := by group
          _ = y * (z : G) ^ n * y⁻¹ := by rw [hn]
      rw [hwexpr]
      have heq : y * (z : G) ^ n * y⁻¹ = ((z : G)⁻¹) ^ n := by
        calc
          y * (z : G) ^ n * y⁻¹ =
              (y * (z : G) * y⁻¹) ^ n := by rw [conj_zpow]
          _ = ((z : G)⁻¹) ^ n := by
            rw [show y * (z : G) * y⁻¹ = (z : G)⁻¹ by
              simpa [hdecomp, hvone] using hzy]
      rw [heq]
      apply (Subgroup.mem_zpowers_iff).2
      refine ⟨-n, ?_⟩
      calc
        (z : G) ^ (-n) = ((z : G) ^ n)⁻¹ := by rw [zpow_neg]
        _ = ((z : G)⁻¹) ^ n := by rw [inv_zpow]
  exact False.elim (hyH (hXN hyX))

/- The source-shaped restriction (5), with the Sylow transfer discharged. -/
public theorem firstCase_klein_restrictionFive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (y : G) (hy : IsInvolution y) (hyH : y ∉ c.Hhat) :
    Nat.card {x : G // x ∈ invertedElements
      (twoCoreOf c.Hhat ⊔ c.U) y} = 1 := by
  exact firstCase_klein_restrictionFive_of_transfer hmin c hfirst hklein
    (firstCase_klein_involution_transfer hmin c hfirst hklein) y hy hyH

end CFSG.GorensteinWalter
