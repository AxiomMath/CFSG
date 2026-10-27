module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUniformInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FittingDecomposition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The commutator-centralization consequence in the Klein-four branch
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise commutatorElement

private theorem piCore_nat_eq_root_piCore
    {F : Type u} [Group F] [Finite F] (π : Set ℕ) :
    GorensteinWalter.piCore π F =
      _root_.CFSG.piCore {p : Nat.Primes | (p : ℕ) ∈ π} F := by
  unfold GorensteinWalter.piCore _root_.CFSG.piCore
  congr 1
  ext K
  constructor
  · intro hK
    refine ⟨hK.1, ?_⟩
    intro p hp
    apply hK.2 p.1
    exact Nat.mem_primeFactors.mpr ⟨p.2, hp, Nat.card_pos.ne'⟩
  · intro hK
    refine ⟨hK.1, ?_⟩
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    let p : Nat.Primes := ⟨q, hqprime⟩
    exact hK.2 p (by simpa using (Nat.dvd_of_mem_primeFactors hq))

private theorem hallSubgroup_of_isHallIn_local
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} (hHall : IsHallIn K H) :
    IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf H) := by
  classical
  rcases hHall with ⟨hKH, hcop⟩
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  refine isHallSubgroup_of (G := H) (subgroupPrimeSet K) (K.subgroupOf H) ?_ ?_
  · intro q hq
    simpa [subgroupPrimeSet, hcard] using hq
  · intro q hqK hqIndex
    have hqCard : q.1 ∣ Nat.card K := by
      simpa [subgroupPrimeSet] using hqK
    exact ((q.2.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hqCard)) hqIndex

private theorem commutator_centralizes_subgroup_of_centralizes_inverts
    {G : Type u} [Group G] [Finite G]
    (M F : Subgroup G) (hFM : F ≤ M) (hFnorm : IsNormalIn F M)
    (hFNil : Group.IsNilpotent (↥F)) (t : G) (htM : t ∈ M)
    (ht : IsInvolution t) (π : Set ℕ)
    (hA_norm : IsNormalIn (piCoreOf F π) M)
    (hB_norm : IsNormalIn (piCoreOf F πᶜ) M)
    (hFtop : GorensteinWalter.piCore π (↥F) ⊔
      GorensteinWalter.piCore πᶜ (↥F) = ⊤)
    (hAcent : t ∈ Subgroup.centralizer (piCoreOf F π : Set G))
    (hBinv : ∀ x : G, x ∈ (piCoreOf F πᶜ : Set G) →
      t * x * t⁻¹ = x⁻¹) :
    ⁅M, Subgroup.zpowers t⁆ ≤
      Subgroup.centralizer (F : Set G) := by
  classical
  let A0 : Subgroup (↥F) := GorensteinWalter.piCore π (↥F)
  let B0 : Subgroup (↥F) := GorensteinWalter.piCore πᶜ (↥F)
  have : Group.IsNilpotent (↥F) := hFNil
  have : A0.Normal := by dsimp [A0]; exact piCore_normal_local π
  have : B0.Normal := by dsimp [B0]; exact piCore_normal_local πᶜ
  have hM_normA : M ≤ Subgroup.normalizer (piCoreOf F π : Set G) :=
    le_normalizer_of_isNormalIn hA_norm
  have hM_normB : M ≤ Subgroup.normalizer (piCoreOf F πᶜ : Set G) :=
    le_normalizer_of_isNormalIn hB_norm
  have ht_sq : t * t = 1 := by simpa [pow_two] using ht.2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_sq
  have hAcentElem : ∀ y : G, y ∈ piCoreOf F π → t * y * t = y := by
    intro y hy
    have hcomm : y * t = t * y :=
      (Subgroup.mem_centralizer_iff (g := t)
        (s := (piCoreOf F π : Set G))).1 hAcent y hy
    calc
      t * y * t = y * t * t := by rw [hcomm]
      _ = y * (t * t) := by rw [mul_assoc]
      _ = y := by rw [ht_sq]; simp
  have hBinvElem : ∀ y : G, y ∈ piCoreOf F πᶜ →
      t * y * t = y⁻¹ := by
    intro y hy
    simpa [ht_inv] using hBinv y hy
  rw [Subgroup.commutator_le]
  intro m hm z hz
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
  have hsq : t ^ (2 : ℤ) = 1 := by
    simpa [zpow_ofNat] using ht.2
  have ht_zpow : ∀ n : ℤ, t ^ n = 1 ∨ t ^ n = t := by
    intro n
    rcases Int.even_or_odd n with h | h
    · left
      rcases h with ⟨k, hk⟩
      rw [hk, ← two_mul, zpow_mul, hsq]
      simp
    · right
      rcases h with ⟨k, hk⟩
      rw [hk, zpow_add, zpow_mul, hsq]
      simp
  rcases ht_zpow n with h1 | htpow
  · rw [h1, Subgroup.mem_centralizer_iff]
    intro x hx
    simp [commutatorElement_def]
  · rw [htpow, Subgroup.mem_centralizer_iff]
    intro x hx
    let xF : ↥F := ⟨x, hx⟩
    have hxFjoin : xF ∈ A0 ⊔ B0 := by
      rw [hFtop]
      exact Subgroup.mem_top xF
    have hxprod : xF ∈ (A0 : Set (↥F)) * (B0 : Set (↥F)) := by
      rw [← Subgroup.mul_normal A0 B0]
      exact hxFjoin
    rcases Set.mem_mul.1 hxprod with ⟨a0, ha0, b0, hb0, hab0⟩
    let a : G := (a0 : ↥F)
    let b : G := (b0 : ↥F)
    have haA : a ∈ piCoreOf F π := by
      exact Subgroup.mem_map.mpr ⟨a0, ha0, rfl⟩
    have hbB : b ∈ piCoreOf F πᶜ := by
      exact Subgroup.mem_map.mpr ⟨b0, hb0, rfl⟩
    have hab : a * b = x := by
      simpa [a, b, xF] using congrArg Subtype.val hab0
    have ha' : m⁻¹ * a * m ∈ piCoreOf F π := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hM_normA (M.inv_mem hm)) a).mp haA
    have hb' : m⁻¹ * b * m ∈ piCoreOf F πᶜ := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hM_normB (M.inv_mem hm)) b).mp hbB
    have hta_comm : t * a = a * t := by
      exact ((Subgroup.mem_centralizer_iff (g := t)
        (s := (piCoreOf F π : Set G))).1 hAcent a haA).symm
    have htabt : t * a * b * t = a * b⁻¹ := by
      calc
        t * a * b * t = a * (t * b * t) := by rw [hta_comm]; group
        _ = a * b⁻¹ := by rw [hBinvElem b hbB]
    have hsplit : ∀ X Y : G, (t * X * t) * (t * Y * t) =
        t * (X * Y) * t := by
      intro X Y
      calc
        (t * X * t) * (t * Y * t) = t * X * (t * t) * Y * t := by group
        _ = t * X * Y * t := by rw [ht_sq]; simp
        _ = t * (X * Y) * t := by group
    have hmain : ⁅m, t⁆ * x * (⁅m, t⁆)⁻¹ = a * b := by
      calc
        ⁅m, t⁆ * x * (⁅m, t⁆)⁻¹ =
            (m * t * m⁻¹ * t) * (a * b) * (t * m * t * m⁻¹) := by
              simp [commutatorElement_def, hab, ht_inv]; group
        _ = m * (t * m⁻¹ * (t * a * b * t) * m * t) * m⁻¹ := by group
        _ = m * (t * (m⁻¹ * (t * a * b * t) * m) * t) * m⁻¹ := by group
        _ = m * (t * (m⁻¹ * (a * b⁻¹) * m) * t) * m⁻¹ := by rw [htabt]
        _ = m * (t * ((m⁻¹ * a * m) * (m⁻¹ * b⁻¹ * m)) * t) * m⁻¹ := by group
        _ = m * (t * ((m⁻¹ * a * m) * (m⁻¹ * b * m)⁻¹) * t) * m⁻¹ := by
              rw [show m⁻¹ * b⁻¹ * m = (m⁻¹ * b * m)⁻¹ by group]
        _ = m * ((t * (m⁻¹ * a * m) * t) *
            (t * (m⁻¹ * b * m)⁻¹ * t)) * m⁻¹ := by
              rw [← hsplit (m⁻¹ * a * m) (m⁻¹ * b * m)⁻¹]
        _ = m * ((m⁻¹ * a * m) *
            (t * (m⁻¹ * b * m)⁻¹ * t)) * m⁻¹ := by
              rw [hAcentElem (m⁻¹ * a * m) ha']
        _ = m * ((m⁻¹ * a * m) * (m⁻¹ * b * m)) * m⁻¹ := by
              have hbinvconj : t * (m⁻¹ * b * m)⁻¹ * t = m⁻¹ * b * m := by
                have hbInv : (m⁻¹ * b * m)⁻¹ ∈ piCoreOf F πᶜ :=
                  (piCoreOf F πᶜ).inv_mem hb'
                simpa [inv_inv] using hBinvElem _ hbInv
              rw [hbinvconj]
        _ = a * b := by group
    have hxcomm : x * ⁅m, t⁆ = ⁅m, t⁆ * x := by
      calc
        x * ⁅m, t⁆ = (⁅m, t⁆ * x * (⁅m, t⁆)⁻¹) * ⁅m, t⁆ := by
          rw [hmain, hab]
        _ = ⁅m, t⁆ * x := by group
    exact hxcomm

public theorem firstCase_klein_commutator_centralizes_fitting
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (r : G) (hr : c.IsReflection r)
    (hrV : r ∉ twoCoreOf c.Hhat) :
    ∃ K : Subgroup G,
      IsInvertedSubgroup K c.U r ∧ IsHallIn K c.FU ∧ K ≠ ⊥ ∧
        (∀ s : G, s ∈ c.Hhat → IsInvolution s →
          s ∉ twoCoreOf c.Hhat → IsInvertedSubgroup K c.U s ∧
            ⁅c.Hhat, Subgroup.zpowers s⁆ ≤
              Subgroup.centralizer (c.FU : Set G)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKr, hKHall, hKne, hKunif⟩ :=
    firstCase_klein_uniform_involution_inverted hmin c hfirst hklein r hr hrV
  have h26 := theorem_2_6 hmin c
  have hUnorm : IsNormalIn c.U c.Hhat := by
    rw [h26.1]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    · intro h hh k hk
      rcases Subgroup.mem_map.mp hk with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : ↥c.Hhat) * y * (⟨h, hh⟩ : ↥c.Hhat)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem
        y hy (⟨h, hh⟩ : ↥c.Hhat)
  have hFUnorm : IsNormalIn c.FU c.Hhat := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.Hhat) (F := c.U) (K := fittingSubgroup (↥c.U))
      fittingSubgroup_characteristic hUnorm
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.Hhat at h
    exact h
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    rw [h26.1]
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
    rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
          c.Hhat.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  refine ⟨K, hKr, hKHall, hKne, ?_⟩
  intro s hsH hsInv hsV
  have hKs := hKunif s hsH hsInv hsV
  let πK : Set Nat.Primes := subgroupPrimeSet K
  let π : Set ℕ := {q : ℕ | ¬ ∃ p : Nat.Primes, p ∈ πK ∧ (p : ℕ) = q}
  let F : Subgroup G := c.FU
  let A : Subgroup G := piCoreOf F π
  let B : Subgroup G := piCoreOf F πᶜ
  have hFNil : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent c.U
  have hKFUHall : IsHallSubgroup πK (K.subgroupOf F) :=
    hallSubgroup_of_isHallIn_local hKHall
  have hKNormal : (K.subgroupOf F).Normal :=
    section15_hall_subgroup_normal_of_nilpotent hFNil hKFUHall
  have hKPi : (K.subgroupOf F) = _root_.CFSG.piCore πK (↥F) := by
    have hPiHall : IsHallSubgroup πK (_root_.CFSG.piCore πK (↥F)) :=
      section12_piCore_isHallSubgroup_of_nilpotent hFNil
    exact hPiHall.eq_of_normal hKFUHall
  have hB_eq_K : B = K := by
    have hpi : GorensteinWalter.piCore πᶜ (↥F) =
        _root_.CFSG.piCore πK (↥F) := by
      rw [piCore_nat_eq_root_piCore]
      congr 1
      ext p
      constructor
      · intro hp
        change ¬ (¬ ∃ q : Nat.Primes, q ∈ πK ∧ (q : ℕ) = (p : ℕ)) at hp
        rcases not_not.mp hp with ⟨q, hq, hqp⟩
        have hEq : q = p := Subtype.ext hqp
        simpa [hEq] using hq
      · intro hp hpin
        exact hpin ⟨p, hp, rfl⟩
    change (GorensteinWalter.piCore πᶜ (↥F)).map F.subtype = K
    rw [hpi, ← hKPi]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKHall.1]
  have hAnorm : IsNormalIn A c.Hhat := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.Hhat) (F := F) (K := GorensteinWalter.piCore π (↥F))
      (GorensteinWalter.piCore_characteristic π) hFUnorm
    simpa [A, F, piCoreOf] using h
  have hBnorm : IsNormalIn B c.Hhat := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.Hhat) (F := F) (K := GorensteinWalter.piCore πᶜ (↥F))
      (GorensteinWalter.piCore_characteristic πᶜ) hFUnorm
    simpa [B, F, piCoreOf] using h
  have hBdisjA : A ⊓ B = ⊥ := by
    change piCoreOf (fittingSubgroupOf c.U) π ⊓
      piCoreOf (fittingSubgroupOf c.U) πᶜ = ⊥
    exact piCoreOf_inf_piCoreOf_compl_eq_bot c.U π
  have hAfix : ∀ x : G, x ∈ A → s * x * s⁻¹ = x := by
    intro x hx
    have hsNormA : ∀ y : G, y ∈ A → s * y * s⁻¹ ∈ A :=
      fun y hy => hAnorm.2 s hsH y hy
    have hAcop : Nat.Coprime 2 (Nat.card A) := by
      have hAleF : A ≤ F := piCoreOf_le F π
      have hFleU : F ≤ c.U := fittingSubgroupOf_le c.U
      exact Nat.Coprime.of_dvd_right
        (Subgroup.card_dvd_of_le (hAleF.trans hFleU)) hUcop
    obtain ⟨z, hzC, i, hiI, hxi⟩ :=
      fact_1_5_ii_decomposition hsInv hAcop hsNormA x hx
    have hiK : i ∈ K := by
      have hFleU : F ≤ c.U := fittingSubgroupOf_le c.U
      have hiU : i ∈ c.U := hFleU ((piCoreOf_le F π) hiI.1)
      have hiInvU : i ∈ invertedElements c.U s := ⟨hiU, hiI.2⟩
      change i ∈ (K : Set G)
      rw [hKs]
      exact hiInvU
    have hiA : i ∈ A := by
      exact hiI.1
    have hiBot : i = 1 := by
      have hiB : i ∈ B := by rw [hB_eq_K]; exact hiK
      have hiInf : i ∈ A ⊓ B := ⟨hiA, hiB⟩
      rw [hBdisjA] at hiInf
      simpa using hiInf
    rw [hiBot] at hxi
    have hzfix : s * z * s⁻¹ = z := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzC.2) s (by simp)
      rw [hcomm]
      group
    simpa [hxi, hiBot] using hzfix
  have hAcent : s ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hsFix := hAfix x hx
    have hcomm : s * x = x * s :=
      mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hsFix)
    exact hcomm.symm
  have hBinv : ∀ x : G, x ∈ (B : Set G) → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    rw [hB_eq_K] at hx
    exact (show x ∈ invertedElements c.U s from by
      rw [← hKs]
      exact hx).2
  have hcomm :=
    commutator_centralizes_subgroup_of_centralizes_inverts
      c.Hhat F (by
        have hFleU : F ≤ c.U := fittingSubgroupOf_le c.U
        exact hFleU.trans hUnorm.1) hFUnorm
      (fittingSubgroupOf_isNilpotent c.U)
      s hsH hsInv π hAnorm hBnorm
      (GorensteinWalter.piCore_sup_piCore_compl_eq_top_of_isNilpotent hFNil π)
      hAcent hBinv
  exact ⟨hKs, hcomm⟩

end CFSG.GorensteinWalter
