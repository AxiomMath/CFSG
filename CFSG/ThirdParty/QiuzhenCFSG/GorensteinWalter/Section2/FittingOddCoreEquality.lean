module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PiCoreCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# `F(O(H)) = O_{2'}(F(H))`

For any finite group `H`, the Fitting subgroup of the odd core equals the
odd part of the Fitting subgroup.  This is the equality behind the paper's
`M ∩ F_{2'}(Ĥ) = M ∩ F(U)` identification in Lemma 2.7.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem oddCoreOf_isNormalIn {G : Type u} [Group G]
    (H : Subgroup G) : IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem y hy (⟨h, hh⟩ : ↥H)

public theorem le_oddCoreOf_of_normal_of_coprime
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hKH : K ≤ H) (hKnormH : IsNormalIn K H)
    (hKcop : Nat.Coprime 2 (Nat.card (↥K))) :
    K ≤ oddCoreOf H := by
  classical
  let K' : Subgroup (↥H) := K.subgroupOf H
  have hK'norm : K'.Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := K)
      (le_normalizer_of_isNormalIn hKnormH)
  have hK'cop : Nat.Coprime 2 (Nat.card (↥K')) := by
    have e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKH
    have hcard : Nat.card (↥K') = Nat.card (↥K) := Nat.card_congr e.toEquiv
    rwa [hcard]
  have hK'le : K' ≤ pPrimeCore 2 H := le_sSup ⟨hK'norm, hK'cop⟩
  have hmap := Subgroup.map_mono (f := H.subtype) hK'le
  have hmap_eq : K'.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  have hmap_odd : (pPrimeCore 2 H).map H.subtype = oddCoreOf H := rfl
  simpa [hmap_eq, hmap_odd] using hmap

private theorem le_piCoreOf_fittingSubgroupOf_odd
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hKF : K ≤ fittingSubgroupOf H)
    (hKnormH : IsNormalIn K H)
    (hKcop : Nat.Coprime 2 (Nat.card (↥K))) :
    K ≤ piCoreOf (fittingSubgroupOf H) {q : ℕ | Odd q} := by
  classical
  let F : Subgroup G := fittingSubgroupOf H
  let A : Subgroup (↥F) := piCore {q : ℕ | Odd q} (↥F)
  let K' : Subgroup (↥F) := K.subgroupOf F
  have hFleH : F ≤ H := by
    simpa [F] using (fittingSubgroupOf_isNormalIn H).1
  have hKnormF : IsNormalIn K F := by
    refine ⟨hKF, ?_⟩
    intro f hf k hk
    exact hKnormH.2 (f : G) (hFleH hf) k hk
  have hK'norm : K'.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKF).2
      (le_normalizer_of_isNormalIn hKnormF)
  have hK'cop : Nat.Coprime 2 (Nat.card (↥K')) := by
    have e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKF
    have hcard : Nat.card (↥K') = Nat.card (↥K) := Nat.card_congr e.toEquiv
    rwa [hcard]
  have hK'odd : ∀ q : ℕ, q ∈ (Nat.card (↥K')).primeFactors → Odd q := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    exact hqprime.odd_of_ne_two (by
      intro hq2
      have hdvd : 2 ∣ Nat.card (↥K') := by
        simpa [hq2] using Nat.dvd_of_mem_primeFactors hq
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hK'cop hdvd)
  have hK'leA : K' ≤ piCore {q : ℕ | Odd q} (↥F) := le_sSup ⟨hK'norm, hK'odd⟩
  have hmap := Subgroup.map_mono (f := F.subtype) hK'leA
  have hmap_eq : K'.map F.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKF
  simpa [A, piCoreOf, hmap_eq] using hmap

/-- `F(O(H)) = O_{2'}(F(H))`. -/
public theorem fittingSubgroupOf_oddCore_eq_oddPart_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    fittingSubgroupOf (oddCoreOf H) =
      piCoreOf (fittingSubgroupOf H) {q : ℕ | Odd q} := by
  classical
  let U : Subgroup G := oddCoreOf H
  let F : Subgroup G := fittingSubgroupOf H
  let A : Subgroup G := piCoreOf F {q : ℕ | Odd q}
  let B : Subgroup G := fittingSubgroupOf U
  have hUleH : U ≤ H := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hUnormH : IsNormalIn U H := oddCoreOf_isNormalIn H
  have hFleH : F ≤ H := by
    simpa [F] using (fittingSubgroupOf_isNormalIn H).1
  have hFnil : Group.IsNilpotent (↥F) := by
    dsimp [F]
    exact fittingSubgroupOf_isNilpotent H
  have hAnormH : IsNormalIn A H := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := H) (F := F) (K := piCore {q : ℕ | Odd q} (↥F))
      (piCore_characteristic {q : ℕ | Odd q})
      (by simpa [F] using fittingSubgroupOf_isNormalIn H)
    simpa [A, piCoreOf] using h
  have hA_le_F : A ≤ F := piCoreOf_le F {q : ℕ | Odd q}
  have hA_le_H : A ≤ H := hA_le_F.trans hFleH
  have hAcop : Nat.Coprime 2 (Nat.card (↥A)) := by
    refine Nat.coprime_two_left.mpr ?_
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2dvd : 2 ∣ Nat.card (↥A) := even_iff_two_dvd.mp heven
    have h2pf : 2 ∈ (Nat.card (↥A)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩
    have h2odd : Odd 2 := by
      simpa using (piCoreOf_primeDivisors F {q : ℕ | Odd q} 2 h2pf)
    norm_num at h2odd
  have hA_le_U : A ≤ U :=
    le_oddCoreOf_of_normal_of_coprime H A hA_le_H hAnormH hAcop
  have hAnormU : IsNormalIn A U := by
    refine ⟨hA_le_U, ?_⟩
    intro u hu a ha
    exact hAnormH.2 (u : G) (hUleH hu) a ha
  have hAnil : Group.IsNilpotent A := by
    let : Group.IsNilpotent (↥F) := hFnil
    have hAsub : A ≤ F := hA_le_F
    have hA' : Group.IsNilpotent (A.subgroupOf F) :=
      Subgroup.isNilpotent (A.subgroupOf F)
    let : Group.IsNilpotent (A.subgroupOf F) := hA'
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAsub)
  have hA_le_B : A ≤ B :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := U) (N := A)
      hA_le_U hAnormU hAnil
  have hBnormH : IsNormalIn B H := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := H) (F := U) (K := fittingSubgroup (↥U))
      (by infer_instance : (fittingSubgroup (↥U)).Characteristic) hUnormH
    simpa [B, fittingSubgroupOf] using h
  have hBleU : B ≤ U := by
    simpa [B] using (fittingSubgroupOf_isNormalIn U).1
  have hBleH : B ≤ H := hBleU.trans hUleH
  have hBnil : Group.IsNilpotent B := by
    dsimp [B]
    exact fittingSubgroupOf_isNilpotent U
  have hBF : B ≤ F :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := H) (N := B)
      hBleH hBnormH hBnil
  have hBodd : Odd (Nat.card (↥B)) :=
    Odd.of_dvd_nat (odd_card_oddCoreOf H) (Subgroup.card_dvd_of_le hBleU)
  have hBcop : Nat.Coprime 2 (Nat.card (↥B)) := Nat.coprime_two_left.mpr hBodd
  have hB_le_A : B ≤ A :=
    le_piCoreOf_fittingSubgroupOf_odd H B hBF hBnormH hBcop
  change B = A
  exact le_antisymm hB_le_A hA_le_B

/-- If `G / O_{2'}(G)` is a `2`-group, then every odd-order subgroup lies
in the odd core. -/
public theorem subgroup_le_pPrimeCore_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G]
    (hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G))
    (P : Subgroup G) (hodd : Odd (Nat.card P)) :
    P ≤ pPrimeCore 2 G := by
  classical
  let O : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  intro x hx
  have hxP : x ∈ P := hx
  have hqOrder : orderOf (q x) ∣ orderOf x := orderOf_map_dvd _ _
  have hqdiv : orderOf (q x) ∣ Nat.card (G ⧸ O) := orderOf_dvd_natCard (q x)
  have hPodd : Odd (orderOf x) := by
    have hdvd : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hxP
    exact Odd.of_dvd_nat hodd hdvd
  rcases (IsPGroup.iff_card).mp hQ with ⟨n, hn⟩
  have hqdiv2 : orderOf (q x) ∣ 2 ^ n := by
    rw [hn] at hqdiv
    exact hqdiv
  have hcop2 : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.mpr hPodd
  have hcopPow : Nat.Coprime (2 ^ n) (orderOf x) := hcop2.pow_left n
  have hor1 : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopPow hqdiv2 hqOrder
  have hq1 : q x = 1 := orderOf_eq_one_iff.mp hor1
  exact (QuotientGroup.eq_one_iff (N := O) x).mp hq1

/-- If a homomorphism maps onto a `p`-group and its kernel lies in a normal
subgroup `N`, then `G / N` is a `p`-group. -/
public theorem isPGroup_quotient_of_map_isPGroup_of_ker_le
    {A B : Type u} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (f : A →* B)
    (N : Subgroup A) [N.Normal] (hker : f.ker ≤ N)
    (hB : IsPGroup p B) :
    IsPGroup p (A ⧸ N) := by
  rw [IsPGroup.iff_orderOf]
  intro a
  rcases QuotientGroup.mk'_surjective N a with ⟨a0, rfl⟩
  have hfa := (IsPGroup.iff_orderOf.mp hB) (f a0)
  rcases hfa with ⟨k, hk⟩
  have hpow_f : (f a0) ^ (p ^ k) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one (f a0)
  have hmem : a0 ^ (p ^ k) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    simpa [map_pow] using hpow_f
  have hN : a0 ^ (p ^ k) ∈ N := hker hmem
  have hqpow : QuotientGroup.mk' N (a0 ^ (p ^ k)) = 1 :=
    (QuotientGroup.eq_one_iff (N := N) (a0 ^ (p ^ k))).2 hN
  have hdvd : orderOf (QuotientGroup.mk' N a0) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using hqpow)
  obtain ⟨j, _hj, hj⟩ :=
    (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact ⟨j, hj⟩

/-- The `2`-core centralizes the odd core of the same group. -/
public theorem twoCoreOf_centralizes_oddCoreOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    twoCoreOf H ≤ Subgroup.centralizer (oddCoreOf H : Set G) := by
  have h := pPrimeCore_map_le_centralizer_pCore_map (p := 2) H
  have h' : Subgroup.map H.subtype (pCore 2 ↥H) ≤
      Subgroup.centralizer
        ((pPrimeCore 2 ↥H).map H.subtype : Set G) :=
    Subgroup.le_centralizer_iff.mp h
  simpa [twoCoreOf, oddCoreOf] using h'

end CFSG.GorensteinWalter
