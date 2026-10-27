module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `π`/`πᶜ` decomposition of the Fitting subgroup

For a subgroup `H`, the nilpotent Fitting subgroup splits as
`F(H) = O_π(F(H)) · O_{πᶜ}(F(H))` with commuting factors of coprime order.
This is the decomposition behind the paper's
`[M,t] ⊆ C_M(F(M)) ⊆ F(M)` step: the distinguished involution centralizes
the `π`-part and inverts the `πᶜ`-part, so every commutator `[m,t]` acts
trivially on `F(M)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `O_π(G)` is normal. -/
public theorem piCore_normal_local {G : Type u} [Group G] [Finite G]
    (π : Set ℕ) : (piCore π G).Normal := by
  refine ⟨?_⟩
  intro n hn g
  change n ∈ sSup (normalPiSubgroups (G := G) π) at hn
  rw [sSup_eq_iSup', Subgroup.iSup_eq_closure] at hn
  have hgen : ∀ y : G,
      y ∈ ⋃ N : {N : Subgroup G // N ∈ normalPiSubgroups (G := G) π},
        (N.1 : Set G) → g * y * g⁻¹ ∈ piCore π G := by
    intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨N, hN⟩
    have hNnorm : (N : Subgroup G).Normal := N.2.1
    have hy' : g * y * g⁻¹ ∈ (N : Subgroup G) := hNnorm.conj_mem y hN g
    exact Subgroup.mem_sSup_of_mem N.2 hy'
  refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hn
  · intro y hy
    simpa [mul_assoc] using (piCore π G).inv_mem (hgen y hy)
  · simpa using (piCore π G).one_mem
  · intro a b _ _ ha hb
    simpa [mul_assoc, mul_left_comm, mul_right_comm] using
      (piCore π G).mul_mem ha hb

/-- `O_q(H) ≤ O_π(F(H))` whenever `q ∈ π`. -/
public theorem qCoreOf_le_piCoreOf_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) (q : ℕ)
    (hq : q.Prime) (hqπ : q ∈ π) :
    qCoreOf H q ≤ piCoreOf (fittingSubgroupOf H) π := by
  classical
  let F : Subgroup G := fittingSubgroupOf H
  have hQleF : qCoreOf H q ≤ F := qCoreOf_le_fittingSubgroupOf H q hq
  have hFH : F ≤ H := by
    simpa [F] using (fittingSubgroupOf_isNormalIn H).1
  have hQnormF : ((qCoreOf H q).subgroupOf F).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hQleF).2
    intro x hx f hf
    exact (qCoreOf_normal_in H q).2 hx (hFH hf) x f
  have hQleQF : qCoreOf H q ≤ qCoreOf F q :=
    le_qCoreOf_of_normal_isPGroup F (qCoreOf H q) q hQleF hQnormF
      (qCoreOf_isPGroup H q)
  exact hQleQF.trans (qCoreOf_le_piCoreOf F π q hqπ hq)

/-- `F(G) ≤ O_π(G) ⊔ O_{πᶜ}(G)`: every prime part of the Fitting subgroup
lies in exactly one of the two Hall parts. -/
public theorem fittingSubgroup_le_sup_piCore_piCore_compl
    {G : Type u} [Group G] [Finite G] (π : Set ℕ) :
    fittingSubgroup G ≤ piCore π G ⊔ piCore πᶜ G := by
  classical
  rw [fitting_eq_sup_pCore G]
  refine iSup_le (fun p => ?_)
  by_cases hpπ : p.1.1 ∈ π
  · have hle : pCore p.1.1 G ≤ piCore π G := by
      change pCore p.1.1 G ≤ sSup (normalPiSubgroups (G := G) π)
      refine le_sSup ?_
      refine ⟨pCore_normal (p := p.1.1), ?_⟩
      intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ Nat.card (↥(pCore p.1.1 G)) := Nat.dvd_of_mem_primeFactors hq
      rcases (IsPGroup.iff_card (p := p.1.1) (G := ↥(pCore p.1.1 G))).mp
        (pCore_isPGroup (p := p.1.1) (G := G)) with ⟨n, hn⟩
      have hdvd' : q ∣ p.1.1 ^ n := by simpa [hn] using hqdvd
      have hqeq : q = p.1.1 :=
        (Nat.prime_dvd_prime_iff_eq (p := q) (q := p.1.1) hqprime
          (Nat.prime_of_mem_primeFactors p.1.2)).mp
          (hqprime.dvd_of_dvd_pow hdvd')
      rwa [hqeq]
    exact hle.trans le_sup_left
  · have hle : pCore p.1.1 G ≤ piCore πᶜ G := by
      change pCore p.1.1 G ≤ sSup (normalPiSubgroups (G := G) πᶜ)
      refine le_sSup ?_
      refine ⟨pCore_normal (p := p.1.1), ?_⟩
      intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ Nat.card (↥(pCore p.1.1 G)) := Nat.dvd_of_mem_primeFactors hq
      rcases (IsPGroup.iff_card (p := p.1.1) (G := ↥(pCore p.1.1 G))).mp
        (pCore_isPGroup (p := p.1.1) (G := G)) with ⟨n, hn⟩
      have hdvd' : q ∣ p.1.1 ^ n := by simpa [hn] using hqdvd
      have hqeq : q = p.1.1 :=
        (Nat.prime_dvd_prime_iff_eq (p := q) (q := p.1.1) hqprime
          (Nat.prime_of_mem_primeFactors p.1.2)).mp
          (hqprime.dvd_of_dvd_pow hdvd')
      rwa [hqeq]
    exact hle.trans le_sup_right

/-- A nilpotent group is its own Fitting subgroup. -/
public theorem fittingSubgroup_eq_top_of_isNilpotent
    {G : Type u} [Group G] [Finite G] (hG : Group.IsNilpotent G) :
    fittingSubgroup G = ⊤ := by
  have : Group.IsNilpotent G := hG
  apply le_antisymm le_top
  intro x hx
  exact le_sSup (s := {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N})
    ⟨inferInstance, Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := G)).symm⟩
    (Subgroup.mem_top x)

/-- In a nilpotent group, the `π`- and `πᶜ`-parts join to the whole group. -/
public theorem piCore_sup_piCore_compl_eq_top_of_isNilpotent
    {G : Type u} [Group G] [Finite G] (hG : Group.IsNilpotent G) (π : Set ℕ) :
    piCore π G ⊔ piCore πᶜ G = ⊤ := by
  have hle : fittingSubgroup G ≤ piCore π G ⊔ piCore πᶜ G :=
    fittingSubgroup_le_sup_piCore_piCore_compl π
  rw [fittingSubgroup_eq_top_of_isNilpotent hG] at hle
  exact le_antisymm le_top hle

/-- `F(H) ≤ O_π(F(H)) ⊔ O_{πᶜ}(F(H))`: the internal decomposition of the
nilpotent Fitting subgroup, mapped to the ambient group. -/
public theorem fittingSubgroupOf_le_sup_piCoreOf_compl
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    fittingSubgroupOf H ≤
      piCoreOf (fittingSubgroupOf H) π ⊔
        piCoreOf (fittingSubgroupOf H) πᶜ := by
  classical
  let F : Subgroup G := fittingSubgroupOf H
  have hFnil : Group.IsNilpotent (↥F) := by
    dsimp [F]
    exact fittingSubgroupOf_isNilpotent H
  have : Group.IsNilpotent (↥F) := hFnil
  have hFtop : fittingSubgroup (↥F) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    exact le_sSup (s := {N : Subgroup (↥F) | N.Normal ∧ Group.IsNilpotent N})
      ⟨inferInstance, Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := ↥F)).symm⟩
        (Subgroup.mem_top x)
  have hle : (⊤ : Subgroup (↥F)) ≤ piCore π (↥F) ⊔ piCore πᶜ (↥F) := by
    rw [← hFtop]
    exact fittingSubgroup_le_sup_piCore_piCore_compl π
  have htop_map : (⊤ : Subgroup (↥F)).map F.subtype = F := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hsup_map : (piCore π (↥F) ⊔ piCore πᶜ (↥F)).map F.subtype =
      piCoreOf F π ⊔ piCoreOf F πᶜ := by
    rw [Subgroup.map_sup]
    rfl
  have hle' : F ≤ piCoreOf F π ⊔ piCoreOf F πᶜ := by
    have h := Subgroup.map_mono (f := F.subtype) hle
    rwa [htop_map, hsup_map] at h
  simpa [F] using hle'

/-- The Fitting subgroup is the join of its `π`- and `πᶜ`-parts. -/
public theorem fittingSubgroupOf_eq_sup_piCoreOf_compl
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    fittingSubgroupOf H =
      piCoreOf (fittingSubgroupOf H) π ⊔
        piCoreOf (fittingSubgroupOf H) πᶜ := by
  apply le_antisymm
  · exact fittingSubgroupOf_le_sup_piCoreOf_compl H π
  · exact sup_le (piCoreOf_le (fittingSubgroupOf H) π)
      (piCoreOf_le (fittingSubgroupOf H) πᶜ)

/-- Two subgroups with disjoint prime divisors have coprime orders. -/
private theorem natCard_coprime_of_primeDivisors_compl
    {G : Type u} [Group G] [Finite G] (K L : Subgroup G) (π : Set ℕ)
    (hKπ : ∀ q : ℕ, q ∈ (Nat.card (↥K)).primeFactors → q ∈ π)
    (hLπ : ∀ q : ℕ, q ∈ (Nat.card (↥L)).primeFactors → q ∈ πᶜ) :
    Nat.Coprime (Nat.card (↥K)) (Nat.card (↥L)) := by
  classical
  rw [Nat.coprime_iff_gcd_eq_one]
  apply le_antisymm
  · by_contra hnot
    have hgt : 1 < (Nat.card (↥K)).gcd (Nat.card (↥L)) := by
      have hpos : 0 < (Nat.card (↥K)).gcd (Nat.card (↥L)) :=
        Nat.gcd_pos_of_pos_left _ (Nat.card_pos (α := K))
      omega
    rcases Nat.exists_prime_and_dvd (by omega : (Nat.card (↥K)).gcd (Nat.card (↥L)) ≠ 1) with
      ⟨p, hp, hpdvd⟩
    have hpK : p ∣ Nat.card (↥K) := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpL : p ∣ Nat.card (↥L) := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpK' : p ∈ (Nat.card (↥K)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpK, Nat.card_pos.ne'⟩
    have hpL' : p ∈ (Nat.card (↥L)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpL, Nat.card_pos.ne'⟩
    exact hLπ p hpL' (hKπ p hpK')
  · have hpos : 0 < (Nat.card (↥K)).gcd (Nat.card (↥L)) :=
      Nat.gcd_pos_of_pos_left _ (Nat.card_pos (α := K))
    omega

/-- The `π`- and `πᶜ`-parts of the Fitting subgroup intersect trivially. -/
public theorem piCoreOf_inf_piCoreOf_compl_eq_bot
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    piCoreOf (fittingSubgroupOf H) π ⊓
      piCoreOf (fittingSubgroupOf H) πᶜ = ⊥ := by
  classical
  let A : Subgroup G := piCoreOf (fittingSubgroupOf H) π
  let B : Subgroup G := piCoreOf (fittingSubgroupOf H) πᶜ
  have hdvdA : Nat.card (↥(A ⊓ B)) ∣ Nat.card (↥A) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdB : Nat.card (↥(A ⊓ B)) ∣ Nat.card (↥B) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hdvd : Nat.card (↥(A ⊓ B)) ∣
      (Nat.card (↥A)).gcd (Nat.card (↥B)) := Nat.dvd_gcd hdvdA hdvdB
  have hcop : Nat.Coprime (Nat.card (↥A)) (Nat.card (↥B)) :=
    natCard_coprime_of_primeDivisors_compl A B π
      (piCoreOf_primeDivisors (fittingSubgroupOf H) π)
      (piCoreOf_primeDivisors (fittingSubgroupOf H) πᶜ)
  have hdvd1 : Nat.card (↥(A ⊓ B)) ∣ 1 := by
    rwa [hcop.gcd_eq_one] at hdvd
  have hle1 : Nat.card (↥(A ⊓ B)) ≤ 1 :=
    Nat.le_of_dvd (by norm_num : 0 < 1) hdvd1
  exact (Subgroup.card_le_one_iff_eq_bot (A ⊓ B)).mp hle1

/-- The `π`- and `πᶜ`-parts of the Fitting subgroup commute. -/
public theorem piCoreOf_commutator_piCoreOf_compl_eq_bot
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    ⁅piCoreOf (fittingSubgroupOf H) π, piCoreOf (fittingSubgroupOf H) πᶜ⁆ = ⊥ := by
  classical
  let F : Subgroup G := fittingSubgroupOf H
  let A : Subgroup (↥F) := piCore π (↥F)
  let B : Subgroup (↥F) := piCore πᶜ (↥F)
  have : A.Normal := by dsimp [A]; exact piCore_normal_local π
  have : B.Normal := by dsimp [B]; exact piCore_normal_local πᶜ
  have hABle : ⁅A, B⁆ ≤ A ⊓ B := Subgroup.commutator_le_inf A B
  have hcardA : Nat.card (↥A) = Nat.card (↥(piCoreOf F π)) := by
    dsimp [A, piCoreOf]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (piCore π (↥F)) F.subtype
      F.subtype_injective).toEquiv
  have hcardB : Nat.card (↥B) = Nat.card (↥(piCoreOf F πᶜ)) := by
    dsimp [B, piCoreOf]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (piCore πᶜ (↥F)) F.subtype
      F.subtype_injective).toEquiv
  have hcop : Nat.Coprime (Nat.card (↥A)) (Nat.card (↥B)) := by
    rw [hcardA, hcardB]
    exact natCard_coprime_of_primeDivisors_compl (piCoreOf F π) (piCoreOf F πᶜ) π
      (piCoreOf_primeDivisors F π)
      (piCoreOf_primeDivisors F πᶜ)
  have hinf_card : Nat.card (↥(A ⊓ B)) ≤ 1 := by
    have hdvdA : Nat.card (↥(A ⊓ B)) ∣ Nat.card (↥A) :=
      Subgroup.card_dvd_of_le inf_le_left
    have hdvdB : Nat.card (↥(A ⊓ B)) ∣ Nat.card (↥B) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hdvd : Nat.card (↥(A ⊓ B)) ∣
        (Nat.card (↥A)).gcd (Nat.card (↥B)) := Nat.dvd_gcd hdvdA hdvdB
    have hdvd1 : Nat.card (↥(A ⊓ B)) ∣ 1 := by
      rwa [hcop.gcd_eq_one] at hdvd
    exact Nat.le_of_dvd (by norm_num : 0 < 1) hdvd1
  have hABbot : A ⊓ B = ⊥ := (Subgroup.card_le_one_iff_eq_bot (A ⊓ B)).mp hinf_card
  have hcommbot : ⁅A, B⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact hABle.trans (le_of_eq hABbot)
  have hmap : (⁅A, B⁆).map F.subtype =
      ⁅piCoreOf F π, piCoreOf F πᶜ⁆ := by
    dsimp [A, B, piCoreOf]
    rw [Subgroup.map_commutator]
  rw [← hmap, hcommbot, Subgroup.map_bot]

/-- `O_π(F(H))` centralizes `O_{πᶜ}(F(H))`. -/
public theorem piCoreOf_centralizer_piCoreOf_compl
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    piCoreOf (fittingSubgroupOf H) π ≤
      Subgroup.centralizer ((piCoreOf (fittingSubgroupOf H) πᶜ : Subgroup G) : Set G) :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := piCoreOf (fittingSubgroupOf H) π)
    (H₂ := piCoreOf (fittingSubgroupOf H) πᶜ)).1
      (piCoreOf_commutator_piCoreOf_compl_eq_bot H π)

/-- `O_{πᶜ}(F(H))` centralizes `O_π(F(H))`. -/
public theorem piCoreOf_compl_centralizer_piCoreOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    piCoreOf (fittingSubgroupOf H) πᶜ ≤
      Subgroup.centralizer ((piCoreOf (fittingSubgroupOf H) π : Subgroup G) : Set G) :=
  (Subgroup.le_centralizer_iff
    (H := piCoreOf (fittingSubgroupOf H) π)
    (K := piCoreOf (fittingSubgroupOf H) πᶜ)).1
      (piCoreOf_centralizer_piCoreOf_compl H π)

end CFSG.GorensteinWalter
