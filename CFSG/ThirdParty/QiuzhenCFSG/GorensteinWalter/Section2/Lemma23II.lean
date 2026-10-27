module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17i
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.InvolutionInvertsOfDisjointHhat
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PiCoreCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.3(ii): the `πᶜ`-part of `F(M)` avoids `Ĥ`

In the paragraph preceding Lemma 2.3, the paper sets
`π := π(F(Ĥ))`; on p. 216 it defines `F_ρ(X) := O_ρ(F(X))`.
Consequently the subgroup in Lemma 2.3(ii) is
`F_{πᶜ}(M) = O_{πᶜ}(F(M))`, not the full odd core `O_{2ᶜ}(M)`.

The first conclusion is therefore the direct all-primes consequence of
Bender [1, 1.7(i)].  The parenthetical second conclusion follows from the
fixed-point-free action of `t` on this normal subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem lemma23II_exists_prime_order_subgroup_le_of_ne_bot
    {G : Type u} [Group G] [Finite G] {P : Subgroup G} (hPne : P ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ R : Subgroup G, R ≤ P ∧ Nat.card R = p.val := by
  classical
  have hcard_ne_one : Nat.card P ≠ 1 := by
    intro hcard
    exact hPne ((Subgroup.eq_bot_iff_card (H := P)).2 hcard)
  obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card' (G := P) p hpdiv
  let R : Subgroup G := Subgroup.zpowers ((a : P) : G)
  have hRleP : R ≤ P := Subgroup.zpowers_le.2 a.property
  let q : Nat.Primes := ⟨p, hpprime⟩
  have horderG : orderOf ((a : P) : G) = q.val := by
    simpa [q, Subgroup.orderOf_coe] using ha_order
  have hRcard : Nat.card R = q.val := by
    simp [R, Nat.card_zpowers, horderG]
  exact ⟨q, R, hRleP, hRcard⟩

/-- Lemma 2.3(ii) (Bender p. 219).  With
`π = π(F(Ĥ))`, the subgroup `F_{πᶜ}(M) = O_{πᶜ}(F(M))` avoids
`Ĥ`; hence `t` inverts it whenever `t ∈ M`. -/
public theorem lemma_2_3_ii
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (_hM : IsCoatom M)
    (hAM : NormalizerControlledBy c.Hhat M)
    (_hne : M ≠ c.Hhat) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    let D := piCoreOf (fittingSubgroupOf M) πᶜ
    D ⊓ c.Hhat = ⊥ ∧
      (c.t ∈ M → ∀ x : G, x ∈ (D : Set G) → c.t * x * c.t⁻¹ = x⁻¹) := by
  classical
  let π := primesOfOrder (fittingSubgroupOf c.Hhat)
  let F := fittingSubgroupOf M
  let D := piCoreOf F πᶜ
  change D ⊓ c.Hhat = ⊥ ∧
    (c.t ∈ M → ∀ x : G, x ∈ (D : Set G) → c.t * x * c.t⁻¹ = x⁻¹)
  have hqdisj : ∀ q : ℕ, q.Prime → q ∉ π → qCoreOf M q ⊓ c.Hhat = ⊥ := by
    rcases controlCore_of_normalizerControlledBy hAM with
      ⟨S, _hSne, hSF, hSM, hSsub, hCS⟩
    exact bender1970_1_7_i_oddCoreDisjoint
      (minimalCounterexample_isSimple hmin) c.Hhat c.Hhat_maximal
      S hSF hSsub hCS hSM
  have hDdisj : D ⊓ c.Hhat = ⊥ := by
    by_contra hnebot
    rcases lemma23II_exists_prime_order_subgroup_le_of_ne_bot hnebot with
      ⟨q, R, hRK, hRcard⟩
    have hRD : R ≤ D := hRK.trans inf_le_left
    have hRH : R ≤ c.Hhat := hRK.trans inf_le_right
    have hRF : R ≤ F := hRD.trans (piCoreOf_le F πᶜ)
    have hFM : F ≤ M := by
      simpa [F] using (fittingSubgroupOf_isNormalIn M).1
    have hFnil : Group.IsNilpotent (↑F) := by
      change Group.IsNilpotent (↑(fittingSubgroupOf M))
      exact fittingSubgroupOf_isNilpotent M
    have hRsubF : (R.subgroupOf F).IsSubnormal :=
      isSubnormal_of_nilpotent hFnil R hRF
    have hRsubM : (R.subgroupOf M).IsSubnormal :=
      isSubnormal_of_isNormalIn_subgroup hFM
        (by simpa [F] using fittingSubgroupOf_isNormalIn M) hRF hRsubF
    have hRp : IsPGroup q.val R := by
      apply IsPGroup.of_card (n := 1)
      simp [hRcard]
    have hRq : R ≤ qCoreOf M q.val :=
      le_qCoreOf_of_isSubnormal_isPGroup M R q.val
        (hRF.trans hFM) hRsubM hRp
    have hqdvdD : q.val ∣ Nat.card D := by
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le hRD
    have hqpfD : q.val ∈ (Nat.card D).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨q.2, hqdvdD, Nat.card_pos.ne'⟩
    have hqnotπ : q.val ∉ π :=
      piCoreOf_primeDivisors F πᶜ q.val hqpfD
    have hQbot : qCoreOf M q.val ⊓ c.Hhat = ⊥ := hqdisj q.val q.2 hqnotπ
    have hRbot : R = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hx' : x ∈ qCoreOf M q.val ⊓ c.Hhat := ⟨hRq hx, hRH hx⟩
      rw [hQbot] at hx'
      exact hx'
    have hqone : q.val = 1 := by
      calc
        q.val = Nat.card R := hRcard.symm
        _ = 1 := by simp [hRbot]
    exact q.2.ne_one hqone
  have hDnormal : IsNormalIn D M := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := M) (F := F) (K := piCore πᶜ (↑F))
      (piCore_characteristic πᶜ)
      (by simpa [F] using fittingSubgroupOf_isNormalIn M)
    simpa [D, piCoreOf] using h
  refine ⟨hDdisj, ?_⟩
  intro htM
  exact involution_inverts_of_mem_normalizer_inf_Hhat_eq_bot c D
    ((le_normalizer_of_isNormalIn hDnormal) htM) hDdisj

end CFSG.GorensteinWalter
