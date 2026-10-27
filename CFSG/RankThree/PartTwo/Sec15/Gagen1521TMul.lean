module

public import CFSG.Open.FusionDefs
public import CFSG.Foundations.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1521T

open CFSG
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma le_normalizer_map_subtype_of_normal {M : Subgroup G} (X : Subgroup M)
    [hX : X.Normal] :
    M ≤ Subgroup.normalizer ((X.map M.subtype : Subgroup G) : Set G) := by
  have hXsub : (X.map M.subtype).subgroupOf M = X :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective X
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le X), hXsub]
  exact hX

private lemma exists_mul_pow_of_le_normalizer {N Q : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) {n : G} (hn : n ∈ N) {q : G} (hq : q ∈ Q) :
    ∀ k : ℕ, ∃ n' ∈ N, (n * q) ^ k = n' * q ^ k := by
  have hconj : ∀ k : ℕ, q ^ k * n * (q ^ k)⁻¹ ∈ N := by
    intro k
    induction k with
    | zero => simpa using hn
    | succ k ih =>
        have hstep : q * (q ^ k * n * (q ^ k)⁻¹) * q⁻¹ ∈ N :=
          (Subgroup.le_normalizer_iff.mp hQN) q hq _ ih
        simpa [pow_succ', mul_assoc] using hstep
  intro k
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
      obtain ⟨n', hn', hk⟩ := ih
      refine ⟨n' * (q ^ k * n * (q ^ k)⁻¹), N.mul_mem hn' (hconj k), ?_⟩
      calc
        (n * q) ^ (k + 1) = (n * q) ^ k * (n * q) := pow_succ _ _
        _ = (n' * q ^ k) * (n * q) := by rw [hk]
        _ = n' * (q ^ k * n * (q ^ k)⁻¹) * (q ^ k * q) := by group
        _ = n' * (q ^ k * n * (q ^ k)⁻¹) * q ^ (k + 1) := by rw [pow_succ]

theorem coe_sup_eq_mul_of_two_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H Q P T : Subgroup G}
    (hH : Group.IsSolvable H) (hHp : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p)
    (hQ : CFSG.Open.fusionIsSylowIn p Q H) (hQc : IsMulCommutative Q) (hPQ : P ≤ Q)
    (hPe : ∀ x ∈ P, x ^ p = 1) (hΩ : ∀ x ∈ Q, x ^ p = 1 → x ∈ P)
    (hT : CFSG.Open.fusionIsSylowIn 2 T H) :
    ((P ⊔ T : Subgroup G) : Set G) = (T : Set G) * (P : Set G) := by
  haveI hsolvH : Group.IsSolvable ↥H := hH
  let K : Subgroup ↥H := CFSG.pCore 2 ↥H
  have hKn : K.Normal := CFSG.pCore_normal
  letI : K.Normal := hKn
  let N : Subgroup G := K.map H.subtype
  have hK2 : IsPGroup 2 K := CFSG.pCore_isPGroup
  have hN2 : IsPGroup 2 N := hK2.map H.subtype
  have hNleH : N ≤ H := Subgroup.map_subtype_le K
  have hNnorm : H ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_map_subtype_of_normal K
  have hQH : Q ≤ H := hQ.1
  have hQp : IsPGroup p Q := hQ.2.1
  have hTH : T ≤ H := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hPH : P ≤ H := hPQ.trans hQH
  have hNleT : N ≤ T := by
    have hsupH : N ⊔ T ≤ H := sup_le hNleH hTH
    have hsup2 : IsPGroup 2 ↥(N ⊔ T) :=
      IsPGroup.to_sup_of_normal_left' hN2 hT2 (hTH.trans hNnorm)
    have hNT : N ⊔ T = T := hT.2.2 (N ⊔ T) hsupH hsup2 le_sup_right
    exact le_sup_left.trans_eq hNT
  have hQN : Q ⊓ N = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp2 Q N hQp hN2)
  let QH : Subgroup ↥H := Q.subgroupOf H
  have hQHp : IsPGroup p QH := hQp.comap_subtype (K := H)
  have hQHmap : QH.map H.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQH
  have hQHmax : ∀ {S : Subgroup ↥H}, IsPGroup p S → QH ≤ S → S = QH := by
    intro S hSp hQHS
    have hSmap_le : S.map H.subtype ≤ H := Subgroup.map_subtype_le S
    have hSmap_p : IsPGroup p (S.map H.subtype) := hSp.map H.subtype
    have hQle : Q ≤ S.map H.subtype := by
      rw [← hQHmap]
      exact Subgroup.map_mono hQHS
    have hSeq : S.map H.subtype = Q := hQ.2.2 (S.map H.subtype) hSmap_le hSmap_p hQle
    exact Subgroup.map_subtype_inj.mp (by rw [hSeq, hQHmap])
  let Qsyl : Sylow p ↥H := Sylow.mk QH hQHp (fun {S} hSp hQHS => hQHmax hSp hQHS)
  let Hbar := ↥H ⧸ K
  let Qbar : Subgroup Hbar := QH.map (QuotientGroup.mk' K)
  let QbarSyl : Sylow p Hbar := Qsyl.mapSurjective (QuotientGroup.mk'_surjective K)
  have hQbarSyl_coe : (QbarSyl : Subgroup Hbar) = Qbar :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective K) Qsyl
  have hHbar_solv : Group.IsSolvable Hbar := inferInstance
  have hcore2 : CFSG.pCore 2 Hbar = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.pCore_quotient_pCore_eq_bot
  have hcorep : CFSG.pPrimeCore p Hbar = ⊥ := by
    set L : Subgroup Hbar := CFSG.pPrimeCore p Hbar
    have hLn : L.Normal := CFSG.pPrimeCore_normal
    have hLcop : Nat.Coprime p (Nat.card L) := CFSG.pPrimeCore_coprime_card
    have hL2 : IsPGroup 2 L := by
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro q hq hqL
      have hqHbar : q ∣ Nat.card Hbar :=
        Nat.dvd_trans hqL (Subgroup.card_subgroup_dvd_card L)
      have hqH : q ∣ Nat.card ↥H :=
        Nat.dvd_trans hqHbar (Subgroup.card_quotient_dvd_card K)
      rcases hHp q hq hqH with hq2 | hqp
      · exact hq2
      · exfalso
        have hpdvd : p ∣ Nat.card L := hqp ▸ hqL
        exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hLcop) hpdvd
    have hle : L ≤ CFSG.pCore 2 Hbar := le_sSup ⟨hLn, hL2⟩
    rw [hcore2] at hle
    exact le_bot_iff.mp hle
  have hQbar_comm : IsMulCommutative Qbar := by
    have hQH_comm : IsMulCommutative QH :=
      Subgroup.comap_injective_isMulCommutative (f := H.subtype) Q H.subtype_injective
    exact Subgroup.map_isMulCommutative QH (QuotientGroup.mk' K)
  have hpCore_le_Qbar : CFSG.pCore p Hbar ≤ Qbar := by
    have h := IsPGroup.le_sylow_of_normal (N := CFSG.pCore p Hbar) CFSG.pCore_isPGroup QbarSyl
    rwa [hQbarSyl_coe] at h
  have hQbar_le_pCore : Qbar ≤ CFSG.pCore p Hbar := by
    haveI : IsMulCommutative Qbar := hQbar_comm
    have h1 : Qbar ≤ Subgroup.centralizer (Qbar : Set Hbar) := Subgroup.le_centralizer Qbar
    have h2 : Subgroup.centralizer (Qbar : Set Hbar) ≤
        Subgroup.centralizer (CFSG.pCore p Hbar : Set Hbar) :=
      Subgroup.centralizer_le (fun x hx => hpCore_le_Qbar hx)
    have h3 : Subgroup.centralizer (CFSG.pCore p Hbar : Set Hbar) ≤ CFSG.pCore p Hbar :=
      CFSG.centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hHbar_solv hcorep
    exact h1.trans (h2.trans h3)
  have hQbar_eq : Qbar = CFSG.pCore p Hbar := le_antisymm hQbar_le_pCore hpCore_le_Qbar
  have hQbar_normal : Qbar.Normal := by
    rw [hQbar_eq]
    exact CFSG.pCore_normal
  have hpre_eq : Qbar.comap (QuotientGroup.mk' K) = K ⊔ QH := by
    change (QH.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = K ⊔ QH
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  have hKQH_normal : (K ⊔ QH).Normal := by
    rw [← hpre_eq]
    exact hQbar_normal.comap _
  have hKQH_map : (K ⊔ QH).map H.subtype = N ⊔ Q := by
    rw [Subgroup.map_sup, hQHmap]
  have hHnormNQ : H ≤ Subgroup.normalizer ((N ⊔ Q : Subgroup G) : Set G) := by
    have h := le_normalizer_map_subtype_of_normal (K ⊔ QH)
    rwa [hKQH_map] at h
  have hQNnorm : Q ≤ Subgroup.normalizer (N : Set G) := hQH.trans hNnorm
  have hNQmul : ((N ⊔ Q : Subgroup G) : Set G) = (N : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N Q hQNnorm
  have hNPmul : ((N ⊔ P : Subgroup G) : Set G) = (N : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N P (hPH.trans hNnorm)
  have hHnormNP : H ≤ Subgroup.normalizer ((N ⊔ P : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh x hx
    change x ∈ ((N ⊔ P : Subgroup G) : Set G) at hx
    change h * x * h⁻¹ ∈ ((N ⊔ P : Subgroup G) : Set G)
    rw [hNPmul] at hx ⊢
    obtain ⟨n, hn, y, hy, rfl⟩ := hx
    have hn' : h * n * h⁻¹ ∈ N :=
      (Subgroup.le_normalizer_iff.mp hNnorm) h hh n hn
    have hyNQ : h * y * h⁻¹ ∈ N ⊔ Q :=
      (Subgroup.le_normalizer_iff.mp hHnormNQ) h hh y (Subgroup.mem_sup_right (hPQ hy))
    change h * y * h⁻¹ ∈ ((N ⊔ Q : Subgroup G) : Set G) at hyNQ
    rw [hNQmul] at hyNQ
    obtain ⟨n₂, hn₂, q, hq, hEq⟩ := hyNQ
    change n₂ * q = h * y * h⁻¹ at hEq
    have hpow : (n₂ * q) ^ p = 1 := by
      rw [hEq, conj_pow, hPe y hy]
      simp
    obtain ⟨n₃, hn₃, hpow_eq⟩ := exists_mul_pow_of_le_normalizer hQNnorm hn₂ hq p
    have hqpowN : q ^ p ∈ N := by
      have hone : n₃ * q ^ p = 1 := by rw [← hpow_eq]; exact hpow
      have hqinv : q ^ p = n₃⁻¹ := (mul_eq_one_iff_inv_eq.mp hone).symm
      rw [hqinv]
      exact N.inv_mem hn₃
    have hqpow_bot : q ^ p = 1 := by
      have hmem : q ^ p ∈ Q ⊓ N := ⟨Q.pow_mem hq p, hqpowN⟩
      rw [hQN] at hmem
      simpa using hmem
    have hqP : q ∈ P := hΩ q hq hqpow_bot
    refine ⟨h * n * h⁻¹ * n₂, N.mul_mem hn' hn₂, q, hqP, ?_⟩
    change h * n * h⁻¹ * n₂ * q = h * (n * y) * h⁻¹
    rw [mul_assoc, hEq]
    group
  have hTN : (T : Set G) * (N : Set G) = (T : Set G) := by
    refine Set.Subset.antisymm (Subgroup.mul_subset (subset_refl _) hNleT) ?_
    intro x hx
    exact ⟨x, hx, 1, N.one_mem, by simp⟩
  have hsup_eq : P ⊔ T = T ⊔ (N ⊔ P) := by
    rw [← sup_assoc, sup_eq_left.mpr hNleT, sup_comm]
  have hTHNP : T ≤ Subgroup.normalizer ((N ⊔ P : Subgroup G) : Set G) :=
    hTH.trans hHnormNP
  calc
    ((P ⊔ T : Subgroup G) : Set G) = ((T ⊔ (N ⊔ P) : Subgroup G) : Set G) := by rw [hsup_eq]
    _ = (T : Set G) * ((N ⊔ P : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right T (N ⊔ P) hTHNP
    _ = (T : Set G) * ((N : Set G) * (P : Set G)) := by rw [hNPmul]
    _ = ((T : Set G) * (N : Set G)) * (P : Set G) := by rw [← mul_assoc]
    _ = (T : Set G) * (P : Set G) := by rw [hTN]

theorem isCharacteristicP_of_two_p {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : Group.IsSolvable H) (hHp : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p)
    (h0 : ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) → IsPGroup p N →
      N = ⊥) :
    IsCharacteristicP 2 ↥H := by
  haveI hsolvH : Group.IsSolvable ↥H := hH
  have hKbot : CFSG.pPrimeCore 2 ↥H = ⊥ := by
    set K : Subgroup ↥H := CFSG.pPrimeCore 2 ↥H with hK
    have hKn : K.Normal := CFSG.pPrimeCore_normal
    have hKcop : Nat.Coprime 2 (Nat.card K) := CFSG.pPrimeCore_coprime_card
    have hKp : IsPGroup p K := by
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro q hq hqK
      have hqH : q ∣ Nat.card ↥H :=
        Nat.dvd_trans hqK (Subgroup.card_subgroup_dvd_card K)
      rcases hHp q hq hqH with hq2 | hqp
      · by_cases hp2 : p = 2
        · exact hq2.trans hp2.symm
        · rw [hq2] at hqK
          exact absurd hqK ((Nat.prime_two.coprime_iff_not_dvd).mp hKcop)
      · exact hqp
    have hNle : K.map H.subtype ≤ H := Subgroup.map_subtype_le K
    have hNnorm : H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) :=
      le_normalizer_map_subtype_of_normal K
    have hNp : IsPGroup p (K.map H.subtype) := hKp.map H.subtype
    have hNbot : K.map H.subtype = ⊥ := h0 (K.map H.subtype) hNle hNnorm hNp
    have hKbot' : K = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective K H.subtype_injective).mp hNbot
    exact hKbot'
  exact CFSG.centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hH hKbot

end CFSG.RankThree.PartTwo.Sec15.Proof1521T
