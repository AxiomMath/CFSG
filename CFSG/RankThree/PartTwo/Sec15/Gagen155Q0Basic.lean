module

public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155Q0

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem le_of_le_sup_of_odd_relIndex {X R Q V H : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hQ : Q ≤ X ⊔ R) (hVQ : V ≤ Q)
    (hV : ¬ 2 ∣ V.relIndex Q) (hXH : X ≤ H) (hVH : V ≤ H) : Q ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := X ⊔ R with hN
  have hXN : X ≤ N := le_sup_left
  have hRN : R ≤ N := le_sup_right
  have hNX : N ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hRX
  have hnorm : (X.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr hNX
  have hdvd : X.relIndex Q ∣ Nat.card R := by
    have hQN : (Q.subgroupOf N).map N.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQ
    have heq : (X.subgroupOf N).relIndex (Q.subgroupOf N) = X.relIndex Q := by
      rw [Subgroup.subgroupOf, Subgroup.relIndex_comap, hQN]
    rw [← heq]
    refine (Subgroup.relIndex_dvd_index_of_normal _ _).trans ?_
    have htop : X.subgroupOf N ⊔ R.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hXN hRN, Subgroup.subgroupOf_self]
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_left]
    refine (Subgroup.relIndex_dvd_card _ _).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR2
  have hHdvd : H.relIndex Q ∣ 2 ^ m :=
    (Subgroup.relIndex_dvd_of_le_left Q hXH).trans (hm ▸ hdvd)
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hHdvd
  have hHV : H.relIndex Q ∣ V.relIndex Q := Subgroup.relIndex_dvd_of_le_left Q hVH
  have hj0 : j = 0 := by
    by_contra hj0
    exact hV ((dvd_pow_self 2 hj0).trans (hjeq ▸ hHV))
  rw [hj0, pow_zero] at hjeq
  exact Subgroup.relIndex_eq_one.mp hjeq

theorem le_sup_delta_of_two_subgroup (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {X K R U : Subgroup G}
    (hF : ∀ P : Subgroup G, P ≤ K → IsPGroup 2 P → A ≤ Subgroup.normalizer (P : Set G) →
      P ∈ scriptQ A (lB A))
    (hXK : X ≤ K) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hU : U ∈ scriptQ A (lB A)) (hU2 : IsPGroup 2 U)
    (hUK : U ≤ Subgroup.normalizer (K : Set G)) (hUR : U ≤ Subgroup.normalizer (R : Set G))
    (hUXR : U ≤ X ⊔ R) :
    U ≤ X ⊔ delta A (lB A) R := by
  have hUR2 : IsPGroup 2 ↥(U ⊔ R) := IsPGroup.to_sup_of_normal_right' hU2 hR2 hUR
  set Z := (U ⊔ R) ⊓ K with hZdef
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    Late.le_normalizer_inf (le_normalizer_sup hU.1.2.2 hAR) hAK
  have hZ : Z ∈ scriptQ A (lB A) := hF Z inf_le_right (hUR2.to_le inf_le_left) hAZ
  have hUZ : U ≤ Subgroup.normalizer (Z : Set G) :=
    Late.le_normalizer_inf (le_sup_left.trans Subgroup.le_normalizer) hUK
  have hW := sup_mem_scriptQ_of_item146 hA h146 hU hZ hUZ
  have hAWR : A ≤ Subgroup.normalizer (((U ⊔ Z) ⊓ R : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hW.1.2.2 hAR
  have hWR : (U ⊔ Z) ⊓ R ≤ delta A (lB A) R :=
    le_delta (mem_scriptQ_of_le hW inf_le_left hAWR) inf_le_right
  intro u hu
  have hu' : u ∈ ((X : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left X R hRX]
    exact hUXR hu
  obtain ⟨x, hx, r, hr, rfl⟩ := hu'
  have hxZ : x ∈ Z := by
    refine ⟨?_, hXK hx⟩
    have he : x = (x * r) * r⁻¹ := by group
    rw [he]
    exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (inv_mem hr))
  have hrW : r ∈ U ⊔ Z := by
    have he : r = x⁻¹ * (x * r) := by group
    rw [he]
    exact mul_mem (Subgroup.mem_sup_right (inv_mem hxZ)) (Subgroup.mem_sup_left hu)
  exact Subgroup.mul_mem_sup hx (hWR ⟨hrW, hr⟩)

theorem le_sup_delta_of_mem_scriptQ (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {X K R Q : Subgroup G}
    (hF : ∀ P : Subgroup G, P ≤ K → IsPGroup 2 P → A ≤ Subgroup.normalizer (P : Set G) →
      P ∈ scriptQ A (lB A))
    (hXK : X ≤ K) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hQ : Q ∈ scriptQ A (lB A)) (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hQR : Q ≤ Subgroup.normalizer (R : Set G)) (hQXR : Q ≤ X ⊔ R) :
    Q ≤ X ⊔ delta A (lB A) R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.2.1
  have hcop : Nat.Coprime 3 (Nat.card Q) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3
  obtain ⟨S, hS⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow 3 2
    Nat.prime_three Nat.prime_two A Q hA.isPGroup hQ.1.2.2 hcop
  set V := (S : Subgroup Q).map Q.subtype with hVdef
  have hVQ : V ≤ Q := Subgroup.map_subtype_le _
  have hV2 : IsPGroup 2 V := S.isPGroup'.map _
  have hVi : ¬ 2 ∣ V.relIndex Q := by
    have heq : V.subgroupOf Q = (S : Subgroup Q) :=
      Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
    rw [Subgroup.relIndex, heq]
    exact S.not_dvd_index
  have hVsc : V ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ hVQ hS
  have hVH := le_sup_delta_of_two_subgroup hA h146 hF hXK hAK hR2 hAR hRX hVsc hV2
    (hVQ.trans hQK) (hVQ.trans hQR) (hVQ.trans hQXR)
  exact le_of_le_sup_of_odd_relIndex hR2 hRX hQXR hVQ hVi le_sup_left hVH

theorem pCoreOf_mem_scriptQ_of_front (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {X K Y : Subgroup G}
    (hF : ∀ P : Subgroup G, P ≤ K → IsPGroup 2 P → A ≤ Subgroup.normalizer (P : Set G) →
      P ∈ scriptQ A (lB A))
    (hXK : X ≤ K) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hYΔ : Y = delta A (lB A) Y) (hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := hRY.trans hYX
  have hYle : Y ≤ X ⊔ delta A (lB A) R := by
    refine hYΔ.le.trans (sSup_le fun Q hQ => ?_)
    have hQY : Q ≤ Y := hQ.2
    exact le_sup_delta_of_mem_scriptQ hA h146 hF hXK hAK hR2 hAR hRX hQ.1 (hQY.trans hYK)
      (hQY.trans hYR) (hQY.trans hY.le)
  have hRX' : R ⊓ X ∈ scriptQ A (lB A) :=
    hF (R ⊓ X) (inf_le_right.trans hXK) (hR2.to_le inf_le_left) (Late.le_normalizer_inf hAR hAX)
  have hRle : R ≤ delta A (lB A) R := by
    intro r hr
    have hr' : r ∈ ((X : Set G) * (delta A (lB A) R : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X _ ((delta_le R).trans hRX)]
      exact hYle (hRY hr)
    obtain ⟨x, hx, d, hd, rfl⟩ := hr'
    have hxR : x ∈ R := by
      have he : x = (x * d) * d⁻¹ := by group
      rw [he]
      exact mul_mem hr (inv_mem (delta_le R hd))
    exact mul_mem (le_delta hRX' inf_le_left ⟨hxR, hx⟩) hd
  have h3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hΔ := delta_mem_scriptQ hA h146 (Z := R)
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr h3, hAR⟩
  exact mem_scriptQ_of_le hΔ hRle hAR

theorem pCoreOf_sup_mem_scriptQ_of_front (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {P J : Subgroup G}
    (hF : ∀ P' : Subgroup G, P' ≤ J → IsPGroup 2 P' → A ≤ Subgroup.normalizer (P' : Set G) →
      P' ∈ scriptQ A (lB A))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hP : P ∈ scriptQ A (lB A)) (hP2 : IsPGroup 2 P)
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) :
    CFSG.Open.pCoreOf 2 (P ⊔ J) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 (P ⊔ J) with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_normalizer_sup hP.1.2.2 hAJ).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hPQ2 : IsPGroup 2 ↥(P ⊔ Q) := IsPGroup.to_sup_of_normal_right' hP2 hQ2 hPQ
  set Z := (P ⊔ Q) ⊓ J with hZdef
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    Late.le_normalizer_inf (le_normalizer_sup hP.1.2.2 hAQ) hAJ
  have hZ : Z ∈ scriptQ A (lB A) := hF Z inf_le_right (hPQ2.to_le inf_le_left) hAZ
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) :=
    Late.le_normalizer_inf (le_sup_left.trans Subgroup.le_normalizer) hPJ
  have hW := sup_mem_scriptQ_of_item146 hA h146 hP hZ hPZ
  refine mem_scriptQ_of_le hW (fun q hq => ?_) hAQ
  have hqJP : q ∈ J ⊔ P := by
    rw [sup_comm]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have hq' : q ∈ ((J : Set G) * (P : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left J P hPJ]
    exact hqJP
  obtain ⟨j, hj, p, hp, rfl⟩ := hq'
  have hjZ : j ∈ Z := by
    refine ⟨?_, hj⟩
    have he : j = (j * p) * p⁻¹ := by group
    rw [he]
    exact mul_mem (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left (inv_mem hp))
  exact mul_mem (Subgroup.mem_sup_right hjZ) (Subgroup.mem_sup_left hp)

end CFSG.RankThree.PartTwo.Sec15.Proof155Q0
