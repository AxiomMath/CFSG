module

public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31Rad

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {A : Type} [Group A] {G₀ : Type} [Group G₀]

theorem isPGroup_of_inf [Finite A] {S H : Subgroup A} (hS : S.Normal)
    (hA2 : Nat.card A ≤ 2 * Nat.card S) (hHS : IsPGroup 2 ↥(S ⊓ H)) : IsPGroup 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSi : S.index ≤ 2 := by
    have h := S.card_mul_index
    have hpos : 0 < Nat.card S := Nat.card_pos
    by_contra hlt
    have : 3 * Nat.card S ≤ Nat.card A := by
      rw [← h, mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hrel : S.relIndex H ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal (H := S) (K := H))).trans hSi
  have hpos : 0 < S.relIndex H := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHS
  have hmul := Subgroup.relIndex_mul_card S H
  rw [hk] at hmul
  rcases (show S.relIndex H = 1 ∨ S.relIndex H = 2 by omega) with h1 | h2
  · exact IsPGroup.of_card (n := k) (by rw [← hmul, h1, one_mul])
  · exact IsPGroup.of_card (n := k + 1) (by rw [← hmul, h2, pow_succ, mul_comm])

theorem perfect_normal_eq {N Q : Subgroup G₀} (hQN : Q ≤ N) (hN : ⁅N, N⁆ = N)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQn : N ≤ Subgroup.normalizer (Q : Set G₀))
    (hs : ∀ K : Subgroup G₀, Q ≤ K → K ≤ N → N ≤ Subgroup.normalizer (K : Set G₀) →
      K = Q ∨ K = N)
    (K : Subgroup G₀) (hKN : K ≤ N) (hNK : N ≤ Subgroup.normalizer (K : Set G₀))
    (hKQ : ¬ K ≤ Q) : K = N := by
  have hKQn : (K ⊔ Q : Subgroup G₀) = N := by
    rcases hs (K ⊔ Q) le_sup_right (sup_le hKN hQN) (fun n hn => by
      have h1 := hNK hn
      have h2 := hQn hn
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
      rw [Subgroup.map_sup, h1, h2]) with h | h
    · exact absurd (h ▸ le_sup_left) hKQ
    · exact h
  refine le_antisymm hKN ?_
  rw [← hN, Subgroup.commutator_le]
  intro x hx z hz
  rw [← hKQn] at hx hz
  have hQK : Q ≤ Subgroup.normalizer (K : Set G₀) := hQN.trans hNK
  have hx' : x ∈ ((K : Set G₀) * (Q : Set G₀)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K Q hQK]; exact hx
  have hz' : z ∈ ((K : Set G₀) * (Q : Set G₀)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K Q hQK]; exact hz
  obtain ⟨k, hk, q, hq, rfl⟩ := hx'
  obtain ⟨k', hk', q', hq', rfl⟩ := hz'
  have hKnN : (K.subgroupOf N).Normal := ⟨fun a ha n => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hNK n.2) a).mp ha⟩
  have hkN : k ∈ N := hKN hk
  have hk'N : k' ∈ N := hKN hk'
  have hqN : q ∈ N := hQN hq
  have hq'N : q' ∈ N := hQN hq'
  set π := QuotientGroup.mk' (K.subgroupOf N) with hπ
  have hπk : π ⟨k, hkN⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hk
  have hπk' : π ⟨k', hk'N⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hk'
  have hc : π ⟨q, hqN⟩ * π ⟨q', hq'N⟩ = π ⟨q', hq'N⟩ * π ⟨q, hqN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQab q hq q' hq')
  have hmem : (⟨k * q * (k' * q') * (k * q)⁻¹ * (k' * q')⁻¹, N.mul_mem (N.mul_mem (N.mul_mem
      (N.mul_mem hkN hqN) (N.mul_mem hk'N hq'N)) (N.inv_mem (N.mul_mem hkN hqN)))
      (N.inv_mem (N.mul_mem hk'N hq'N))⟩ : ↥N) ∈ K.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff (N := K.subgroupOf N)]
    have e : (⟨k * q * (k' * q') * (k * q)⁻¹ * (k' * q')⁻¹, N.mul_mem (N.mul_mem (N.mul_mem
        (N.mul_mem hkN hqN) (N.mul_mem hk'N hq'N)) (N.inv_mem (N.mul_mem hkN hqN)))
        (N.inv_mem (N.mul_mem hk'N hq'N))⟩ : ↥N) =
        ⟨k, hkN⟩ * ⟨q, hqN⟩ * (⟨k', hk'N⟩ * ⟨q', hq'N⟩) * (⟨k, hkN⟩ * ⟨q, hqN⟩)⁻¹ *
          (⟨k', hk'N⟩ * ⟨q', hq'N⟩)⁻¹ := rfl
    rw [e]
    change π _ = 1
    simp only [map_mul, map_inv, hπk, hπk', one_mul]
    rw [hc]
    group
  exact hmem

theorem config_of_abelCent [Finite A] [Finite G₀] {S M₀ R M V : Subgroup A} (hS : S.Normal)
    (hA2 : Nat.card A ≤ 2 * Nat.card S) (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀)
    (hR : IsPGroup 2 ↥R) (hRM : R ≤ M) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A))
    (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hVM₀ : V ≤ M₀) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V)
    (hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) {y t : A} (hy : y ∈ M₀) (ht : t ∈ V)
    (hyt : y * t * y⁻¹ ≠ t) (ι : G₀ →* A) (hι : Function.Injective ι) (hιS : ι.range = S)
    {U Q N : Subgroup G₀} (hQ : Subgroup.centralizer (U : Set G₀) = Q)
    (hQ2 : IsPGroup 2 ↥Q) (hΩ : ∀ q ∈ Q, q * q = 1 → q ∈ U) (hQN : Q ≤ N)
    (hN : Subgroup.normalizer (U : Set G₀) = N)
    (hNs : ∀ K : Subgroup G₀, K ≤ N → N ≤ Subgroup.normalizer (K : Set G₀) → ⁅K, K⁆ = K →
      ¬ K ≤ Q → K = N)
    (hU : orbSub y t = U.map ι) :
    V = U.map ι ∧ pCoreOf 2 M₀ = Q.map ι ∧ M₀ = N.map ι ∧
      R = Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) := by
  obtain ⟨hVO, hOR, hRC, hNRM⟩ := orb_facts hR hRM hMN hM₀R hsyl hVM₀ hV hcomm hVc hNR
  have hM₀V := le_normalizer_of_comm hcomm
  have hUV : U.map ι ≤ V := hU ▸ orbSub_le (hM₀V hy) ht
  have hCS : S ⊓ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) = Q.map ι := by
    rw [← hQ, ← hιS, ← map_centralizer_eq ι hι U]
  have hVab : V ≤ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := hV.1.is_comm.comm ⟨u, hUV hu⟩ ⟨v, hv⟩
    simpa using congrArg Subtype.val this
  have hVQ : V ≤ Q.map ι := hCS ▸ le_inf (hVM₀.trans hM₀S) hVab
  have hVU : V = U.map ι := by
    refine le_antisymm (fun v hv => ?_) hUV
    obtain ⟨q, hq, rfl⟩ := hVQ hv
    refine ⟨q, hΩ q hq (hι ?_), rfl⟩
    rw [map_mul, map_one]
    have := hV.2 _ hv
    rwa [sq] at this
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer ((U.map ι : Subgroup A) : Set A)) := by
    refine isPGroup_of_inf hS hA2 ?_
    rw [hCS]
    exact hQ2.map ι
  have hRV : R = Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) := by
    rw [← hVU] at hC2 ⊢
    exact eq_centralizer_of_isPGroup hMN hM₀V hsyl hNR hRC hC2
  have hNU : Subgroup.normalizer ((U.map ι : Subgroup A) : Set A) ≤
      Subgroup.normalizer (M₀ : Set A) := by
    rw [hRV] at hNRM
    exact (normalizer_le_normalizer_centralizer _).trans hNRM
  have hNmap : N.map ι = S ⊓ Subgroup.normalizer ((U.map ι : Subgroup A) : Set A) := by
    rw [← hN, ← hιS]; exact map_normalizer_eq ι hι U
  have hM₀r : M₀ ≤ ι.range := hιS ▸ hM₀S
  set K₀ := M₀.comap ι with hK₀
  have hK₀map : K₀.map ι = M₀ := map_comap_eq_of_le_range ι hM₀r
  have hK₀perf : ⁅K₀, K₀⁆ = K₀ :=
    Subgroup.map_injective hι (by rw [Subgroup.map_commutator, hK₀map, hper])
  have hK₀N : K₀ ≤ N := by
    intro k hk
    have h1 : ι k ∈ N.map ι := by
      rw [hNmap]; exact ⟨hM₀S hk, (hVU ▸ hM₀V) hk⟩
    obtain ⟨k', hk', hkk'⟩ := h1
    rwa [← hι hkk']
  have hNK₀ : N ≤ Subgroup.normalizer (K₀ : Set G₀) := by
    intro n hn
    have hnA : ι n ∈ Subgroup.normalizer (M₀ : Set A) := by
      have : ι n ∈ N.map ι := ⟨n, hn, rfl⟩
      rw [hNmap] at this
      exact hNU this.2
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simp only [hK₀, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hnA (ι k)
  have hK₀Q : ¬ K₀ ≤ Q := by
    intro hle
    have hyQ : y ∈ Q.map ι := by
      rw [← hK₀map] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact ⟨k, hle hk, rfl⟩
    rw [← hCS] at hyQ
    have htU : t ∈ U.map ι := hU ▸ mem_orbSub y t
    have := Subgroup.mem_centralizer_iff.mp hyQ.2 t htU
    exact hyt (by rw [← this, mul_inv_cancel_right])
  have hM : M₀ = N.map ι := by
    rw [← hK₀map, hNs K₀ hK₀N hNK₀ hK₀perf hK₀Q]
  have hOQ : pCoreOf 2 M₀ ≤ Q.map ι := by
    rw [← hCS]
    exact le_inf ((pCoreOf_le 2 M₀).trans hM₀S) (hOR.trans (hRC.trans (hVU ▸ le_rfl)))
  have hQO : Q.map ι ≤ pCoreOf 2 M₀ := by
    refine le_pCoreOf_of_le_normalizer 2 (hM ▸ Subgroup.map_mono hQN) (fun m hm => ?_)
      (hQ2.map ι)
    rw [hM] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have hnQ : n ∈ Subgroup.normalizer (Q : Set G₀) := by
      rw [← hQ]
      exact normalizer_le_normalizer_centralizer U (hN ▸ hn)
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨n * q * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnQ q).mp hq, by simp⟩
    · rintro ⟨q, hq, hqe⟩
      refine ⟨n⁻¹ * q * n, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnQ) q).mp hq
        simpa using this
      · have : ι q = ι n * a * (ι n)⁻¹ := hqe
        rw [map_mul, map_mul, map_inv, this]
        group
  exact ⟨hVU, le_antisymm hOQ hQO, hM, hRV⟩

end CFSG.Quasithin.KGC31

end
