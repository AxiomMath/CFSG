module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Count

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem oTwoQuot_perm3_of_relIndex {X P : Subgroup G} (hP : IsSylowTwoOf P X)
    (hPQ : ¬ P ≤ pCoreOf 2 X) (h3 : P.relIndex X = 3) :
    Nonempty (OTwoQuot X ≃* Perm (Fin 3)) := by
  set φ := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) with hφ
  set T : Subgroup (OTwoQuot X) := (P.subgroupOf X).map φ with hT
  have hT2 : IsPGroup 2 T := (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).map _
  have hkerP : φ.ker ≤ P.subgroupOf X := by
    intro x hx
    rw [hφ, QuotientGroup.ker_mk', F1.mem_pCore_iff_coe] at hx
    exact isSylowTwoOf_pCoreOf_le hP hx
  have hTi : T.index = 3 := by
    rw [hT, Subgroup.index_map_eq (f := φ) (H := P.subgroupOf X) (QuotientGroup.mk'_surjective _)
      hkerP]
    exact h3
  have hT0 : T ≠ ⊥ := by
    intro hT0
    apply hPQ
    intro p hp
    have hpT : φ ⟨p, hP.1 hp⟩ ∈ T := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
    rw [hT0, Subgroup.mem_bot] at hpT
    exact (F1.mem_pCore_iff_coe _).mp ((QuotientGroup.eq_one_iff _).mp hpT)
  exact nonempty_mulEquiv_perm3 (noNormalTwo_oTwoQuot X) hT2 hT0 hTi

omit [Finite G] in
theorem mem_or_of_relIndex_two {K L : Subgroup G} (h2 : K.relIndex L = 2) {a b : G}
    (ha : a ∈ L) (hb : b ∈ L) (haK : a ∉ K) : b ∈ K ∨ a⁻¹ * b ∈ K := by
  have hidx : (K.subgroupOf L).index = 2 := h2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥L)⁻¹) (b := ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
  by_cases hbK : b ∈ K
  · exact Or.inl hbK
  · refine Or.inr ?_
    have := key.mpr (by
      constructor
      · intro hh; exact absurd (by simpa using hh) haK
      · intro hh; exact absurd hh hbK)
    simpa using this

omit [Finite G] in
theorem mul_self_mem_of_relIndex_two {K L : Subgroup G} (h2 : K.relIndex L = 2) {a : G}
    (ha : a ∈ L) : a * a ∈ K := by
  have hidx : (K.subgroupOf L).index = 2 := h2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥L)) (b := ⟨a, ha⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
  have := key.mpr Iff.rfl
  simpa using this

namespace SitSigma

variable {δ μ : Geo H M} {X : Subgroup G}

theorem shape_three_of_not_le (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) : Nonempty (OTwoQuot X ≃* Perm (Fin 3)) := by
  obtain ⟨hv, hQP2, hQA2, -⟩ := h.counts hA hPn hQ0
  have hPQ : ¬ Qv μ ⊓ X ≤ pCoreOf 2 X := h.not_le_pCore hA hPn
  obtain ⟨n, ψ, hn, -, hker⟩ := exists_quotHom hA δ
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv'⟩
  swap
  · rw [hv] at hv'; exact absurd hv' (by decide)
  set Q := pCoreOf 2 X with hQ
  set P := Qv μ ⊓ X with hP
  have hQP : Q ≤ P := h.R_le_P
  have hQX : Q ≤ X := (hQP.trans inf_le_right)
  set φ : ↥X →* Perm (Fin 5) := ψ.comp (Subgroup.inclusion h.le_stab) with hφ
  have hφ1 : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ Qv δ := fun x => hker _
  obtain ⟨q₀, hq₀Q, hq₀A⟩ : ∃ q ∈ Q, q ∉ Qv δ := by
    by_contra hcon
    exact hQ0 fun g hg => by_contra fun hn => hcon ⟨g, hg, hn⟩
  set t : Perm (Fin 5) := φ ⟨q₀, hQX hq₀Q⟩ with ht
  have ht1 : t ≠ 1 := fun h1 => hq₀A ((hφ1 _).mp h1)
  have hKA : P ⊓ Qv δ ≤ Qv δ := inf_le_right
  have hq₀K : q₀ ∉ P ⊓ Qv δ := fun hh => hq₀A hh.2
  have ht2 : t * t = 1 := by
    have hmem := mul_self_mem_of_relIndex_two hQA2 hq₀Q
    have : φ (⟨q₀, hQX hq₀Q⟩ * ⟨q₀, hQX hq₀Q⟩) = 1 := (hφ1 _).mpr hmem.2
    rwa [map_mul] at this
  have hI : ∀ q (hq : q ∈ Q), φ ⟨q, hQX hq⟩ = 1 ∨ φ ⟨q, hQX hq⟩ = t := by
    intro q hq
    rcases mem_or_of_relIndex_two hQA2 hq₀Q hq hq₀K with hqK | hqK
    · exact Or.inl ((hφ1 _).mpr hqK.2)
    · refine Or.inr ?_
      have h1 : φ (⟨q₀, hQX hq₀Q⟩⁻¹ * ⟨q, hQX hq⟩) = 1 := (hφ1 _).mpr hqK.2
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.mp h1).symm
  have hIII : ∀ x : ↥X, φ x * t = t * φ x := by
    intro x
    have hq : (x : G) * q₀ * (x : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X x.2) q₀).mp
        hq₀Q
    have hconj : φ ⟨(x : G) * q₀ * (x : G)⁻¹, hQX hq⟩ = φ x * t * (φ x)⁻¹ := by
      have : (⟨(x : G) * q₀ * (x : G)⁻¹, hQX hq⟩ : ↥X) = x * ⟨q₀, hQX hq₀Q⟩ * x⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    rcases hI _ hq with h1 | h1
    · rw [hconj] at h1
      exact absurd (by simpa using h1) ht1
    · rw [hconj] at h1
      calc φ x * t = (φ x * t * (φ x)⁻¹) * φ x := by group
        _ = t * φ x := by rw [h1]
  have hm_odd : ¬ 2 ∣ P.relIndex X := h.sylow.2.2
  have hm_ne : P.relIndex X ≠ 1 := fun hh => by
    have hXP : X ≤ P := Subgroup.relIndex_eq_one.mp hh
    have hX2 : IsPGroup 2 ↥X := h.sylow.2.1.to_le hXP
    have hXQ : X ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
      Subgroup.le_normalizer hX2
    exact hPQ (inf_le_right.trans hXQ)
  have hm15 : P.relIndex X ∣ 15 := by
    have hE2 : IsPGroup 2 ↥(stab δ ⊓ stab μ) := h.isPGroup_edge hA
    have hPE : P ≤ stab δ ⊓ stab μ := h.P_le_edge hA
    obtain ⟨j, hj⟩ := hE2.index ((P.subgroupOf (stab δ ⊓ stab μ)))
    have hcX : P.relIndex X * Nat.card P = Nat.card X := by
      have := Subgroup.relIndex_mul_card (H := P) (K := X)
      rwa [inf_of_le_left h.sylow.1] at this
    have hcE : P.relIndex (stab δ ⊓ stab μ) * Nat.card P = Nat.card (stab δ ⊓ stab μ : Subgroup G) := by
      have := Subgroup.relIndex_mul_card (H := P) (K := stab δ ⊓ stab μ)
      rwa [inf_of_le_left hPE] at this
    have hcG : (stab δ ⊓ stab μ).relIndex (stab δ) * Nat.card (stab δ ⊓ stab μ : Subgroup G) =
        Nat.card (stab δ) := by
      have := Subgroup.relIndex_mul_card (H := stab δ ⊓ stab μ) (K := stab δ)
      rwa [inf_of_le_left (inf_le_left : stab δ ⊓ stab μ ≤ stab δ)] at this
    have h15 : (stab δ ⊓ stab μ).relIndex (stab δ) = 15 := by
      have h1 := card_nbrs_eq_relIndex_geom (show μ ∈ nbrs δ from h.adj)
      rw [card_nbrs_false hA hv] at h1
      exact h1.symm
    have hdvd : Nat.card X ∣ Nat.card (stab δ) := Subgroup.card_dvd_of_le h.le_stab
    rw [← hcX, ← hcG, h15, ← hcE] at hdvd
    have hj' : P.relIndex (stab δ ⊓ stab μ) = 2 ^ j := hj
    rw [hj'] at hdvd
    have hdvd2 : P.relIndex X ∣ 15 * 2 ^ j := by
      have : P.relIndex X * Nat.card P ∣ (15 * 2 ^ j) * Nat.card P := by
        have e : 15 * (2 ^ j * Nat.card P) = (15 * 2 ^ j) * Nat.card P := by ring
        rwa [e] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos this
    have hcop : Nat.Coprime (P.relIndex X) (2 ^ j) := by
      refine Nat.Coprime.pow_right _ ?_
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm_odd)
    exact hcop.dvd_of_dvd_mul_right hdvd2
  have hm5 : ¬ 5 ∣ P.relIndex X := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h5X : 5 ∣ Nat.card ↥X := h5.trans (Subgroup.index_dvd_card (P.subgroupOf X))
    obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5X
    have hφx : φ x ≠ 1 := by
      intro h1
      have hxA : (x : G) ∈ Qv δ := (hφ1 x).mp h1
      have hxQ : (x : G) ∈ Q := h.inf_Qv_le_R ⟨x.2, hxA⟩
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) ⟨x, hxQ⟩
      have h1' : (x : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      have := orderOf_dvd_of_pow_eq_one h1'
      rw [hx5] at this
      have h5' := Nat.Prime.dvd_of_dvd_pow Nat.prime_five this
      omega
    have hx5' : x ^ 5 = 1 := hx5 ▸ pow_orderOf_eq_one x
    have hφ5 : φ x ^ 5 = 1 := by rw [← map_pow, hx5', map_one]
    exact perm5_no_commute _ hφ5 hφx t ht2 ht1 (hIII x).symm
  have hm3 : P.relIndex X = 3 := by
    have hmem : P.relIndex X ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hm15, by norm_num⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h3 | h5 | h15
    · exact absurd h1 hm_ne
    · exact h3
    · exact absurd (by rw [h5]) hm5
    · exact absurd (by rw [h15]; norm_num) hm5
  exact oTwoQuot_perm3_of_relIndex h.sylow hPQ hm3

end SitSigma

end CFSG.Quasithin.F53
