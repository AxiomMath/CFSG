module

public import CFSG.Quasithin.EmptyFaithful.S1421QA16Defs
public import CFSG.Quasithin.EmptyFaithful.S1421QA16Cnt
public import CFSG.Quasithin.EmptyFaithful.S1421QA16Perf
public import CFSG.Quasithin.EmptyFaithful.S1421Q9D

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Q16

theorem exists_mul_ne_of_isQ8D8 {P : Type*} [Group P] (h : IsQ8D8 P) :
    ∃ a b : P, a * b ≠ b * a := by
  obtain ⟨-, A, B, -, ⟨eA⟩, -⟩ := h
  have hq : ∃ u v : QuaternionGroup 2, u * v ≠ v * u := by decide
  obtain ⟨u, v, huv⟩ := hq
  refine ⟨((eA.symm u : A) : P), ((eA.symm v : A) : P), fun hc => huv ?_⟩
  have h1 : eA.symm u * eA.symm v = eA.symm v * eA.symm u := Subtype.ext hc
  have h2 := congrArg eA h1
  simpa using h2

theorem commutator_eq_top_of_commutator_eq {G : Type*} [Group G] {K : Subgroup G}
    (h : ⁅K, K⁆ = K) : commutator ↥K = ⊤ := by
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, htop, h]

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem q16Irred_of_dvd_five (st : Setting1427 T M H K1) (h5 : 5 ∣ Nat.card (OTwoQuot K1))
    (hs : IsSimpleGroup (OTwoQuot K1)) (hQ : IsQ8D8 ↥(pCoreOf 2 K1)) : Q16Irred G T K1 := by
  intro W hZW hWQ hinv
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hWZ, hWQ'⟩ := hne
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5K : 5 ∣ Nat.card ↥K1 := h5.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K1) 5 h5K
  have hx5 : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
  have hxG : (x : G) ^ 5 = 1 := by simpa using congrArg Subtype.val hx5
  have hN2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥K1) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hxN : x ∉ CFSG.Open.pCore 2 ↥K1 := by
    intro hxm
    obtain ⟨k, hk⟩ := hN2 ⟨x, hxm⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : 5 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h2
    omega
  have hxW : (x : G) ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hinv _ x.2 w hw, fun hw => ?_⟩
    have := hinv _ (K1.inv_mem x.2) _ hw
    simpa [mul_assoc] using this
  have hxQ : (x : G) ∈ Subgroup.normalizer (pCoreOf 2 K1 : Set G) :=
    le_normalizer_pCoreOf 2 K1 x.2
  have hZx : quasithinOmegaOneCenter T ≤ Subgroup.centralizer {(x : G)} := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    exact (Subgroup.mem_centralizer_iff.mp (Q9.k1_le_mcOf st x.2) z hz).symm
  have hcen : pCoreOf 2 K1 ≤ Subgroup.centralizer {(x : G)} :=
    le_centralizer_of_ne_ne hQ.1 st.hyp.card_omegaOneCenter hZW hWQ hWZ hWQ' hxW hxQ hxG hZx
  have hperf : commutator ↥K1 = ⊤ :=
    commutator_eq_top_of_commutator_eq (perfect_of_mem_cComp st.notation_.cComp_mem)
  have hnormal : (CFSG.Open.pCore 2 ↥K1).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hxc : x ∈ Subgroup.centralizer ((CFSG.Open.pCore 2 ↥K1 : Subgroup ↥K1) : Set ↥K1) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnQ : (n : G) ∈ pCoreOf 2 K1 := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hcen hnQ) (x : G) (Set.mem_singleton _)
    exact Subtype.ext this.symm
  have htop := centralizer_eq_top_of_perfect (CFSG.Open.pCore 2 ↥K1) hN2 hs hperf hxN hxc
  have hcomm : ∀ a ∈ pCoreOf 2 K1, ∀ b ∈ pCoreOf 2 K1, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have hb'c : b' ∈ Subgroup.centralizer ((CFSG.Open.pCore 2 ↥K1 : Subgroup ↥K1) : Set ↥K1) := by
      rw [htop]
      trivial
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hb'c a' ha')
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isQ8D8 hQ
  exact hab (Subtype.ext (hcomm a a.2 b b.2))

end Q16

end CFSG.Quasithin
