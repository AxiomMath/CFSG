module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.G92

open CFSG.Open

@[expose] def piPrimeCoreG92 {A : Type*} [Group A] (π : Set ℕ) (H : Subgroup A) : Subgroup A :=
  sSup {N | N ≤ H ∧ (N.subgroupOf H).Normal ∧ ∀ q ∈ π, q.Prime → Nat.Coprime q (Nat.card N)}

theorem piPrimeCoreG92_anti {A : Type*} [Group A] {π π' : Set ℕ} (h : π ⊆ π') (H : Subgroup A) :
    piPrimeCoreG92 π' H ≤ piPrimeCoreG92 π H := by
  refine sSup_le_sSup ?_
  rintro N ⟨hNH, hNn, hNc⟩
  exact ⟨hNH, hNn, fun q hq => hNc q (h hq)⟩

private theorem le_iSup_pCore_of_normal_nilpotent {Y : Type*} [Group Y] [Finite Y]
    {K : Subgroup Y} (hK : K.Normal) (hnil : Group.IsNilpotent ↥K) :
    K ≤ ⨆ p ∈ (Nat.card ↥K).primeFactors, pCore p Y := by
  have hsup : (⨆ p ∈ (Nat.card ↥K).primeFactors,
      ((default : Sylow p ↥K) : Subgroup ↥K)).map K.subtype = K := by
    rw [Sylow.iSup_sylow_eq_top (G := ↥K), ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine hsup.symm.le.trans ?_
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun p hp => ?_
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact le_iSup₂_of_le p hp (Sylow.map_le_pCore hK hnil p (default : Sylow p ↥K))

theorem commutator_piPrimeCoreG92_eq_bot {G : Type*} [Group G] [Finite G]
    (X A : Subgroup G) (hX : Group.IsNilpotent ↥X) (π : Set ℕ)
    (h : ∀ q : ℕ, q.Prime → q ∉ π → A ≤ Subgroup.centralizer (pCoreOf q X : Set G)) :
    ⁅piPrimeCoreG92 π X, A⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sSup_le fun N hN => ?_
  obtain ⟨hNX, hNn, hNc⟩ := hN
  haveI := hX
  have hKnil : Group.IsNilpotent ↥(N.subgroupOf X) := inferInstance
  have hKle := le_iSup_pCore_of_normal_nilpotent hNn hKnil
  have hcard : Nat.card ↥(N.subgroupOf X) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hCle : (⨆ p ∈ (Nat.card ↥(N.subgroupOf X)).primeFactors, pCore p ↥X) ≤
      (Subgroup.centralizer (A : Set G)).comap X.subtype := by
    refine iSup₂_le fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ Nat.card ↥N := by
      rw [← hcard]
      exact Nat.dvd_of_mem_primeFactors hp
    have hpπ : p ∉ π := fun hpπ => hpp.one_lt.ne' ((hNc p hpπ hpp).eq_one_of_dvd hpdvd)
    intro y hy
    have hy' : (y : G) ∈ pCoreOf p X := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact Subgroup.le_centralizer_iff.mp (h p hpp hpπ) hy'
  intro g hg
  exact hCle (hKle (show (⟨g, hNX hg⟩ : ↥X) ∈ N.subgroupOf X from hg))

theorem dihedral_eq_closure {G : Type*} [Group G] {K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (e : ↥K ≃* DihedralGroup p) {x a : G} (hxK : x ∈ K) (haK : a ∈ K)
    (hxo : orderOf x = p) (ha2 : a * a = 1) (hax : a * x * a⁻¹ = x⁻¹) :
    K = Subgroup.closure {x, a} := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥K := Finite.of_equiv _ e.symm.toEquiv
  have hKcard : Nat.card ↥K = 2 * p := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hSK : Subgroup.closure ({x, a} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [hxK, haK]
  haveI : Finite ↥(Subgroup.closure ({x, a} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hSK)
  have hxS : x ∈ Subgroup.closure ({x, a} : Set G) := Subgroup.subset_closure (by simp)
  have haS : a ∈ Subgroup.closure ({x, a} : Set G) := Subgroup.subset_closure (by simp)
  have hpdvd : p ∣ Nat.card ↥(Subgroup.closure ({x, a} : Set G)) := by
    have := Subgroup.orderOf_dvd_natCard _ hxS
    rwa [hxo] at this
  have ha1 : a ≠ 1 := by
    rintro rfl
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      simp only [inv_one, mul_one, one_mul] at hax
      exact mul_eq_one_iff_eq_inv.mpr hax
    have hpd : p ∣ 2 := by
      have := orderOf_dvd_of_pow_eq_one hx2
      rwa [hxo] at this
    obtain ⟨k, hk⟩ := hodd
    have h1 := Nat.le_of_dvd two_pos hpd
    have h2 := hp.two_le
    omega
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.closure ({x, a} : Set G)) := by
    have := Subgroup.orderOf_dvd_natCard _ haS
    rwa [ha_ord] at this
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two hp]
    intro h2p
    obtain ⟨k, hk⟩ := hodd
    omega
  have h2p : 2 * p ∣ Nat.card ↥(Subgroup.closure ({x, a} : Set G)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2dvd hpdvd
  have hge : Nat.card ↥K ≤ Nat.card ↥(Subgroup.closure ({x, a} : Set G)) := by
    rw [hKcard]
    exact Nat.le_of_dvd Nat.card_pos h2p
  exact (Subgroup.eq_of_le_of_card_ge hSK hge).symm

end CFSG.Quasithin.G92
