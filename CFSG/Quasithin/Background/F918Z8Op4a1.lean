module

public import CFSG.Quasithin.Background.F918Z8Op0
import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic

public section

namespace CFSG.Quasithin

open CFSG.ShultStronglyClosedTI.OddPrimeInverters

section Generic

variable {G : Type*} [Group G]

theorem opq4a_not_commute_of_pElement
    (hcent : ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} (hx : IsPGroup p (Subgroup.zpowers x))
    (hx1 : x ≠ 1) {s : G} (hs : orderOf s = 2) : s * x ≠ x * s := by
  intro hsx
  have hmem : x ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hsx.symm
  obtain ⟨n, hn⟩ := hcent s hs ⟨x, hmem⟩
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have h1 : orderOf x ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have h2 : orderOf x ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have hc : Nat.Coprime (2 ^ n) (p ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  exact hx1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc h1 h2))

theorem opq4a_inv_ne_self {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
    (hx : IsPGroup p (Subgroup.zpowers x)) (hx1 : x ≠ 1) : x⁻¹ ≠ x := by
  intro h
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]
    calc x * x = x * x⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel x)
  have h2 : orderOf x ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have hc : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  exact hx1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc h1 h2))

theorem opq4a_exists_involution_inverts_sylow [Finite G] {q N : ℕ} (hperf : commutator G = ⊤)
    (hcyc : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G, IsCyclic P)
    (hcent : ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G)))
    (hcard : Nat.card G = (q - 1) * N) (hcop : Nat.Coprime (q - 1) N)
    (T₀ : Subgroup G) (hT₀ : Nat.card T₀ = q - 1) (w : G) (hw : ∀ t ∈ T₀, w * t * w⁻¹ = t⁻¹)
    (hfrob : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ q - 1 → ∀ y g : G,
      IsPGroup p (Subgroup.zpowers y) → g * y * g⁻¹ ∈ Subgroup.zpowers y → g * y * g⁻¹ ≠ y →
      g * y * g⁻¹ = y⁻¹ ∨ g ^ 2 * y * (g ^ 2)⁻¹ = y⁻¹)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S : Sylow p G) (hS1 : (S : Subgroup G) ≠ ⊥) :
    ∃ s : G, s * s = 1 ∧ ∀ x ∈ (S : Subgroup G), s * x * s⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hindex : T₀.index = N := by
    have h1 := T₀.card_mul_index
    rw [hT₀, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hcard; exact Nat.card_pos.ne' hcard) h1
  obtain ⟨⟨y, hyS⟩, hy⟩ := (hcyc p hp2 S).exists_generator
  have hSy : (S : Subgroup G) = Subgroup.zpowers y := by
    refine le_antisymm (fun z hz => ?_) ((Subgroup.zpowers_le).mpr hyS)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hyp : IsPGroup p (Subgroup.zpowers y) := hSy ▸ S.isPGroup'
  have hy1 : y ≠ 1 := by
    intro h
    apply hS1
    rw [hSy, h, Subgroup.zpowers_one_eq_bot]
  obtain ⟨h, hh⟩ : ∃ h : G, h * y * h⁻¹ = y⁻¹ := by
    by_cases hpq : p ∣ q - 1
    · refine exists_inverts_of_not_dvd_index T₀ ?_ hw hyp
      rw [hindex]
      intro hpN
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpq hpN)
    · exact exists_inverts_of_frobenius hperf (hcyc p hp2) (hfrob p hp hp2 hpq) hyp hy1
  obtain ⟨s, hs2, hsy⟩ := exists_involution_inverts_of_inverts hh (opq4a_inv_ne_self hp hp2 hyp hy1)
    (fun s hs => opq4a_not_commute_of_pElement hcent hp hp2 hyp hy1 hs)
  refine ⟨s, ?_, fun x hx => ?_⟩
  · rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hs2)
  · rw [hSy] at hx
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hsy, inv_zpow]

end Generic

theorem opq4a_invSylAll_of_mulEquiv {G : Type} [Group G] {L : Subgroup G} {F : Type} [Group F]
    [Finite F] (e : ↥L ≃* F) {p : ℕ} (hp : p.Prime) (hpL : p ∣ Nat.card L)
    (h : ∀ S : Sylow p F, (S : Subgroup F) ≠ ⊥ →
      ∃ s : F, s * s = 1 ∧ ∀ x ∈ (S : Subgroup F), s * x * s⁻¹ = x⁻¹) :
    InvSylAll L p := by
  intro P hPL hPp ⟨m, hm, hpm⟩
  have : Fact p.Prime := ⟨hp⟩
  have hFL : Nat.card F = Nat.card L := (Nat.card_congr e.toEquiv).symm
  set P0 : Subgroup ↥L := P.subgroupOf L with hP0
  set P' : Subgroup F := P0.map e.toMonoidHom with hP'
  have hcardP0 : Nat.card P0 = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hcardP' : Nat.card P' = Nat.card P :=
    (Subgroup.card_map_of_injective e.injective).trans hcardP0
  have hP0p : IsPGroup p P0 := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hP'p : IsPGroup p P' := hP0p.map _
  have hidx : P'.index = m := by
    have h1 := P'.card_mul_index
    rw [hFL, hm, ← hcardP'] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hpidx : ¬ p ∣ P'.index := by rw [hidx]; exact hpm
  have hpP : p ∣ Nat.card P := by
    rw [hm] at hpL
    exact (hp.dvd_mul.mp hpL).resolve_right hpm
  have hS1 : (hP'p.toSylow hpidx : Subgroup F) ≠ ⊥ := by
    rw [IsPGroup.toSylow_coe]
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardP'
    rw [← hcardP'] at hpP
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpP)
  obtain ⟨s, hs2, hs⟩ := h _ hS1
  refine ⟨((e.symm s : ↥L) : G), (e.symm s).2, ?_, fun x hx => ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, hs2, map_one, Subgroup.coe_one]
  · have hxL : x ∈ L := hPL hx
    have hmem : e ⟨x, hxL⟩ ∈ (hP'p.toSylow hpidx : Subgroup F) := by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have h1 := congrArg e.symm (hs _ hmem)
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    exact congrArg Subtype.val h1

end CFSG.Quasithin
