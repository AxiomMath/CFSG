module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.E1Defs
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem perm_seven_orderOf_ne_three {a b : Equiv.Perm (Fin 7)} (hb : orderOf b = 5)
    (hab : a * b = b * a) : orderOf a ≠ 3 := by
  intro ha
  have hmem5 : ∀ n ∈ b.cycleType, n = 5 := by
    intro n hn
    have h1 := Equiv.Perm.dvd_of_mem_cycleType hn
    rw [hb] at h1
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
    · omega
    · exact h
  have hrep : b.cycleType = Multiset.replicate (Multiset.card b.cycleType) 5 :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem5⟩
  have hsum := Equiv.Perm.sum_cycleType_le b
  have hne : Multiset.card b.cycleType ≠ 0 := by
    intro h0
    have hb1 : b = 1 := Equiv.Perm.card_cycleType_eq_zero.mp h0
    rw [hb1, orderOf_one] at hb
    omega
  have hcard : Multiset.card b.cycleType = 1 := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
    omega
  have hct : b.cycleType = {5} := by
    rw [hrep, hcard]
    rfl
  have hcen : Nat.card (Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin 7)))) = 10 := by
    rw [Equiv.Perm.nat_card_centralizer, hct]
    simp [Multiset.toFinset_singleton]
  have hmem : a ∈ Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin 7))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hab.symm
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hcen, ha] at hdvd
  omega

variable {G : Type} [Group G]

theorem orderOf_mk_eq {J : Subgroup G} {x : G} (hx : x ∈ J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hxo : orderOf x = p) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥J) (⟨x, hx⟩ : ↥J)) = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo' : orderOf (⟨x, hx⟩ : ↥J) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥J) (⟨x, hx⟩ : ↥J)) ∣ p :=
    hxo' ▸ orderOf_map_dvd _ _
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exfalso
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨_, h⟩
    have h1 : orderOf (⟨x, hx⟩ : ↥J) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    rw [hxo'] at h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
    exact hp2 this
  · exact h

theorem false_of_commute_of_alternatingSeven {J : Subgroup G}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 7)) {x z : G} (hx : x ∈ J) (hz : z ∈ J)
    (hxo : orderOf x = 5) (hzo : orderOf z = 3) (hxz : x * z = z * x) : False := by
  set π : ↥J →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) with hπ
  have hord : ∀ {y : G} (hy : y ∈ J) {p : ℕ}, p.Prime → p ≠ 2 → orderOf y = p →
      orderOf ((π ⟨y, hy⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = p := by
    intro y hy p hp hp2 hyo
    rw [Subgroup.orderOf_coe, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.orderOf_eq]
    exact orderOf_mk_eq hy hp hp2 hyo
  have hc : ((π ⟨z, hz⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
      (π ⟨x, hx⟩ : alternatingGroup (Fin 7)) =
      (π ⟨x, hx⟩ : alternatingGroup (Fin 7)) * (π ⟨z, hz⟩ : alternatingGroup (Fin 7)) := by
    have hc' : (⟨z, hz⟩ : ↥J) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨z, hz⟩ := Subtype.ext hxz.symm
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc']
  exact perm_seven_orderOf_ne_three (hord hx Nat.prime_five (by norm_num) hxo) hc
    (hord hz Nat.prime_three (by norm_num) hzo)

theorem false_of_oPrimeResidual_eq {X J L : Subgroup G}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 7)) (hJX : J = oPrimeResidualOf 3 X)
    (hLJ : L ≤ J) {x z : G} (hxL : x ∈ L) (hxo : orderOf x = 5) (hzX : z ∈ X)
    (hzo : orderOf z = 3) (hzL : z ∈ Subgroup.centralizer (L : Set G)) : False := by
  have hzJ : z ∈ J := by
    rw [hJX]
    exact Subgroup.subset_closure ⟨hzX, 1, by rw [hzo, pow_one]⟩
  exact false_of_commute_of_alternatingSeven e (hLJ hxL) hzJ hxo hzo
    (Subgroup.mem_centralizer_iff.mp hzL x hxL)

end CFSG.Quasithin.Vol2.Ch10.SecF
