module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeNbr
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

section PComp

variable [Finite G]

theorem eq_of_pComponents_of_perfect_common {p : ℕ} [Fact p.Prime] {X A A' P : Subgroup G}
    (hA : LargeEvenPComponent p X A) (hA' : LargeEvenPComponent p X A') (hPA : P ≤ A)
    (hPA' : P ≤ A') (hperf : P ≤ ⁅P, P⁆) {g : G} (hg : g ∈ P) (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    A = A' := by
  by_contra hne
  have hcomm : (⁅A, A'⁆ : Subgroup G) ≤ CFSG.Open.lBalancePrimeCore p X :=
    commutator_le_lBalancePrimeCore_of_ne hA hA' hne
  have hP : P ≤ CFSG.Open.lBalancePrimeCore p X :=
    hperf.trans ((Subgroup.commutator_mono hPA hPA').trans hcomm)
  have hgmem : g ∈ CFSG.Open.lBalancePrimeCore p X := hP hg
  have hdvd : p ∣ Nat.card (CFSG.Open.lBalancePrimeCore p X) := by
    have h := orderOf_dvd_natCard (⟨g, hgmem⟩ : CFSG.Open.lBalancePrimeCore p X)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hgp hg1] at h
  have hcop : Nat.Coprime p (Nat.card (CFSG.Open.lBalancePrimeCore p X)) :=
    CFSG.ComponentClassification.LBalance.primeCore_coprime p X
  exact (Fact.out : Nat.Prime p).not_dvd_one
    (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hdvd)

theorem largeEvenPComponent_conj_centralizer_singleton {p : ℕ} {y : G} {K : Subgroup G}
    (h : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K) (a : G) :
    LargeEvenPComponent p (Subgroup.centralizer ({a * y * a⁻¹} : Set G))
      (K.map (MulAut.conj a).toMonoidHom) := by
  have h' := largeEvenPComponent_map_conj' h a
  rwa [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton] at h'

theorem eq_map_conj_of_pComponents {p : ℕ} [Fact p.Prime] {x y : G} {K L : Subgroup G} (a b : G)
    (hK : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K)
    (hL : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hzw : Subgroup.zpowers (a * y * a⁻¹) = Subgroup.zpowers (b * x * b⁻¹)) {P : Subgroup G}
    (hPa : P ≤ K.map (MulAut.conj a).toMonoidHom) (hPb : P ≤ L.map (MulAut.conj b).toMonoidHom)
    (hperf : P ≤ ⁅P, P⁆) {g : G} (hg : g ∈ P) (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    K.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom := by
  have hA : LargeEvenPComponent p (Subgroup.centralizer ({a * y * a⁻¹} : Set G))
      (K.map (MulAut.conj a).toMonoidHom) :=
    largeEvenPComponent_conj_centralizer_singleton hK a
  have hA' : LargeEvenPComponent p (Subgroup.centralizer ({b * x * b⁻¹} : Set G))
      (L.map (MulAut.conj b).toMonoidHom) :=
    largeEvenPComponent_conj_centralizer_singleton hL b
  rw [centralizer_singleton_eq_of_zpowers_eq hzw.symm] at hA'
  exact eq_of_pComponents_of_perfect_common hA hA' hPa hPb hperf hg hg1 hgp

end PComp

end CFSG.StandardType
