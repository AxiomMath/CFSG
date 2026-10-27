module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus3
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFix

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

section Main


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem closure_layer_two_X (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x₁ x₂ : C0 σ} (h1 : IsClassX σ x₁) (h2 : IsClassX σ x₂)
    (hc : x₁ * x₂ = x₂ * x₁) (hne : Subgroup.zpowers x₁ ≠ Subgroup.zpowers x₂)
    {H : Subgroup (C0 σ)}
    (hH1 : ⁅Subgroup.centralizer ({x₁} : Set (C0 σ)), Subgroup.centralizer ({x₁} : Set (C0 σ))⁆ ≤ H)
    (hH2 : ⁅Subgroup.centralizer ({x₂} : Set (C0 σ)), Subgroup.centralizer ({x₂} : Set (C0 σ))⁆ ≤ H) :
    H = ⊤ := by
  classical
  have hD : D4Par n X σ := ⟨by omega, hX, hσ⟩
  obtain ⟨ε, p, hε, hp, hp5, hpd, h3⟩ := exists_prime_dvd_cyclotomic_three n hn
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₁, hy₁o, hy₁c⟩ := fibre_exists σ n hn hX hσ hε hp hp5 hpd h3 h1
  obtain ⟨y₂, hy₂o, hy₂c⟩ := fibre_exists σ n hn hX hσ hε hp hp5 hpd h3 h2
  have hy₁p : y₁ ^ p = 1 := by rw [← hy₁o]; exact pow_orderOf_eq_one y₁
  have hy₂p : y₂ ^ p = 1 := by rw [← hy₂o]; exact pow_orderOf_eq_one y₂
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy₁o
    exact hp.one_lt.ne hy₁o
  have hy₂1 : y₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy₂o
    exact hp.one_lt.ne hy₂o
  have hc12 : y₁ * y₂ = y₂ * y₁ := by
    have hx1y2 : x₁ ∈ Subgroup.centralizer ({y₂} : Set (C0 σ)) := by
      rw [hy₂c, Subgroup.mem_centralizer_singleton_iff]
      exact hc
    have hx1y2' : x₁ * y₂ = y₂ * x₁ := Subgroup.mem_centralizer_singleton_iff.mp hx1y2
    have hy2x1 : y₂ ∈ Subgroup.centralizer ({x₁} : Set (C0 σ)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hx1y2'.symm
    rw [← hy₁c, Subgroup.mem_centralizer_singleton_iff] at hy2x1
    exact hy2x1.symm
  have hne' : Subgroup.zpowers y₁ ≠ Subgroup.zpowers y₂ := by
    intro h
    have hy2 : y₂ ∈ Subgroup.zpowers y₁ := by rw [h]; exact Subgroup.mem_zpowers y₂
    have hy1 : y₁ ∈ Subgroup.zpowers y₂ := by rw [← h]; exact Subgroup.mem_zpowers y₁
    have hC : Subgroup.centralizer ({x₁} : Set (C0 σ)) =
        Subgroup.centralizer ({x₂} : Set (C0 σ)) := by
      rw [← hy₁c, ← hy₂c]
      exact le_antisymm (centralizer_le_of_mem_zpowers hy2) (centralizer_le_of_mem_zpowers hy1)
    exact hne (classX_centralizer_inj σ hD hn h1 h2 hC)
  obtain ⟨hpow, hcard⟩ := plane_of_two_commuting_prime_elements hp hy₁p hy₁1 hy₂p hy₂1 hc12 hne'
  set E : Subgroup (C0 σ) := Subgroup.closure ({y₁, y₂} : Set (C0 σ)) with hE
  haveI : Finite (C0 σ) := finite_C0
  have hEpg : IsPGroup p E := IsPGroup.of_card (n := 2) hcard
  obtain ⟨S, hES⟩ := hEpg.exists_le_sylow
  obtain ⟨Y, Pf, hY, -, hPle, hYeven, hgen, hrot, hperf⟩ :=
    routeC_summary_perfect σ n hn hX hσ hε hp hp5 hpd S E hES hpow hcard
  have hy₁E : y₁ ∈ E := Subgroup.subset_closure (by simp)
  have hy₂E : y₂ ∈ E := Subgroup.subset_closure (by simp)
  have he1 : Even (Nat.card (Subgroup.centralizer ({y₁} : Set (C0 σ)))) := by
    rw [hy₁c]
    exact classX_even_centralizer σ hD h1
  have he2 : Even (Nat.card (Subgroup.centralizer ({y₂} : Set (C0 σ)))) := by
    rw [hy₂c]
    exact classX_even_centralizer σ hD h2
  obtain ⟨j₁, hj₁⟩ := hYeven y₁ hy₁E hy₁1 he1
  obtain ⟨j₂, hj₂⟩ := hYeven y₂ hy₂E hy₂1 he2
  have hYp : ∀ j, Y j ^ p = 1 := fun j => hpow _ (hY j).1
  have hj : j₁ ≠ j₂ := by
    intro h
    subst h
    apply hne'
    have e1 := zpowers_eq_of_mem_zpowers_prime hp hy₁p hy₁1 (hYp j₁) (hY j₁).2 hj₁
    have e2 := zpowers_eq_of_mem_zpowers_prime hp hy₂p hy₂1 (hYp j₁) (hY j₁).2 hj₂
    rw [e1, e2]
  have hC1 : Pf j₁ ≤ Subgroup.centralizer ({x₁} : Set (C0 σ)) :=
    (hPle j₁).trans ((centralizer_le_of_mem_zpowers hj₁).trans hy₁c.le)
  have hC2 : Pf j₂ ≤ Subgroup.centralizer ({x₂} : Set (C0 σ)) :=
    (hPle j₂).trans ((centralizer_le_of_mem_zpowers hj₂).trans hy₂c.le)
  have hP1 : Pf j₁ ≤ H := (hperf j₁).symm.le.trans ((Subgroup.commutator_mono hC1 hC1).trans hH1)
  have hP2 : Pf j₂ ≤ H := (hperf j₂).symm.le.trans ((Subgroup.commutator_mono hC2 hC2).trans hH2)
  exact eq_top_of_two_factors Pf hgen hrot hj hP1 hP2

theorem closure_cent_two_X (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x₁ x₂ : C0 σ} (h1 : IsClassX σ x₁) (h2 : IsClassX σ x₂)
    (hc : x₁ * x₂ = x₂ * x₁) (hne : Subgroup.zpowers x₁ ≠ Subgroup.zpowers x₂)
    {H : Subgroup (C0 σ)} (hH1 : Subgroup.centralizer ({x₁} : Set (C0 σ)) ≤ H)
    (hH2 : Subgroup.centralizer ({x₂} : Set (C0 σ)) ≤ H) : H = ⊤ :=
  closure_layer_two_X σ n hn hX hσ h1 h2 hc hne ((commutator_self_le _).trans hH1)
    ((commutator_self_le _).trans hH2)

theorem conj_ne_one_C0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x : C0 σ} (hx : x ≠ 1) :
    (MulAut.conj x : MulAut (C0 σ)) ≠ 1 := fun h =>
  hx (conj_injective_C0 σ n hn hX hσ (by rw [h, map_one]))

theorem planeGen_of_two_X_lines (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} {x₁ x₂ : C0 σ}
    (h1 : IsClassX σ x₁) (h2 : IsClassX σ x₂) (hc : x₁ * x₂ = x₂ * x₁)
    (hne : Subgroup.zpowers x₁ ≠ Subgroup.zpowers x₂) (he1 : (MulAut.conj x₁ : MulAut (C0 σ)) ∈ E)
    (he2 : (MulAut.conj x₂ : MulAut (C0 σ)) ∈ E) : PlaneGen E :=
  closure_cent_two_X σ n hn hX hσ h1 h2 hc hne
    (centralizer_le_planeClosure he1 (conj_ne_one_C0 σ n (by omega) hX hσ h1.2.1))
    (centralizer_le_planeClosure he2 (conj_ne_one_C0 σ n (by omega) hX hσ h2.2.1))

theorem planeGen_of_pair (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} {x h : C0 σ}
    {β : MulAut (C0 σ)} (hx : IsClassX σ x) (hxE : (MulAut.conj x : MulAut (C0 σ)) ∈ E)
    (hβE : β ∈ E) (hβ1 : β ≠ 1) (hh : β h = h)
    (hcomm : (h * x * h⁻¹) * x = x * (h * x * h⁻¹))
    (hne : h * x * h⁻¹ ∉ Subgroup.zpowers x) : PlaneGen E := by
  have hl1 : Subgroup.centralizer ({x} : Set (C0 σ)) ≤ planeClosure E :=
    centralizer_le_planeClosure hxE (conj_ne_one_C0 σ n (by omega) hX hσ hx.2.1)
  have hhH : h ∈ planeClosure E := mem_planeClosure_of_fixed hβE hβ1 hh
  have hl2 : Subgroup.centralizer ({h * x * h⁻¹} : Set (C0 σ)) ≤ planeClosure E := by
    intro k hk
    have hk' := (mem_centralizer_conj_iff h x k).mp hk
    have : k = h * (h⁻¹ * k * h) * h⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhH (hl1 hk')) (Subgroup.inv_mem _ hhH)
  refine closure_cent_two_X σ n hn hX hσ hx (hx.conj_mem σ h) hcomm.symm ?_ hl1 hl2
  intro heq
  exact hne (heq ▸ Subgroup.mem_zpowers _)

end Main

end CFSG.RankThree.PartTwo.Sec19
