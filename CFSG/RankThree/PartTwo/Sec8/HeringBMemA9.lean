module

public import CFSG.RankThree.PartTwo.Sec8.HeringBMemFree
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

theorem a9_perm_apply_comm {M : Type*} [Group M] (ρ : M →* Equiv.Perm (Fin 9)) {x y : M}
    (h : x * y = y * x) (ω : Fin 9) : ρ x (ρ y ω) = ρ y (ρ x ω) := by
  have h2 : ρ x * ρ y = ρ y * ρ x := by rw [← map_mul, ← map_mul, h]
  have h3 := congrArg (fun g : Equiv.Perm (Fin 9) => g ω) h2
  simpa only [Equiv.Perm.mul_apply] using h3

theorem a9_support_invariant {M : Type*} [Group M] (ρ : M →* Equiv.Perm (Fin 9)) {Q : Subgroup M}
    {x : M} (hx : ∀ q ∈ Q, ∀ ω : Fin 9, ρ x (ρ q ω) = ρ q (ρ x ω)) :
    ∀ q ∈ Q, ∀ ω ∈ (ρ x).support, ρ q ω ∈ (ρ x).support := by
  intro q hq ω hω
  apply Equiv.Perm.mem_support.mpr
  intro h
  apply Equiv.Perm.mem_support.mp hω
  apply (ρ q).injective
  rw [← hx q hq ω]
  exact h

theorem a9_false {M : Type} [Group M] [Finite M] (e : M ≃* alternatingGroup (Fin 9))
    {Q : Subgroup M} {v z : M} (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1)
    (hQv : Q ≤ Subgroup.centralizer ({v} : Set M)) (hQ8 : Nat.card Q = 8)
    (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hz : ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z) : False := by
  obtain ⟨ρ, hρinj⟩ : ∃ ρ : M →* Equiv.Perm (Fin 9), Function.Injective ρ := by
    refine ⟨(alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom, ?_⟩
    intro a b hab
    apply e.injective
    apply Subtype.ext
    exact hab
  have hcomm : ∀ x ∈ Q, x * z = z * x := (quat_z_central hQ8 hzQ hz1 hz).2
  have hvq : ∀ q ∈ Q, v * q = q * v := fun q hq =>
    Subgroup.mem_centralizer_iff.mp (hQv hq) v (Set.mem_singleton v)
  have hvz : v * z = z * v := hvq z hzQ
  have hzinv : ∀ q ∈ Q, ∀ ω ∈ (ρ z).support, ρ q ω ∈ (ρ z).support :=
    a9_support_invariant ρ (fun q hq ω => a9_perm_apply_comm ρ (hcomm q hq).symm ω)
  have hzS : (ρ z).support.card = 8 := by
    have hdvd := eight_dvd_card_of_free ρ hQ8 hz (ρ z).support hzinv
      (fun ω hω => Equiv.Perm.mem_support.mp hω)
    have hle := Finset.card_le_univ (ρ z).support
    rw [Fintype.card_fin] at hle
    have hne : (ρ z).support.card ≠ 0 := by
      intro h0
      have h1 : ρ z = 1 := Equiv.Perm.card_support_eq_zero.mp h0
      have hρ1 : ρ z = ρ 1 := by rw [h1, map_one]
      exact hz1 (hρinj hρ1)
    omega
  have hcompl : (ρ z).supportᶜ.card = 1 := by
    have h := Finset.card_add_card_compl (ρ z).support
    rw [Fintype.card_fin, hzS] at h
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcompl
  have huniq : ∀ ω, ρ z ω = ω → ω = a := by
    intro ω hω
    have hmem : ω ∈ (ρ z).supportᶜ :=
      Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr hω)
    rw [ha, Finset.mem_singleton] at hmem
    exact hmem
  have hza : ρ z a = a := by
    have hmem : a ∈ (ρ z).supportᶜ := by
      rw [ha]
      exact Finset.mem_singleton_self a
    exact Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hmem)
  have hva : ρ v a = a := by
    have h1 : ρ z (ρ v a) = ρ v a := by
      rw [a9_perm_apply_comm ρ hvz.symm a, hza]
    exact huniq _ h1
  have hvinv : ∀ q ∈ Q, ∀ ω ∈ (ρ v).support, ρ q ω ∈ (ρ v).support :=
    a9_support_invariant ρ (fun q hq ω => a9_perm_apply_comm ρ (hvq q hq) ω)
  have hpow : ρ v ^ 3 ^ 1 = 1 := by
    show ρ v ^ 3 = 1
    rw [← map_pow, hv3, map_one]
  have hmod : (ρ v).supportᶜ.card ≡ 9 [MOD 3] := by
    have h := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hpow
    rwa [Fintype.card_fin] at h
  have hmod' : (ρ v).supportᶜ.card % 3 = 9 % 3 := hmod
  have hsum := Finset.card_add_card_compl (ρ v).support
  rw [Fintype.card_fin] at hsum
  have hlt : (ρ v).support.card < Fintype.card (Fin 9) :=
    Finset.card_lt_univ_of_notMem (Equiv.Perm.notMem_support.mpr hva)
  rw [Fintype.card_fin] at hlt
  have hvS : (ρ v).support.card < 8 := by omega
  have hfixz := fixed_of_card_lt_eight ρ hQ8 hzQ hz hz1 (ρ v).support hvinv hvS
  have hvid : ∀ ω, ρ v ω = ω := by
    intro ω
    by_contra hne
    have hωa : ω = a := huniq ω (hfixz ω (Equiv.Perm.mem_support.mpr hne))
    apply hne
    rw [hωa]
    exact hva
  have hvone : ρ v = ρ 1 := by
    rw [map_one]
    exact Equiv.ext hvid
  exact hv1 (hρinj hvone)

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
