module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P58

theorem not_lineSingLe {F : FanTree Γ G} (h40 : Fan40 F) (ℓ : Line Γ) {N : ℕ} (hN : N ≤ 3) :
    ¬ LineSingLe Γ G ℓ N := by
  rintro ⟨k, i, hk1, hk, h | h⟩
  · exact lineNSR_of_fan40 h40 ℓ hk1 (by omega) i h
  · exact lineNSL_of_fan40 h40 ℓ hk1 (by omega) i h

theorem eq_of_three {v : V} (hv3 : valence Γ v = 3) {p q r : V} (hp : Γ.Adj v p)
    (hq : Γ.Adj v q) (hr : Γ.Adj v r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {n : V}
    (hn : Γ.Adj v n) : n = p ∨ n = q ∨ n = r := by
  have hs : (Γ.neighborSet v).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hv3
  have hfin : (Γ.neighborSet v).Finite := Set.finite_of_ncard_pos (by omega)
  have hsub : ({p, q, r} : Set V) ⊆ Γ.neighborSet v := by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({p, q, r} : Set V).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  have : n ∈ ({p, q, r} : Set V) := by
    rw [heq]
    exact hn
  simpa using this

section Fan

variable (F : FanTree Γ G)
include F

theorem conj_mem_nbrStab {v : V} {g h : G} (hg : g • v = v) (hh : h ∈ nbrStab Γ G v) :
    g * h * g⁻¹ ∈ nbrStab Γ G v := by
  have := (F.mem_nbrStab_smul_iff g v (h := g * h * g⁻¹)).2 (by
    rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group]
    exact hh)
  rwa [hg] at this

theorem exists_swap (h40 : Fan40 F) {v p q ω : V} (hv3 : valence Γ v = 3) (hp : Γ.Adj v p)
    (hq : Γ.Adj v q) (hω : Γ.Adj v ω) (hpq : p ≠ q) (hpω : p ≠ ω) (hqω : q ≠ ω) :
    ∃ y ∈ nbrStab Γ G ω, y • v = v ∧ y • p = q ∧ y • q = p := by
  obtain ⟨y, hyω, hyK⟩ := IsConcreteLE.not_le_iff_exists.1 (F.not_nbrStab_le_nbrStab h40 hω.symm)
  have hyv : y • v = v := mem_nbrStab.1 hyω v hω.symm
  have hyω' : y • ω = ω := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer ω hyω)
  have hadj : ∀ n, Γ.Adj v n → Γ.Adj v (y • n) := fun n hn => by
    have := (F.adj_smul y v n).2 hn
    rwa [hyv] at this
  have hne : ∀ n, Γ.Adj v n → n ≠ ω → y • n ≠ n := fun n hn hnω hfix =>
    hyK (F.fix_two_nbrs hn hω hnω hfix hyω')
  have hneω : ∀ n, n ≠ ω → y • n ≠ ω := fun n hn h =>
    hn (MulAction.injective y (h.trans hyω'.symm))
  refine ⟨y, hyω, hyv, ?_, ?_⟩
  · rcases eq_of_three hv3 hp hq hω hpq hpω hqω (hadj p hp) with h | h | h
    · exact absurd h (hne p hp hpω)
    · exact h
    · exact absurd h (hneω p hpω)
  · rcases eq_of_three hv3 hp hq hω hpq hpω hqω (hadj q hq) with h | h | h
    · exact h
    · exact absurd h (hne q hq hqω)
    · exact absurd h (hneω q hqω)

theorem locTr_of_pow {M : Subgroup G} {v : V} {y : G} (hyM : y ∈ M)
    (hy : y ∈ MulAction.stabilizer G v) (hyo : orderOf y = valence Γ v) : LocTr Γ M v := by
  intro p q hp hq
  obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hy hyo hp hq
  exact ⟨y ^ i, M.pow_mem hyM i,
    MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G v).pow_mem hy i), hi⟩

theorem eq_one_of_locTr {M : Subgroup G} {z : G} {u w : V} (huw : Γ.Adj u w)
    (hz : ∀ h ∈ M, h * z = z * h) (hzu : z • u = u) (hzw : z • w = w) (hu : LocTr Γ M u)
    (hw : LocTr Γ M w) : z = 1 := by
  have hall := F.locTr_all huw hu hw
  have hne : valence Γ u ≠ valence Γ w := F.alternating _ _ huw
  have hval : ∀ x : V, valence Γ x = valence Γ u ∨ valence Γ x = valence Γ w := by
    intro x
    have h1 : valence Γ x = 3 ∨ valence Γ x = 5 := F.valence x
    have h2 : valence Γ u = 3 ∨ valence Γ u = 5 := F.valence u
    have h3 : valence Γ w = 3 ∨ valence Γ w = 5 := F.valence w
    omega
  refine F.faithful z fun x => ?_
  rcases hval x with h | h
  · obtain ⟨g, hg, rfl⟩ := F.exists_mem_smul_eq hall h
    rw [← mul_smul, show z * g = g * z from (hz g hg).symm, mul_smul, hzu]
  · obtain ⟨g, hg, rfl⟩ := F.exists_mem_smul_eq hall h
    rw [← mul_smul, show z * g = g * z from (hz g hg).symm, mul_smul, hzw]

end Fan

end P58

end CFSG.Quasithin.Fan86
