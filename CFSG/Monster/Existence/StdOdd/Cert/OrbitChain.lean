module

public import CFSG.Monster.Existence.StdOdd.Cert.Chain

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Subgroup

variable {G X : Type*} [Group G] [MulAction G X]

open Classical in
@[expose] noncomputable def choiceT (β : ℕ → X) (i : ℕ) (y : X) : G :=
  if h : ∃ k ∈ baseStab (G := G) β i, k • β i = y then h.choose else 1

theorem IsStabChain.of_exists {β : ℕ → X} {n : ℕ} {B : ℕ → Finset X} {L : Finset G}
    (hB : ∀ i < n, ∀ y ∈ B i, ∃ k ∈ baseStab (G := G) β i, k • β i = y)
    (hL : ∀ k ∈ L, k ∈ baseStab β n)
    (hcard : (∏ i ∈ Finset.range n, (B i).card) * L.card = Nat.card G) :
    IsStabChain β n B (choiceT β) L := by
  refine ⟨⟨fun i hi y hy => ?_, fun i hi y hy => ?_⟩, hL, hcard⟩
  · have h := hB i hi y hy
    rw [choiceT, dite_eq_left h]
    exact h.choose_spec.1
  · have h := hB i hi y hy
    rw [choiceT, dite_eq_left h]
    exact h.choose_spec.2

theorem not_exists_of_fail [Finite G] {β : ℕ → X} {n : ℕ} {B : ℕ → Finset X} {T : ℕ → X → G}
    {L : Finset G} (hc : IsStabChain β n B T L) {m : ℕ} (h1 : 1 ≤ m) (hm : m < n)
    (t : ℕ → ℕ → X) (f : ℕ → G) (h0 : t 1 0 = β 0)
    (hf : ∀ j, 1 ≤ j → j < m → f j ∈ baseStab β j ∧ f j • β j = t j j)
    (ht : ∀ j, 1 ≤ j → j < m → ∀ i < n, t (j + 1) i = (f j)⁻¹ • t j i)
    (hfail : t m m ∉ B m) :
    ¬ ∃ k : G, ∀ i < n, k • β i = t 1 i := by
  rintro ⟨k, hk⟩
  have key : ∀ j, 1 ≤ j → j ≤ m → ∃ kj ∈ baseStab (G := G) β j, ∀ i < n, kj • β i = t j i := by
    intro j hj1 hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨k, ?_, hk⟩
        rw [mem_baseStab]
        intro i hi
        have : i = 0 := by omega
        subst this
        rw [hk 0 (by omega), h0]
      · obtain ⟨kj, hkj, hkt⟩ := ih hj (by omega)
        obtain ⟨hfj, hfs⟩ := hf j hj (by omega)
        refine ⟨(f j)⁻¹ * kj, ?_, fun i hi => ?_⟩
        · rw [baseStab_succ]
          refine Subgroup.mem_inf.2 ⟨(baseStab β j).mul_mem ((baseStab β j).inv_mem hfj) hkj, ?_⟩
          rw [MulAction.mem_stabilizer_iff, mul_smul, hkt j (by omega), ← hfs, inv_smul_smul]
        · rw [mul_smul, hkt i hi, ht j hj (by omega) i hi]
  obtain ⟨km, hkm, hkt⟩ := key m h1 le_rfl
  exact hfail (hc.exact m hm _ ⟨⟨km, hkm⟩, hkt m hm⟩)

theorem not_mem_orbit_of_fail {x : G} {b r : X} {e : ℕ → ℕ} {n : ℕ} (g : G) (hg : g • b = r)
    (hfail : ¬ ∃ k : G, ∀ i < n, k • orbitBase x b e i = g⁻¹ • (x ^ e i • r)) :
    ¬ ∃ c ∈ centralizer ({x} : Set G), c • b = r := by
  rintro ⟨c, hc, rfl⟩
  refine hfail ⟨g⁻¹ * c, fun i _ => ?_⟩
  rw [orbitBase_apply, mul_smul, smul_pow_smul_of_mem_centralizer hc (e i) b]

theorem card_centralizer_of_orbits [Finite G] [DecidableEq X] {x : G} {b : X} {e : ℕ → ℕ}
    {n : ℕ} {B : ℕ → Finset X} {T : ℕ → X → G} {L : Finset G}
    (hc : IsStabChain (orbitBase x b e) n B T L)
    (hcover : ∀ j < orderOf x, ∃ i < n, x ^ e i = x ^ j)
    (hcomm : ∀ κ ∈ L, κ * x = x * κ) (hcop : Nat.Coprime L.card (orderOf x)) (S Ob : Finset X)
    (hS : ∀ c ∈ centralizer ({x} : Set G), c • b ∈ S)
    (hOb : ∀ u ∈ Ob, ∃ c ∈ centralizer ({x} : Set G), c • b = u)
    (hrest : ∀ u ∈ S, u ∉ Ob → ¬ ∃ c ∈ centralizer ({x} : Set G), c • b = u) :
    Nat.card (centralizer ({x} : Set G)) = Ob.card * L.card := by
  classical
  have hP : ∀ u ∈ S, u ∈ Ob ↔ SiftPasses B T (orbitBase x u e) n := by
    intro u hu
    rw [← exists_centralizer_smul_eq_iff_of_coprime hc hcover hcomm hcop]
    exact ⟨hOb u, fun h => by_contra fun hn => hrest u hu hn h⟩
  rw [card_centralizer_eq_of_chain_coprime hc hcover hcomm hcop S hS (· ∈ Ob) hP]
  congr 1
  rw [Finset.filter_mem_eq_inter]
  congr 1
  ext u
  simp only [Finset.mem_inter, and_iff_right_iff_imp]
  intro hu
  obtain ⟨c, hc', rfl⟩ := hOb u hu
  exact hS c hc'

end CFSG.Monster.Existence.StdOdd.Cert

end
