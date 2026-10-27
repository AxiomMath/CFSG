module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreNarrow
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRest
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

@[expose] def GGIOneMoreUnitaryDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1

@[expose] def GGIOneMoreUnitaryThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p = 3 ∧ ¬ p ∣ lab.rank + 1 ∧
    (lab.rank = 3 → p ∣ lab.n) ∧ ¬ (lab.rank = 4 ∧ lab.n = 1)

@[expose] def GGIOneMoreUnitaryFiveTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1 ∧ p = 3

theorem ggIOneMoreUnitaryRestLabel_cover {p : ℕ} {lab : LargeEvenLabel}
    (h : GGIOneMoreUnitaryRestLabel p lab) :
    GGIOneMoreUnitaryDvdLabel p lab ∨ GGIOneMoreUnitaryThreeLabel p lab ∨
      GGIOneMoreUnitaryFiveTwoLabel p lab := by
  obtain ⟨ht, hl, hpq, hc, hn⟩ := h
  by_cases hpd : p ∣ lab.rank + 1
  · exact Or.inl ⟨ht, hl, hpq, hpd⟩
  · have hp3 : p = 3 := hc.resolve_left hpd
    by_cases h41 : lab.rank = 4 ∧ lab.n = 1
    · exact Or.inr (Or.inr ⟨ht, h41.1, h41.2, hp3⟩)
    · exact Or.inr (Or.inl ⟨ht, hl, hpq, hp3, hpd, hn, h41⟩)

abbrev UnitaryR (K : Type) [Field K] (n d : ℕ) : Type :=
  LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))

abbrev UnitaryI (K : Type) [Field K] (n d : ℕ) : Set (MulAut (UnitaryR K n d)) :=
  LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (LargeEvenGUSet (Fin d) K (2 ^ n))

@[expose] def GGIOneUnitaryThreeRootInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n d : ℕ), Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n → 4 ≤ d →
    ¬ 3 ∣ d → 3 ∣ 2 ^ n + 1 → (d = 4 → 3 ∣ n) → ¬ (d = 5 ∧ n = 1) →
      GGEndNodeRootEltBig 3 (d - 2) (UnitaryR K n d)

@[expose] def GGIOneUnitaryFiveTwoInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 →
    GGEndNodeIOne 3 3 (UnitaryR K 1 5) (UnitaryI K 1 5)

@[expose] def GGIOneUnitaryDvdRootInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n d p : ℕ), Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n → 5 ≤ d →
    p.Prime → p ∣ 2 ^ n + 1 → p ∣ d →
      GGEndNodeRoot p (ggUnitaryTorusRank p d) (UnitaryR K n d) (UnitaryI K n d)

@[expose] def GGIOneUnitaryDvdDeltaInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n d p : ℕ), Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n → 5 ≤ d →
    p.Prime → p ∣ 2 ^ n + 1 → p ∣ d →
      GGEndNodeIOneDelta p (ggUnitaryTorusRank p d) (UnitaryR K n d) (UnitaryI K n d)

section Certs

theorem unitary_hdq {d n : ℕ} (hd : 4 ≤ d) : (d, 2 ^ n) ≠ (3, 2) := fun he => by
  have := congrArg Prod.fst he
  omega

theorem ggEndNodeIOne_unitaryThree_of_root (hE : GGIOneUnitaryThreeRootInput) {K : Type}
    [Field K] [Finite K] {n d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (h3d : ¬ 3 ∣ d) (hpq : 3 ∣ 2 ^ n + 1) (hd4 : d = 4 → 3 ∣ n) (h52 : ¬ (d = 5 ∧ n = 1)) :
    GGEndNodeIOne 3 (d - 2) (UnitaryR K n d) (UnitaryI K n d) := by
  have h := TableBU.unitaryFieldData_of_card hK hn
  have hdq := unitary_hdq (n := n) hd
  exact ggEndNodeIOne_of_rootEltBig
    (fun φ hφ hφp => TableBUE.mem_range_conj_of_pow_eq_one h hK (by omega) hdq Nat.prime_three hpq
      h3d hφ hφp)
    (TableBUE.center_proj_eq_bot hK (by omega) hdq)
    (StdSubRestU.ggCenterPrime_unitary hK hn (by omega) hdq Nat.prime_three (by norm_num) h3d)
    (hE K n d hK hn hd h3d hpq hd4 h52)

theorem largeEvenLabelAll_endNodeIOne_unitaryThree (hE : GGIOneUnitaryThreeRootInput)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) {p : ℕ}
    (h : GGIOneMoreUnitaryThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl3, hpq, rfl, hpd, hl4, h41⟩ := h
  dsimp only at htag hl3 hpq hpd hl4 h41
  subst htag
  have hn : 1 ≤ n := hlab.1
  have h1 := largeEvenLabelAll_torusLift_twA hlab rfl Nat.prime_three hpq
  have hr : ggUnitaryTorusRank 3 (l + 1) = l + 1 - 2 := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  intro Q hQ
  have hQ' := h1 Q hQ
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hlift⟩ := hQ'
  rw [hr] at hlift
  refine ⟨K, i1, i2, hK, hq, ggOutdiagOdd_of_prime fun φ hφ hφp =>
    TableBUE.mem_range_conj_of_pow_eq_one (TableBU.unitaryFieldData_of_card hK hn) hK (by omega)
      (unitary_hdq (n := n) (by omega)) Nat.prime_three hpq hpd hφ hφp, l + 1 - 2, hlift,
    ggEndNodeIOne_unitaryThree_of_root hE hK hn (by omega) hpd hpq (fun h => hl4 (by omega))
      (by omega)⟩

theorem ggStdSubIOneProperInputOn_unitaryThree (ha₀ : GGLNoncyclicInput)
    (hE : GGIOneUnitaryThreeRootInput) : GGStdSubIOneProperInputOn GGIOneMoreUnitaryThreeLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_endNodeIOne_unitaryThree hE hlab h

theorem ggStdSubIOneProperInputOn_twDThreeField (ha₀ : GGLNoncyclicInput)
    (hE : GGIOneUnitaryThreeRootInput) :
    GGStdSubIOneProperInputOn GGIOneMoreTwDThreeFieldLabel := by
  refine ggStdSubIOneProperInputOn_of_labels ha₀ fun p lab hp hlab hS _ => ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq, rfl, hpn⟩ := hS
  dsimp only at ht hl hpq hpn
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hlab' : LargeEvenInLambda2 ⟨.twA, 3, n⟩ := ⟨hn, by norm_num, by norm_num⟩
  exact largeEvenLabelAll_twDThree_of_twA (largeEvenLabelAll_endNodeIOne_unitaryThree hE hlab'
    (p := 3) ⟨rfl, le_rfl, hpq, rfl, by norm_num, fun _ => hpn, fun h => absurd h.1 (by norm_num)⟩)

end Certs

end CFSG.StandardType
