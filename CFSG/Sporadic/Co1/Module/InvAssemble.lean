module

public import CFSG.Sporadic.Co1.Module.InvReps

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

theorem co1Inv_fix_eq (g : Co1) :
    co1Fix g = {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act g v = v} := rfl

theorem co1Inv_isConj_invariants
    {s t : Co1} (h : IsConj s t) :
    (co1Fix s).ncard = (co1Fix t).ncard ∧
      {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act s v = v ∧
        CFSG.Sporadic.Co1.Module.q₀ v = 1}.ncard =
      {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act t v = v ∧
        CFSG.Sporadic.Co1.Module.q₀ v = 1}.ncard ∧
      Nat.card (Subgroup.centralizer ({s} : Set Co1)) =
        Nat.card (Subgroup.centralizer ({t} : Set Co1)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  subst hc
  exact ⟨(CFSG.Sporadic.Co1.Module.ncard_fix_conj c s).symm,
    (CFSG.Sporadic.Co1.Module.ncard_fixQ_conj c s).symm,
    (CFSG.Sporadic.Co1.Module.card_centralizer_conj c s).symm⟩

theorem co1Inv_classes
    {sA sB sC : Co1} (h : CFSG.Sporadic.Co1.Module.RepFacts sA sB sC)
    (c : ℕ → Co1)
    (hc : ∀ s : Co1, orderOf s = 2 → ∃ i ∈ ({1, 2, 6} : Finset ℕ), IsConj (c i) s) :
    ∀ s : Co1, orderOf s = 2 → IsConj s sA ∨ IsConj s sB ∨ IsConj s sC := by
  obtain ⟨hoA, hoB, hoC, hfA, hfB, hfC, hqA, hqB, hqC, -⟩ := h
  have nAB : ¬ IsConj sA sB := fun h' => by
    have h1 := (co1Inv_isConj_invariants h').1
    have e1 : (co1Fix sA).ncard = 2 ^ 16 := hfA
    have e2 : (co1Fix sB).ncard = 2 ^ 12 := hfB
    rw [e1, e2] at h1
    norm_num at h1
  have nAC : ¬ IsConj sA sC := fun h' => by
    have h1 := (co1Inv_isConj_invariants h').1
    have e1 : (co1Fix sA).ncard = 2 ^ 16 := hfA
    have e2 : (co1Fix sC).ncard = 2 ^ 12 := hfC
    rw [e1, e2] at h1
    norm_num at h1
  have nBC : ¬ IsConj sB sC := fun h' => by
    have h1 := (co1Inv_isConj_invariants h').2.1
    rw [hqB, hqC] at h1
    norm_num at h1
  intro s hs
  by_contra hne
  push Not at hne
  obtain ⟨iS, hiS, hcS⟩ := hc s hs
  obtain ⟨iA, hiA, hcA⟩ := hc sA hoA
  obtain ⟨iB, hiB, hcB⟩ := hc sB hoB
  obtain ⟨iC, hiC, hcC⟩ := hc sC hoC
  have hpig : ∀ a ∈ ({1, 2, 6} : Finset ℕ), ∀ b ∈ ({1, 2, 6} : Finset ℕ),
      ∀ c ∈ ({1, 2, 6} : Finset ℕ), ∀ d ∈ ({1, 2, 6} : Finset ℕ),
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by decide
  rcases hpig iS hiS iA hiA iB hiB iC hiC with h | h | h | h | h | h
  · subst h
    exact hne.1 (hcS.symm.trans hcA)
  · subst h
    exact hne.2.1 (hcS.symm.trans hcB)
  · subst h
    exact hne.2.2 (hcS.symm.trans hcC)
  · subst h
    exact nAB (hcA.symm.trans hcB)
  · subst h
    exact nAC (hcA.symm.trans hcC)
  · subst h
    exact nBC (hcB.symm.trans hcC)

theorem co1Inv_orderOf_conj (d y : Co1) : orderOf (d⁻¹ * y * d) = orderOf y := by
  have h := MulEquiv.orderOf_eq (MulAut.conj d⁻¹) y
  rwa [MulAut.conj_apply, inv_inv] at h

theorem co1Inv_ne_two_pow {n : ℕ} (h : n = 3 ∨ n = 10 ∨ n = 12) (k : ℕ) : n ≠ 2 ^ k := by
  intro e
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k <;> omega
  · have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

theorem co1Inv_witness {r s sA sX w : Co1} {n : ℕ} (hn : ∀ k, n ≠ 2 ^ k)
    (h1 : IsConj r sA) (h2 : IsConj s sX) (hw : orderOf (w * sA * w⁻¹ * sX) = n) :
    ∃ g : Co1, ∀ k : ℕ, orderOf (g * r * g⁻¹ * s) ≠ 2 ^ k := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  obtain ⟨d, hd⟩ := isConj_iff.1 h2
  refine ⟨d⁻¹ * w * c, fun k => ?_⟩
  have hr : r = c⁻¹ * sA * c := by
    rw [← hc]
    group
  have hs : s = d⁻¹ * sX * d := by
    rw [← hd]
    group
  have key : (d⁻¹ * w * c) * r * (d⁻¹ * w * c)⁻¹ * s = d⁻¹ * (w * sA * w⁻¹ * sX) * d := by
    rw [hr, hs]
    group
  rw [key, co1Inv_orderOf_conj, hw]
  exact hn k

theorem co1InvolutionFacts_of_classes
    (c : ℕ → Co1)
    (hc : ∀ s : Co1, orderOf s = 2 → ∃ i ∈ ({1, 2, 6} : Finset ℕ), IsConj (c i) s) :
    Co1InvolutionFacts := by
  obtain ⟨sA, sB, sC, hrep⟩ := CFSG.Sporadic.Co1.Module.rep_facts
  have hcls := co1Inv_classes hrep c hc
  obtain ⟨hoA, hoB, hoC, hfA, hfB, hfC, -, -, -, hcA, hcB, hcC, wA, wB, wC⟩ := hrep
  have hdata : ∀ s : Co1, orderOf s = 2 →
      (IsConj s sA ∧ (co1Fix s).ncard = 2 ^ 16 ∧
        Nat.card (Subgroup.centralizer ({s} : Set Co1)) ≤ 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7) ∨
      (IsConj s sB ∧ (co1Fix s).ncard = 2 ^ 12 ∧
        Nat.card (Subgroup.centralizer ({s} : Set Co1)) * 2 ^ 12 < 2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7) ∨
      (IsConj s sC ∧ (co1Fix s).ncard = 2 ^ 12 ∧
        Nat.card (Subgroup.centralizer ({s} : Set Co1)) * 2 ^ 12 < 2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7) := by
    intro s hs
    rcases hcls s hs with h | h | h
    · obtain ⟨h1, -, h3⟩ := co1Inv_isConj_invariants h
      exact Or.inl ⟨h, h1.trans hfA, h3 ▸ hcA⟩
    · obtain ⟨h1, -, h3⟩ := co1Inv_isConj_invariants h
      exact Or.inr (Or.inl ⟨h, h1.trans hfB, h3 ▸ hcB⟩)
    · obtain ⟨h1, -, h3⟩ := co1Inv_isConj_invariants h
      exact Or.inr (Or.inr ⟨h, h1.trans hfC, h3 ▸ hcC⟩)
  have hmax : ∀ r : Co1, orderOf r = 2 →
      (co1Fix r).ncard * Nat.card (Subgroup.centralizer ({r} : Set Co1)) =
        2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 → IsConj r sA := by
    intro r hr hrb
    rcases hdata r hr with ⟨h, -, -⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · exact h
    · rw [h1] at hrb
      omega
    · rw [h1] at hrb
      omega
  refine ⟨fun s hs => ?_, fun r s hr hs hrb => ?_, fun r r' hr hr' hrb hrb' => ?_⟩
  · rcases hdata s hs with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · rw [h1]
      refine ⟨?_, fun _ => rfl⟩
      calc 2 ^ 16 * Nat.card (Subgroup.centralizer ({s} : Set Co1))
          ≤ 2 ^ 16 * (2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7) := Nat.mul_le_mul_left _ h2
        _ = 2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num
    · rw [h1]
      exact ⟨by omega, fun h => by omega⟩
    · rw [h1]
      exact ⟨by omega, fun h => by omega⟩
  · have hrA := hmax r hr hrb
    rcases hdata s hs with ⟨hsA, -, -⟩ | ⟨hsB, -, -⟩ | ⟨hsC, -, -⟩
    · obtain ⟨w, hw⟩ := wA
      exact co1Inv_witness (co1Inv_ne_two_pow (Or.inl rfl)) hrA hsA
        (by rw [hw])
    · obtain ⟨w, hw⟩ := wB
      exact co1Inv_witness (co1Inv_ne_two_pow (Or.inr (Or.inl rfl))) hrA hsB
        (by rw [hw])
    · obtain ⟨w, hw⟩ := wC
      exact co1Inv_witness (co1Inv_ne_two_pow (Or.inr (Or.inr rfl))) hrA hsC
        (by rw [hw])
  · exact (hmax r hr hrb).trans (hmax r' hr' hrb').symm

end CFSG.Monster.GMS
