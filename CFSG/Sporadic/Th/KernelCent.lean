
module

public import CFSG.Sporadic.Th.KernelCentralizerBase

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th.Max3 TauCeti Pointwise MulAction

@[expose] def fixB (c : ℕ) (n : Fin 11 → ℕ) (D : Fin 11) : ℕ :=
  if D = 0 then 1 else c * n D / mD D

theorem card_fix_le_of [Finite P] (hP : Nat.card P = thOrder) {v : Fin 11 → P} (hv0 : v 0 = 1)
    (hcov : ∀ g : P, ∃ D, ∃ k ∈ K, ∃ k' ∈ K, g = k * v D * k')
    (hstab : ∀ D, mD D ≤ Nat.card (stabK (v D))) (hK : Nat.card K ≤ 634023936)
    (t : K) {c : ℕ} (hc : Nat.card (Subgroup.centralizer ({t} : Set K)) ≤ c) (n : Fin 11 → ℕ)
    (hn : ∀ D, D ≠ 0 →
      Nat.card {k : P // k ∈ stabK (v D) ∧ ∃ g ∈ K, g * t * g⁻¹ = k} ≤ n D) :
    Nat.card {p : Om // (t : P) • p = p} ≤ ∑ D, fixB c n D := by
  classical
  obtain ⟨-, -, hc', -, hlab⟩ := orbitData hP hv0 hcov hstab hK
  have : Fintype Om := Fintype.ofFinite Om
  have hD : ∀ D, Nat.card {p : Om // lab v hc' p = D ∧ (t : P) • p = p} ≤ fixB c n D := by
    intro D
    have e : Nat.card {p : Om // lab v hc' p = D ∧ (t : P) • p = p} =
        Nat.card {p : orb (v D) // t • p = p} := by
      refine Nat.card_congr ⟨fun p => ⟨⟨p.1, (hlab _ _).2 p.2.1⟩, Subtype.ext p.2.2⟩,
        fun p => ⟨p.1.1, (hlab _ _).1 p.1.2, congrArg Subtype.val p.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [e]
    by_cases hD0 : D = 0
    · subst hD0
      have : Subsingleton (orb (v 0)) := by
        rw [hv0, orb_one]
        infer_instance
      rw [fixB, if_pos rfl]
      exact Finite.card_le_one_iff_subsingleton.2 inferInstance
    · have h1 := fix_orb_le (v D) t (hstab D) (hn D hD0) hc
      rw [fixB, if_neg hD0]
      exact (Nat.le_div_iff_mul_le (mD_pos D)).2 h1
  calc Nat.card {p : Om // (t : P) • p = p}
      = ∑ D, Nat.card {p : Om // lab v hc' p = D ∧ (t : P) • p = p} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rw [Finset.card_eq_sum_card_fiberwise (f := lab v hc') (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun D _ => ?_
        congr 1
        ext p
        simp [and_comm]
    _ ≤ ∑ D, fixB c n D := Finset.sum_le_sum fun D _ => hD D

theorem card_centralizer_mul_le [Finite P] (hKc : Nat.card K = 634023936) (t : P) {r : ℕ}
    (s : Fin r → K) (c : Fin r → ℕ) (hs : ∀ i, IsConj t (s i : P))
    (hsd : ∀ i j, i ≠ j → ¬IsConj (s i) (s j))
    (hc : ∀ i, Nat.card (Subgroup.centralizer ({s i} : Set K)) ≤ c i) :
    Nat.card (Subgroup.centralizer ({t} : Set P)) * ∑ i, 634023936 / c i ≤
      Nat.card {p : Om // t • p = p} * 634023936 := by
  classical
  have hf := CFSG.GroupAction.card_fix_mul_card_stabilizer (G := P) (X := Om) (pt 1) t
  rw [MulAction.stabilizer_quotient, hKc] at hf
  let F : (Σ i : Fin r, conjugatesOf (s i)) → {h : P // h ∈ K ∧ IsConj t h} := fun x =>
    ⟨((x.2 : K) : P), (x.2 : K).2,
      (hs x.1).trans (by
        obtain ⟨g, hg⟩ := isConj_iff.1 (show IsConj (s x.1) (x.2 : K) from x.2.2)
        exact isConj_iff.2 ⟨(g : P), by rw [← hg]; rfl⟩)⟩
  have hF : Function.Injective F := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have e : ((x : K) : P) = ((y : K) : P) := by
      have := congrArg Subtype.val hxy
      exact this
    have e' : (x : K) = (y : K) := Subtype.ext e
    by_cases hij : i = j
    · subst hij
      have : x = y := Subtype.ext e'
      rw [this]
    · exfalso
      refine hsd i j hij ?_
      have hx : IsConj (s i) (x : K) := x.2
      have hy : IsConj (s j) (y : K) := y.2
      rw [e'] at hx
      exact hx.trans hy.symm
  have hcard : ∑ i, 634023936 / c i ≤ Nat.card {h : P // h ∈ K ∧ IsConj t h} := by
    refine le_trans ?_ (Nat.card_le_card_of_injective F hF)
    rw [Nat.card_sigma]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := card_centralizer_mul_ncard (s i)
    rw [hKc] at h1
    rw [Nat.card_coe_set_eq]
    by_cases hc0 : c i = 0
    · rw [hc0, Nat.div_zero]
      exact Nat.zero_le _
    · have hpos : 0 < Nat.card (Subgroup.centralizer ({s i} : Set K)) := Nat.card_pos
      calc 634023936 / c i ≤ 634023936 / Nat.card (Subgroup.centralizer ({s i} : Set K)) :=
            Nat.div_le_div_left (hc i) hpos
        _ = (conjugatesOf (s i)).ncard := by
            rw [← h1, Nat.mul_div_cancel_left _ hpos]
  calc Nat.card (Subgroup.centralizer ({t} : Set P)) * ∑ i, 634023936 / c i
      ≤ Nat.card (Subgroup.centralizer ({t} : Set P)) *
          Nat.card {h : P // h ∈ K ∧ IsConj t h} := Nat.mul_le_mul_left _ hcard
    _ = Nat.card {p : Om // t • p = p} * 634023936 := hf.symm

end CFSG.Sporadic.Th.Kernel

end
