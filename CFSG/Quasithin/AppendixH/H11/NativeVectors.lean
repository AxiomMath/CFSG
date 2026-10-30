module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin
open scoped BigOperators

private theorem toAdd_allOnes_zpow (k : ℤ) (i : Fin 12) :
    Multiplicative.toAdd (G6.allOnes 12 ^ k) i = (k : ZMod 2) := by
  simp [G6.allOnes, toAdd_zpow]

private theorem intCast_two_mul (j : ℤ) : ((2 * j : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_mul, Int.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem intCast_two_mul_add_one (j : ℤ) : ((2 * j + 1 : ℤ) : ZMod 2) = 1 := by
  rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]

private theorem mem_zpowers_allOnes_iff (z : G6.PermMod 12) :
    z ∈ Subgroup.zpowers (G6.allOnes 12) ↔
      Multiplicative.toAdd z = 0 ∨ ∀ i, Multiplicative.toAdd z i = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · left
      funext i
      rw [hj, toAdd_allOnes_zpow]
      exact intCast_two_mul j
    · right
      intro i
      rw [hj, toAdd_allOnes_zpow]
      exact intCast_two_mul_add_one j
  · rintro (h0 | h1)
    · refine ⟨0, ?_⟩
      apply Multiplicative.toAdd.injective
      simpa using h0.symm
    · refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_allOnes_zpow]
      simp [h1 i]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : b = a := by
  revert a b
  decide

private theorem eq_add_one_of_add_eq_one {a b : ZMod 2} (h : a + b = 1) : b = a + 1 := by
  revert a b
  decide

private theorem zmod2_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  revert a
  decide

private theorem toAdd_comm (σ : Equiv.Perm (Fin 12)) (x : G6.PermMod 12) (i : Fin 12) :
    Multiplicative.toAdd (G6.permAct 12 σ x * x⁻¹) i =
      Multiplicative.toAdd x (σ⁻¹ i) + Multiplicative.toAdd x i := by
  rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply]
  rcases zmod2_eq_zero_or_one (Multiplicative.toAdd x i) with h | h
  · rw [h, show (-(0 : ZMod 2)) = 0 by decide]
  · rw [h, show (-(1 : ZMod 2)) = 1 by decide]

private def evec (p : Fin 12) : Fin 12 → ZMod 2 := fun i => if i = p then 1 else 0

private def pairVec (p q : Fin 12) : G6.PermMod 12 :=
  Multiplicative.ofAdd (evec p + evec q)

private theorem toAdd_pairVec (p q i : Fin 12) :
    Multiplicative.toAdd (pairVec p q) i = evec p i + evec q i := rfl

private theorem pairVec_mem_coreMod (p q : Fin 12) (hpq : p ≠ q) :
    pairVec p q ∈ G6.coreMod 12 := by
  rw [G6.mem_coreMod]
  simp only [toAdd_pairVec, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  have hp : ∑ i, evec p i = 1 := by
    rw [Finset.sum_eq_single p]
    · simp [evec]
    · intro b _ hb; simp [evec, hb]
    · intro hp'; exact absurd (Finset.mem_univ p) hp'
  have hq : ∑ i, evec q i = 1 := by
    rw [Finset.sum_eq_single q]
    · simp [evec]
    · intro b _ hb; simp [evec, hb]
    · intro hq'; exact absurd (Finset.mem_univ q) hq'
  rw [hp, hq]
  exact CharTwo.add_self_eq_zero 1

private theorem toAdd_pairVec_self_left (p q : Fin 12) (hpq : p ≠ q) :
    Multiplicative.toAdd (pairVec p q) p = 1 := by
  rw [toAdd_pairVec]
  simp [evec, hpq]

private theorem toAdd_pairVec_eq_one_iff {p q : Fin 12} (hpq : p ≠ q) {i : Fin 12} :
    Multiplicative.toAdd (pairVec p q) i = 1 ↔ i = p ∨ i = q := by
  rw [toAdd_pairVec]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [evec, if_neg hc.1, evec, if_neg hc.2, add_zero] at h
    exact zero_ne_one h
  · rintro (rfl | rfl)
    · simp [evec, hpq]
    · simp [evec, hpq.symm]

theorem eq_one_of_mem_zpowers_allOnes (σ : Equiv.Perm (Fin 12))
    (h : ∀ x ∈ G6.coreMod 12,
      G6.permAct 12 σ x * x⁻¹ ∈ Subgroup.zpowers (G6.allOnes 12)) :
    σ = 1 := by
  have key : ∀ i j : Fin 12, i ≠ j →
      Multiplicative.toAdd (G6.permAct 12 σ (pairVec i j) * (pairVec i j)⁻¹) = 0 := by
    intro i j hij
    have hz := h (pairVec i j) (pairVec_mem_coreMod i j hij)
    rcases (mem_zpowers_allOnes_iff _).mp hz with h0 | h1
    · exact h0
    · exfalso
      have hcard : ({i, j, σ i, σ j} : Finset (Fin 12)).card < 12 := by
        have hle := Finset.card_le_four (a := i) (b := j) (c := σ i) (d := σ j)
        omega
      obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i, j, σ i, σ j} : Finset (Fin 12))) (t := Finset.univ) hcard
      have hpi : p ≠ i := fun hh => hp (by simp [hh])
      have hpj : p ≠ j := fun hh => hp (by simp [hh])
      have hpsi : p ≠ σ i := fun hh => hp (by simp [hh])
      have hpsj : p ≠ σ j := fun hh => hp (by simp [hh])
      have hzero : Multiplicative.toAdd
          (G6.permAct 12 σ (pairVec i j) * (pairVec i j)⁻¹) p = 0 := by
        rw [toAdd_comm, toAdd_pairVec, toAdd_pairVec]
        have h1p : evec i p + evec j p = 0 := by
          show (if p = i then (1 : ZMod 2) else 0) + (if p = j then 1 else 0) = 0
          rw [if_neg hpi, if_neg hpj, add_zero]
        have hne1 : σ⁻¹ p ≠ i := by
          intro hh; apply hpsi
          have := congrArg σ hh
          simpa using this
        have hne2 : σ⁻¹ p ≠ j := by
          intro hh; apply hpsj
          have := congrArg σ hh
          simpa using this
        have h2p : evec i (σ⁻¹ p) + evec j (σ⁻¹ p) = 0 := by
          show (if σ⁻¹ p = i then (1 : ZMod 2) else 0) +
            (if σ⁻¹ p = j then 1 else 0) = 0
          rw [if_neg hne1, if_neg hne2, add_zero]
        rw [h1p, h2p, add_zero]
      have hp1 : Multiplicative.toAdd
          (G6.permAct 12 σ (pairVec i j) * (pairVec i j)⁻¹) p = 1 := h1 p
      rw [hzero] at hp1
      exact zero_ne_one hp1
  have hfix : ∀ i : Fin 12, σ⁻¹ i = i := by
    intro i
    have hex : ∃ j k : Fin 12, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
      fin_cases i <;> decide
    obtain ⟨j, k, hj, hk, hjk⟩ := hex
    have h1 := congrFun (key i j hj.symm) i
    have h2 := congrFun (key i k hk.symm) i
    rw [toAdd_comm, toAdd_pairVec_self_left i j hj.symm] at h1
    rw [toAdd_comm, toAdd_pairVec_self_left i k hk.symm] at h2
    have hj' : Multiplicative.toAdd (pairVec i j) (σ⁻¹ i) = 1 := by
      have h := eq_neg_of_add_eq_zero_left h1
      rw [show (-1 : ZMod 2) = 1 by decide] at h
      exact h
    have hk' : Multiplicative.toAdd (pairVec i k) (σ⁻¹ i) = 1 := by
      have h := eq_neg_of_add_eq_zero_left h2
      rw [show (-1 : ZMod 2) = 1 by decide] at h
      exact h
    rcases (toAdd_pairVec_eq_one_iff hj.symm).mp hj' with h | h
    · exact h
    · rcases (toAdd_pairVec_eq_one_iff hk.symm).mp hk' with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hjk
  have hinv : σ⁻¹ = 1 := Equiv.ext hfix
  exact inv_eq_one.mp hinv

theorem mem_zpowers_allOnes_of_order_eleven (σ : Equiv.Perm (Fin 12)) (h11 : σ ^ 11 = 1)
    (h1 : σ ≠ 1) {x : G6.PermMod 12} (hx : x ∈ G6.coreMod 12)
    (h : G6.permAct 12 σ x * x⁻¹ ∈ Subgroup.zpowers (G6.allOnes 12)) :
    x ∈ Subgroup.zpowers (G6.allOnes 12) := by
  apply (mem_zpowers_allOnes_iff x).mpr
  have hsum : ∑ i, Multiplicative.toAdd x i = 0 := G6.mem_coreMod.mp hx
  have hne : ∃ i0, σ i0 ≠ i0 := by
    by_contra h'
    push Not at h'
    exact h1 (Equiv.ext h')
  rcases (mem_zpowers_allOnes_iff (G6.permAct 12 σ x * x⁻¹)).mp h with hc | hc
  ·
    have hstep0 : ∀ i, Multiplicative.toAdd x (σ i) = Multiplicative.toAdd x i := by
      intro i
      have hσi : σ⁻¹ (σ i) = i := Equiv.symm_apply_apply σ i
      have hi := congrFun hc (σ i)
      rw [toAdd_comm, hσi] at hi
      exact eq_of_add_eq_zero hi
    obtain ⟨i0, hi0⟩ := hne
    have hper : Function.IsPeriodicPt (⇑σ) 11 i0 := by
      show (⇑σ)^[11] i0 = i0
      rw [Equiv.Perm.iterate_eq_pow, h11]
      rfl
    have hmpne : Function.minimalPeriod (⇑σ) i0 ≠ 1 := by
      intro hmm
      exact hi0 (Function.minimalPeriod_eq_one_iff_isFixedPt.mp hmm)
    have hmp : Function.minimalPeriod (⇑σ) i0 = 11 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp hper.minimalPeriod_dvd).resolve_left hmpne
    let O : Finset (Fin 12) := Finset.univ.image (fun k : Fin 11 => (σ ^ (k : ℕ)) i0)
    have hinj : Function.Injective (fun k : Fin 11 => (σ ^ (k : ℕ)) i0) := by
      have hinjOn := (Function.iterate_injOn_Iio_minimalPeriod (f := ⇑σ) (x := i0))
      rw [hmp] at hinjOn
      intro k l hkl
      apply Fin.ext
      exact hinjOn (Set.mem_Iio.mpr k.2) (Set.mem_Iio.mpr l.2) hkl
    have hconst : ∀ k : ℕ, Multiplicative.toAdd x ((σ ^ k) i0) =
        Multiplicative.toAdd x i0 := by
      intro k
      induction k with
      | zero => simp
      | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hstep0, ih]
    have hOcard : O.card = 11 := by
      dsimp only [O]
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hcompl : Oᶜ.card = 1 := by
      rw [Finset.card_compl, hOcard, Fintype.card_fin]
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcompl
    have hsumO : Finset.sum O (fun i => Multiplicative.toAdd x i) = Multiplicative.toAdd x i0 := by
      have h1O : Finset.sum O (fun i => Multiplicative.toAdd x i) =
          ∑ k : Fin 11, Multiplicative.toAdd x ((σ ^ (k : ℕ)) i0) := by
        dsimp only [O]
        rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      rw [h1O]
      simp_rw [hconst]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ZMod.natCast_eq_one_iff_odd.mpr (by norm_num : Odd 11), one_mul]
    have hsumCompl :
        Finset.sum Oᶜ (fun i => Multiplicative.toAdd x i) = Multiplicative.toAdd x p := by
      rw [hp, Finset.sum_singleton]
    have hvp : Multiplicative.toAdd x p = Multiplicative.toAdd x i0 := by
      have hdec := Finset.sum_add_sum_compl O (fun i => Multiplicative.toAdd x i)
      rw [hsumO, hsumCompl, hsum] at hdec
      exact eq_of_add_eq_zero hdec
    have hconst_all : ∀ i, Multiplicative.toAdd x i = Multiplicative.toAdd x i0 := by
      intro i
      by_cases hi : i ∈ O
      · dsimp only [O] at hi
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hi
        rw [← hk, hconst k]
      · have hi' : i ∈ Oᶜ := Finset.mem_compl.mpr hi
        rw [hp, Finset.mem_singleton] at hi'
        rw [hi', hvp]
    rcases zmod2_eq_zero_or_one (Multiplicative.toAdd x i0) with hv | hv
    · left; funext i; rw [hconst_all i, hv]; rfl
    · right; intro i; rw [hconst_all i, hv]
  ·
    exfalso
    have hstep : ∀ i, Multiplicative.toAdd x (σ i) = Multiplicative.toAdd x i + 1 := by
      intro i
      have hσi : σ⁻¹ (σ i) = i := Equiv.symm_apply_apply σ i
      have hi := hc (σ i)
      rw [toAdd_comm, hσi] at hi
      exact eq_add_one_of_add_eq_one hi
    obtain ⟨i0, hi0⟩ := hne
    have hpow : ∀ k : ℕ, Multiplicative.toAdd x ((σ ^ k) i0) =
        Multiplicative.toAdd x i0 + (k : ZMod 2) := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih]
          push_cast
          ring
    have hcontra : Multiplicative.toAdd x i0 = Multiplicative.toAdd x i0 + 1 := by
      have hh := hpow 11
      rw [h11] at hh
      rw [ZMod.natCast_eq_one_iff_odd.mpr (by norm_num : Odd 11)] at hh
      simpa using hh
    exact zmod2_ne_add_one (Multiplicative.toAdd x i0) hcontra

private theorem zmod2_cancel_pair (x y z : ZMod 2) : (x + y) + (z + y) = z + x := by
  rw [show (x + y) + (z + y) = (z + x) + (y + y) by abel, CharTwo.add_self_eq_zero, add_zero]

private theorem inv_eq_self_of_mul_self {γ : Equiv.Perm (Fin 12)} (hγ : γ * γ = 1) :
    γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ

private theorem apply_apply_self {γ : Equiv.Perm (Fin 12)} (hγ : γ * γ = 1) (x : Fin 12) :
    γ (γ x) = x := by
  rw [← Equiv.Perm.mul_apply, hγ]
  rfl

private theorem evec_comp {γ : Equiv.Perm (Fin 12)} (hγ : γ * γ = 1) (p i : Fin 12) :
    evec p (γ i) = evec (γ p) i := by
  simp only [evec]
  by_cases h : γ i = p
  · have hi : i = γ p := by
      have h' := congrArg γ h
      rw [apply_apply_self hγ] at h'
      exact h'
    rw [if_pos h, if_pos hi]
  · have hi : i ≠ γ p := fun hh => h (by rw [hh, apply_apply_self hγ])
    rw [if_neg h, if_neg hi]

private theorem toAdd_comm_pairVec_fixed {γ : Equiv.Perm (Fin 12)} (hγ : γ * γ = 1)
    {p q f i : Fin 12} (hp : γ p = q) (hf : γ f = f) :
    Multiplicative.toAdd (G6.permAct 12 γ (pairVec p f) * (pairVec p f)⁻¹) i =
      evec p i + evec q i := by
  rw [toAdd_comm, inv_eq_self_of_mul_self hγ, toAdd_pairVec, toAdd_pairVec]
  rw [evec_comp hγ p i, evec_comp hγ f i, hp, hf]
  rw [zmod2_cancel_pair]

private theorem toAdd_prod_apply (S : Finset (Fin 4)) (u : Fin 4 → G6.PermMod 12) (i : Fin 12) :
    Multiplicative.toAdd (∏ s ∈ S, u s) i = ∑ s ∈ S, Multiplicative.toAdd (u s) i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, toAdd_mul, Pi.add_apply, ih]

private theorem sum_pairVec_eval_left {p q : Fin 4 → Fin 12}
    (hpq : ∀ k, p k ≠ q k)
    (hdisj : ∀ k l, k ≠ l → p k ≠ p l ∧ p k ≠ q l ∧ q k ≠ q l)
    (S : Finset (Fin 4)) {k : Fin 4} (hk : k ∈ S) :
    (Finset.sum S (fun s => evec (p s) + evec (q s))) (p k) = 1 := by
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k
    (fun l _ hl => by
      obtain ⟨h1, h2, _⟩ := hdisj k l hl.symm
      simp [evec, h1, h2])
    (fun hk' => absurd hk hk')]
  simp [evec, hpq k]

private theorem sum_pairVec_eval_other {p q : Fin 4 → Fin 12}
    (S : Finset (Fin 4)) {e : Fin 12} (he : ∀ s, e ≠ p s ∧ e ≠ q s) :
    (Finset.sum S (fun s => evec (p s) + evec (q s))) e = 0 := by
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro s _
  simp [evec, (he s).1, (he s).2]

theorem exists_independent_commutators (γ : Equiv.Perm (Fin 12)) (hγ : γ * γ = 1)
    (a b : Fin 4 → Fin 12) (hab : ∀ k, γ (a k) = b k ∧ γ (b k) = a k) (hne : ∀ k, a k ≠ b k)
    (hdisj : ∀ k l, k ≠ l → a k ≠ a l ∧ a k ≠ b l ∧ b k ≠ b l) :
    ∃ u : Fin 4 → G6.PermMod 12, (∀ s, u s ∈ G6.coreMod 12) ∧
      ∀ S : Finset (Fin 4), S.Nonempty →
        ∏ s ∈ S, (G6.permAct 12 γ (u s) * (u s)⁻¹) ∉ Subgroup.zpowers (G6.allOnes 12) := by
  by_cases hfix : ∃ f, γ f = f
  ·
    obtain ⟨f, hf⟩ := hfix
    have haf : ∀ s, a s ≠ f := by
      intro s h
      have h1 := (hab s).1
      rw [h, hf] at h1
      exact (hne s) (h.trans h1)
    have hbf : ∀ s, b s ≠ f := by
      intro s h
      have h1 := (hab s).2
      rw [h, hf] at h1
      exact (hne s) (h1.symm.trans h.symm)
    refine ⟨fun s => pairVec (a s) f, ?_, ?_⟩
    · intro s
      exact pairVec_mem_coreMod (a s) f (haf s)
    · intro S hS
      obtain ⟨k0, hk0⟩ := hS
      have hcommA : ∀ s i, Multiplicative.toAdd
          (G6.permAct 12 γ (pairVec (a s) f) * (pairVec (a s) f)⁻¹) i =
          evec (a s) i + evec (b s) i := by
        intro s i
        exact toAdd_comm_pairVec_fixed hγ (hab s).1 hf
      have hprod_eval : ∀ i, Multiplicative.toAdd
          (∏ s ∈ S, (G6.permAct 12 γ (pairVec (a s) f) * (pairVec (a s) f)⁻¹)) i =
          (Finset.sum S (fun s => evec (a s) + evec (b s))) i := by
        intro i
        rw [toAdd_prod_apply, Finset.sum_apply]
        exact Finset.sum_congr rfl (fun s _ => hcommA s i)
      rw [mem_zpowers_allOnes_iff]
      push Not
      constructor
      · intro hzero
        have hh := congrFun hzero (a k0)
        rw [hprod_eval, sum_pairVec_eval_left hne hdisj S hk0] at hh
        exact (by decide : (1 : ZMod 2) ≠ 0) (by simpa using hh)
      · refine ⟨f, ?_⟩
        rw [hprod_eval, sum_pairVec_eval_other S (fun s => ⟨(haf s).symm, (hbf s).symm⟩)]
        decide
  ·
    have hno : ∀ f, γ f ≠ f := fun f h => hfix ⟨f, h⟩
    let tg : Fin 4 × Bool → Fin 12 := fun p => if p.2 then b p.1 else a p.1
    let T8 : Finset (Fin 12) := Finset.univ.image tg
    have ha_mem : ∀ k, a k ∈ T8 := fun k => Finset.mem_image.mpr ⟨(k, false), by simp [tg]⟩
    have hb_mem : ∀ k, b k ∈ T8 := fun k => Finset.mem_image.mpr ⟨(k, true), by simp [tg]⟩
    have hT8card : T8.card ≤ 8 := by
      dsimp only [T8]
      calc (Finset.univ.image tg).card ≤ (Finset.univ : Finset (Fin 4 × Bool)).card :=
            Finset.card_image_le
        _ = 8 := by simp
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := T8) (t := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    let T10 : Finset (Fin 12) := T8 ∪ {c, γ c}
    have hT10card : T10.card ≤ 10 := by
      dsimp only [T10]
      calc (T8 ∪ {c, γ c}).card ≤ T8.card + ({c, γ c} : Finset (Fin 12)).card :=
            Finset.card_union_le _ _
        _ ≤ 8 + 2 := by
            have h2 := Finset.card_le_two (a := c) (b := γ c)
            omega
        _ = 10 := by norm_num
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := T10) (t := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    let px : Fin 4 → Fin 12 := ![a 1, a 2, a 3, c]
    let py : Fin 4 → Fin 12 := ![b 1, b 2, b 3, γ c]
    have ha_mem10 : ∀ k, a k ∈ T10 := fun k => Finset.mem_union_left _ (ha_mem k)
    have hb_mem10 : ∀ k, b k ∈ T10 := fun k => Finset.mem_union_left _ (hb_mem k)
    have hc_mem10 : c ∈ T10 := Finset.mem_union_right _ (by simp)
    have hgc_mem10 : γ c ∈ T10 := Finset.mem_union_right _ (by simp)
    have hcA : ∀ k, c ≠ a k := fun k h => hc (by rw [h]; exact ha_mem k)
    have hcB : ∀ k, c ≠ b k := fun k h => hc (by rw [h]; exact hb_mem k)
    have hgcA : ∀ k, γ c ≠ a k := by
      intro k h; apply hc; rw [← apply_apply_self hγ c, h, (hab k).1]; exact hb_mem k
    have hgcB : ∀ k, γ c ≠ b k := by
      intro k h; apply hc; rw [← apply_apply_self hγ c, h, (hab k).2]; exact ha_mem k
    have hcgc : c ≠ γ c := fun h => hno c h.symm
    have hpy : ∀ s, γ (px s) = py s := by
      intro s
      fin_cases s
      · simpa [px, py] using (hab 1).1
      · simpa [px, py] using (hab 2).1
      · simpa [px, py] using (hab 3).1
      · simp [px, py]
    have hpx_py_ne : ∀ s, px s ≠ py s := by
      intro s
      fin_cases s
      · simpa [px, py] using hne 1
      · simpa [px, py] using hne 2
      · simpa [px, py] using hne 3
      · simpa [px, py] using hcgc
    have hpxy_disj : ∀ k l, k ≠ l → px k ≠ px l ∧ px k ≠ py l ∧ py k ≠ py l := by
      intro k l hkl
      fin_cases k <;> fin_cases l <;> refine ⟨?_, ?_, ?_⟩ <;>
        first
        | exact (hdisj _ _ (by decide)).1
        | exact (hdisj _ _ (by decide)).2.1
        | exact (hdisj _ _ (by decide)).2.2
        | exact Ne.symm ((hdisj _ _ (by decide)).1)
        | exact Ne.symm ((hdisj _ _ (by decide)).2.1)
        | exact Ne.symm ((hdisj _ _ (by decide)).2.2)
        | exact hcA _
        | exact hcB _
        | exact hgcA _
        | exact hgcB _
        | exact Ne.symm (hcA _)
        | exact Ne.symm (hcB _)
        | exact Ne.symm (hgcA _)
        | exact Ne.symm (hgcB _)
        | exact hcgc
        | exact Ne.symm hcgc
        | exact absurd rfl hkl
    have hpx_not_common : ∀ s, px s ≠ a 0 ∧ px s ≠ b 0 := by
      intro s
      fin_cases s
      · exact ⟨(hdisj 1 0 (by decide)).1, (hdisj 1 0 (by decide)).2.1⟩
      · exact ⟨(hdisj 2 0 (by decide)).1, (hdisj 2 0 (by decide)).2.1⟩
      · exact ⟨(hdisj 3 0 (by decide)).1, (hdisj 3 0 (by decide)).2.1⟩
      · exact ⟨hcA 0, hcB 0⟩
    have he_a : ∀ k, e ≠ a k := fun k h => he (by rw [h]; exact ha_mem10 k)
    have he_b : ∀ k, e ≠ b k := fun k h => he (by rw [h]; exact hb_mem10 k)
    have he_c : e ≠ c := fun h => he (by rw [h]; exact hc_mem10)
    have he_gc : e ≠ γ c := fun h => he (by rw [h]; exact hgc_mem10)
    have he_px : ∀ s, e ≠ px s := by
      intro s; fin_cases s
      · exact he_a 1
      · exact he_a 2
      · exact he_a 3
      · exact he_c
    have he_py : ∀ s, e ≠ py s := by
      intro s; fin_cases s
      · exact he_b 1
      · exact he_b 2
      · exact he_b 3
      · exact he_gc
    let u : Fin 4 → G6.PermMod 12 := fun s => pairVec (a 0) (px s)
    refine ⟨u, ?_, ?_⟩
    · intro s
      exact pairVec_mem_coreMod (a 0) (px s) (hpx_not_common s).1.symm
    · intro S hS
      obtain ⟨k0, hk0⟩ := hS
      have hcommB : ∀ s i, Multiplicative.toAdd
          (G6.permAct 12 γ (u s) * (u s)⁻¹) i =
          evec (a 0) i + evec (b 0) i + (evec (px s) i + evec (py s) i) := by
        intro s i
        dsimp only [u]
        rw [toAdd_comm, inv_eq_self_of_mul_self hγ, toAdd_pairVec, toAdd_pairVec]
        rw [evec_comp hγ (a 0) i, (hab 0).1, evec_comp hγ (px s) i, hpy s]
        abel
      have hprod_eval : ∀ i, Multiplicative.toAdd
          (∏ s ∈ S, (G6.permAct 12 γ (u s) * (u s)⁻¹)) i =
          (Finset.sum S (fun s => (evec (a 0) + evec (b 0)) + (evec (px s) + evec (py s)))) i := by
        intro i
        rw [toAdd_prod_apply, Finset.sum_apply]
        exact Finset.sum_congr rfl (fun s _ => hcommB s i)
      have hcommon : (evec (a 0) + evec (b 0)) (px k0) = 0 := by
        simp [evec, (hpx_not_common k0).1, (hpx_not_common k0).2]
      have hsummand : ∀ s, ((evec (a 0) + evec (b 0)) + (evec (px s) + evec (py s))) (px k0) =
          (evec (px s) + evec (py s)) (px k0) := by
        intro s
        rw [Pi.add_apply, hcommon, zero_add]
      have h1pt : Multiplicative.toAdd
          (∏ s ∈ S, (G6.permAct 12 γ (u s) * (u s)⁻¹)) (px k0) = 1 := by
        rw [hprod_eval, Finset.sum_apply]
        rw [Finset.sum_congr rfl (fun s _ => hsummand s)]
        rw [← Finset.sum_apply]
        exact sum_pairVec_eval_left hpx_py_ne hpxy_disj S hk0
      have h0pt : Multiplicative.toAdd
          (∏ s ∈ S, (G6.permAct 12 γ (u s) * (u s)⁻¹)) e = 0 := by
        rw [hprod_eval, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro s _
        simp [evec, Pi.add_apply, he_a 0, he_b 0, he_px s, he_py s]
      rw [mem_zpowers_allOnes_iff]
      push Not
      constructor
      · intro hzero
        have hh := congrFun hzero (px k0)
        rw [h1pt] at hh
        exact (by decide : (1 : ZMod 2) ≠ 0) (by simpa using hh)
      · exact ⟨e, by rw [h0pt]; decide⟩

private def aPairX (k : Fin 4) : Fin 12 := ![0, 2, 4, 5] k
private def aPairY (k : Fin 4) : Fin 12 := ![3, 9, 10, 11] k

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := CharTwo.add_self_eq_zero a

private def aPair (k : Fin 4) : G6.PermMod 12 := pairVec (aPairX k) (aPairY k)

private theorem toAdd_finset_prod (S : Finset (Fin 4)) (u : Fin 4 → G6.PermMod 12) :
    Multiplicative.toAdd (Finset.prod S u) =
      Finset.sum S (fun s => Multiplicative.toAdd (u s)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, toAdd_mul, ih]

private theorem toAdd_aPair_pow (k : Fin 4) (f : ZMod 2) :
    Multiplicative.toAdd (aPair k ^ f.val) =
      fun i => f * (evec (aPairX k) i + evec (aPairY k) i) := by
  funext i
  rw [toAdd_pow]
  simp only [Pi.smul_apply, Pi.add_apply, aPair, toAdd_pairVec]
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem m12gA_inv_apply' (i : Fin 12) :
    (CFSG.Sporadic.Mathieu.m12gA)⁻¹ i = ![3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5] i := by
  fin_cases i <;> decide

theorem commutators_le_closure_m12gA :
    ∃ c : Fin 4 → G6.PermMod 12, ∀ x ∈ G6.coreMod 12,
      G6.permAct 12 CFSG.Sporadic.Mathieu.m12gA x * x⁻¹ ∈ Subgroup.closure (Set.range c) := by
  refine ⟨aPair, fun x _ => ?_⟩
  set d : Fin 4 → ZMod 2 :=
    fun k => Multiplicative.toAdd x (aPairX k) + Multiplicative.toAdd x (aPairY k) with hd
  have hw : G6.permAct 12 CFSG.Sporadic.Mathieu.m12gA x * x⁻¹ =
      ∏ k : Fin 4, aPair k ^ (d k).val := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_comm, m12gA_inv_apply']
    rw [toAdd_finset_prod, Finset.sum_apply]
    simp only [toAdd_aPair_pow]
    rw [Fin.sum_univ_four]
    fin_cases i <;> simp [hd, aPairX, aPairY, evec, zmod2_add_self] <;> ring
  rw [hw]
  exact Subgroup.prod_mem (Subgroup.closure (Set.range aPair))
    (fun k _ => Subgroup.pow_mem (Subgroup.closure (Set.range aPair))
      (Subgroup.subset_closure (Set.mem_range_self k)) (d k).val)

end CFSG.Quasithin.AppendixH.H11
