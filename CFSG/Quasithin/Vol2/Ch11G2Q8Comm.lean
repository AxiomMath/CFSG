module

public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F]

@[expose] def tv (i j : Fin 3) (hij : i ≠ j) (t : F) : SL3 F :=
  ⟨transvection i j t, det_transvection_of_ne i j hij t⟩

abbrev eu (i : Fin 3) (t : F) : Ix3 → F := Pi.single (Sum.inl i) t

abbrev ev (i : Fin 3) (t : F) : Ix3 → F := Pi.single (Sum.inr i) t

variable [CharP F 2]

theorem tv_mul_self (i j : Fin 3) (hij : i ≠ j) (t : F) : tv i j hij t * tv i j hij t = 1 := by
  apply Subtype.ext
  change transvection i j t * transvection i j t = 1
  rw [transvection_mul_transvection_same i j hij, CharTwo.add_self_eq_zero, transvection_zero]

theorem tv_inv (i j : Fin 3) (hij : i ≠ j) (t : F) : (tv i j hij t)⁻¹ = tv i j hij t :=
  inv_eq_of_mul_eq_one_right (tv_mul_self i j hij t)

theorem adjugate_tv (i j : Fin 3) (hij : i ≠ j) (t : F) :
    adjugate ((tv i j hij t : SL3 F) : Matrix (Fin 3) (Fin 3) F) = transvection i j t := by
  change (((tv i j hij t)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [tv_inv]
  rfl

omit [CharP F 2] in
theorem transvection_entry (i j : Fin 3) (t : F) (a b : Fin 3) :
    transvection i j t a b = (if a = b then 1 else 0) + (if i = a ∧ j = b then t else 0) := by
  simp [transvection, one_apply, single_apply]

theorem g2Act_tv (i j : Fin 3) (hij : i ≠ j) (t : F) (w : Ix3 → F) :
    g2Act (g2A (tv i j hij t)) w =
      w + eu i (t * w (.inl j)) + ev j (t * w (.inr i)) := by
  conv_lhs => rw [q6_eta w]
  rw [g2Act_g2A, adjugate_tv]
  have hA : ((tv i j hij t : SL3 F) : Matrix (Fin 3) (Fin 3) F) = transvection i j t := rfl
  simp only [hA, transvection_entry]
  funext k
  rcases k with k | k <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp_all [q6, Pi.add_apply] <;> ring

theorem g2Act_x0 (w : Ix3 → F) :
    g2Act (g2X ![1, 0, 0]) w =
      q6 (w (.inl 0) + w (.inr 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0))
        (w (.inr 1) + w (.inl 2)) (w (.inr 2) + w (.inl 1)) := by
  rw [g2Act_apply]
  change zP (xaFun _ (zI w)) = _
  rw [q6_eta w, zI_q6, xaFun_zmk, zP_zmk]
  simp only [q6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Sum.elim_inl, Sum.elim_inr, Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> simp [CharTwo.sub_eq_add]

theorem exists_third (i j : Fin 3) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

theorem commutant_cayley (T : (Ix3 → F) →+ (Ix3 → F))
    (hT : ∀ (g : ↥(cayleyGroup F)) (x : Ix3 → F), T (g2Act g x) = g2Act g (T x)) :
    ∃ c : F, ∀ x, T x = c • x := by
  have hδ : ∀ i j (hij : i ≠ j) (t : F) (w : Ix3 → F),
      T (eu i (t * w (.inl j)) + ev j (t * w (.inr i))) =
        eu i (t * T w (.inl j)) + ev j (t * T w (.inr i)) := by
    intro i j hij t w
    have h := hT (g2A (tv i j hij t)) w
    rw [g2Act_tv, g2Act_tv] at h
    have e : w + eu i (t * w (.inl j)) + ev j (t * w (.inr i)) =
        w + (eu i (t * w (.inl j)) + ev j (t * w (.inr i))) := add_assoc _ _ _
    rw [e, map_add, add_assoc (T w)] at h
    exact add_left_cancel h
  have hA : ∀ i j, i ≠ j → ∀ t : F,
      T (eu i t) = eu i (t * T (eu j 1) (.inl j)) + ev j (t * T (eu j 1) (.inr i)) := by
    intro i j hij t
    have h := hδ i j hij t (eu j 1)
    simpa [Pi.single_apply, hij, Ne.symm hij] using h
  have hB : ∀ i j, i ≠ j → ∀ t : F,
      T (ev j t) = eu i (t * T (ev i 1) (.inl j)) + ev j (t * T (ev i 1) (.inr i)) := by
    intro i j hij t
    have h := hδ i j hij t (ev i 1)
    simpa [Pi.single_apply, hij, Ne.symm hij] using h
  have hA0 : ∀ i j, i ≠ j → T (eu j 1) (.inr i) = 0 := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := exists_third i j
    have h1 := congrFun (hA i j hij 1) (.inr j)
    have h2 := congrFun (hA i k (Ne.symm hki) 1) (.inr j)
    simp [Ne.symm hkj] at h1 h2
    rw [← h1, h2]
  have hB0 : ∀ i j, i ≠ j → T (ev i 1) (.inl j) = 0 := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := exists_third i j
    have h1 := congrFun (hB i j hij 1) (.inl i)
    have h2 := congrFun (hB k j hkj 1) (.inl i)
    simp [Ne.symm hki] at h1 h2
    rw [← h1, h2]
  have hA' : ∀ i j, i ≠ j → ∀ t : F, T (eu i t) = eu i (t * T (eu j 1) (.inl j)) := by
    intro i j hij t
    rw [hA i j hij t, hA0 i j hij, mul_zero]
    simp
  have hB' : ∀ i j, i ≠ j → ∀ t : F, T (ev j t) = ev j (t * T (ev i 1) (.inr i)) := by
    intro i j hij t
    rw [hB i j hij t, hB0 i j hij, mul_zero]
    simp
  have hcu : ∀ j j' : Fin 3, T (eu j 1) (.inl j) = T (eu j' 1) (.inl j') := by
    intro j j'
    by_cases hjj : j = j'
    · rw [hjj]
    obtain ⟨i, hij, hij'⟩ := exists_third j j'
    have h1 := congrFun (hA' i j hij 1) (.inl i)
    have h2 := congrFun (hA' i j' hij' 1) (.inl i)
    simp at h1 h2
    rw [← h1, h2]
  have hcv : ∀ i i' : Fin 3, T (ev i 1) (.inr i) = T (ev i' 1) (.inr i') := by
    intro i i'
    by_cases hii : i = i'
    · rw [hii]
    obtain ⟨j, hji, hji'⟩ := exists_third i i'
    have h1 := congrFun (hB' i j (Ne.symm hji) 1) (.inr j)
    have h2 := congrFun (hB' i' j (Ne.symm hji') 1) (.inr j)
    simp at h1 h2
    rw [← h1, h2]
  set c := T (eu 0 1) (.inl 0) with hcdef
  set d := T (ev 0 1) (.inr 0) with hddef
  have hu : ∀ i t, T (eu i t) = eu i (t * c) := by
    intro i t
    obtain ⟨j, hji, -⟩ := exists_third i i
    rw [hA' i j (Ne.symm hji) t, hcu j 0]
  have hv : ∀ j t, T (ev j t) = ev j (t * d) := by
    intro j t
    obtain ⟨i, hij, -⟩ := exists_third j j
    rw [hB' i j hij t, hcv i 0]
  have hcd : c = d := by
    have h := hT (g2X ![1, 0, 0]) (ev 0 1)
    have e1 : g2Act (g2X ![1, 0, 0]) (ev 0 (1 : F)) = ev 0 1 + eu 0 1 := by
      rw [g2Act_x0]
      funext k
      rcases k with k | k <;> fin_cases k <;> simp [q6]
    have e2 : g2Act (g2X ![1, 0, 0]) (ev 0 d) = ev 0 d + eu 0 d := by
      rw [g2Act_x0]
      funext k
      rcases k with k | k <;> fin_cases k <;> simp [q6]
    rw [e1, map_add, hv 0 1, hu 0 1, one_mul, one_mul, e2] at h
    have h' := congrFun (add_left_cancel h) (.inl 0)
    simpa using h'
  refine ⟨c, fun x => ?_⟩
  have hsum : x = ∑ k : Ix3, Pi.single k (x k) := (Finset.univ_sum_single x).symm
  rw [hsum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases k with k | k
  · rw [hu, ← Pi.single_smul, smul_eq_mul, mul_comm]
  · rw [hv, ← hcd, ← Pi.single_smul, smul_eq_mul, mul_comm]

theorem commutant_g2Derived {c₀ : F} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (hle : ⁅quasithinG2 F, quasithinG2 F⁆ ≤ cayleyGroup F) (T : (Ix3 → F) →+ (Ix3 → F))
    (hT : ∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      T ((linModelZorn _ hle).lin γ x) = (linModelZorn _ hle).lin γ (T x)) :
    ∃ c : F, ∀ x, T x = c • x := by
  have heq : ⁅quasithinG2 F, quasithinG2 F⁆ = cayleyGroup F := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      cayley_commutator_eq hc0 hc1]
  refine commutant_cayley T fun g x => ?_
  have h := hT ⟨g, heq.ge g.2⟩ x
  rw [linModelZorn_lin, linModelZorn_lin] at h
  exact h

end CFSG.Quasithin.Vol2.Ch11.G2Q8
