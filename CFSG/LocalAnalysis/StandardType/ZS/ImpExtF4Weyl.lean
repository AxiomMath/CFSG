module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.HardMathSupport.Kantor79.CommutatorSpace
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Mat
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Refl
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Pair
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4WeylMem
import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.FFourCoord

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma zmod3_eq_one_or_neg_one {x : ZMod 3} (hx : x ≠ 0) : x = 1 ∨ x = -1 := by
  revert x
  decide

private lemma zmod3_sq_one : (1 : ZMod 3) * 1 = 1 := rfl

private lemma zmod3_sq_neg : (-1 : ZMod 3) * (-1) = 1 := by decide

private lemma zmod3_sum : (2 : ZMod 3) + -1 + -1 = 0 := by decide

private lemma zmod_two_ne_zero_of_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp (le_antisymm hle (Fact.out : p.Prime).two_le)

private lemma sum_single_mul (a : Fin 4) (v : Fin 4 → ZMod p) :
    ∑ l, (Pi.single a (1 : ZMod p) : Fin 4 → ZMod p) l * v l = v a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba; simp [hba]
  · intro ha; exact absurd (Finset.mem_univ a) ha

private lemma mul_self_eq_one_of_conj {f : Module.Basis (Fin 4) (ZMod p) U}
    {k : U ≃ₗ[ZMod p] U} {u κ : Fin 4 → ZMod p}
    (hkmat : LinearMap.toMatrix f f k.toLinearMap = 1 - Matrix.vecMulVec u κ)
    (hbond : ∑ i, κ i * u i = 2) : k * k = 1 := by
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul, hkmat, one_sub_vecMulVec_mul_self hbond]
  simp

private lemma conj_mem_weyl {f : Module.Basis (Fin 4) (ZMod p) U}
    {H G : Subgroup (U ≃ₗ[ZMod p] U)} (hHW : H ≤ basisClosure f weylF4Mats)
    (hFG : basisClosure f weylF4Mats ≤ G)
    (inH : ∀ y ∈ G, IsRefl p y → HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → y ∈ H)
    {x k : U ≃ₗ[ZMod p] U} (hx : x ∈ G) (hk : k ∈ basisClosure f weylF4Mats)
    {v' w' : Fin 4 → ZMod p}
    (hym : LinearMap.toMatrix f f ((k * x * k).toLinearMap) = 1 - Matrix.vecMulVec v' w')
    (hrefl : IsRefl p (k * x * k)) (hroot : v' 3 = 0) (hkk : k * k = 1) :
    x ∈ basisClosure f weylF4Mats := by
  have hkG : k ∈ G := hFG hk
  have hyG : k * x * k ∈ G := G.mul_mem (G.mul_mem hkG hx) hkG
  have hyH : k * x * k ∈ H :=
    inH _ hyG hrefl (movedSpace_le_span_of_toMatrix f hym hroot)
  have hyW : k * x * k ∈ basisClosure f weylF4Mats := hHW hyH
  have hxeq : x = k * (k * x * k) * k := by
    have h : k * (k * x * k) * k = (k * k) * x * (k * k) := by group
    rw [h, hkk, one_mul, mul_one]
  rw [hxeq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hyW) hk

private lemma isRefl_conj_mul_self {x k : U ≃ₗ[ZMod p] U} (h : IsRefl p x) (hkk : k * k = 1) :
    IsRefl p (k * x * k) := by
  have hkkinv : k⁻¹ = k := mul_eq_one_iff_inv_eq.mp hkk
  have := h.conj k
  simpa [hkkinv] using this

private def swapU (i' : Fin 3) : Fin 4 → ZMod p :=
  Pi.single i'.castSucc (1 : ZMod p) - Pi.single 3 (1 : ZMod p)

private lemma swapU_three (i' : Fin 3) : swapU (p := p) i' 3 = -1 := by
  have h3i : (3 : Fin 4) ≠ i'.castSucc := fun h => Fin.castSucc_ne_last i' h.symm
  have h : swapU (p := p) i' 3 = (Pi.single i'.castSucc (1 : ZMod p) : Fin 4 → ZMod p) 3
      - (Pi.single 3 (1 : ZMod p) : Fin 4 → ZMod p) 3 := rfl
  rw [h, Pi.single_eq_of_ne h3i, Pi.single_eq_same]
  norm_num

private lemma swapU_self (i' : Fin 3) : swapU (p := p) i' i'.castSucc = 1 := by
  have hii : i'.castSucc ≠ 3 := Fin.castSucc_ne_last i'
  have h : swapU (p := p) i' i'.castSucc
      = (Pi.single i'.castSucc (1 : ZMod p) : Fin 4 → ZMod p) i'.castSucc
        - (Pi.single 3 (1 : ZMod p) : Fin 4 → ZMod p) i'.castSucc := rfl
  rw [h, Pi.single_eq_same, Pi.single_eq_of_ne hii]
  norm_num

private lemma swapU_bond (i' : Fin 3) : ∑ l, swapU (p := p) i' l * swapU i' l = 2 := by
  have h : ∑ l, swapU (p := p) i' l * swapU i' l
      = (∑ l : Fin 4,
          (Pi.single i'.castSucc (1 : ZMod p) : Fin 4 → ZMod p) l * swapU i' l)
        - ∑ l : Fin 4, (Pi.single 3 (1 : ZMod p) : Fin 4 → ZMod p) l * swapU i' l := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    simp only [swapU, Pi.sub_apply]
    rw [sub_mul]
  rw [h, sum_single_mul, sum_single_mul, swapU_self, swapU_three]
  norm_num

private lemma swapU_root (i' : Fin 3) (v : Fin 4 → ZMod p) :
    ∑ l, swapU (p := p) i' l * v l = v i'.castSucc - v 3 := by
  have h : ∑ l, swapU (p := p) i' l * v l
      = (∑ l : Fin 4,
          (Pi.single i'.castSucc (1 : ZMod p) : Fin 4 → ZMod p) l * v l)
        - ∑ l : Fin 4, (Pi.single 3 (1 : ZMod p) : Fin 4 → ZMod p) l * v l := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    simp only [swapU, Pi.sub_apply]
    rw [sub_mul]
  rw [h, sum_single_mul, sum_single_mul]

private lemma swap_conj_mem_weyl (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {H G : Subgroup (U ≃ₗ[ZMod p] U)} (hHW : H ≤ basisClosure f weylF4Mats)
    (hFG : basisClosure f weylF4Mats ≤ G)
    (inH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hreflx : IsRefl p x) (i' : Fin 3) (hi : v i'.castSucc = 0) :
    x ∈ basisClosure f weylF4Mats := by
  obtain ⟨k, hkW, hkmat⟩ := exists_mem_weylF4_swapRefl hp f i'
  have hkk : k * k = 1 := mul_self_eq_one_of_conj hkmat (swapU_bond (p := p) i')
  let v' : Fin 4 → ZMod p := v - (∑ l, swapU (p := p) i' l * v l) • swapU i'
  let w' : Fin 4 → ZMod p := w - (∑ l, w l * swapU (p := p) i' l) • swapU i'
  refine conj_mem_weyl (v' := v') (w' := w') hHW hFG inH hx hkW ?_
    (isRefl_conj_mul_self hreflx hkk) ?_ hkk
  · have hkmat' : LinearMap.toMatrix f f k.toLinearMap
        = 1 - Matrix.vecMulVec (swapU (p := p) i') (swapU i') := hkmat
    rw [toMatrix_coe_mul, toMatrix_coe_mul, hkmat', hxm,
      one_sub_vecMulVec_conj (swapU_bond (p := p) i')]
  · simp only [v', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, swapU_three, swapU_root, hi]
    ring

private def halfU (ε : Fin 4 → ZMod p) : Fin 4 → ZMod p := Function.update ε 3 (-ε 3)

private lemma halfU_sign {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∀ i, halfU (p := p) ε i = 1 ∨ halfU ε i = -1 := by
  intro i
  by_cases hi : i = 3
  · subst hi
    simp only [halfU, Function.update_apply, if_true]
    rcases hε 3 with h | h <;> rw [h] <;> norm_num
  · simp only [halfU, Function.update_apply, if_neg hi]
    exact hε i

private lemma halfU_three (ε : Fin 4 → ZMod p) : halfU (p := p) ε 3 = -ε 3 := by
  simp only [halfU, Function.update_apply, if_true]

private lemma eps_sq {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) : ε 3 * ε 3 = 1 := by
  rcases hε 3 with h | h <;> rw [h] <;> norm_num

private lemma halfU_bond (hp : p ≠ 2) {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∑ l, ((2 : ZMod p)⁻¹ • halfU (p := p) ε) l * halfU ε l = 2 := by
  have hsq : ∀ l, halfU (p := p) ε l * halfU ε l = 1 := fun l => by
    rcases halfU_sign (p := p) hε l with h | h <;> rw [h] <;> norm_num
  rw [show (∑ l, ((2 : ZMod p)⁻¹ • halfU (p := p) ε) l * halfU ε l)
      = (2 : ZMod p)⁻¹ * ∑ l, halfU (p := p) ε l * halfU ε l by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    simp only [Pi.smul_apply]; ring]
  rw [show (∑ l, halfU (p := p) ε l * halfU ε l) = 4 by
    rw [Fin.sum_univ_four]; simp [hsq]; norm_num]
  rw [show ((2 : ZMod p)⁻¹ * 4 : ZMod p) = 2 by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num, ← mul_assoc,
      inv_mul_cancel₀ (zmod_two_ne_zero_of_ne_two hp), one_mul]]

private lemma halfU_sum {ε v : Fin 4 → ZMod p} (hεv : ∑ i, ε i * v i = 0) :
    ∑ l, halfU (p := p) ε l * v l = -2 * ε 3 * v 3 := by
  have hεv4 : ε 0 * v 0 + ε 1 * v 1 + ε 2 * v 2 + ε 3 * v 3 = 0 := by
    simpa only [Fin.sum_univ_four] using hεv
  simp only [halfU, Function.update_apply, Fin.sum_univ_four]
  simp only [if_neg (by decide : ¬((0 : Fin 4) = 3)),
    if_neg (by decide : ¬((1 : Fin 4) = 3)),
    if_neg (by decide : ¬((2 : Fin 4) = 3)), if_true]
  linear_combination hεv4

private lemma halfU_root (hp : p ≠ 2) {ε v : Fin 4 → ZMod p}
    (hεv : ∑ i, ε i * v i = 0) :
    ∑ l, ((2 : ZMod p)⁻¹ • halfU (p := p) ε) l * v l = -ε 3 * v 3 := by
  rw [show (∑ l, ((2 : ZMod p)⁻¹ • halfU (p := p) ε) l * v l)
      = (2 : ZMod p)⁻¹ * ∑ l, halfU (p := p) ε l * v l by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    simp only [Pi.smul_apply]; ring]
  rw [halfU_sum hεv]
  rw [show ((2 : ZMod p)⁻¹ * (-2 * ε 3 * v 3) : ZMod p) = -ε 3 * v 3 by
    have h2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
      mul_inv_cancel₀ (zmod_two_ne_zero_of_ne_two hp)
    linear_combination (-(ε 3 * v 3)) * h2]

private lemma half_conj_mem_weyl (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {H G : Subgroup (U ≃ₗ[ZMod p] U)} (hHW : H ≤ basisClosure f weylF4Mats)
    (hFG : basisClosure f weylF4Mats ≤ G)
    (inH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hreflx : IsRefl p x) {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hεv : ∑ i, ε i * v i = 0) :
    x ∈ basisClosure f weylF4Mats := by
  obtain ⟨k, hkW, hkmat⟩ := exists_mem_weylF4_halfRefl hp f (halfU_sign (p := p) hε)
  have hkk : k * k = 1 := mul_self_eq_one_of_conj hkmat (halfU_bond (p := p) hp hε)
  let v' : Fin 4 → ZMod p := v - (∑ l, ((2 : ZMod p)⁻¹ • halfU (p := p) ε) l * v l) • halfU ε
  let w' : Fin 4 → ZMod p := w - (∑ l, w l * halfU (p := p) ε l) • ((2 : ZMod p)⁻¹ • halfU ε)
  refine conj_mem_weyl (v' := v') (w' := w') hHW hFG inH hx hkW ?_
    (isRefl_conj_mul_self hreflx hkk) ?_ hkk
  · rw [toMatrix_coe_mul, toMatrix_coe_mul, hkmat, hxm,
      one_sub_vecMulVec_conj (halfU_bond (p := p) hp hε)]
  · simp only [v', Pi.sub_apply]
    rw [halfU_root (p := p) hp hεv]
    simp only [Pi.smul_apply, halfU_three, smul_eq_mul]
    rw [show -ε 3 * v 3 * -ε 3 = v 3 * (ε 3 * ε 3) by ring, eps_sq hε, mul_one]
    ring

theorem mem_weylF4_of_short_zero (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {H G : Subgroup (U ≃ₗ[ZMod p] U)} (hHW : H ≤ basisClosure f weylF4Mats)
    (hFG : basisClosure f weylF4Mats ≤ G)
    (inH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hz : (∃ i, v i = 0) ∨
      ∃ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∑ i, ε i * v i = 0) :
    x ∈ basisClosure f weylF4Mats := by
  have hreflx : IsRefl p x := isRefl_of_toMatrix hp f hxm hwv
  rcases hz with ⟨i, hi⟩ | ⟨ε, hε, hεv⟩
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · exact swap_conj_mem_weyl hp hHW hFG inH hx hxm hreflx i' hi
    · exact hHW (inH x hx hreflx (movedSpace_le_span_of_toMatrix f hxm hi))
  · exact half_conj_mem_weyl hp hHW hFG inH hx hxm hreflx hε hεv

theorem short_zero_of_eq_three (hp : p = 3) (v : Fin 4 → ZMod p) :
    (∃ i, v i = 0) ∨
      ∃ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∑ i, ε i * v i = 0 := by
  subst hp
  by_cases h : ∃ i, v i = 0
  · exact Or.inl h
  · push Not at h
    refine Or.inr ⟨![v 0, v 1, -v 2, -v 3], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp
      · exact zmod3_eq_one_or_neg_one (h 0)
      · exact zmod3_eq_one_or_neg_one (h 1)
      · rcases zmod3_eq_one_or_neg_one (h 2) with h2 | h2
        · rw [h2]; exact Or.inr rfl
        · rw [h2]; exact Or.inl (neg_neg 1)
      · rcases zmod3_eq_one_or_neg_one (h 3) with h3 | h3
        · rw [h3]; exact Or.inr rfl
        · rw [h3]; exact Or.inl (neg_neg 1)
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      have h0 : v 0 * v 0 = 1 := by
        rcases zmod3_eq_one_or_neg_one (h 0) with h0 | h0
        · rw [h0]; exact zmod3_sq_one
        · rw [h0]; exact zmod3_sq_neg
      have h1 : v 1 * v 1 = 1 := by
        rcases zmod3_eq_one_or_neg_one (h 1) with h1 | h1
        · rw [h1]; exact zmod3_sq_one
        · rw [h1]; exact zmod3_sq_neg
      have h2 : v 2 * v 2 = 1 := by
        rcases zmod3_eq_one_or_neg_one (h 2) with h2 | h2
        · rw [h2]; exact zmod3_sq_one
        · rw [h2]; exact zmod3_sq_neg
      have h3 : v 3 * v 3 = 1 := by
        rcases zmod3_eq_one_or_neg_one (h 3) with h3 | h3
        · rw [h3]; exact zmod3_sq_one
        · rw [h3]; exact zmod3_sq_neg
      have e2 : (-v 2) * v 2 = -(v 2 * v 2) := neg_mul _ _
      have e3 : (-v 3) * v 3 = -(v 3 * v 3) := neg_mul _ _
      rw [e2, e3, h0, h1, h2, h3]
      exact zmod3_sum

private lemma zmod_two_ne_zero_of_five_le (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private lemma eq_zero_of_sum_eq_zero_of_eq_zero_or (hp5 : 5 ≤ p) {c : ZMod p} (hc : c ≠ 0)
    {y : Fin 4 → ZMod p} (hy : ∀ i, y i = 0 ∨ y i = c) (h : ∑ i, y i = 0) :
    ∀ i, y i = 0 := by
  have hy' : ∀ i, y i = c * (if y i = c then (1 : ZMod p) else 0) := by
    intro i
    rcases hy i with hi | hi
    · rw [hi, if_neg (fun h0 : (0 : ZMod p) = c => hc h0.symm)]
      ring
    · rw [hi, if_pos rfl]
      ring
  have hsum : ∑ i, y i = c * ((Finset.univ.filter (fun i => y i = c)).card : ZMod p) := by
    calc ∑ i, y i = ∑ i, c * (if y i = c then (1 : ZMod p) else 0) :=
          Finset.sum_congr rfl (fun i _ => hy' i)
      _ = c * ∑ i, (if y i = c then (1 : ZMod p) else 0) := by rw [Finset.mul_sum]
      _ = c * ((Finset.univ.filter (fun i => y i = c)).card : ZMod p) := by
          rw [← Finset.natCast_card_filter (R := ZMod p) (p := fun i => y i = c)
            (s := Finset.univ)]
  have hc0 : ((Finset.univ.filter (fun i => y i = c)).card : ZMod p) = 0 := by
    have : c * ((Finset.univ.filter (fun i => y i = c)).card : ZMod p) = c * 0 := by
      rw [← hsum, h, mul_zero]
    exact mul_left_cancel₀ hc this
  have hdvd : p ∣ (Finset.univ.filter (fun i => y i = c)).card :=
    (ZMod.natCast_eq_zero_iff _ p).mp hc0
  have hlt : (Finset.univ.filter (fun i => y i = c)).card < p := by
    calc (Finset.univ.filter (fun i => y i = c)).card ≤ Fintype.card (Fin 4) :=
          Finset.card_le_univ _
      _ = 4 := Fintype.card_fin 4
      _ < p := by omega
  have hs0 : (Finset.univ.filter (fun i => y i = c)).card = 0 := by
    by_contra hne
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) (not_le.mpr hlt)
  have hse : Finset.univ.filter (fun i => y i = c) = ∅ := Finset.card_eq_zero.mp hs0
  intro i
  rcases hy i with hi | hi
  · exact hi
  · exfalso
    have : i ∈ Finset.univ.filter (fun i => y i = c) := by simp [hi]
    rw [hse] at this
    simp at this

private lemma frame_eq_two {F : Fin 4 → ZMod p} (hp5 : 5 ≤ p)
    (hF : ∀ i, F i = 2 ∨ F i = 4) (hsum : ∑ i, F i = 8) : ∀ i, F i = 2 := by
  have hy : ∀ i, F i - 2 = 0 ∨ F i - 2 = 2 := by
    intro i
    rcases hF i with h | h <;> rw [h] <;> norm_num
  have hsum' : ∑ i, (F i - 2) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have h0 := eq_zero_of_sum_eq_zero_of_eq_zero_or (p := p) hp5 (c := 2)
    (zmod_two_ne_zero_of_five_le hp5) hy hsum'
  intro i
  have := h0 i
  rwa [sub_eq_zero] at this

private lemma frame_sum_eq (fr : Fin 4 → Fin 4 → ZMod p) (frZ : Fin 4 → Fin 4 → ℤ)
    (hcast : ∀ k i, fr k i = ((frZ k i : ℤ) : ZMod p))
    (horth : ∀ i j, (∑ k, frZ k i * frZ k j) = if i = j then 4 else 0)
    (v w : Fin 4 → ZMod p) :
    (∑ k, (∑ i, fr k i * v i) * (∑ j, fr k j * w j)) = 4 * ∑ i, v i * w i := by
  have hcast_sum : ∀ i j, (∑ k, fr k i * fr k j) = ((∑ k, frZ k i * frZ k j : ℤ) : ZMod p) := by
    intro i j
    calc ∑ k, fr k i * fr k j
        = ∑ k, ((frZ k i * frZ k j : ℤ) : ZMod p) := by
            apply Finset.sum_congr rfl; intro k _
            rw [hcast k i, hcast k j, ← Int.cast_mul]
      _ = ((∑ k, frZ k i * frZ k j : ℤ) : ZMod p) := by rw [Int.cast_sum]
  have hexp : ∀ k, (∑ i, fr k i * v i) * (∑ j, fr k j * w j)
      = ∑ i, ∑ j, (fr k i * fr k j) * (v i * w j) := by
    intro k
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  calc ∑ k, (∑ i, fr k i * v i) * (∑ j, fr k j * w j)
      = ∑ k, ∑ i, ∑ j, (fr k i * fr k j) * (v i * w j) := by
          apply Finset.sum_congr rfl; intro k _; exact hexp k
    _ = ∑ i, ∑ k, ∑ j, (fr k i * fr k j) * (v i * w j) := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ k, (fr k i * fr k j) * (v i * w j) := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (∑ k, fr k i * fr k j) * (v i * w j) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (if i = j then (4 : ZMod p) else 0) * (v i * w j) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          have hite : ((if i = j then (4 : ℤ) else 0 : ℤ) : ZMod p) =
              if i = j then 4 else 0 := by split <;> simp
          rw [hcast_sum i j, horth i j, hite]
    _ = ∑ i, 4 * (v i * w i) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [show ¬ (i = j) from fun h => hji h.symm]
          · intro hi; exact absurd (Finset.mem_univ i) hi
    _ = 4 * ∑ i, v i * w i := by rw [Finset.mul_sum]

private lemma sum_update_mul (ε u : Fin 4 → ZMod p) (i : Fin 4) :
    ∑ l, Function.update ε i (-ε i) l * u l = (∑ l, ε l * u l) - 2 * (ε i * u i) := by
  have hupdate : ∑ l, Function.update ε i (-ε i) l * u l
      = ∑ l ∈ Finset.univ.erase i, ε l * u l + (-ε i * u i) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun l => Function.update ε i (-ε i) l * u l) (Finset.mem_univ i)]
    congr 1
    · apply Finset.sum_congr rfl
      intro l hl
      rw [Function.update_apply, if_neg (Finset.mem_erase.mp hl).1]
    · rw [Function.update_apply, if_pos rfl]
  have hsplit : ∑ l ∈ Finset.univ.erase i, ε l * u l + ε i * u i = ∑ l, ε l * u l :=
    Finset.sum_erase_add Finset.univ (fun l => ε l * u l) (Finset.mem_univ i)
  rw [hupdate, ← hsplit]
  ring

private lemma update_prod_sub {v w : Fin 4 → ZMod p} (i : Fin 4) (ε : Fin 4 → ZMod p) :
    (∑ l, Function.update ε i (-ε i) l * v l) *
        (∑ l, Function.update ε i (-ε i) l * w l)
      - (∑ l, ε l * v l) * (∑ l, ε l * w l)
    = -2 * ε i * ∑ l ∈ Finset.univ.erase i, ε l * (v i * w l + v l * w i) := by
  have hv := sum_update_mul ε v i
  have hw := sum_update_mul ε w i
  have hA : ∑ l, ε l * v l = ε i * v i + ∑ l ∈ Finset.univ.erase i, ε l * v l := by
    have h := Finset.sum_erase_add Finset.univ (fun l => ε l * v l) (Finset.mem_univ i)
    rw [add_comm]
    exact h.symm
  have hB : ∑ l, ε l * w l = ε i * w i + ∑ l ∈ Finset.univ.erase i, ε l * w l := by
    have h := Finset.sum_erase_add Finset.univ (fun l => ε l * w l) (Finset.mem_univ i)
    rw [add_comm]
    exact h.symm
  have hC : ∑ l ∈ Finset.univ.erase i, ε l * (v i * w l + v l * w i)
      = v i * (∑ l ∈ Finset.univ.erase i, ε l * w l)
        + w i * (∑ l ∈ Finset.univ.erase i, ε l * v l) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hv, hw, hA, hB, hC]
  ring

private def fr1Z : Fin 4 → Fin 4 → ℤ :=
  ![![1,1,1,1], ![1,1,-1,-1], ![1,-1,1,-1], ![1,-1,-1,1]]

private def fr2Z : Fin 4 → Fin 4 → ℤ :=
  ![![1,1,1,-1], ![1,1,-1,1], ![1,-1,1,1], ![1,-1,-1,-1]]

private def fr1 (p : ℕ) : Fin 4 → Fin 4 → ZMod p := fun k i => ((fr1Z k i : ℤ) : ZMod p)

private def fr2 (p : ℕ) : Fin 4 → Fin 4 → ZMod p := fun k i => ((fr2Z k i : ℤ) : ZMod p)

private lemma fr1_sign : ∀ k i, fr1 p k i = 1 ∨ fr1 p k i = -1 := by
  intro k i
  have h : fr1Z k i = 1 ∨ fr1Z k i = -1 := by fin_cases k <;> fin_cases i <;> decide
  rcases h with h | h
  · left; rw [show fr1 p k i = ((fr1Z k i : ℤ) : ZMod p) from rfl, h, Int.cast_one]
  · right
    rw [show fr1 p k i = ((fr1Z k i : ℤ) : ZMod p) from rfl, h, Int.cast_neg, Int.cast_one]

private lemma fr2_sign : ∀ k i, fr2 p k i = 1 ∨ fr2 p k i = -1 := by
  intro k i
  have h : fr2Z k i = 1 ∨ fr2Z k i = -1 := by fin_cases k <;> fin_cases i <;> decide
  rcases h with h | h
  · left; rw [show fr2 p k i = ((fr2Z k i : ℤ) : ZMod p) from rfl, h, Int.cast_one]
  · right
    rw [show fr2 p k i = ((fr2Z k i : ℤ) : ZMod p) from rfl, h, Int.cast_neg, Int.cast_one]

private lemma fr1_orth : ∀ i j : Fin 4, (∑ k, fr1Z k i * fr1Z k j) = if i = j then 4 else 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> decide

private lemma fr2_orth : ∀ i j : Fin 4, (∑ k, fr2Z k i * fr2Z k j) = if i = j then 4 else 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> decide

private lemma frame_value1 {v w : Fin 4 → ZMod p} (hp5 : 5 ≤ p)
    (hvw : ∑ i, v i * w i = 2)
    (hhalf : ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2 ∨
        (∑ i, ε i * v i) * (∑ i, ε i * w i) = 4) :
    ∀ k, (∑ i, fr1 p k i * v i) * (∑ i, fr1 p k i * w i) = 2 := by
  refine frame_eq_two hp5 (fun k => hhalf (fr1 p k) (fr1_sign (p := p) k)) ?_
  rw [frame_sum_eq (fr1 p) fr1Z (fun k i => rfl) fr1_orth v w, hvw]
  norm_num

private lemma frame_value2 {v w : Fin 4 → ZMod p} (hp5 : 5 ≤ p)
    (hvw : ∑ i, v i * w i = 2)
    (hhalf : ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2 ∨
        (∑ i, ε i * v i) * (∑ i, ε i * w i) = 4) :
    ∀ k, (∑ i, fr2 p k i * v i) * (∑ i, fr2 p k i * w i) = 2 := by
  refine frame_eq_two hp5 (fun k => hhalf (fr2 p k) (fr2_sign (p := p) k)) ?_
  rw [frame_sum_eq (fr2 p) fr2Z (fun k i => rfl) fr2_orth v w, hvw]
  norm_num

private lemma canon_value {v w : Fin 4 → ZMod p}
    (hF1 : ∀ k, (∑ i, fr1 p k i * v i) * (∑ i, fr1 p k i * w i) = 2)
    (hF2 : ∀ k, (∑ i, fr2 p k i * v i) * (∑ i, fr2 p k i * w i) = 2) :
    ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) → ε 0 = 1 →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2 := by
  intro ε hε h0
  rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;> rcases hε 3 with h3 | h3
  · rw [show ε = fr1 p 0 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr1, fr1Z]]
    exact hF1 0
  · rw [show ε = fr2 p 0 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr2, fr2Z]]
    exact hF2 0
  · rw [show ε = fr2 p 1 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr2, fr2Z]]
    exact hF2 1
  · rw [show ε = fr1 p 1 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr1, fr1Z]]
    exact hF1 1
  · rw [show ε = fr2 p 2 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr2, fr2Z]]
    exact hF2 2
  · rw [show ε = fr1 p 2 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr1, fr1Z]]
    exact hF1 2
  · rw [show ε = fr1 p 3 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr1, fr1Z]]
    exact hF1 3
  · rw [show ε = fr2 p 3 by funext i; fin_cases i <;> simp [h0, h1, h2, h3, fr2, fr2Z]]
    exact hF2 3

private lemma hall_value {v w : Fin 4 → ZMod p}
    (hcanon : ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) → ε 0 = 1 →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2) :
    ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2 := by
  intro ε hε
  by_cases h0 : ε 0 = 1
  · exact hcanon ε hε h0
  · have h0' : ε 0 = -1 := (hε 0).resolve_left h0
    have hne : (-ε) 0 = 1 := by simp only [Pi.neg_apply, h0']; norm_num
    have hsign : ∀ i, (-ε) i = 1 ∨ (-ε) i = -1 := by
      intro i
      rcases hε i with hi | hi <;> simp only [Pi.neg_apply, hi] <;> norm_num
    have h := hcanon (-ε) hsign hne
    have hneg : (∑ i, (-ε) i * v i) * (∑ i, (-ε) i * w i)
        = (∑ i, ε i * v i) * (∑ i, ε i * w i) := by
      have h1 : ∑ i, (-ε) i * v i = -(∑ i, ε i * v i) := by
        simp [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      have h2 : ∑ i, (-ε) i * w i = -(∑ i, ε i * w i) := by
        simp [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      rw [h1, h2]; ring
    rwa [hneg] at h

private lemma row_sum_zero {v w : Fin 4 → ZMod p} (hp5 : 5 ≤ p)
    (hall : ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2) :
    ∀ (i : Fin 4) (ε : Fin 4 → ZMod p), (∀ l, ε l = 1 ∨ ε l = -1) →
      ∑ l ∈ Finset.univ.erase i, ε l * (v i * w l + v l * w i) = 0 := by
  intro i ε hε
  have hupd : ∀ l, Function.update ε i (-ε i) l = 1 ∨ Function.update ε i (-ε i) l = -1 := by
    intro l
    rw [Function.update_apply]
    by_cases hl : l = i
    · rw [if_pos hl]
      rcases hε i with hi | hi
      · rw [hi]; exact Or.inr rfl
      · rw [hi]; exact Or.inl (neg_neg 1)
    · rw [if_neg hl]
      exact hε l
  have h1 := hall ε hε
  have h2 := hall (Function.update ε i (-ε i)) hupd
  have hsub := update_prod_sub (v := v) (w := w) i ε
  have hzero : -2 * ε i * ∑ l ∈ Finset.univ.erase i, ε l * (v i * w l + v l * w i) = 0 := by
    rw [← hsub, h2, h1]
    ring
  have hεne : ε i ≠ 0 := by
    rcases hε i with hi | hi
    · rw [hi]; exact one_ne_zero
    · rw [hi]; exact neg_ne_zero.mpr one_ne_zero
  exact (mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero (neg_ne_zero.mpr (zmod_two_ne_zero_of_five_le hp5)) hεne)

private lemma s_ij_zero {v w : Fin 4 → ZMod p} (hp5 : 5 ≤ p)
    (hrow : ∀ (i : Fin 4) (ε : Fin 4 → ZMod p), (∀ l, ε l = 1 ∨ ε l = -1) →
      ∑ l ∈ Finset.univ.erase i, ε l * (v i * w l + v l * w i) = 0) :
    ∀ i j : Fin 4, i ≠ j → v i * w j + v j * w i = 0 := by
  intro i j hij
  have hε1 : ∀ l, (fun _ : Fin 4 => (1 : ZMod p)) l = 1 ∨
      (fun _ : Fin 4 => (1 : ZMod p)) l = -1 := by
    intro l; left; rfl
  have hε2 : ∀ l, (Function.update (fun _ : Fin 4 => (1 : ZMod p)) i (-1)) l = 1 ∨
      (Function.update (fun _ : Fin 4 => (1 : ZMod p)) i (-1)) l = -1 := by
    intro l
    rw [Function.update_apply]
    by_cases hl : l = i
    · rw [if_pos hl]; norm_num
    · rw [if_neg hl]; exact Or.inl rfl
  have h1 := hrow j (fun _ : Fin 4 => (1 : ZMod p)) hε1
  have h2 := hrow j (Function.update (fun _ : Fin 4 => (1 : ZMod p)) i (-1)) hε2
  have hdiff : (∑ l ∈ Finset.univ.erase j, (fun _ : Fin 4 => (1 : ZMod p)) l
          * (v j * w l + v l * w j))
      - ∑ l ∈ Finset.univ.erase j,
          (Function.update (fun _ : Fin 4 => (1 : ZMod p)) i (-1)) l
            * (v j * w l + v l * w j)
      = 2 * (1 : ZMod p) * (v j * w i + v i * w j) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp only [Function.update_apply, if_true]
      ring
    · intro l _ hl
      rw [Function.update_apply, if_neg hl]
      ring
    · intro hi
      exact absurd (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) hi
  have hz : 2 * (1 : ZMod p) * (v j * w i + v i * w j) = 0 := by
    rw [← hdiff, h1, h2]
    ring
  have hres := (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (zmod_two_ne_zero_of_five_le hp5) one_ne_zero)
  simpa only [add_comm] using hres

private lemma coord_one {v w : Fin 4 → ZMod p} (hp5 : 5 ≤ p)
    (hwv : ∑ i, w i * v i = 2)
    (hcoord : ∀ i, 2 * (v i * w i) = 1 ∨ 2 * (v i * w i) = 2) :
    ∀ i, 2 * (v i * w i) = 1 := by
  have hvw : ∑ i, v i * w i = 2 := by
    rw [show (∑ i, v i * w i) = ∑ i, w i * v i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hwv]
  have hcoord_sum : ∑ i, 2 * (v i * w i) = 4 := by
    rw [← Finset.mul_sum, hvw]
    norm_num
  have hcoord_y : ∀ i, 2 * (v i * w i) - 1 = 0 ∨ 2 * (v i * w i) - 1 = 1 := by
    intro i
    rcases hcoord i with h | h <;> rw [h] <;> norm_num
  have hcoord_sum_y : ∑ i, (2 * (v i * w i) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hcoord_sum]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h0 := eq_zero_of_sum_eq_zero_of_eq_zero_or (p := p) hp5 (c := 1) one_ne_zero
    hcoord_y hcoord_sum_y
  intro i
  have := h0 i
  rwa [sub_eq_zero] at this

theorem false_of_short_bonds (hp5 : 5 ≤ p) {v w : Fin 4 → ZMod p}
    (hwv : ∑ i, w i * v i = 2)
    (hcoord : ∀ i, 2 * (v i * w i) = 1 ∨ 2 * (v i * w i) = 2)
    (hhalf : ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2 ∨
        (∑ i, ε i * v i) * (∑ i, ε i * w i) = 4) :
    False := by
  have hvw : ∑ i, v i * w i = 2 := by
    rw [show (∑ i, v i * w i) = ∑ i, w i * v i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hwv]
  have hcoord1 := coord_one hp5 hwv hcoord
  have hF1 := frame_value1 hp5 hvw hhalf
  have hF2 := frame_value2 hp5 hvw hhalf
  have hq := s_ij_zero hp5 (row_sum_zero hp5 (hall_value (canon_value hF1 hF2)))
  have hv0_ne : v 0 ≠ 0 := by
    intro h
    have h0 := hcoord1 0
    rw [h] at h0
    simp at h0
  have hsq01 : v 0 * v 0 + v 1 * v 1 = 0 := by
    have hs := hq 0 1 (by norm_num)
    have h0 := hcoord1 0
    have h1 := hcoord1 1
    linear_combination 2 * (v 0 * v 1) * hs - v 1 * v 1 * h0 - v 0 * v 0 * h1
  have hsq02 : v 0 * v 0 + v 2 * v 2 = 0 := by
    have hs := hq 0 2 (by norm_num)
    have h0 := hcoord1 0
    have h2 := hcoord1 2
    linear_combination 2 * (v 0 * v 2) * hs - v 2 * v 2 * h0 - v 0 * v 0 * h2
  have hsq12 : v 1 * v 1 + v 2 * v 2 = 0 := by
    have hs := hq 1 2 (by norm_num)
    have h1 := hcoord1 1
    have h2 := hcoord1 2
    linear_combination 2 * (v 1 * v 2) * hs - v 2 * v 2 * h1 - v 1 * v 1 * h2
  have h2v0 : 2 * (v 0 * v 0) = 0 := by
    linear_combination hsq01 + hsq02 - hsq12
  have htwo : (2 : ZMod p) = 0 := by
    have := mul_eq_zero.mp h2v0
    exact this.resolve_right (mul_ne_zero hv0_ne hv0_ne)
  exact absurd htwo (zmod_two_ne_zero_of_five_le hp5)

private lemma coord_bonds_of_not_weyl (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hd : DMax p G 4) (hF : basisClosure f weylF4Mats ≤ G)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv : ∀ i, v i ≠ 0)
    (hxW : x ∉ basisClosure f weylF4Mats) :
    ∀ i, 2 * (v i * w i) = 1 ∨ 2 * (v i * w i) = 2 := by
  intro i
  obtain ⟨k, hkW, hkmat⟩ := exists_mem_weylF4_coordRefl hp f i
  have hkG : k ∈ G := hF hkW
  have hne : x ≠ k := fun h => hxW (h ▸ hkW)
  have hκρ : ∑ l, (Pi.single i (2 : ZMod p) : Fin 4 → ZMod p) l
      * (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l = 2 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi; simp [hbi]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have heta := etaOK_four_of_toMatrix hp hd f hxG hkG hne hxm hwv hkmat hκρ
  have hw1 : (∑ l, w l * (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l) = w i := by
    calc ∑ l, w l * (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l
        = ∑ l, (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l * w l := by
          apply Finset.sum_congr rfl; intro l _; ring
      _ = w i := sum_single_mul i w
  have hv2 : (∑ l, (Pi.single i (2 : ZMod p) : Fin 4 → ZMod p) l * v l) = 2 * v i := by
    calc ∑ l, (Pi.single i (2 : ZMod p) : Fin 4 → ZMod p) l * v l
        = ∑ l, 2 * ((Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l * v l) := by
          apply Finset.sum_congr rfl; intro l _
          by_cases hl : l = i <;> simp [hl]
      _ = 2 * ∑ l, (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l * v l := by
          rw [Finset.mul_sum]
      _ = 2 * v i := by rw [sum_single_mul]
  rw [hw1, hv2] at heta
  have ht : 2 * v i ≠ 0 := mul_ne_zero (zmod_two_ne_zero_of_ne_two hp) (hv i)
  rcases mul_eq_one_or_two_of_etaOK_four heta ht with h | h
  · left; linear_combination h
  · right; linear_combination h

private lemma half_root_bond (hp : p ≠ 2) {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∑ l, ((2 : ZMod p)⁻¹ • ε) l * ε l = 2 := by
  have hsq : ∀ l, ε l * ε l = 1 := fun l => by
    rcases hε l with h | h <;> rw [h] <;> norm_num
  rw [show (∑ l, ((2 : ZMod p)⁻¹ • ε) l * ε l)
      = (2 : ZMod p)⁻¹ * ∑ l, ε l * ε l by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    simp only [Pi.smul_apply]; ring]
  rw [show (∑ l, ε l * ε l) = 4 by rw [Fin.sum_univ_four]; simp [hsq]; norm_num]
  rw [show ((2 : ZMod p)⁻¹ * 4 : ZMod p) = 2 by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num, ← mul_assoc,
      inv_mul_cancel₀ (zmod_two_ne_zero_of_ne_two hp), one_mul]]

private lemma half_bonds_of_not_weyl (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hd : DMax p G 4) (hF : basisClosure f weylF4Mats ≤ G)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hv : ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) → ∑ i, ε i * v i ≠ 0)
    (hxW : x ∉ basisClosure f weylF4Mats) :
    ∀ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∑ i, ε i * v i) * (∑ i, ε i * w i) = 2 ∨
        (∑ i, ε i * v i) * (∑ i, ε i * w i) = 4 := by
  intro ε hε
  obtain ⟨k, hkW, hkmat⟩ := exists_mem_weylF4_halfRefl hp f hε
  have hkG : k ∈ G := hF hkW
  have hne : x ≠ k := fun h => hxW (h ▸ hkW)
  have hκρ := half_root_bond hp hε
  have heta := etaOK_four_of_toMatrix hp hd f hxG hkG hne hxm hwv hkmat hκρ
  have hw1 : (∑ l, w l * ε l) = ∑ l, ε l * w l := by
    apply Finset.sum_congr rfl; intro l _; ring
  have hv2 : (∑ l, ((2 : ZMod p)⁻¹ • ε) l * v l)
      = (2 : ZMod p)⁻¹ * ∑ l, ε l * v l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    simp only [Pi.smul_apply]; ring
  rw [hw1, hv2] at heta
  have ht : (2 : ZMod p)⁻¹ * (∑ l, ε l * v l) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (zmod_two_ne_zero_of_ne_two hp)) (hv ε hε)
  have hconv : (∑ i, ε i * v i) * (∑ i, ε i * w i)
      = 2 * ((∑ i, ε i * w i) * ((2 : ZMod p)⁻¹ * ∑ i, ε i * v i)) := by
    rw [show (2 : ZMod p) * ((∑ i, ε i * w i) * ((2 : ZMod p)⁻¹ * ∑ i, ε i * v i))
        = (2 * (2 : ZMod p)⁻¹) * ((∑ i, ε i * w i) * (∑ i, ε i * v i)) by ring,
      mul_inv_cancel₀ (zmod_two_ne_zero_of_ne_two hp), one_mul, mul_comm]
  rcases mul_eq_one_or_two_of_etaOK_four heta ht with h | h
  · left; rw [hconv, h, mul_one]
  · right; rw [hconv, h]; ring

theorem le_weylF4_of_inH (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : ReflGen p G) (hd : DMax p G 4) (hF : basisClosure f weylF4Mats ≤ G)
    (hHW : H ≤ basisClosure f weylF4Mats)
    (inH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H) :
    G ≤ basisClosure f weylF4Mats := by
  rw [hG, Subgroup.closure_le]
  rintro x ⟨hxG, hxrefl⟩
  obtain ⟨v, w, hxm, hwv⟩ := exists_toMatrix_of_isRefl hp f hxrefl
  by_cases hz : (∃ i, v i = 0) ∨
      ∃ ε : Fin 4 → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∑ i, ε i * v i = 0
  · exact mem_weylF4_of_short_zero hp hHW hF inH hxG hxm hwv hz
  · push Not at hz
    have hp3 : p ≠ 3 := by
      intro h3
      subst h3
      rcases short_zero_of_eq_three rfl v with ⟨i, hi⟩ | ⟨ε, hε, hsum⟩
      · exact hz.1 i hi
      · exact hz.2 ε hε hsum
    have hp5 : 5 ≤ p := (Fact.out : p.Prime).five_le_of_ne_two_of_ne_three hp hp3
    by_contra hxW
    exact false_of_short_bonds hp5 hwv
      (coord_bonds_of_not_weyl hp hd hF hxG hxm hwv hz.1 hxW)
      (half_bonds_of_not_weyl hp hd hF hxG hxm hwv hz.2 hxW)

end CFSG.StandardType.ZS.FFourCoord

end
