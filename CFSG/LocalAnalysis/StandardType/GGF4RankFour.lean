module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import CFSG.LocalAnalysis.StandardType.GGF4WeylQuad
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType.F4Model

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem IsRefl.mul_self {R : F4Rep W} {t : W} (ht : R.IsRefl t) : t * t = 1 := by
  obtain ⟨g, j, rfl⟩ := ht
  have h : g * R.s j * g⁻¹ * (g * R.s j * g⁻¹) = g * (R.s j * R.s j) * g⁻¹ := by group
  rw [h, R.s_sq, mul_one, mul_inv_cancel]

theorem ord_mat {a b : W} {x y : M4} (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat) {n : ℕ}
    (h : orderOf (a * b) = n) : orderOf ((x.mul y).toMat) = n := by
  rw [← R.rho_mul ha hb, orderOf_injective R.ρ R.inj, h]

theorem ord2b_of {a b : W} {x y : M4} (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat)
    (h : orderOf (a * b) = 2) : ord2b x y = true := by
  have h' := R.ord_mat ha hb h
  rw [ord2b_iff]
  refine ⟨?_, ?_⟩
  · apply M4.toMat_injective
    rw [M4.toMat_pw2, M4.toMat_one, ← pow_two]
    have hp := pow_orderOf_eq_one ((x.mul y).toMat)
    rwa [h'] at hp
  · intro hone
    rw [hone, M4.toMat_one, orderOf_one] at h'
    omega

theorem ord3b_of {a b : W} {x y : M4} (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat)
    (h : orderOf (a * b) = 3) : ord3b x y = true := by
  have h' := R.ord_mat ha hb h
  rw [ord3b_iff]
  refine ⟨?_, ?_⟩
  · apply M4.toMat_injective
    rw [M4.toMat_pw3, M4.toMat_one, ← pow_three]
    have hp := pow_orderOf_eq_one ((x.mul y).toMat)
    rwa [h'] at hp
  · intro hone
    rw [hone, M4.toMat_one, orderOf_one] at h'
    omega

theorem ord4b_of {a b : W} {x y : M4} (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat)
    (h : orderOf (a * b) = 4) : ord4b x y = true := by
  have h' := R.ord_mat ha hb h
  rw [ord4b_iff]
  refine ⟨?_, ?_⟩
  · apply M4.toMat_injective
    rw [M4.toMat_pw4, M4.toMat_one]
    have hp := pow_orderOf_eq_one ((x.mul y).toMat)
    rw [h', pow_four_eq] at hp
    exact hp
  · intro hpw
    have h2 := congrArg M4.toMat hpw
    rw [M4.toMat_pw2, M4.toMat_one, ← pow_two] at h2
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h']; norm_num) h2

@[expose] def wdF (a : Fin 4 → W) (l : List (Fin 4)) : W := (l.map a).prod

theorem wdF_append (a : Fin 4 → W) (l l' : List (Fin 4)) :
    wdF a (l ++ l') = wdF a l * wdF a l' := by
  simp [wdF]

theorem wdF_reverse {a : Fin 4 → W} (hinv : ∀ i, a i * a i = 1) (l : List (Fin 4)) :
    wdF a l.reverse = (wdF a l)⁻¹ := by
  have hai : ∀ i, (a i)⁻¹ = a i := fun i => inv_eq_of_mul_eq_one_right (hinv i)
  induction l with
  | nil => simp [wdF]
  | cons i l ih =>
    have h1 : wdF a (i :: l).reverse = wdF a l.reverse * a i := by simp [wdF]
    have h2 : wdF a (i :: l) = a i * wdF a l := by simp [wdF]
    rw [h1, h2, mul_inv_rev, ih, hai i]

theorem wdF_mem (H : Subgroup W) {a : Fin 4 → W} (haH : ∀ i, a i ∈ H) (l : List (Fin 4)) :
    wdF a l ∈ H := by
  unfold wdF
  apply list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact haH i

theorem rho_wdF {a : Fin 4 → W} {x : Fin 4 → M4} (hx : ∀ i, R.ρ (a i) = (x i).toMat)
    (l : List (Fin 4)) : R.ρ (wdF a l) = (evalG x l).toMat := by
  induction l with
  | nil => simp [wdF, evalG, M4.toMat_one]
  | cons i l ih =>
    have h : wdF a (i :: l) = a i * wdF a l := by simp [wdF]
    rw [h, map_mul, ih, hx i, ← M4.toMat_mul]
    rfl

theorem wordsB_form (j : Fin 4) :
    ∃ (l : List (Fin 4)) (c : Fin 4), wordsB j = l ++ [c] ++ l.reverse := by
  fin_cases j
  · exact ⟨[0, 1, 2], 3, by first | rfl | decide⟩
  · exact ⟨[1, 2], 3, by first | rfl | decide⟩
  · exact ⟨[2], 3, by first | rfl | decide⟩
  · exact ⟨[], 3, by first | rfl | decide⟩

theorem wordsD_form (j : Fin 4) :
    ∃ (l : List (Fin 4)) (c : Fin 4), wordsD j = l ++ [c] ++ l.reverse := by
  fin_cases j
  · exact ⟨[], 0, by first | rfl | decide⟩
  · exact ⟨[], 2, by first | rfl | decide⟩
  · exact ⟨[], 3, by first | rfl | decide⟩
  · exact ⟨[1, 0, 2, 3], 1, by first | rfl | decide⟩

theorem rho_quad {a : Fin 4 → W} {x0 x1 x2 x3 : M4} (ρ0 : R.ρ (a 0) = x0.toMat)
    (ρ1 : R.ρ (a 1) = x1.toMat) (ρ2 : R.ρ (a 2) = x2.toMat) (ρ3 : R.ρ (a 3) = x3.toMat) :
    ∀ i, R.ρ (a i) = (quadF x0 x1 x2 x3 i).toMat := by
  intro i
  fin_cases i
  · first | exact ρ0 | simpa [quadF] using ρ0
  · first | exact ρ1 | simpa [quadF] using ρ1
  · first | exact ρ2 | simpa [quadF] using ρ2
  · first | exact ρ3 | simpa [quadF] using ρ3

theorem rank_four_pack (H : Subgroup W) {a : Fin 4 → W} (ha : ∀ i, R.IsRefl (a i))
    (haH : ∀ i, a i ∈ H) (words : Fin 4 → List (Fin 4))
    (hform : ∀ j, ∃ (l : List (Fin 4)) (c : Fin 4), words j = l ++ [c] ++ l.reverse)
    {x : Fin 4 → M4} (hx : ∀ i, R.ρ (a i) = (x i).toMat)
    (hok : famOk (fun j => evalG x (words j)) = true) :
    ∃ t : Fin 4 → W, (∀ k, t k ∈ H) ∧ (∀ k, ∃ (g : W) (j : Fin 4), t k = g * a j * g⁻¹) ∧
      (∀ j k, t j * t k = t k * t j) ∧ Function.Injective t := by
  have hinv : ∀ i, a i * a i = 1 := fun i => (ha i).mul_self
  have hm : ∀ j, R.ρ (wdF a (words j)) = (evalG x (words j)).toMat :=
    fun j => R.rho_wdF hx (words j)
  obtain ⟨hcomm, hne⟩ := (famOk_iff _).1 hok
  have hcomm' : ∀ j k, (evalG x (words j)).mul (evalG x (words k)) =
      (evalG x (words k)).mul (evalG x (words j)) := hcomm
  have hne' : ∀ j k, j ≠ k → evalG x (words j) ≠ evalG x (words k) := hne
  refine ⟨fun j => wdF a (words j), ?_, ?_, ?_, ?_⟩
  · intro k
    exact wdF_mem H haH _
  · intro k
    obtain ⟨l, c, hl⟩ := hform k
    refine ⟨wdF a l, c, ?_⟩
    show wdF a (words k) = _
    rw [hl, wdF_append, wdF_append, wdF_reverse hinv]
    simp [wdF]
  · intro j k
    show wdF a (words j) * wdF a (words k) = wdF a (words k) * wdF a (words j)
    apply R.inj
    rw [map_mul, map_mul, hm j, hm k, ← M4.toMat_mul, ← M4.toMat_mul]
    exact congrArg M4.toMat (hcomm' j k)
  · intro j k hjk
    by_contra hjk'
    refine hne' j k hjk' (M4.toMat_injective ?_)
    rw [← hm j, ← hm k]
    exact congrArg R.ρ hjk

theorem rank_four_B (H : Subgroup W) {a : Fin 4 → W} (ha : ∀ i, R.IsRefl (a i))
    (haH : ∀ i, a i ∈ H) (o01 : orderOf (a 0 * a 1) = 3) (o12 : orderOf (a 1 * a 2) = 3)
    (o23 : orderOf (a 2 * a 3) = 4) (o02 : orderOf (a 0 * a 2) = 2)
    (o03 : orderOf (a 0 * a 3) = 2) (o13 : orderOf (a 1 * a 3) = 2) :
    ∃ t : Fin 4 → W, (∀ k, t k ∈ H) ∧ (∀ k, ∃ (g : W) (j : Fin 4), t k = g * a j * g⁻¹) ∧
      (∀ j k, t j * t k = t k * t j) ∧ Function.Injective t := by
  obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep (ha 0)
  obtain ⟨x1, hx1, ρ1⟩ := R.refl_rep (ha 1)
  obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep (ha 2)
  obtain ⟨x3, hx3, ρ3⟩ := R.refl_rep (ha 3)
  have hq := quadB x0 hx0 x1 hx1 (R.ord3b_of ρ0 ρ1 o01) x2 hx2 (R.ord3b_of ρ1 ρ2 o12)
    (R.ord2b_of ρ0 ρ2 o02) x3 hx3 (R.ord4b_of ρ2 ρ3 o23) (R.ord2b_of ρ0 ρ3 o03)
    (R.ord2b_of ρ1 ρ3 o13)
  exact R.rank_four_pack H ha haH wordsB wordsB_form (R.rho_quad ρ0 ρ1 ρ2 ρ3) hq

theorem rank_four_D (H : Subgroup W) {a : Fin 4 → W} (ha : ∀ i, R.IsRefl (a i))
    (haH : ∀ i, a i ∈ H) (o01 : orderOf (a 0 * a 1) = 3) (o12 : orderOf (a 1 * a 2) = 3)
    (o13 : orderOf (a 1 * a 3) = 3) (o02 : orderOf (a 0 * a 2) = 2)
    (o03 : orderOf (a 0 * a 3) = 2) (o23 : orderOf (a 2 * a 3) = 2) :
    ∃ t : Fin 4 → W, (∀ k, t k ∈ H) ∧ (∀ k, ∃ (g : W) (j : Fin 4), t k = g * a j * g⁻¹) ∧
      (∀ j k, t j * t k = t k * t j) ∧ Function.Injective t := by
  obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep (ha 0)
  obtain ⟨x1, hx1, ρ1⟩ := R.refl_rep (ha 1)
  obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep (ha 2)
  obtain ⟨x3, hx3, ρ3⟩ := R.refl_rep (ha 3)
  have hq := quadD x0 hx0 x1 hx1 (R.ord3b_of ρ0 ρ1 o01) x2 hx2 (R.ord3b_of ρ1 ρ2 o12)
    (R.ord2b_of ρ0 ρ2 o02) x3 hx3 (R.ord3b_of ρ1 ρ3 o13) (R.ord2b_of ρ0 ρ3 o03)
    (R.ord2b_of ρ2 ρ3 o23)
  exact R.rank_four_pack H ha haH wordsD wordsD_form (R.rho_quad ρ0 ρ1 ρ2 ρ3) hq

end F4Rep

end CFSG.StandardType.F4Model

end
