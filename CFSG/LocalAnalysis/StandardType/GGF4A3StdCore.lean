module

public import CFSG.LocalAnalysis.StandardType.GGF4A3Data
public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
import CFSG.LocalAnalysis.StandardType.GGF4RankFour

public section

namespace CFSG.StandardType.F4Model

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

@[expose] def rL : W := R.wd [1, 0, 2] * R.s 1 * (R.wd [1, 0, 2])⁻¹

@[expose] def rS : W := R.wd [0, 2, 1, 2] * R.s 3 * (R.wd [0, 2, 1, 2])⁻¹

theorem rho_rL : R.ρ R.rL = (Rm a3xL).toMat := by
  rw [rL, R.rho_conj_wd [1, 0, 2] (R.hs 1), a3_rL]

theorem rho_rS : R.ρ R.rS = (Rm a3xS).toMat := by
  rw [rS, R.rho_conj_wd [0, 2, 1, 2] (R.hs 3), a3_rS]

private def quintW (a b c d e : W) : Fin 5 → W :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else
    if i.val = 3 then d else e

private theorem rho_quintW {a b c d e : W} {x y z u v : M4}
    (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat) (hc : R.ρ c = z.toMat)
    (hd : R.ρ d = u.toMat) (he : R.ρ e = v.toMat) :
    ∀ i : Fin 5, R.ρ (quintW a b c d e i) = (quintF x y z u v i).toMat := by
  intro i
  fin_cases i <;> simp [quintW, quintF, ha, hb, hc, hd, he]

private theorem rho_prod_word {a : Fin 5 → W} {x : Fin 5 → M4}
    (hx : ∀ i, R.ρ (a i) = (x i).toMat) (l : List (Fin 5)) :
    R.ρ ((l.map a).prod) = (evalG5 x l).toMat := by
  induction l with
  | nil => simp [evalG5, M4.toMat_one]
  | cons i l ih =>
    have h : ((i :: l).map a).prod = a i * (l.map a).prod := by simp
    rw [h, map_mul, ih, hx i, ← M4.toMat_mul]
    rfl

private theorem prod_word_mem {a : Fin 5 → W} {S : Set W} (ha : ∀ i, a i ∈ S)
    (l : List (Fin 5)) : (l.map a).prod ∈ Subgroup.closure S := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure (ha i)

private theorem normalizer_ne_top_of_not_norm {Cl : List Nat} {i : Fin 4} {c : Nat}
    (hc : c ∈ Cl) (hc24 : c < 24)
    (hnot : ∀ c' ∈ Cl, (Sm i).mul ((Rm c).mul (Sm i)) ≠ Rm c') :
    Subgroup.normalizer (R.ClSet Cl) ≠ ⊤ := by
  intro htop
  have hsi : R.s i ∈ Subgroup.normalizer (R.ClSet Cl) := by
    rw [htop]; exact Subgroup.mem_top _
  have hρn : R.ρ (R.wd (W1 c).reverse * R.s (T1 c) * (R.wd (W1 c).reverse)⁻¹) =
      (Rm c).toMat := by
    rw [R.rho_conj_wd (W1 c).reverse (R.hs (T1 c)), a3_Rm_conj c hc24]
  let n := R.wd (W1 c).reverse * R.s (T1 c) * (R.wd (W1 c).reverse)⁻¹
  have hn : n ∈ R.ClSet Cl := (R.mem_ClSet).2 ⟨c, hc, hρn⟩
  rw [Subgroup.mem_set_normalizer_iff] at hsi
  have hconj : R.s i * n * (R.s i)⁻¹ ∈ R.ClSet Cl := (hsi n).1 hn
  obtain ⟨c', hc', hρ⟩ := (R.mem_ClSet).1 hconj
  have hmat : R.ρ (R.s i * n * (R.s i)⁻¹) = ((Sm i).mul ((Rm c).mul (Sm i))).toMat := by
    rw [R.s_inv i]
    exact R.rho_mul3 (R.hs i) hρn (R.hs i)
  rw [hmat] at hρ
  exact hnot c' hc' (M4.toMat_injective hρ)

private theorem exists_frame_normalizer_L {y : Nat} (hy : y < 24) :
    ∃ j : Fin 3, normM (Rm y) (a3QL j) := by
  have h := a3L_frame y hy
  by_cases h3 : a3frL y = 3
  · exact ⟨0, h.2 0 (Or.inl h3)⟩
  · have hlt : a3frL y < 3 := Nat.lt_of_le_of_ne h.1 h3
    exact ⟨⟨a3frL y, hlt⟩, h.2 ⟨a3frL y, hlt⟩ (Or.inr rfl)⟩

private theorem exists_frame_normalizer_S {y : Nat} (hy : y < 24) :
    ∃ j : Fin 3, normM (Rm y) (a3QS j) := by
  have h := a3S_frame y hy
  by_cases h3 : a3frS y = 3
  · exact ⟨0, h.2 0 (Or.inl h3)⟩
  · have hlt : a3frS y < 3 := Nat.lt_of_le_of_ne h.1 h3
    exact ⟨⟨a3frS y, hlt⟩, h.2 ⟨a3frS y, hlt⟩ (Or.inr rfl)⟩

private theorem exists_mem_normalizer_L {t : W} (ht : R.IsRefl t) :
    ∃ j : Fin 3, t ∈ Subgroup.normalizer (R.ClSet (a3QL j)) := by
  obtain ⟨y, hy, hρ⟩ := R.refl_rep ht
  obtain ⟨j, hj⟩ := exists_frame_normalizer_L hy
  exact ⟨j, R.mem_normalizer hρ (Rm_sq y hy) hj⟩

private theorem exists_mem_normalizer_S {t : W} (ht : R.IsRefl t) :
    ∃ j : Fin 3, t ∈ Subgroup.normalizer (R.ClSet (a3QS j)) := by
  obtain ⟨y, hy, hρ⟩ := R.refl_rep ht
  obtain ⟨j, hj⟩ := exists_frame_normalizer_S hy
  exact ⟨j, R.mem_normalizer hρ (Rm_sq y hy) hj⟩

private theorem mem_all_frames_L {t t' : W} {y y' : Nat} (hy : y < 24) (hy' : y' < 24)
    (hρ : R.ρ t = (Rm y).toMat) (hρ' : R.ρ t' = (Rm y').toMat)
    (h3 : a3frL y = 3) (h3' : a3frL y' = 3) :
    ∀ j : Fin 3, t ∈ Subgroup.normalizer (R.ClSet (a3QL j)) ∧
      t' ∈ Subgroup.normalizer (R.ClSet (a3QL j)) := by
  intro j
  have h := a3L_frame y hy
  have h' := a3L_frame y' hy'
  exact ⟨R.mem_normalizer hρ (Rm_sq y hy) (h.2 j (Or.inl h3)),
    R.mem_normalizer hρ' (Rm_sq y' hy') (h'.2 j (Or.inl h3'))⟩

private theorem mem_all_frames_S {t t' : W} {y y' : Nat} (hy : y < 24) (hy' : y' < 24)
    (hρ : R.ρ t = (Rm y).toMat) (hρ' : R.ρ t' = (Rm y').toMat)
    (h3 : a3frS y = 3) (h3' : a3frS y' = 3) :
    ∀ j : Fin 3, t ∈ Subgroup.normalizer (R.ClSet (a3QS j)) ∧
      t' ∈ Subgroup.normalizer (R.ClSet (a3QS j)) := by
  intro j
  have h := a3S_frame y hy
  have h' := a3S_frame y' hy'
  exact ⟨R.mem_normalizer hρ (Rm_sq y hy) (h.2 j (Or.inl h3)),
    R.mem_normalizer hρ' (Rm_sq y' hy') (h'.2 j (Or.inl h3'))⟩

private theorem closure_top_of_dif_L {t t' : W} {y y' : Nat} (hy : y < 24) (hy' : y' < 24)
    (hρ : R.ρ t = (Rm y).toMat) (hρ' : R.ρ t' = (Rm y').toMat)
    (hdif : a3difL y y' = true) :
    Subgroup.closure ({R.s 0, R.s 1, R.rL, t, t'} : Set W) = ⊤ := by
  let S : Set W := {R.s 0, R.s 1, R.rL, t, t'}
  let a : Fin 5 → W := quintW (R.s 0) (R.s 1) R.rL t t'
  have haS : ∀ i : Fin 5, a i ∈ S := by
    intro i
    fin_cases i <;> simp [a, S, quintW]
  have hx : ∀ i : Fin 5,
      R.ρ (a i) = (quintF (Sm 0) (Sm 1) (Rm a3xL) (Rm y) (Rm y') i).toMat := by
    apply rho_quintW R
    · exact R.hs 0
    · exact R.hs 1
    · exact R.rho_rL
    · exact hρ
    · exact hρ'
  have hword0 : ((a3GL y y' 0).map a).prod = R.s 2 := by
    apply R.inj
    rw [rho_prod_word R hx (a3GL y y' 0), R.hs 2, (a3L_gen y hy y' hy' hdif).1]
  have hword1 : ((a3GL y y' 1).map a).prod = R.s 3 := by
    apply R.inj
    rw [rho_prod_word R hx (a3GL y y' 1), R.hs 3, (a3L_gen y hy y' hy' hdif).2]
  have h2 : R.s 2 ∈ Subgroup.closure S := hword0 ▸ prod_word_mem haS (a3GL y y' 0)
  have h3 : R.s 3 ∈ Subgroup.closure S := hword1 ▸ prod_word_mem haS (a3GL y y' 1)
  apply R.closure_eq_top_of
  intro i
  fin_cases i
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact h2
  · exact h3

private theorem closure_top_of_dif_S {t t' : W} {y y' : Nat} (hy : y < 24) (hy' : y' < 24)
    (hρ : R.ρ t = (Rm y).toMat) (hρ' : R.ρ t' = (Rm y').toMat)
    (hdif : a3difS y y' = true) :
    Subgroup.closure ({R.s 3, R.s 2, R.rS, t, t'} : Set W) = ⊤ := by
  let S : Set W := {R.s 3, R.s 2, R.rS, t, t'}
  let a : Fin 5 → W := quintW (R.s 3) (R.s 2) R.rS t t'
  have haS : ∀ i : Fin 5, a i ∈ S := by
    intro i
    fin_cases i <;> simp [a, S, quintW]
  have hx : ∀ i : Fin 5,
      R.ρ (a i) = (quintF (Sm 3) (Sm 2) (Rm a3xS) (Rm y) (Rm y') i).toMat := by
    apply rho_quintW R
    · exact R.hs 3
    · exact R.hs 2
    · exact R.rho_rS
    · exact hρ
    · exact hρ'
  have hword0 : ((a3GS y y' 0).map a).prod = R.s 0 := by
    apply R.inj
    rw [rho_prod_word R hx (a3GS y y' 0), R.hs 0, (a3S_gen y hy y' hy' hdif).1]
  have hword1 : ((a3GS y y' 1).map a).prod = R.s 1 := by
    apply R.inj
    rw [rho_prod_word R hx (a3GS y y' 1), R.hs 1, (a3S_gen y hy y' hy' hdif).2]
  have h0 : R.s 0 ∈ Subgroup.closure S := hword0 ▸ prod_word_mem haS (a3GS y y' 0)
  have h1 : R.s 1 ∈ Subgroup.closure S := hword1 ▸ prod_word_mem haS (a3GS y y' 1)
  apply R.closure_eq_top_of
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem std_A3L : ∃ H : Fin 3 → Subgroup W, (∀ j, H j ≠ ⊤) ∧
    (∀ j, R.s 0 ∈ H j ∧ R.s 1 ∈ H j ∧ R.rL ∈ H j) ∧ (∀ t, R.IsRefl t → ∃ j, t ∈ H j) ∧
    ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
      (∀ j, t ∈ H j ∧ t' ∈ H j) ∨ Subgroup.closure ({R.s 0, R.s 1, R.rL, t, t'} : Set W) = ⊤ := by
  refine ⟨fun j => Subgroup.normalizer (R.ClSet (a3QL j)), ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i, c, hc, hc24, hnot⟩ := a3L_notnorm j
    exact normalizer_ne_top_of_not_norm R hc hc24 hnot
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · exact R.mem_normalizer (R.hs 0) (Sm_sq 0) (a3L_norm j).1
    · exact R.mem_normalizer (R.hs 1) (Sm_sq 1) (a3L_norm j).2.1
    · exact R.mem_normalizer R.rho_rL (Rm_sq a3xL (by decide)) (a3L_norm j).2.2
  · exact fun t ht => exists_mem_normalizer_L R ht
  · intro t t' ht ht' hord
    obtain ⟨y, hy, hρ⟩ := R.refl_rep ht
    obtain ⟨y', hy', hρ'⟩ := R.refl_rep ht'
    have hord3b : ord3b (Rm y) (Rm y') = true := R.ord3b_of hρ hρ' hord
    rcases a3L_ord3 y hy y' hy' hord3b with ⟨h3, h3'⟩ | hdif
    · exact Or.inl (mem_all_frames_L R hy hy' hρ hρ' h3 h3')
    · exact Or.inr (closure_top_of_dif_L R hy hy' hρ hρ' hdif)

theorem std_A3S : ∃ H : Fin 3 → Subgroup W, (∀ j, H j ≠ ⊤) ∧
    (∀ j, R.s 3 ∈ H j ∧ R.s 2 ∈ H j ∧ R.rS ∈ H j) ∧ (∀ t, R.IsRefl t → ∃ j, t ∈ H j) ∧
    ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
      (∀ j, t ∈ H j ∧ t' ∈ H j) ∨ Subgroup.closure ({R.s 3, R.s 2, R.rS, t, t'} : Set W) = ⊤ := by
  refine ⟨fun j => Subgroup.normalizer (R.ClSet (a3QS j)), ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i, c, hc, hc24, hnot⟩ := a3S_notnorm j
    exact normalizer_ne_top_of_not_norm R hc hc24 hnot
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · exact R.mem_normalizer (R.hs 3) (Sm_sq 3) (a3S_norm j).1
    · exact R.mem_normalizer (R.hs 2) (Sm_sq 2) (a3S_norm j).2.1
    · exact R.mem_normalizer R.rho_rS (Rm_sq a3xS (by decide)) (a3S_norm j).2.2
  · exact fun t ht => exists_mem_normalizer_S R ht
  · intro t t' ht ht' hord
    obtain ⟨y, hy, hρ⟩ := R.refl_rep ht
    obtain ⟨y', hy', hρ'⟩ := R.refl_rep ht'
    have hord3b : ord3b (Rm y) (Rm y') = true := R.ord3b_of hρ hρ' hord
    rcases a3S_ord3 y hy y' hy' hord3b with ⟨h3, h3'⟩ | hdif
    · exact Or.inl (mem_all_frames_S R hy hy' hρ hρ' h3 h3')
    · exact Or.inr (closure_top_of_dif_S R hy hy' hρ hρ' hdif)

end F4Rep

end CFSG.StandardType.F4Model

end
