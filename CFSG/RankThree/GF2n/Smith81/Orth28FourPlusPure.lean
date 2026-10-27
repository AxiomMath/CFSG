module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron
public import CFSG.RankThree.GF2n.Smith81.TiD2Alg

public section

namespace CFSG.RankThree.GF2n.Smith81.FourPlus

open CFSG.RankThree.GF2n.Smith81.OrthTN CFSG.RankThree.GF2n.Smith81.D2
open scoped Matrix

section Pure

variable {K : Type} [Field K]

@[expose] def pure3 (v : Fin 3 → Fin 2 → K) : Cube 3 K := fun x => ∏ i, v i (x i)

theorem pure3_apply (v : Fin 3 → Fin 2 → K) (x : Fin 3 → Fin 2) :
    pure3 v x = ∏ i, v i (x i) := rfl

theorem prod_update_apply (f : Fin 3 → Fin 2 → K) (x : Fin 3 → Fin 2) (i : Fin 3) (b : Fin 2) :
    ∏ l, f l ((Function.update x i b) l) = f i b * ∏ l ∈ Finset.univ.erase i, f l (x l) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun l => f l ((Function.update x i b) l))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

theorem actMap_pure3 (i : Fin 3) (A : Mat2 K) (v : Fin 3 → Fin 2 → K) :
    actMap i A (pure3 v) = pure3 (Function.update v i (A *ᵥ v i)) := by
  funext x
  rw [actMap_apply]
  simp only [pure3_apply]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun l => (Function.update v i (A *ᵥ v i)) l (x l)) (Finset.mem_univ i)]
  have h1 : ∏ l ∈ Finset.univ.erase i, (Function.update v i (A *ᵥ v i)) l (x l) =
      ∏ l ∈ Finset.univ.erase i, v l (x l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [h1]
  simp only [prod_update_apply, Function.update_self, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

theorem exists_sl_not_span (v : Fin 2 → K) (hv : v ≠ 0) :
    ∃ A : Mat2 K, A.det = 1 ∧ ∀ m : K, A *ᵥ v ≠ m • v := by
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext i
      fin_cases i <;> simp [h0, hv1]
    refine ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two], fun m hm => ?_⟩
    have h := congrFun hm 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv1] at h
    exact hv0 h
  · refine ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two], fun m hm => ?_⟩
    have h0 := congrFun hm 0
    have h1 := congrFun hm 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hm1 : m = 1 := by
      have : (m - 1) * v 1 = 0 := by linear_combination -h1
      have := (mul_eq_zero.mp this).resolve_right hv1
      exact sub_eq_zero.mp this
    rw [hm1] at h0
    apply hv1
    linear_combination h0

theorem pure3_update_eq {v : Fin 3 → Fin 2 → K} (hv : ∀ l, v l ≠ 0) {i j : Fin 3} (hij : i ≠ j)
    {w w' : Fin 2 → K} {lam : K}
    (h : pure3 (Function.update v j w') = pure3 (Function.update v i w) + lam • pure3 v) :
    ∃ m : K, w = m • v i := by
  classical
  have hx₀ : ∀ l, ∃ b : Fin 2, v l b ≠ 0 := by
    intro l
    by_contra hcon
    push Not at hcon
    exact hv l (funext hcon)
  choose x₀ hx₀ using hx₀
  set R : K := ∏ l ∈ (Finset.univ.erase i).erase j, v l (x₀ l) with hR
  have hR0 : R ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => hx₀ l
  have hji : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hij' : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have hall : ∀ a b : Fin 2, v i a * w' b = (w a + lam * v i a) * v j b := by
    intro a b
    set x : Fin 3 → Fin 2 := Function.update (Function.update x₀ i a) j b with hx
    have hxi : x i = a := by
      rw [hx, Function.update_of_ne hij, Function.update_self]
    have hxj : x j = b := by rw [hx, Function.update_self]
    have hxl : ∀ l ∈ (Finset.univ.erase i).erase j, x l = x₀ l := by
      intro l hl
      have hlj := Finset.ne_of_mem_erase hl
      have hli := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [hx, Function.update_of_ne hlj, Function.update_of_ne hli]
    have hRx : ∏ l ∈ (Finset.univ.erase i).erase j, v l (x l) = R :=
      Finset.prod_congr rfl fun l hl => by rw [hxl l hl]
    have e1 := congrFun h x
    simp only [pure3_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1
    have dec : ∀ f : Fin 3 → Fin 2 → K, ∏ l, f l (x l) =
        f i (x i) * (f j (x j) * ∏ l ∈ (Finset.univ.erase i).erase j, f l (x l)) := by
      intro f
      rw [← Finset.mul_prod_erase Finset.univ (fun l => f l (x l)) (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) (fun l => f l (x l)) hji]
    rw [dec, dec, dec] at e1
    have hrest : ∀ (k : Fin 3), (k = i ∨ k = j) →
        ∏ l ∈ (Finset.univ.erase i).erase j, (Function.update v k (if k = i then w else w')) l
          (x l) = R := by
      intro k hk
      rw [← hRx]
      refine Finset.prod_congr rfl fun l hl => ?_
      have hlj := Finset.ne_of_mem_erase hl
      have hli := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      have : l ≠ k := by
        rcases hk with rfl | rfl
        · exact hli
        · exact hlj
      rw [Function.update_of_ne this]
    have hwR := hrest i (Or.inl rfl)
    have hw'R := hrest j (Or.inr rfl)
    simp only [if_true] at hwR
    rw [if_neg hij.symm] at hw'R
    rw [hwR, hw'R, hRx] at e1
    simp only [hxi, hxj, Function.update_self, Function.update_of_ne hij,
      Function.update_of_ne hij.symm] at e1
    have e2 : (v i a * w' b - (w a + lam * v i a) * v j b) * R = 0 := by
      linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hR0)
  obtain ⟨b₀, hb₀⟩ : ∃ b : Fin 2, v j b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv j (funext hcon)
  refine ⟨w' b₀ / v j b₀ - lam, funext fun a => ?_⟩
  have := hall a b₀
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -this

theorem exists_moved {v : Fin 3 → Fin 2 → K} (hv : ∀ l, v l ≠ 0)
    {T : Cube 3 K ≃ₗ[K] Cube 3 K} {π : Equiv.Perm (Fin 3)} (hπ : π ≠ 1)
    (hTp : T (pure3 v) = pure3 v)
    (hT : ∀ i : Fin 3, ∀ A : Mat2 K, A.det = 1 → ∃ A' : Mat2 K, A'.det = 1 ∧
      ∀ w, T (actMap i A w) = actMap (π i) A' (T w)) :
    ∃ (i : Fin 3) (A : Mat2 K), A.det = 1 ∧
      ∀ lam : K, T (actMap i A (pure3 v)) - actMap i A (pure3 v) ≠ lam • pure3 v := by
  obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hπ (Equiv.ext hcon)
  obtain ⟨A, hA, hAv⟩ := exists_sl_not_span (v i) (hv i)
  refine ⟨i, A, hA, fun lam hlam => ?_⟩
  obtain ⟨A', hA', hTA⟩ := hT i A hA
  have h1 : T (actMap i A (pure3 v)) = actMap (π i) A' (pure3 v) := by rw [hTA, hTp]
  have h2 : actMap (π i) A' (pure3 v) = actMap i A (pure3 v) + lam • pure3 v := by
    rw [← h1]
    exact sub_eq_iff_eq_add'.mp hlam
  rw [actMap_pure3, actMap_pure3] at h2
  obtain ⟨m, hm⟩ := pure3_update_eq hv (Ne.symm hi) h2
  exact hAv m hm

end Pure

end CFSG.RankThree.GF2n.Smith81.FourPlus
