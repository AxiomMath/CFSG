module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.GLBasics
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem pairQn_mul_add_add {n : ℕ} (x y : PairN n) :
    pairQn n (x * y) + pairQn n x + pairQn n y = polarN n x y := by
  rw [pairQn_mul]
  generalize pairQn n x = a
  generalize pairQn n y = b
  generalize polarN n x y = c
  revert a b c
  decide

theorem isQuadFormN_pairQn (n : ℕ) : IsQuadFormN (pairQn n) := by
  refine ⟨?_, fun x x' y => ?_⟩
  · rw [pairVec_one (n := n), pairQn_pairVec]
    simp
  · rw [pairQn_mul_add_add (x * x') y, pairQn_mul_add_add x y, pairQn_mul_add_add x' y,
      polarN_mul_left]

private theorem exists_one_of_ne_zero {n : ℕ} {b : Fin n → ZMod 2} (hb : b ≠ 0) :
    ∃ i, b i = 1 := by
  by_contra h
  refine hb (funext fun i => ?_)
  rcases zmod_two_cases (b i) with h0 | h1
  · exact h0
  · exact (h ⟨i, h1⟩).elim

theorem isNondegN_pairQn (n : ℕ) (hn : 0 < n) : IsNondegN (pairQn n) := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      exact hx pairVec_one.symm
    obtain ⟨i, hi⟩ := exists_one_of_ne_zero hb
    refine ⟨pairVec (Pi.single i 1) 0, ?_⟩
    rw [pairQn_mul_add_add, polarN_pairVec]
    simp [single_dotProduct, hi]
  · obtain ⟨i, hi⟩ := exists_one_of_ne_zero ha
    refine ⟨pairVec 0 (Pi.single i 1), ?_⟩
    rw [pairQn_mul_add_add, polarN_pairVec]
    simp [dotProduct_single, hi]

private theorem pairQn_eq_zero_of_mem_V1n {n : ℕ} {v : PairN n} (hv : v ∈ V1n n) :
    pairQn n v = 0 := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj v
  have hb : (pairVec a b).2 = 1 := mem_V1n.mp hv
  have hb0 : b = 0 := by
    have : Multiplicative.ofAdd b = (1 : Multiplicative (Fin n → ZMod 2)) := hb
    exact ofAdd_eq_one.mp this
  rw [pairQn_pairVec, hb0, dotProduct_zero]

private theorem form_eq_zero_of_mem_V2n {n : ℕ} {q' : PairN n → ZMod 2}
    (hinv : ∀ g ∈ Mg n, ∀ x, q' (g x) = q' x) (hV1 : ∀ v ∈ V1n n, q' v = 0) (b : Fin n → ZMod 2) :
    q' (pairVec 0 b) = 0 := by
  have h := hinv (swapN n) swapN_mem_Mg (pairVec b 0)
  rw [swapN_pairVec] at h
  rw [h]
  exact hV1 _ (pairVec_mem_V1n b)

private theorem form_add_left {n : ℕ} {q' : PairN n → ZMod 2} (hq : IsQuadFormN q')
    (hinv : ∀ g ∈ Mg n, ∀ x, q' (g x) = q' x) (hV1 : ∀ v ∈ V1n n, q' v = 0)
    (a a' b : Fin n → ZMod 2) :
    q' (pairVec (a + a') b) = q' (pairVec a b) + q' (pairVec a' b) := by
  have h := hq.2 (pairVec a 0) (pairVec a' 0) (pairVec 0 b)
  simp only [pairVec_mul, add_zero, zero_add] at h
  rw [hV1 _ (pairVec_mem_V1n (a + a')), hV1 _ (pairVec_mem_V1n a), hV1 _ (pairVec_mem_V1n a'),
    form_eq_zero_of_mem_V2n hinv hV1 b] at h
  simpa using h

private theorem form_orbit {n : ℕ} {q' : PairN n → ZMod 2}
    (hinv : ∀ g ∈ Mg n, ∀ x, q' (g x) = q' x) {a b a' b' : Fin n → ZMod 2} (ha : a ≠ 0)
    (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0) (h : b ⬝ᵥ a = b' ⬝ᵥ a') :
    q' (pairVec a' b') = q' (pairVec a b) := by
  obtain ⟨A, hA1, hA2⟩ := exists_GL_mulVec_pair ha hb ha' hb' h
  have h1 := hinv (pairActN n A) (Lg_le_Mg (pairActN_mem_Lg A)) (pairVec a b)
  rwa [pairActN_pairVec, hA1, hA2] at h1

private theorem eq_pairQn_of_invariant {n : ℕ} (hn : 2 ≤ n) {q' : PairN n → ZMod 2}
    (hq : IsQuadFormN q') (hnd : IsNondegN q') (hinv : ∀ g ∈ Mg n, ∀ x, q' (g x) = q' x)
    (hV1 : ∀ v ∈ V1n n, q' v = 0) : q' = pairQn n := by
  let i₁ : Fin n := ⟨0, by omega⟩
  let i₂ : Fin n := ⟨1, by omega⟩
  have h12 : i₁ ≠ i₂ := by
    intro h
    have := congrArg Fin.val h
    simp [i₁, i₂] at this
  let u : Fin n → ZMod 2 := Pi.single i₁ 1
  let w : Fin n → ZMod 2 := Pi.single i₂ 1
  have hu : u ≠ 0 := by
    intro h
    have := congrFun h i₁
    simp [u] at this
  have hw : w ≠ 0 := by
    intro h
    have := congrFun h i₂
    simp [w] at this
  have huu : u ⬝ᵥ u = 1 := by simp [u, single_dotProduct]
  have huw : u ⬝ᵥ w = 0 := by simp [u, w, single_dotProduct, h12.symm]
  have huw' : u + w ≠ 0 := by
    intro h
    have := congrFun h i₁
    simp [u, w, h12] at this
  have hu_uw : u ⬝ᵥ (u + w) = 1 := by rw [dotProduct_add, huu, huw]; simp
  have hwu0 : q' (pairVec w u) = 0 := by
    have h1 : q' (pairVec (u + w) u) = q' (pairVec u u) :=
      form_orbit hinv hu hu huw' hu (by rw [hu_uw, huu])
    have h2 := form_add_left hq hinv hV1 u w u
    rw [h1] at h2
    simpa using h2
  have hG2 : ∀ a b : Fin n → ZMod 2, a ≠ 0 → b ≠ 0 → b ⬝ᵥ a = 0 → q' (pairVec a b) = 0 := by
    intro a b ha hb hab
    exact (form_orbit hinv hw hu ha hb (by rw [hab, huw])).trans hwu0
  have hG3 : ∀ a b : Fin n → ZMod 2, a ≠ 0 → b ≠ 0 → b ⬝ᵥ a = 1 →
      q' (pairVec a b) = q' (pairVec u u) := by
    intro a b ha hb hab
    exact form_orbit hinv hu hu ha hb (by rw [hab, huu])
  have hG4 : ∀ a b : Fin n → ZMod 2, q' (pairVec a b) = q' (pairVec u u) * (a ⬝ᵥ b) := by
    intro a b
    by_cases ha : a = 0
    · subst ha
      rw [form_eq_zero_of_mem_V2n hinv hV1 b, zero_dotProduct, mul_zero]
    by_cases hb : b = 0
    · subst hb
      rw [hV1 _ (pairVec_mem_V1n a), dotProduct_zero, mul_zero]
    rw [dotProduct_comm a b]
    rcases zmod_two_cases (b ⬝ᵥ a) with h | h
    · rw [hG2 a b ha hb h, h, mul_zero]
    · rw [hG3 a b ha hb h, h, mul_one]
  have hc : q' (pairVec u u) = 1 := by
    rcases zmod_two_cases (q' (pairVec u u)) with h | h
    · exfalso
      have hzero : ∀ x : PairN n, q' x = 0 := by
        intro x
        obtain ⟨a, b, rfl⟩ := pairVec_surj x
        rw [hG4, h, zero_mul]
      have hx : (pairVec u 0 : PairN n) ≠ 1 := by
        intro h1
        rw [pairVec_one] at h1
        exact hu (pairVec_inj.mp h1).1
      obtain ⟨y, hy⟩ := hnd _ hx
      exact hy (by simp [hzero])
    · exact h
  funext x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [hG4, hc, one_mul, pairQn_pairVec]

theorem h91_clause1 (n : ℕ) (hn : 2 ≤ n) :
    (IsQuadFormN (pairQn n) ∧ IsNondegN (pairQn n) ∧ (∀ g ∈ Mg n, ∀ x, pairQn n (g x) = pairQn n x) ∧
      (∀ v ∈ V1n n, pairQn n v = 0) ∧
      ∀ q' : PairN n → ZMod 2, IsQuadFormN q' → IsNondegN q' → (∀ g ∈ Mg n, ∀ x, q' (g x) = q' x) →
        (∀ v ∈ V1n n, q' v = 0) → q' = pairQn n) := by
  exact ⟨isQuadFormN_pairQn n, isNondegN_pairQn n (by omega),
    fun g hg x => pairQn_of_mem_Mg hg x, fun v hv => pairQn_eq_zero_of_mem_V1n hv,
    fun q' hq hnd hinv hV1 => eq_pairQn_of_invariant hn hq hnd hinv hV1⟩

end CFSG.ASVolI.ChH
