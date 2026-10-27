module

public import Certificates.Data.CFSGNative.SporLat.Spec
public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.Quasithin.EmptyFaithful.S151S9TNineData
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm LatAux
open scoped commutatorElement

namespace NineAux

section Words

variable {Γ : Type} [Group Γ]

theorem pow_three_sub_mod {x : Γ} (hx : x * x * x = 1) {a : ℕ} (ha : a < 3) :
    x ^ ((3 - a) % 3) = (x ^ a)⁻¹ := by
  have h2 : x * x = x⁻¹ := eq_inv_of_mul_eq_one_left hx
  interval_cases a
  · simp
  · simpa [pow_two] using h2
  · have : x ^ 2 = x⁻¹ := by rw [pow_two]; exact h2
    simp [this]

theorem evalElt_replicate (els : Array Γ) (l k : ℕ) :
    evalElt els (List.replicate k l) = els.getD l 1 ^ k := by
  simp [evalElt, List.map_replicate, List.prod_replicate]

theorem evalElt_append (els : Array Γ) (u v : List ℕ) :
    evalElt els (u ++ v) = evalElt els u * evalElt els v := by
  simp [evalElt]

theorem evalElt_conj9Word {x₁ x₆ r : Γ} (h1 : x₁ * x₁ * x₁ = 1) (h6 : x₆ * x₆ * x₆ = 1)
    {a b : ℕ} (ha : a < 3) (hb : b < 3) :
    evalElt #[x₁, x₆, r] (conj9Word a b) = (x₁ ^ a * x₆ ^ b)⁻¹ * r * (x₁ ^ a * x₆ ^ b) := by
  have e0 : (#[x₁, x₆, r] : Array Γ).getD 0 1 = x₁ := rfl
  have e1 : (#[x₁, x₆, r] : Array Γ).getD 1 1 = x₆ := rfl
  have e2 : evalElt (#[x₁, x₆, r] : Array Γ) [2] = r := by simp [evalElt]
  simp only [conj9Word, evalElt_append, evalElt_replicate, e0, e1, e2,
    pow_three_sub_mod h1 ha, pow_three_sub_mod h6 hb, mul_inv_rev, mul_assoc]

end Words

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem cube_eq_one_of_tab {x : Γ} {s : Array ℕ} (hs : s = (tab n x).toArray)
    (h : wordTabA #[s] n [0, 0, 0] = idTab n) : x * x * x = 1 := by
  have := evalElt_eq_one_of_wordTabA (hel_one hs) (w := [0, 0, 0]) (by simp) h
  simpa [evalElt, mul_assoc] using this

theorem orderOf_eq_three_of_tab {x : Γ} {s : Array ℕ} (hs : s = (tab n x).toArray)
    (h3 : wordTabA #[s] n [0, 0, 0] = idTab n) (h1 : s ≠ idTab n) : orderOf x = 3 := by
  have hx : x * x * x = 1 := cube_eq_one_of_tab hs h3
  refine orderOf_eq_prime (p := 3) ?_ ?_
  · rw [pow_succ, pow_two]; exact hx
  · intro h
    apply h1
    rw [hs, h, tab_one_arr]

end Tables

section Tabs

variable {Lab : Type}

theorem fT_zero (W : Idx9Wit) (n : ℕ) (D : LatData Lab) : W.fT n D 0 = W.x1T n D := by
  simp [Idx9Wit.fT]

theorem fT_one (W : Idx9Wit) (n : ℕ) (D : LatData Lab) : W.fT n D 1 = W.x6T n D := by
  simp [Idx9Wit.fT]

theorem fT_two (W : Idx9Wit) (n : ℕ) (D : LatData Lab) :
    W.fT n D 2 = wordTabA #[W.x1T n D, W.x6T n D] n [0, 1] := by
  simp [Idx9Wit.fT]

theorem fT_three (W : Idx9Wit) (n : ℕ) (D : LatData Lab) :
    W.fT n D 3 = wordTabA #[W.x1T n D, W.x6T n D] n [0, 1, 1] := by
  simp [Idx9Wit.fT]

end Tabs

end NineAux

section Main

open NineAux

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem Idx9Wit.sound (C : LatCtx Γ n Lab) (W : Idx9Wit) (hok : W.Ok n C.A.act C.Δ C.D) :
    ∃ x₁ ∈ C.Y W.p₁, ∃ x₆ ∈ C.Y W.p₆, orderOf x₁ = 3 ∧ orderOf x₆ = 3 ∧ x₁ * x₆ = x₆ * x₁ ∧
      ∃ r : Fin 5 → Γ, (∀ i, ∀ a b : Fin 3,
        (x₁ ^ (a : ℕ) * x₆ ^ (b : ℕ))⁻¹ * r i * (x₁ ^ (a : ℕ) * x₆ ^ (b : ℕ)) ∈ C.S) ∧
      ∀ f : Γ, f ∈ ({x₁, x₆, x₁ * x₆, x₁ * x₆⁻¹} : Set Γ) →
        Function.Injective fun i => ⁅⁅r i, f⁆, f⁆ := by
  obtain ⟨hp₁, hp₆, hmt₁, hmt₆, hx1w, hx6w, hx13, hx11, hx63, hx61, hcomm, -, -, hr, hf⟩ := hok
  obtain ⟨x₁, hx₁Y, hx₁T⟩ := exists_xElt C ⟨W.p₁, W.x1w, [], [], []⟩ hp₁ hmt₁ hx1w
  obtain ⟨x₆, hx₆Y, hx₆T⟩ := exists_xElt C ⟨W.p₆, W.x6w, [], [], []⟩ hp₆ hmt₆ hx6w
  replace hx₁T : W.x1T n C.D = (tab n x₁).toArray := hx₁T
  replace hx₆T : W.x6T n C.D = (tab n x₆).toArray := hx₆T
  have hrex : ∀ i : Fin 5, ∃ s ∈ C.S, W.rT n C.D i.val = (tab n s).toArray :=
    fun i => exists_sElt C (hr i.val i.isLt).1
  have hriex : ∀ i : Fin 5, ∃ s ∈ C.S, W.riT n C.D i.val = (tab n s).toArray :=
    fun i => exists_sElt C (hr i.val i.isLt).2.1
  choose r hrS hrT using hrex
  choose r' hr'S hr'T using hriex
  have hx1c : x₁ * x₁ * x₁ = 1 := cube_eq_one_of_tab hx₁T hx13
  have hx6c : x₆ * x₆ * x₆ = 1 := cube_eq_one_of_tab hx₆T hx63
  have hxx6 : x₆ * x₆ = x₆⁻¹ := eq_inv_of_mul_eq_one_left hx6c
  have hr'i : ∀ i : Fin 5, r' i = (r i)⁻¹ := fun i => by
    have := evalElt_eq_one_of_wordTabA (hel_two (hrT i) (hr'T i)) (w := [0, 1]) (by simp)
      (hr i.val i.isLt).2.2.1
    simp only [evalElt] at this
    simpa using eq_inv_of_mul_eq_one_right (by simpa using this)
  have hcomm' : x₁ * x₆ = x₆ * x₁ := by
    rw [wordTabA_eq #[x₁, x₆] #[W.x1T n C.D, W.x6T n C.D] (hel_two hx₁T hx₆T) [0, 1] (by simp),
      wordTabA_eq #[x₁, x₆] #[W.x1T n C.D, W.x6T n C.D] (hel_two hx₁T hx₆T) [1, 0]
        (by simp)] at hcomm
    simpa [evalElt] using eq_of_tab_eq hcomm
  have key : ∀ k < 4, ∀ f : Γ, W.fT n C.D k = (tab n f).toArray →
      Function.Injective fun i => ⁅⁅r i, f⁆, f⁆ := by
    intro k hk f hfT
    obtain ⟨hf3, hinj⟩ := hf k hk
    have hfc : f * f * f = 1 := cube_eq_one_of_tab hfT hf3
    have hdcE : ∀ i : Fin 5, W.dcT n C.D k i.val = (tab n ⁅⁅r i, f⁆, f⁆).toArray := fun i => by
      have h := wordTabA_eq #[r i, f, r' i] #[W.rT n C.D i.val, W.fT n C.D k, W.riT n C.D i.val]
        (hel_three (hrT i) hfT (hr'T i)) dcWord (by simp [dcWord])
      show wordTabA _ n dcWord = _
      rw [h, ← dc_word_eq (r i) f hfc, hr'i i]
      simp [evalElt, dcWord]
    intro i i' hii'
    have h1 : W.dcT n C.D k i.val = W.dcT n C.D k i'.val := by
      rw [hdcE, hdcE]
      exact congrArg (fun g => (tab n g).toArray) hii'
    exact Fin.ext (hinj i.val i.isLt i'.val i'.isLt h1)
  refine ⟨x₁, hx₁Y, x₆, hx₆Y, orderOf_eq_three_of_tab hx₁T hx13 hx11,
    orderOf_eq_three_of_tab hx₆T hx63 hx61, hcomm', r, fun i a b => ?_, fun f hfS => ?_⟩
  · have h := (hr i.val i.isLt).2.2.2 a.val a.isLt b.val b.isLt
    rw [wordTabA_eq #[x₁, x₆, r i] #[W.x1T n C.D, W.x6T n C.D, W.rT n C.D i.val]
      (hel_three hx₁T hx₆T (hrT i)) (conj9Word a b) (fun l hl => by
        simp only [conj9Word, List.mem_append, List.mem_replicate, List.mem_singleton] at hl
        show l < 3
        omega)] at h
    have h2 := mem_S_of_act_eq C h
    rwa [evalElt_conj9Word hx1c hx6c a.isLt b.isLt] at h2
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfS
    rcases hfS with rfl | rfl | rfl | rfl
    · exact key 0 (by norm_num) _ ((fT_zero W n C.D).trans hx₁T)
    · exact key 1 (by norm_num) _ ((fT_one W n C.D).trans hx₆T)
    · refine key 2 (by norm_num) _ ?_
      rw [fT_two, wordTabA_eq #[x₁, x₆] #[W.x1T n C.D, W.x6T n C.D] (hel_two hx₁T hx₆T) [0, 1]
        (by simp)]
      simp [evalElt]
    · refine key 3 (by norm_num) _ ?_
      rw [fT_three, wordTabA_eq #[x₁, x₆] #[W.x1T n C.D, W.x6T n C.D] (hel_two hx₁T hx₆T)
        [0, 1, 1] (by simp)]
      simp [evalElt, hxx6]

end Main

end CFSG.Quasithin.S151S9T
