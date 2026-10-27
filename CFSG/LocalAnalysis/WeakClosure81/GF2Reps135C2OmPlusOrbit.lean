module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

@[expose] def omHalfSpin2 (n : ℕ) (h : Fin n) : Fin n → ℤ :=
  omFromStdD2 n (fun a => if h.val + 2 = n ∧ a.val + 1 = n then -1 else 1)


private def ompOrb_omHalfVec (n : ℕ) (h : Fin n) : Fin n → ℤ :=
  fun a => if h.val + 2 = n ∧ a.val + 1 = n then -1 else 1


private theorem ompOrb_omHalfVec_eq_one {n : ℕ} {h a : Fin n} (_hspin : h.val + 2 = n)
    (ha : a.val + 1 ≠ n) : ompOrb_omHalfVec n h a = 1 := by
  unfold ompOrb_omHalfVec
  rw [if_neg]
  rintro ⟨-, h⟩
  exact ha h

private theorem ompOrb_omHalfVec_eq_neg_one {n : ℕ} {h a : Fin n} (hspin : h.val + 2 = n)
    (ha : a.val + 1 = n) : ompOrb_omHalfVec n h a = -1 := by
  unfold ompOrb_omHalfVec
  rw [if_pos ⟨hspin, ha⟩]

private theorem ompOrb_omHalfVec_zero {n : ℕ} {h : Fin n} (hn : 1 < n) :
    ompOrb_omHalfVec n h ⟨0, by omega⟩ = 1 := by
  unfold ompOrb_omHalfVec
  rw [if_neg]
  rintro ⟨-, h⟩
  simp only at h
  omega

private theorem ompOrb_stdReflD_omHalfVec_of_lt {n : ℕ} {h k : Fin n}
    (hspin : h.val + 2 = n) (hlt : k.val + 1 < n) (hk2 : k.val + 2 ≠ n) :
    stdReflD n k (ompOrb_omHalfVec n h) = ompOrb_omHalfVec n h := by
  rw [stdReflD_of_lt n hlt]
  funext a
  rw [Function.comp_apply]
  by_cases hak : a = k
  · rw [hak, Equiv.swap_apply_left,
      ompOrb_omHalfVec_eq_one hspin (a := ⟨k.val + 1, hlt⟩) (by omega),
      ompOrb_omHalfVec_eq_one hspin (a := k) (by omega)]
  · by_cases hak' : a = ⟨k.val + 1, hlt⟩
    · rw [hak', Equiv.swap_apply_right,
        ompOrb_omHalfVec_eq_one hspin (a := k) (by omega),
        ompOrb_omHalfVec_eq_one hspin (a := ⟨k.val + 1, hlt⟩) (by omega)]
    · rw [Equiv.swap_apply_of_ne_of_ne hak hak']

private theorem ompOrb_stdReflD_omHalfVec_of_not_lt {n : ℕ} {h k : Fin n}
    (hspin : h.val + 2 = n) (hlt : ¬ k.val + 1 < n) :
    stdReflD n k (ompOrb_omHalfVec n h) = ompOrb_omHalfVec n h := by
  rw [stdReflD_of_not_lt n hlt]
  have hkval : k.val = n - 1 := by have := k.isLt; omega
  have hhval : h.val = n - 2 := by omega
  have hkp : (⟨k.val - 1, by omega⟩ : Fin n) = h := Fin.ext (by simp only; omega)
  rw [hkp]
  funext a
  by_cases hah : a = h
  · rw [hah, if_pos (Or.inl hspin), Equiv.swap_apply_left,
      ompOrb_omHalfVec_eq_neg_one hspin (a := k) (by omega),
      ompOrb_omHalfVec_eq_one hspin (a := h) (by omega)]
    norm_num
  · by_cases hak : a = k
    · rw [hak, if_pos (Or.inr (by omega)), Equiv.swap_apply_right,
        ompOrb_omHalfVec_eq_neg_one hspin (a := k) (by omega),
        ompOrb_omHalfVec_eq_one hspin (a := h) (by omega)]
      norm_num
    · have hiff : ¬(a.val + 2 = n ∨ a.val + 1 = n) := by
        rintro (h' | h')
        · exact hah (Fin.ext (by omega))
        · exact hak (Fin.ext (by omega))
      rw [if_neg hiff, Equiv.swap_apply_of_ne_of_ne hah hak,
        ompOrb_omHalfVec_eq_one hspin (a := a) (by omega)]
      norm_num

private theorem ompOrb_stdReflD_omHalfVec_of_ne {n : ℕ} {h k : Fin n}
    (hh : n ≤ h.val + 2) (hspin : ¬ h.val + 2 = n) (hk : k ≠ h) :
    stdReflD n k (ompOrb_omHalfVec n h) = ompOrb_omHalfVec n h := by
  have hone : ompOrb_omHalfVec n h = fun _ => 1 := by
    funext a
    unfold ompOrb_omHalfVec
    rw [if_neg]
    rintro ⟨h', -⟩
    have := h.isLt
    omega
  have hklt : k.val + 1 < n := by
    by_contra h'
    exact hk (Fin.ext (by omega))
  rw [hone, stdReflD_of_lt n hklt]
  funext a
  rfl

private theorem ompOrb_stdReflD_omHalfVec {n : ℕ} {h k : Fin n} (hh : n ≤ h.val + 2) (hk : k ≠ h) :
    stdReflD n k (ompOrb_omHalfVec n h) = ompOrb_omHalfVec n h := by
  by_cases hspin : h.val + 2 = n
  · have hk2 : k.val + 2 ≠ n := by
      intro h'
      apply hk
      apply Fin.ext
      have hhv : h.val = n - 2 := by omega
      omega
    by_cases hlt : k.val + 1 < n
    · exact ompOrb_stdReflD_omHalfVec_of_lt hspin hlt hk2
    · exact ompOrb_stdReflD_omHalfVec_of_not_lt hspin hlt
  · exact ompOrb_stdReflD_omHalfVec_of_ne hh hspin hk

private theorem ompOrb_prod_spSgnOn {n : ℕ} (T : Finset (Fin n)) :
    ∏ a, spSgnOn T a = (-1 : ℤ) ^ T.card := by
  rw [show (∏ a, spSgnOn T a) = ∏ a, (if a ∈ T then (-1 : ℤ) else 1) from
    Finset.prod_congr rfl (fun a _ => rfl)]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

private theorem ompOrb_prod_spSgnOn_eq_one {n : ℕ} {T : Finset (Fin n)} (hT : Even T.card) :
    ∏ a, spSgnOn T a = 1 := by
  rw [ompOrb_prod_spSgnOn, hT.neg_one_pow]

private theorem ompOrb_even_card_pair {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b) :
    Even ({a, b} : Finset α).card := by
  rw [Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]
  exact ⟨1, rfl⟩

private theorem ompOrb_prod_mul_spSgnOn {n : ℕ} {h : Fin n}
    (hc : SpIsSign (ompOrb_omHalfVec n h)) (T : Finset (Fin n)) :
    ∏ a, ompOrb_omHalfVec n h a * spSgnOn T a * ompOrb_omHalfVec n h a = ∏ a, spSgnOn T a := by
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rcases hc a with h | h <;> rw [h] <;> ring

private theorem ompOrb_prod_mul_three {n : ℕ} {h : Fin n}
    (hc : SpIsSign (ompOrb_omHalfVec n h)) (u v : Fin n → ℤ) :
    ∏ a, (ompOrb_omHalfVec n h a * u a * v a) * ompOrb_omHalfVec n h a =
      (∏ a, u a) * ∏ a, v a := by
  have hsplit : ∏ a, (ompOrb_omHalfVec n h a * u a * v a) * ompOrb_omHalfVec n h a =
      ∏ a, u a * v a := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rcases hc a with h | h <;> rw [h] <;> ring
  rw [hsplit, Finset.prod_mul_distrib]

private theorem ompOrb_spSgnOn_injective {n : ℕ} :
    Function.Injective (spSgnOn : Finset (Fin n) → Fin n → ℤ) := by
  intro S T h
  ext a
  have h' := congrFun h a
  simp only [spSgnOn] at h'
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp_all

private theorem ompOrb_spSgnOn_of_not_mem {n : ℕ} {S : Finset (Fin n)} {a : Fin n} (h : a ∉ S) :
    spSgnOn S a = 1 := by
  unfold spSgnOn
  rw [if_neg h]

private theorem ompOrb_spSgnOn_of_mem {n : ℕ} {S : Finset (Fin n)} {a : Fin n} (h : a ∈ S) :
    spSgnOn S a = -1 := by
  unfold spSgnOn
  rw [if_pos h]

private theorem ompOrb_omHalfVec_one {n : ℕ} {h : Fin n} (hn : 3 ≤ n) :
    ompOrb_omHalfVec n h ⟨1, by omega⟩ = 1 := by
  unfold ompOrb_omHalfVec
  rw [if_neg]
  rintro ⟨-, hh⟩
  simp only at hh
  omega

private theorem ompOrb_exists_orbit {n : ℕ} (hn : 2 ≤ n) {h : Fin n}
    {d : Fin n → ℤ} (hd : SpIsSign d)
    (hprod : ∏ a, d a * ompOrb_omHalfVec n h a = 1) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      toStdD n (weylAction (isFiniteType_cartanD n) w (omHalfSpin2 n h)) =
        fun a => 2 * d a := by
  have hcS : SpIsSign (ompOrb_omHalfVec n h) := by
    intro a
    unfold ompOrb_omHalfVec
    split_ifs <;> simp
  have hτ : SpIsSign (fun a => d a * ompOrb_omHalfVec n h a) := hd.mul hcS (Equiv.refl (Fin n))
  obtain ⟨w, hw⟩ := exists_omRealizes_of_even hn (Equiv.refl (Fin n)) hτ hprod
  refine ⟨w, ?_⟩
  have key := hw (omHalfSpin2 n h)
  rw [show toStdD n (omHalfSpin2 n h) = fun a => 2 * ompOrb_omHalfVec n h a from
    toStdD_omFromStdD2 hn (ompOrb_omHalfVec n h)] at key
  rw [key]
  funext b
  have hcc := hcS.mul_self b
  calc (d b * ompOrb_omHalfVec n h b) * (2 * ompOrb_omHalfVec n h b)
      = 2 * d b * (ompOrb_omHalfVec n h b * ompOrb_omHalfVec n h b) := by ring
    _ = 2 * d b := by rw [hcc, mul_one]

private theorem ompOrb_orbit_four_of_sep {n : ℕ} (hn : 2 ≤ n) {h : Fin n}
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s)
    (d : Fin 4 → Fin n → ℤ)
    (hd : ∀ i, SpIsSign (d i))
    (hprod : ∀ i, ∏ a, d i a * ompOrb_omHalfVec n h a = 1)
    (hinj : Function.Injective d)
    (hsep : ∀ i j, (fun a => 2 * d i a) ≠
      fun b => s (π.symm b) * (2 * d j (π.symm b))) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omHalfSpin2 n h)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanD n) x (u j) := by
  choose w hw using fun i => ompOrb_exists_orbit hn (hd i) (hprod i)
  let u : Fin 4 → Fin n → ℤ := fun i =>
    weylAction (isFiniteType_cartanD n) (w i) (omHalfSpin2 n h)
  have hwu : ∀ i, toStdD n (u i) = fun a => 2 * d i a := fun i => hw i
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    exact ⟨w i, rfl⟩
  · intro i j hij
    apply hinj
    have key := congrArg (toStdD n) hij
    rw [hwu i, hwu j] at key
    funext a
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key a)
  · intro i j hij
    have key := congrArg (toStdD n) hij
    rw [hwu i, hxr (u j), hwu j] at key
    exact hsep i j key

theorem weylAction_simple_omHalfSpin2 {n : ℕ} (hn : 2 ≤ n) {h k : Fin n}
    (hh : n ≤ h.val + 2) (hk : k ≠ h) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) (omHalfSpin2 n h) =
      omHalfSpin2 n h := by
  have hdef : omHalfSpin2 n h = omFromStdD2 n (ompOrb_omHalfVec n h) := rfl
  rw [hdef, weylAction_simple_omFromStdD2 hn _ k, ompOrb_stdReflD_omHalfVec hh hk]

private theorem ompOrb_spIsSign_omHalfVec (n : ℕ) (h : Fin n) :
    SpIsSign (ompOrb_omHalfVec n h) := by
  intro a
  unfold ompOrb_omHalfVec
  split_ifs <;> simp

private theorem ompOrb_omHalfVec_ne_zero (n : ℕ) (h : Fin n) :
    ∀ a, ompOrb_omHalfVec n h a ≠ 0 := by
  intro a
  rcases ompOrb_spIsSign_omHalfVec n h a with h' | h' <;> rw [h'] <;> norm_num

private theorem ompOrb_even_card_pair_quad {α : Type*} [DecidableEq α] {a b c d e f : α}
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) :
    ∀ i : Fin 4, Even ((![∅, {a, b}, {c, d}, {e, f}] : Fin 4 → Finset α) i).card := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · simpa using ompOrb_even_card_pair hab
  · simpa using ompOrb_even_card_pair hcd
  · simpa using ompOrb_even_card_pair hef

private theorem ompOrb_four_data {n : ℕ} {base : Fin n → ℤ}
    (hbase : SpIsSign base) (hbase_ne : ∀ a, base a ≠ 0)
    {p q : Fin n} {T : Fin 4 → Finset (Fin n)}
    (hTmem : Function.Injective (fun i => (p ∈ T i, q ∈ T i))) :
    (∀ i, SpIsSign (fun a => base a * spSgnOn (T i) a)) ∧
      Function.Injective (fun i => fun a => base a * spSgnOn (T i) a) := by
  refine ⟨fun i => hbase.mul (spIsSign_spSgnOn (T i)) (Equiv.refl (Fin n)), ?_⟩
  intro i j hij
  have hf : spSgnOn (T i) = spSgnOn (T j) := by
    funext a
    have h' := congrFun hij a
    dsimp only at h'
    exact mul_left_cancel₀ (hbase_ne a) h'
  have hT : T i = T j := ompOrb_spSgnOn_injective hf
  exact hTmem (by
    show (p ∈ T i, q ∈ T i) = (p ∈ T j, q ∈ T j)
    rw [hT])

private theorem ompOrb_sep_of_probe {n : ℕ} {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    {r r' : Fin n} (hsym : π.symm r = r') {σ v w : ℤ} (hs : s r' = σ)
    {d : Fin 4 → Fin n → ℤ} (hvr : ∀ i, d i r = v) (hwr : ∀ i, d i r' = w)
    (hne : 2 * v ≠ σ * (2 * w)) :
    ∀ i j, (fun a => 2 * d i a) ≠ fun b => s (π.symm b) * (2 * d j (π.symm b)) := by
  intro i j hcontra
  have h0 := congrFun hcontra r
  rw [hsym, hs, hvr i, hwr j] at h0
  exact hne h0

private theorem ompOrb_base_zero {n : ℕ} (hn : 3 ≤ n) :
    spSgnOn ({(⟨1, by omega⟩ : Fin n), ⟨n - 1, by omega⟩} : Finset (Fin n))
        ⟨0, by omega⟩ = 1 := by
  rw [ompOrb_spSgnOn_of_not_mem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h'; exact Fin.ne_of_val_ne (by norm_num) h'
    · intro h'; exact Fin.ne_of_val_ne (by show (0 : ℕ) ≠ n - 1; omega) h')]

private theorem ompOrb_base_one {n : ℕ} (hn : 3 ≤ n) :
    spSgnOn ({(⟨1, by omega⟩ : Fin n), ⟨n - 1, by omega⟩} : Finset (Fin n))
        ⟨1, by omega⟩ = -1 := by
  rw [ompOrb_spSgnOn_of_mem (by simp)]

private theorem ompOrb_move_zero_data {n : ℕ} (hn : 5 ≤ n) {h : Fin n} {g : Fin n → ℤ}
    (hg : SpIsSign g) (hg0 : g ⟨0, by omega⟩ = 1) (hgprod : ∏ a, g a = 1)
    (hcS : SpIsSign (ompOrb_omHalfVec n h)) :
    ∃ d : Fin 4 → Fin n → ℤ,
      (∀ i, SpIsSign (d i)) ∧
      (∀ i, ∏ a, d i a * ompOrb_omHalfVec n h a = 1) ∧
      Function.Injective d ∧ (∀ i, d i ⟨0, by omega⟩ = 1) ∧
      (∀ i, d i ⟨1, by omega⟩ = g ⟨1, by omega⟩) := by
  let T : Fin 4 → Finset (Fin n) :=
    ![∅, {(⟨2, by omega⟩ : Fin n), ⟨3, by omega⟩},
      {⟨2, by omega⟩, ⟨4, by omega⟩}, {⟨3, by omega⟩, ⟨4, by omega⟩}]
  let base : Fin n → ℤ := fun a => ompOrb_omHalfVec n h a * g a
  let d : Fin 4 → Fin n → ℤ := fun i a => base a * spSgnOn (T i) a
  have hbase : SpIsSign base := hcS.mul hg (Equiv.refl (Fin n))
  have hbase_ne : ∀ a, base a ≠ 0 := fun a => by
    rcases hbase a with h' | h' <;> rw [h'] <;> norm_num
  have hTeven : ∀ i, Even (T i).card := ompOrb_even_card_pair_quad
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))
  have hprod : ∀ i, ∏ a, d i a * ompOrb_omHalfVec n h a = 1 := fun i => by
    show ∏ a, (ompOrb_omHalfVec n h a * g a * spSgnOn (T i) a) * ompOrb_omHalfVec n h a = 1
    rw [ompOrb_prod_mul_three hcS g (spSgnOn (T i)), hgprod,
      ompOrb_prod_spSgnOn_eq_one (hTeven i), one_mul]
  have hTmem : Function.Injective
      (fun i => ((⟨2, by omega⟩ : Fin n) ∈ T i, (⟨3, by omega⟩ : Fin n) ∈ T i)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T, Fin.ext_iff]
  obtain ⟨hd, hinj⟩ := ompOrb_four_data hbase hbase_ne hTmem
  refine ⟨d, hd, hprod, hinj, fun i => ?_, fun i => ?_⟩
  · have hi0 : (⟨0, by omega⟩ : Fin n) ∉ T i := by fin_cases i <;> simp [T, Fin.ext_iff]
    dsimp only [d, base]
    rw [ompOrb_spSgnOn_of_not_mem hi0, mul_one, ompOrb_omHalfVec_zero (by omega), hg0, one_mul]
  · have hi1 : (⟨1, by omega⟩ : Fin n) ∉ T i := by fin_cases i <;> simp [T, Fin.ext_iff]
    dsimp only [d, base]
    rw [ompOrb_spSgnOn_of_not_mem hi1, mul_one, ompOrb_omHalfVec_one (by omega), one_mul]

private theorem ompOrb_orbit_four_of_neg_zero {n : ℕ} (hn : 4 ≤ n) {h : Fin n}
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s)
    (hπ0 : π ⟨0, by omega⟩ = ⟨0, by omega⟩) (hs0 : s ⟨0, by omega⟩ = -1) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omHalfSpin2 n h)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanD n) x (u j) := by
  have hcS : SpIsSign (ompOrb_omHalfVec n h) := ompOrb_spIsSign_omHalfVec n h
  have hcS_ne : ∀ a, ompOrb_omHalfVec n h a ≠ 0 := ompOrb_omHalfVec_ne_zero n h
  have hsymi : π.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := (Equiv.symm_apply_eq π).2 hπ0.symm
  let T : Fin 4 → Finset (Fin n) :=
    ![∅, {(⟨1, by omega⟩ : Fin n), ⟨2, by omega⟩},
      {⟨1, by omega⟩, ⟨3, by omega⟩}, {⟨2, by omega⟩, ⟨3, by omega⟩}]
  let d : Fin 4 → Fin n → ℤ := fun i a => ompOrb_omHalfVec n h a * spSgnOn (T i) a
  have hTeven : ∀ i, Even (T i).card := ompOrb_even_card_pair_quad
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))
  have hTmem : Function.Injective
      (fun i => ((⟨1, by omega⟩ : Fin n) ∈ T i, (⟨2, by omega⟩ : Fin n) ∈ T i)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T, Fin.ext_iff]
  obtain ⟨hd, hinj⟩ := ompOrb_four_data hcS hcS_ne hTmem
  have hprod : ∀ i, ∏ a, d i a * ompOrb_omHalfVec n h a = 1 := fun i => by
    show ∏ a, ompOrb_omHalfVec n h a * spSgnOn (T i) a * ompOrb_omHalfVec n h a = 1
    rw [ompOrb_prod_mul_spSgnOn hcS (T i), ompOrb_prod_spSgnOn_eq_one (hTeven i)]
  have hd0 : ∀ i, d i ⟨0, by omega⟩ = 1 := fun i => by
    have hi0 : (⟨0, by omega⟩ : Fin n) ∉ T i := by fin_cases i <;> simp [T, Fin.ext_iff]
    dsimp only [d]
    rw [ompOrb_omHalfVec_zero (by omega), ompOrb_spSgnOn_of_not_mem hi0, one_mul]
  have hsep := ompOrb_sep_of_probe hsymi hs0 hd0 hd0 (by norm_num)
  exact ompOrb_orbit_four_of_sep (by omega) hxr d hd hprod hinj hsep

private theorem ompOrb_orbit_four_of_move_zero_neg {n : ℕ} (hn : 5 ≤ n) {h : Fin n}
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s)
    (hsym : π.symm ⟨0, by omega⟩ = ⟨1, by omega⟩) (hs1 : s ⟨1, by omega⟩ = -1) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omHalfSpin2 n h)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanD n) x (u j) := by
  have hcS : SpIsSign (ompOrb_omHalfVec n h) := ompOrb_spIsSign_omHalfVec n h
  obtain ⟨d, hd, hprod, hinj, hd0, hd1⟩ :=
    ompOrb_move_zero_data hn (spIsSign_one : SpIsSign (1 : Fin n → ℤ)) rfl (by simp) hcS
  have hsep := ompOrb_sep_of_probe hsym hs1 hd0 hd1 (by norm_num)
  exact ompOrb_orbit_four_of_sep (by omega) hxr d hd hprod hinj hsep

private theorem ompOrb_orbit_four_of_move_zero_pos {n : ℕ} (hn : 5 ≤ n) {h : Fin n}
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s)
    (hsym : π.symm ⟨0, by omega⟩ = ⟨1, by omega⟩) (hs1 : s ⟨1, by omega⟩ = 1) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omHalfSpin2 n h)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanD n) x (u j) := by
  have hcS : SpIsSign (ompOrb_omHalfVec n h) := ompOrb_spIsSign_omHalfVec n h
  let g : Fin n → ℤ :=
    spSgnOn ({(⟨1, by omega⟩ : Fin n), ⟨n - 1, by omega⟩} : Finset (Fin n))
  have hg : SpIsSign g := spIsSign_spSgnOn _
  have hg0 : g ⟨0, by omega⟩ = 1 := ompOrb_base_zero (by omega)
  have hg1 : g ⟨1, by omega⟩ = -1 := ompOrb_base_one (by omega)
  have hgprod : ∏ a, g a = 1 := ompOrb_prod_spSgnOn_eq_one
    (ompOrb_even_card_pair (Fin.ne_of_val_ne (by show (1 : ℕ) ≠ n - 1; omega)))
  obtain ⟨d, hd, hprod, hinj, hd0, hd1⟩ := ompOrb_move_zero_data hn hg hg0 hgprod hcS
  have hsep := ompOrb_sep_of_probe hsym hs1 hd0 hd1 (by rw [hg1]; norm_num)
  exact ompOrb_orbit_four_of_sep (by omega) hxr d hd hprod hinj hsep

theorem exists_four_orbit_omHalfSpin2 {n : ℕ} (hn : 5 ≤ n) {h : Fin n} (hh : n ≤ h.val + 2)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s) (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omHalfSpin2 n h)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanD n) x (u j) := by
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ0, hπ1, hs01⟩
  · exact ompOrb_orbit_four_of_neg_zero (by have := hh; omega) hxr hπ0 hs0
  · have hsymi0 : π.symm ⟨0, by omega⟩ = ⟨1, by omega⟩ := (Equiv.symm_apply_eq π).2 hπ1.symm
    rcases hs ⟨0, by omega⟩ with hsig | hsig
    · exact ompOrb_orbit_four_of_move_zero_pos hn hxr hsymi0 (by rw [← hs01, hsig])
    · exact ompOrb_orbit_four_of_move_zero_neg hn hxr hsymi0 (by rw [← hs01, hsig])

end CFSG.LocalAnalysis.WeakClosure81
