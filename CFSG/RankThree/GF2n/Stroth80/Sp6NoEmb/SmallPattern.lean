module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.RecApply
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Sym

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open CFSG.Open
open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal (block)

@[expose] def constLabel (A : Finset ℕ) : Fin 3 → Finset ℕ := fun _ => A

@[expose] def lsize (J : Fin 3 → Finset ℕ) : ℕ := (J 0).card + (J 1).card + (J 2).card

theorem lsize_eq_sum (J : Fin 3 → Finset ℕ) : lsize J = ∑ s, (J s).card := by
  rw [lsize, Fin.sum_univ_three]

theorem lsize_comp_perm (J : Fin 3 → Finset ℕ) (σ : Equiv.Perm (Fin 3)) :
    lsize (J ∘ σ) = lsize J := by
  rw [lsize_eq_sum, lsize_eq_sum]
  exact Equiv.sum_comp σ (fun s => (J s).card)

theorem lsize_trivLabel : lsize trivLabel = 0 := by simp [lsize, trivLabel]

theorem lsize_slotLabel (s : Fin 3) (a : ℕ) : lsize (slotLabel s {a}) = 1 := by
  fin_cases s <;> simp [lsize, slotLabel]

theorem lsize_constLabel (a : ℕ) : lsize (constLabel {a}) = 3 := by
  simp [lsize, constLabel]

theorem isLabel_constLabel {n : ℕ} {A : Finset ℕ} (hA : ∀ i ∈ A, i < n) :
    IsLabel n (constLabel A) := fun _ => hA

theorem slotLabel_ne_slotLabel {s t : Fin 3} {a b : ℕ} (h : a ≠ b) :
    slotLabel s {a} ≠ slotLabel t {b} := by
  intro h'
  by_cases hst : s = t
  · subst hst
    have := congrFun h' s
    rw [slotLabel_self, slotLabel_self] at this
    exact h (Finset.singleton_injective this)
  · have := congrFun h' s
    rw [slotLabel_self, slotLabel_of_ne hst] at this
    exact Finset.singleton_ne_empty a this

theorem slotLabel_comp_swap (s t : Fin 3) (A : Finset ℕ) :
    slotLabel s A ∘ Equiv.swap s t = slotLabel t A := by
  funext u
  simp only [Function.comp_apply, slotLabel]
  congr 1
  apply propext
  constructor
  · intro h
    have := congrArg (Equiv.swap s t) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
  · rintro rfl
    exact Equiv.swap_apply_right s u

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
  {Y : Type} [AddCommGroup Y] [Module K Y] [Module.Finite K Y]

theorem pat_slotLabel_eq (hK : Fintype.card K = 2 ^ n) (ρ : Representation K (StatedSp 3 K) Y)
    {a : ℕ} (ha : a < n) (s t : Fin 3) :
    pat (ρ.comp block) (slotLabel t {a}) = pat (ρ.comp block) (slotLabel s {a}) := by
  have ha' : ∀ i ∈ ({a} : Finset ℕ), i < n := fun i hi => (Finset.mem_singleton.mp hi) ▸ ha
  rw [← slotLabel_comp_swap s t]
  exact pat_block_perm hK ρ (isLabel_slotLabel ha' s) _

theorem sum_pat_le_finrank (hK : Fintype.card K = 2 ^ n) (ρ : Representation K (StatedSp 3 K) Y)
    {S : Finset (Fin 3 → Finset ℕ)} (hS : ∀ J ∈ S, IsLabel n J) :
    ∑ J ∈ S, pat (ρ.comp block) J * 2 ^ lsize J ≤ finrank K Y := by
  rw [finrank_eq_sum_pat hK (ρ.comp block)]
  exact Finset.sum_le_sum_of_subset (fun J hJ => mem_labels.mpr (hS J hJ))

theorem label_of_pat_ne_zero (hK : Fintype.card K = 2 ^ n)
    (ρ : Representation K (StatedSp 3 K) Y) (hdim : finrank K Y ≤ 8) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) (hp : pat (ρ.comp block) J ≠ 0) :
    J = trivLabel ∨ (∃ s a, a < n ∧ J = slotLabel s {a}) ∨ (∃ a, a < n ∧ J = constLabel {a}) := by
  set p := pat (ρ.comp block) with hpdef
  have hp1 : 1 ≤ p J := Nat.one_le_iff_ne_zero.mpr hp
  have h1 : p J * 2 ^ lsize J ≤ 8 := by
    have := sum_pat_le_finrank hK ρ (S := {J}) (by simpa using hJ)
    rw [← hpdef, Finset.sum_singleton] at this
    exact this.trans hdim
  by_cases hc : J 0 = J 1 ∧ J 1 = J 2
  · obtain ⟨h01, h12⟩ := hc
    have hsz : lsize J = 3 * (J 0).card := by
      rw [lsize, ← h12, ← h01]
      ring
    have hcard : (J 0).card ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h64 : 64 ≤ 2 ^ lsize J := by
        rw [hsz]
        calc 64 = 2 ^ (3 * 2) := rfl
          _ ≤ 2 ^ (3 * (J 0).card) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h0
    · left
      have he : J 0 = ∅ := Finset.card_eq_zero.mp h0
      funext s
      fin_cases s
      · exact he
      · exact h01 ▸ he
      · exact h12 ▸ h01 ▸ he
    · right; right
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h0
      refine ⟨a, hJ 0 a (by rw [ha]; exact Finset.mem_singleton_self a), ?_⟩
      funext s
      fin_cases s
      · exact ha
      · exact h01 ▸ ha
      · exact h12 ▸ h01 ▸ ha
  ·
    let c : Equiv.Perm (Fin 3) := finRotate 3
    have hc0 : c 0 = 1 := rfl
    have hc1 : c 1 = 2 := rfl
    have hc2 : c 2 = 0 := rfl
    have hJc : IsLabel n (J ∘ c) := isLabel_comp_perm hJ c
    have hJcc : IsLabel n (J ∘ c ∘ c) := isLabel_comp_perm hJc c
    have hp2 : p (J ∘ c) = p J := pat_block_perm hK ρ hJ c
    have hp3 : p (J ∘ c ∘ c) = p J := by
      rw [← hp2]
      exact pat_block_perm hK ρ hJc c
    have hne1 : J ≠ J ∘ c := fun h => by
      have e0 : J 0 = J 1 := congrFun h 0
      have e1 : J 1 = J 2 := congrFun h 1
      exact hc ⟨e0, e1⟩
    have hne2 : J ≠ J ∘ c ∘ c := fun h => by
      have e0 : J 0 = J 2 := congrFun h 0
      have e1 : J 1 = J 0 := congrFun h 1
      exact hc ⟨e1.symm, e1.trans e0⟩
    have hne3 : J ∘ c ≠ J ∘ c ∘ c := fun h => by
      have e0 : J 1 = J 2 := congrFun h 0
      have e1 : J 2 = J 0 := congrFun h 1
      exact hc ⟨(e0.trans e1).symm, e0⟩
    have h3 := sum_pat_le_finrank hK ρ (S := {J, J ∘ c, J ∘ c ∘ c}) (by
      intro J' hJ'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hJ'
      rcases hJ' with rfl | rfl | rfl
      exacts [hJ, hJc, hJcc])
    rw [← hpdef] at h3
    have hls : lsize (J ∘ c ∘ c) = lsize J :=
      (lsize_comp_perm (J ∘ c) c).trans (lsize_comp_perm J c)
    rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
      Finset.sum_singleton, hp2, hp3, lsize_comp_perm, hls] at h3
    have hsz : lsize J ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h4 : 4 ≤ 2 ^ lsize J := by
        calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ lsize J := Nat.pow_le_pow_right (by norm_num) hcon
      nlinarith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsz with h0 | h0
    · exfalso
      apply hc
      have : (J 0).card = 0 ∧ (J 1).card = 0 ∧ (J 2).card = 0 := by
        rw [lsize] at h0
        omega
      rw [Finset.card_eq_zero.mp this.1, Finset.card_eq_zero.mp this.2.1,
        Finset.card_eq_zero.mp this.2.2]
      exact ⟨rfl, rfl⟩
    · right; left
      rw [lsize] at h0
      have hcase : ((J 0).card = 1 ∧ (J 1).card = 0 ∧ (J 2).card = 0) ∨
          ((J 0).card = 0 ∧ (J 1).card = 1 ∧ (J 2).card = 0) ∨
          ((J 0).card = 0 ∧ (J 1).card = 0 ∧ (J 2).card = 1) := by omega
      rcases hcase with ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h0'
        refine ⟨0, a, hJ 0 a (by rw [ha]; exact Finset.mem_singleton_self a), ?_⟩
        funext s
        fin_cases s
        · simp [slotLabel, ha]
        · simp [slotLabel, Finset.card_eq_zero.mp h1']
        · simp [slotLabel, Finset.card_eq_zero.mp h2']
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1'
        refine ⟨1, a, hJ 1 a (by rw [ha]; exact Finset.mem_singleton_self a), ?_⟩
        funext s
        fin_cases s
        · simp [slotLabel, Finset.card_eq_zero.mp h0']
        · simp [slotLabel, ha]
        · simp [slotLabel, Finset.card_eq_zero.mp h2']
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h2'
        refine ⟨2, a, hJ 2 a (by rw [ha]; exact Finset.mem_singleton_self a), ?_⟩
        funext s
        fin_cases s
        · simp [slotLabel, Finset.card_eq_zero.mp h0']
        · simp [slotLabel, Finset.card_eq_zero.mp h1']
        · simp [slotLabel, ha]

theorem pattern_cases (hK : Fintype.card K = 2 ^ n) (ρ : Representation K (StatedSp 3 K) Y)
    (hdim : finrank K Y ≤ 8) :
    (∀ J, IsLabel n J → J ≠ trivLabel → pat (ρ.comp block) J = 0) ∨
    (∃ a, a < n ∧ ∀ J, IsLabel n J → pat (ρ.comp block) J = if J = constLabel {a} then 1 else 0) ∨
    (∃ a, a < n ∧ ∃ z, z ≤ 2 ∧ ∀ J, IsLabel n J → pat (ρ.comp block) J =
      (if J = trivLabel then z else 0) + ∑ s : Fin 3, if J = slotLabel s {a} then 1 else 0) := by
  set p := pat (ρ.comp block) with hpdef
  have hsing : ∀ {a : ℕ}, a < n → ∀ i ∈ ({a} : Finset ℕ), i < n :=
    fun ha i hi => (Finset.mem_singleton.mp hi) ▸ ha
  by_cases hA : ∃ a, a < n ∧ p (constLabel {a}) ≠ 0
  · obtain ⟨a, ha, hpa⟩ := hA
    right; left
    refine ⟨a, ha, fun J hJ => ?_⟩
    have hca : IsLabel n (constLabel {a}) := isLabel_constLabel (hsing ha)
    split_ifs with hJa
    · subst hJa
      have := sum_pat_le_finrank hK ρ (S := {constLabel {a}}) (by simpa using hca)
      rw [← hpdef, Finset.sum_singleton, lsize_constLabel] at this
      have := this.trans hdim
      have : 1 ≤ p (constLabel {a}) := Nat.one_le_iff_ne_zero.mpr hpa
      omega
    · have := sum_pat_le_finrank hK ρ (S := {constLabel {a}, J}) (by
        intro J' hJ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hJ'
        rcases hJ' with rfl | rfl
        exacts [hca, hJ])
      rw [← hpdef, Finset.sum_insert (by simpa using Ne.symm hJa), Finset.sum_singleton,
        lsize_constLabel] at this
      have h1 : 1 ≤ p (constLabel {a}) := Nat.one_le_iff_ne_zero.mpr hpa
      have h2 : 1 ≤ 2 ^ lsize J := Nat.one_le_two_pow
      by_contra hne
      have : 1 ≤ p J := Nat.one_le_iff_ne_zero.mpr hne
      nlinarith
  push Not at hA
  by_cases hB : ∃ s a, a < n ∧ p (slotLabel s {a}) ≠ 0
  · obtain ⟨s₀, a, ha, hpa⟩ := hB
    right; right
    have hsl : ∀ t, IsLabel n (slotLabel t {a}) := fun t => isLabel_slotLabel (hsing ha) t
    have heq : ∀ t, p (slotLabel t {a}) = p (slotLabel s₀ {a}) := fun t =>
      pat_slotLabel_eq hK ρ ha s₀ t
    have hd01 : slotLabel (0 : Fin 3) {a} ≠ slotLabel 1 {a} := fun h =>
      absurd (slotLabel_inj (Finset.singleton_nonempty a) h) (by decide)
    have hd02 : slotLabel (0 : Fin 3) {a} ≠ slotLabel 2 {a} := fun h =>
      absurd (slotLabel_inj (Finset.singleton_nonempty a) h) (by decide)
    have hd12 : slotLabel (1 : Fin 3) {a} ≠ slotLabel 2 {a} := fun h =>
      absurd (slotLabel_inj (Finset.singleton_nonempty a) h) (by decide)
    have hbig : ∀ J, IsLabel n J → J ≠ slotLabel 0 {a} → J ≠ slotLabel 1 {a} →
        J ≠ slotLabel 2 {a} → p (slotLabel 0 {a}) * 2 + p (slotLabel 1 {a}) * 2 +
          p (slotLabel 2 {a}) * 2 + p J * 2 ^ lsize J ≤ 8 := by
      intro J hJ h0 h1 h2
      have := sum_pat_le_finrank hK ρ (S := {slotLabel 0 {a}, slotLabel 1 {a}, slotLabel 2 {a}, J})
        (by
          intro J' hJ'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hJ'
          rcases hJ' with rfl | rfl | rfl | rfl
          exacts [hsl 0, hsl 1, hsl 2, hJ])
      rw [← hpdef, Finset.sum_insert (by simp [hd01, hd02, Ne.symm h0]),
        Finset.sum_insert (by simp [hd12, Ne.symm h1]), Finset.sum_insert (by simp [Ne.symm h2]),
        Finset.sum_singleton, lsize_slotLabel, lsize_slotLabel, lsize_slotLabel] at this
      omega
    have hm1 : p (slotLabel s₀ {a}) = 1 := by
      have := hbig trivLabel isLabel_trivLabel (Ne.symm (slotLabel_ne_trivLabel
        (Finset.singleton_nonempty a) 0)) (Ne.symm (slotLabel_ne_trivLabel
        (Finset.singleton_nonempty a) 1)) (Ne.symm (slotLabel_ne_trivLabel
        (Finset.singleton_nonempty a) 2))
      rw [heq 0, heq 1, heq 2] at this
      have : 1 ≤ p (slotLabel s₀ {a}) := Nat.one_le_iff_ne_zero.mpr hpa
      omega
    refine ⟨a, ha, p trivLabel, ?_, fun J hJ => ?_⟩
    · have := hbig trivLabel isLabel_trivLabel (Ne.symm (slotLabel_ne_trivLabel
        (Finset.singleton_nonempty a) 0)) (Ne.symm (slotLabel_ne_trivLabel
        (Finset.singleton_nonempty a) 1)) (Ne.symm (slotLabel_ne_trivLabel
        (Finset.singleton_nonempty a) 2))
      rw [heq 0, heq 1, heq 2, hm1, lsize_trivLabel] at this
      omega
    · by_cases hJt : J = trivLabel
      · subst hJt
        rw [if_pos rfl]
        simp [Fin.sum_univ_three, Ne.symm (slotLabel_ne_trivLabel (Finset.singleton_nonempty a) _)]
      rw [if_neg hJt, zero_add]
      by_cases hJs : ∃ t, J = slotLabel t {a}
      · obtain ⟨t, rfl⟩ := hJs
        rw [heq t, hm1, Finset.sum_eq_single t]
        · rw [if_pos rfl]
        · intro u _ hut
          rw [if_neg (fun h => hut (slotLabel_inj (Finset.singleton_nonempty a) h).symm)]
        · intro h
          exact absurd (Finset.mem_univ t) h
      · push Not at hJs
        rw [Finset.sum_eq_zero fun t _ => if_neg (hJs t)]
        by_contra hne
        rcases label_of_pat_ne_zero hK ρ hdim hJ hne with h | ⟨t, b, hb, rfl⟩ | ⟨b, hb, rfl⟩
        · exact hJt h
        ·
          have hab : b ≠ a := fun h => hJs t (h ▸ rfl)
          have hpb : ∀ u, p (slotLabel u {b}) = p (slotLabel t {b}) := fun u =>
            pat_slotLabel_eq hK ρ hb t u
          have hd : ∀ u v, slotLabel u {b} ≠ slotLabel v {a} := fun u v =>
            slotLabel_ne_slotLabel hab
          have hb1 : 1 ≤ p (slotLabel t {b}) := Nat.one_le_iff_ne_zero.mpr hne
          have := sum_pat_le_finrank hK ρ (S := {slotLabel 0 {a}, slotLabel 1 {a},
            slotLabel 2 {a}, slotLabel 0 {b}, slotLabel 1 {b}, slotLabel 2 {b}}) (by
              intro J' hJ'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hJ'
              rcases hJ' with rfl | rfl | rfl | rfl | rfl | rfl
              exacts [hsl 0, hsl 1, hsl 2, isLabel_slotLabel (hsing hb) 0,
                isLabel_slotLabel (hsing hb) 1, isLabel_slotLabel (hsing hb) 2])
          have hdb01 : slotLabel (0 : Fin 3) {b} ≠ slotLabel 1 {b} := fun h =>
            absurd (slotLabel_inj (Finset.singleton_nonempty b) h) (by decide)
          have hdb02 : slotLabel (0 : Fin 3) {b} ≠ slotLabel 2 {b} := fun h =>
            absurd (slotLabel_inj (Finset.singleton_nonempty b) h) (by decide)
          have hdb12 : slotLabel (1 : Fin 3) {b} ≠ slotLabel 2 {b} := fun h =>
            absurd (slotLabel_inj (Finset.singleton_nonempty b) h) (by decide)
          rw [← hpdef, Finset.sum_insert (by simp [hd01, hd02, Ne.symm (hd 0 0), Ne.symm (hd 1 0),
              Ne.symm (hd 2 0)]),
            Finset.sum_insert (by simp [hd12, Ne.symm (hd 0 1), Ne.symm (hd 1 1),
              Ne.symm (hd 2 1)]),
            Finset.sum_insert (by simp [Ne.symm (hd 0 2), Ne.symm (hd 1 2), Ne.symm (hd 2 2)]),
            Finset.sum_insert (by simp [hdb01, hdb02]), Finset.sum_insert (by simp [hdb12]),
            Finset.sum_singleton] at this
          simp only [lsize_slotLabel, pow_one] at this
          rw [heq 0, heq 1, heq 2, hm1, hpb 0, hpb 1, hpb 2] at this
          have := this.trans hdim
          omega
        · exact hne (hA b hb)
  · push Not at hB
    left
    intro J hJ hJt
    by_contra hne
    rcases label_of_pat_ne_zero hK ρ hdim hJ hne with h | ⟨t, b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · exact hJt h
    · exact hne (hB t b hb)
    · exact hne (hA b hb)

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
