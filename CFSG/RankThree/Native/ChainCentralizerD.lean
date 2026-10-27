module

public import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.ChainArrays

@[expose] def relOKD (base : Array ℕ) (ys : Array (Array ℕ)) (rels : List (ℕ × ℕ × ℕ)) (i : ℕ)
    (acc : Array ℕ) (q : ℕ) : Bool :=
  rels.all fun r => !(decide (max r.1 r.2.1 = i)) ||
    relImg base i acc q r.2.1 == (ys[r.2.2]!)[relImg base i acc q r.1]!

@[expose] def ptailOKD (n : ℕ) (L : Array Level) (base : Array ℕ) (gs ys : Array (Array ℕ))
    (rels : List (ℕ × ℕ × ℕ)) (mem : Array ℕ → Bool) : ℕ → ℕ → Array ℕ → Bool
  | 0, _, acc => !(gs.all (commA n acc)) || mem acc
  | fuel + 1, i, acc => allLt (L[i]!).pts.size fun k =>
      !(relOKD base ys rels i acc (L[i]!).pts[k]!) ||
        ptailOKD n L base gs ys rels mem fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem ptailOKD_spec {gs : Array (Array ℕ)} {G : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, Rep n gs[j]! (G j)) {ys : Array (Array ℕ)} {Y : ℕ → Equiv.Perm (Fin n)}
    (hys : ∀ j < ys.size, Rep n ys[j]! (Y j))
    (hY : ∀ c : Equiv.Perm (Fin n), (∀ j < gs.size, c * G j = G j * c) →
      ∀ j < ys.size, c * Y j = Y j * c)
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < ys.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (ys[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {mem : Array ℕ → Bool} :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      ptailOKD n (rawLevels n S base) base gs ys rels mem fuel i acc = true →
      ∀ h ∈ Q.levelSubgroup i, (∀ j < gs.size, A * h * G j = G j * (A * h)) →
        ∃ a, Rep n a (A * h) ∧ mem a = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc A hacc htail h hh hcomm
    rw [Nat.add_zero] at hi
    subst hi
    rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot] at hh
    subst hh
    simp only [mul_one] at hcomm ⊢
    have hc : gs.all (commA n acc) = true := by
      rw [Array.all_eq_true]
      intro j hj
      have := (commA_iff hacc (hgs j hj)).2 (hcomm j hj)
      rwa [getElem!_pos gs j hj] at this
    simp only [ptailOKD, hc, Bool.not_true, Bool.false_or] at htail
    exact ⟨acc, hacc, htail⟩
  | succ fuel ih =>
    intro i hi acc A hacc htail h hh hcomm
    have hib : i < Q.baseCount := by omega
    obtain ⟨k, hk, hpt, hk'⟩ := exists_levT_inv_mul_mem hA hF hQ hib hh
    have hstep := allLt_spec htail hk
    have hbase : ∀ m (hm : m < Q.baseCount), ((Q.base.get ⟨m, hm⟩ : Fin n) : ℕ) = base[m]! :=
      fun m hm => hA.base_val ⟨m, hm⟩
    have himg : ∀ m (hm : m ≤ i), relImg base i acc ((rawLevels n S base)[i]!).pts[k]! m =
        ((A * h) (Q.base.get ⟨m, by omega⟩) : ℕ) := by
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hlt | rfl
      · rw [relImg, ite_eq_left hlt, ← hbase m (by omega), hacc, Equiv.Perm.mul_apply,
          Q.levelSubgroup_fixes_base_index i h hh ⟨m, by omega⟩ hlt]
      · rw [relImg, ite_eq_right (lt_irrefl _), show ((rawLevels n S base)[m]!).pts[k]! =
          (lev n S base m).pts[k]! from rfl, hpt, hacc, Equiv.Perm.mul_apply]
    have hAhY := hY (A * h) hcomm
    have hrel : relOKD base ys rels i acc ((rawLevels n S base)[i]!).pts[k]! = true := by
      rw [relOKD, List.all_eq_true]
      intro r hr
      obtain ⟨hj, hl, hl', hry⟩ := hrels r hr
      rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
      by_cases hmax : max r.1 r.2.1 = i
      · right
        have hl1 : r.1 ≤ i := hmax ▸ le_max_left _ _
        have hl2 : r.2.1 ≤ i := hmax ▸ le_max_right _ _
        have hbs := hA.base_size
        have hYe : (Y r.2.2) (Q.base.get ⟨r.1, by omega⟩) = Q.base.get ⟨r.2.1, by omega⟩ := by
          apply Fin.ext
          rw [← hys r.2.2 hj, hbase r.1 (by omega), hbase r.2.1 (by omega), hry]
        rw [himg r.2.1 hl2, himg r.1 hl1, hys r.2.2 hj, ← hYe]
        congr 1
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hAhY r.2.2 hj]
      · exact Or.inl hmax
    rw [hrel, Bool.not_true, Bool.false_or] at hstep
    have hrep : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc (hA.rep_levT hF hib hk)
    have e : A * h = A * levT n S base i k * ((levT n S base i k)⁻¹ * h) := by group
    rw [e] at hcomm ⊢
    exact ih (i + 1) (by omega) _ _ hrep hstep _ hk' hcomm

theorem centralizer_subset_of_ptailOKD {gs : Array (Array ℕ)} {G : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, Rep n gs[j]! (G j)) {ys : Array (Array ℕ)} {Y : ℕ → Equiv.Perm (Fin n)}
    (hys : ∀ j < ys.size, Rep n ys[j]! (Y j))
    (hY : ∀ c : Equiv.Perm (Fin n), (∀ j < gs.size, c * G j = G j * c) →
      ∀ j < ys.size, c * Y j = Y j * c)
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < ys.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (ys[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {mem : Array ℕ → Bool}
    (htail : ptailOKD n (rawLevels n S base) base gs ys rels mem Q.baseCount 0 (idA n) = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup)
    (hgc : ∀ j < gs.size, g * G j = G j * g) : ∃ a, Rep n a g ∧ mem a = true := by
  rw [← Q.levelSubgroup_zero_eq_original hQ] at hg
  have hcomm : ∀ j < gs.size, 1 * g * G j = G j * (1 * g) := by
    intro j hj
    rw [one_mul]
    exact hgc j hj
  obtain ⟨a, hre, ha⟩ := ptailOKD_spec hA hF hQ hgs hys hY hrels Q.baseCount 0 (by omega)
    (idA n) 1 rep_idA htail g hg hcomm
  rw [one_mul] at hre
  exact ⟨a, hre, ha⟩

end Facts

end CFSG.RankThree.Native
