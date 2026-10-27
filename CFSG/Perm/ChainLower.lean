module

public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Schreier.J4SChain

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.LevelChain
  CFSG.Sporadic.LevelChain.Native CFSG.Sporadic.J4Schreier

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem card_lvlGroup_ge [Finite G] {letters : Array Table} {gs : ℕ → G} {starts base : Array ℕ}
    {trees : Array Tree}
    (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hinv : ∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true)
    (hsz : letters.size = 2 * starts[base.size]!) (hsts : starts.size = base.size + 1)
    (hmono : ∀ i < base.size, starts[i]! ≤ starts[i + 1]!)
    (htree : ∀ i < base.size,
      Perm.Native.treeOK n base[i]! trees[i]! letters (levelLv starts i) = true)
    (hfixgen : ∀ i, 1 ≤ i → i < base.size → ∀ j, starts[i]! ≤ j → j < starts[i + 1]! →
      ap letters[2 * j]! base[i - 1]! = base[i - 1]!)
    (hnest : ∀ i, 1 ≤ i → i < base.size → ∀ j, starts[i]! ≤ j → j < starts[i + 1]! →
      gs j ∈ lvlGroup starts gs (i - 1)) :
    ∀ i ≤ base.size, ∏ l ∈ Finset.Ico i base.size, trees[l]!.pts.size ≤
      Nat.card (lvlGroup starts gs i) := by
  set m := base.size with hm
  set lG := pairG gs with hlG
  have h2 : letters.size % 2 = 0 := by omega
  have hrepAll := rep_pairG hrep h2 hinv
  have hmono' := starts_mono hmono
  have hlvlt : ∀ i < m, ∀ l ∈ levelLv starts i, l < letters.size := by
    intro i hi l hl
    rw [mem_levelLv (hmono i hi)] at hl
    have := hmono' (i + 1) m (by omega) le_rfl
    omega
  have hTF : ∀ i < m, TreeFacts n trees[i]! (levelLv starts i) lG base[i]! :=
    fun i hi => treeOK_facts (fun l hl => hrepAll l (hlvlt i hi l hl)) (htree i hi)
  have hbot : lvlGroup starts gs m = ⊥ := by
    apply lvlGroup_eq_bot_of_le
    rw [getElem!_neg starts (m + 1) (by omega)]
    exact Nat.zero_le _
  have hstep : ∀ l', 1 ≤ l' → l' ≤ m → lvlGroup starts gs l' ≤ lvlGroup starts gs (l' - 1) := by
    intro l' hl1 hl2
    rcases Nat.eq_or_lt_of_le hl2 with rfl | hlt
    · rw [hbot]; exact bot_le
    · exact lvlGroup_le gs _ fun j hj1 hj2 => hnest l' hl1 hlt j hj1 hj2
  have hnestle : ∀ i l', i ≤ l' → l' ≤ m → lvlGroup starts gs l' ≤ lvlGroup starts gs i := by
    intro i l' hil hlm
    induction l' with
    | zero => obtain rfl : i = 0 := by omega
              exact le_rfl
    | succ l' ih =>
      rcases Nat.eq_or_lt_of_le hil with rfl | hlt
      · exact le_rfl
      · exact le_trans (hstep (l' + 1) (by omega) hlm) (ih (by omega) (by omega))
  have hfixb : ∀ i < m, ∀ g ∈ lvlGroup starts gs (i + 1), idx n g base[i]! = base[i]! := by
    intro i hi g hg
    have hb : base[i]! < n := (hTF i hi).r_lt
    rcases (show i + 1 = m ∨ i + 1 < m by omega) with heq | hlt
    · rw [heq, hbot, Subgroup.mem_bot] at hg
      rw [hg, idx_one]
    · have hle := lvlGroup_le (starts := starts) gs
        (MulAction.stabilizer G (⟨base[i]!, hb⟩ : Fin n)) (i := i + 1)
        (fun j hj1 hj2 => by
          rw [MulAction.mem_stabilizer_iff]
          apply Fin.ext
          rw [smul_val_eq_idx]
          have hjL : j < letters.size / 2 := by
            have := hmono' (i + 1 + 1) m (by omega) le_rfl
            omega
          rw [← hrep j hjL _ hb]
          exact hfixgen (i + 1) (by omega) hlt j hj1 hj2)
      have := hle hg
      rw [MulAction.mem_stabilizer_iff] at this
      have := congrArg Fin.val this
      rwa [smul_val_eq_idx] at this
  intro i hi
  induction h' : m - i generalizing i with
  | zero =>
    obtain rfl : i = m := by omega
    rw [hbot, Subgroup.card_bot, Finset.Ico_self, Finset.prod_empty]
  | succ d ih =>
    have him : i < m := by omega
    have hKH := hnestle i (i + 1) (Nat.le_succ i) (by omega)
    have hfix : ∀ g ∈ lvlGroup starts gs (i + 1),
        g • (⟨base[i]!, (hTF i him).r_lt⟩ : Fin n) = ⟨base[i]!, (hTF i him).r_lt⟩ :=
      fun g hg => Fin.ext (by rw [smul_val_eq_idx]; exact hfixb i him g hg)
    have h1 := card_eq_orbit_mul_stabilizer (lvlGroup starts gs i)
      (⟨base[i]!, (hTF i him).r_lt⟩ : Fin n)
    have h3 := card_le_card_stabilizer hKH hfix
    have h4 : (MulAction.orbit (lvlGroup starts gs i)
        (⟨base[i]!, (hTF i him).r_lt⟩ : Fin n)).ncard = trees[i]!.pts.size := by
      rw [← Nat.card_coe_set_eq]
      exact (hTF i him).card_orbit
    rw [Finset.prod_eq_prod_Ico_succ_bot him, h1, h4]
    exact Nat.mul_le_mul_left _ ((ih (i + 1) (by omega) (by omega)).trans h3)

end CFSG.Perm
