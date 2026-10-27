
module

public import CFSG.Sporadic.Th.ChainBase

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

theorem Chain.mk_pl0 (a b : Table) (c : ℕ → Table) (d e : Table) (f : ℕ → Table) :
    (Chain.mk a b c d e f).pl0 = a := rfl

theorem Chain.mk_pos0 (a b : Table) (c : ℕ → Table) (d e : Table) (f : ℕ → Table) :
    (Chain.mk a b c d e f).pos0 = b := rfl

theorem Chain.mk_pl1 (a b : Table) (c : ℕ → Table) (d e : Table) (f : ℕ → Table) :
    (Chain.mk a b c d e f).pl1 = e := rfl

theorem Chain.mk_pts1 (a b : Table) (c : ℕ → Table) (d e : Table) (f : ℕ → Table) :
    (Chain.mk a b c d e f).pts1 = d := rfl

theorem chainT_pl0 : chainT.pl0 = q0T.2.1 :=
  Chain.mk_pl0 _ _ _ _ _ _

theorem chainT_pos0 : chainT.pos0 = q0T.2.2 :=
  Chain.mk_pos0 _ _ _ _ _ _

theorem chainT_pl1 : chainT.pl1 = q1T.2 :=
  Chain.mk_pl1 _ _ _ _ _ _

theorem chainT_pts1 : chainT.pts1 = q1T.1 :=
  Chain.mk_pts1 _ _ _ _ _ _

section Local

variable {c : ℕ} (hC : CertFacts c)
include hC

omit hC in
theorem levelTwo_stab_eq_one {G : Type*} [Group G] {n m : ℕ} [MulAction G (Fin n)] {g₁ g₂ : G}
    {pts pl : Table} {c : Chain} {gens : ℕ → Table} (hn : 124 ≤ n)
    (hT : TreeData n g₁ g₂ m 2 (ap pts) (findPt pts) pl)
    (hlev : ∀ k, 0 ≤ k → k < m → (levelTwoTest c gens 1 k && levelTwoTest c gens 2 k) = true)
    (hg : ∀ s, Rep n (gens s) (lettersG g₁ g₂ s))
    (hinv : ∀ s, Rep n (c.inv1 s) (lettersG g₁ g₂ s)⁻¹) (hpl : c.pl1 = pl) (hpts : c.pts1 = pts)
    (hres : ∀ {g r : G}, (∀ j < 124, idx n (r⁻¹ * g) j = j) → g = r) :
    ∀ l ∈ Subgroup.closure ({g₁, g₂} : Set G), idx n l 2 = 2 → l = 1 := by
  refine hT.stab_eq_one (P := fun s k => findPt pts (idx n (lettersG g₁ g₂ s) (ap pts k)))
    (fun s k _ => rfl) ?_
  intro k hk s hs
  have hks := hlev k (Nat.zero_le _) hk
  simp only [Bool.and_eq_true] at hks
  have hkn : ap c.pts1 k < n := by rw [hpts]; exact hT.pts_lt k hk
  have htest : levelTwoTest c gens s k = true := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hks.1
    · exact hks.2
  have := levelTwoTest_spec hn hg hinv hkn htest
  rw [hpl, hpts] at this
  exact hres (r := 1) (by simpa using this)

omit hC in
theorem levelOne_stab_le {G : Type*} [Group G] {n m : ℕ} [MulAction G (Fin n)] {g₁ g₂ : G}
    {lG : ℕ → G} {pts pl pos mx my : Table} {c : Chain} (K : Subgroup G) (hn : 124 ≤ n)
    (hT : TreeData n g₁ g₂ m 1 (ap pts) (ap pos) pl) (hg₁ : g₁ ^ 2 = 1) (hg₂ : g₂ ^ 3 = 1)
    (hx : Rep n mx g₁) (hy : Rep n my g₂)
    (hlev : ∀ k < m,
      ((!reqTwo pl (fun j => ap pos (ap mx (ap pts j))) 1 k ||
          levelOneTest pts c (letters mx my) 1 k) &&
        (!reqThree pl (fun j => ap pos (ap my (ap pts j))) 2 k ||
          levelOneTest pts c (letters mx my) 2 k)) = true)
    (hgl : ∀ s, Rep n (letters mx my s) (lettersG g₁ g₂ s))
    (h0 : ∀ s, Rep n (c.inv0 s) (lettersG g₁ g₂ s)⁻¹) (h1 : ∀ s, Rep n (c.inv1 s) (lG s)⁻¹)
    (hpl : c.pl0 = pl) (hpos : c.pos0 = pos) (hmemK : ∀ (t : Table) (k : ℕ), treeElt t lG k ∈ K)
    (hres : ∀ {g r : G}, (∀ j < 124, idx n (r⁻¹ * g) j = j) → g = r) :
    ∀ h ∈ Subgroup.closure ({g₁, g₂} : Set G), idx n h 1 = 1 → h ∈ K := by
  subst hpl hpos
  refine hT.stab_le_two_three hg₁ hg₂ K
    (P₁ := fun j => ap c.pos0 (ap mx (ap pts j)))
    (P₂ := fun j => ap c.pos0 (ap my (ap pts j)))
    (fun k hk => by rw [hx _ (hT.pts_lt k hk)])
    (fun k hk => by rw [hy _ (hT.pts_lt k hk)]) ?_ ?_
  · intro k hk hreq
    have hks := hlev k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hks
    have htest : levelOneTest pts c (letters mx my) 1 k = true := by
      rcases hks.1 with h | h
      · exact absurd (hreq.symm.trans h) (by decide)
      · exact h
    obtain ⟨k1, hk1⟩ := levelOneTest_spec hn hgl h0 h1 (hT.pts_lt k hk) htest
    have hxx : lettersG g₁ g₂ 1 = g₁ := by simp [lettersG]
    have hp : ap c.pos0 (idx n (lettersG g₁ g₂ 1) (ap pts k)) =
        ap c.pos0 (ap mx (ap pts k)) := by
      rw [hxx, hx _ (hT.pts_lt k hk)]
    have heq := hres hk1
    rw [hp] at heq
    rw [hxx] at heq
    rw [heq]
    exact hmemK _ k1
  · intro k hk hreq
    have hks := hlev k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hks
    have htest : levelOneTest pts c (letters mx my) 2 k = true := by
      rcases hks.2 with h | h
      · exact absurd (hreq.symm.trans h) (by decide)
      · exact h
    obtain ⟨k1, hk1⟩ := levelOneTest_spec hn hgl h0 h1 (hT.pts_lt k hk) htest
    have hyy : lettersG g₁ g₂ 2 = g₂ := by simp [lettersG]
    have hp : ap c.pos0 (idx n (lettersG g₁ g₂ 2) (ap pts k)) =
        ap c.pos0 (ap my (ap pts k)) := by
      rw [hyy, hy _ (hT.pts_lt k hk)]
    have heq := hres hk1
    rw [hp] at heq
    rw [hyy] at heq
    rw [heq]
    exact hmemK _ k1

theorem one_lt_nX : 1 < nX := lt_of_lt_of_le (by norm_num) (nX_ge hC)

theorem two_lt_nX : 2 < nX := lt_of_lt_of_le (by norm_num) (nX_ge hC)

end Local

end CFSG.Sporadic.Th
