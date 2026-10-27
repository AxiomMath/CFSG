module

public import CFSG.Quasithin.Recognition.St84.Gen.TransportSp4q
public import CFSG.Quasithin.Recognition.St84.Gen.TransportD4q
public import CFSG.Quasithin.Recognition.St84.Gen.G2qVertexData
public import CFSG.Quasithin.Recognition.St84.Gen.TransportU4q
public import CFSG.Quasithin.Recognition.St84.Gen.Sec46D4qDefs
public import CFSG.Quasithin.Recognition.St84.Sec46Cases
public import CFSG.Quasithin.Recognition.St84.Sec45
public import CFSG.Quasithin.Recognition.St84.Sec48A

import CFSG.Quasithin.Recognition.St84.Gen.Sec46D4q
import CFSG.Quasithin.Recognition.St84.Gen.Sec46G2q
import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qOfCaseB
import CFSG.Quasithin.Recognition.St84.Sec4Switch
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Sec5Tree
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.Quasithin.F112R.St84

namespace Setup

section Row

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Sec4Row (X : Setup Γ G) : Prop :=
  (X.n 1 = X.n 0 ∧ Sp4qLocalData (X.L 0) (X.L 1) X.S (X.n 0)) ∨
    (X.n 0 = 3 * X.n 1 ∧ D4qLocalData (X.L 0) (X.L 1) X.S (X.n 1)) ∨
    (X.n 1 = X.n 0 ∧ G2qVertexData (X.L 0) (X.L 1) X.S (X.n 0)) ∨
    (X.n 1 = 2 * X.n 0 ∧ U4qLocalData (X.L 0) (X.L 1) X.S (X.n 0))

theorem sec4Row_swap_iff (X : Setup Γ G) :
    X.swap.Sec4Row ↔
      (X.n 0 = X.n 1 ∧ Sp4qLocalData (X.L 1) (X.L 0) X.S (X.n 1)) ∨
        (X.n 1 = 3 * X.n 0 ∧ D4qLocalData (X.L 1) (X.L 0) X.S (X.n 0)) ∨
        (X.n 0 = X.n 1 ∧ G2qVertexData (X.L 1) (X.L 0) X.S (X.n 1)) ∨
        (X.n 0 = 2 * X.n 1 ∧ U4qLocalData (X.L 1) (X.L 0) X.S (X.n 1)) := by
  simp [Sec4Row]

theorem sec4Row_swap_swap_iff (X : Setup Γ G) : X.swap.swap.Sec4Row ↔ X.Sec4Row := by
  simp [Sec4Row]

end Row

section Outcome

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem sec4Row_of_noncomm (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) (hA : X.CaseA → X.CaseAGen) : X.Sec4Row := by
  rcases Nat.even_or_odd d₁ with hev | hodd
  · obtain ⟨-, -, -, A⟩ := X.caseA_of H hd₁ hR hR1 hev
    have AG := hA A
    by_cases hn : X.n 1 = X.n 0
    · exact Or.inr (Or.inr (Or.inl ⟨hn, X.caseA_g2q AG hn⟩))
    · obtain ⟨h3, hD, -⟩ := X.caseA_d4q AG hn
      exact Or.inr (Or.inl ⟨h3, hD⟩)
  · obtain ⟨-, -, -, -, B⟩ := X.caseB_of H hd₀ hd₁ hR hR1 hodd
    exact Or.inl (X.caseB_sp4q_of_caseB B)

theorem sec4Row_of
    (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) (hA : ∀ Y : Setup Γ G, Y.CaseA → Y.CaseAGen)
    (hV4 : ∀ (Y : Setup Γ G) {r d : ℕ}, Y.Sec4Hyp s r → Y.HasB 1 d →
      ⁅Y.Z 1, Y.Z ((d : ℤ) + 1)⁆ = ⊥ → Y.Sec4Row ∨ Y.swap.Sec4Row) :
    X.Sec4Row ∨ X.swap.Sec4Row := by
  rcases Setup.comm_Z_one_or_swap X H with ⟨d, hd, hR⟩ | ⟨hr, d, hd, hR, hR1⟩
  · obtain ⟨d₀, hd₀⟩ := Setup.exists_hasB X H 0
    by_cases hbot : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ = ⊥
    · exact hV4 X H hd hbot
    · exact Or.inl (X.sec4Row_of_noncomm H hd₀ hd hR hbot (hA X))
  · have H' : X.swap.Sec4Hyp s r := Setup.Sec4Hyp.swap X H hr
    obtain ⟨d₀, hd₀⟩ := Setup.exists_hasB X.swap H' 0
    exact Or.inr (X.swap.sec4Row_of_noncomm H' hd₀ hd hR hR1 (hA X.swap))

theorem sec4Row_of_comm_eq_bot
    (hC : ∀ (Y : Setup Γ G) {r d : ℕ}, Y.Comm48 s r d →
      Y.n 1 = 2 * Y.n 0 ∧ U4qLocalData (Y.L 0) (Y.L 1) Y.S (Y.n 0))
    (X : Setup Γ G) {r d : ℕ} (H : X.Sec4Hyp s r) (hd : X.HasB 1 d)
    (hR : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ = ⊥) : X.Sec4Row ∨ X.swap.Sec4Row := by
  rcases Nat.even_or_odd (d + 1) with heven | hodd
  · exact Or.inl (Or.inr (Or.inr (Or.inr
      (hC X { hyp := H, hasB := hd, even := heven, comm := hR }))))
  · obtain ⟨hr, d', hd', heven', hcomm'⟩ := Setup.comm_eq_bot_switch X H hd hodd hR
    exact Or.inr (Or.inr (Or.inr (Or.inr (hC X.swap
      { hyp := Setup.Sec4Hyp.swap X H hr, hasB := hd', even := heven', comm := hcomm' }))))

end Outcome

end Setup

end CFSG.Quasithin.St84

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
open SimpleGraph CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.Stroth

variable {H : Type} [Group H] [Finite H]

theorem f112ll_exists_setup_rightSingular {L1 L2 S : Subgroup H} {m n s : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hs : IsSingularity (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) s) (hodd : Odd s) :
    ∃ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      ((X.vert 0 = baseA (f112Gold L1 L2 S) ∧ X.vert 1 = baseB (f112Gold L1 L2 S)) ∨
        (X.vert 0 = baseB (f112Gold L1 L2 S) ∧ X.vert 1 = baseA (f112Gold L1 L2 S))) ∧
      ¬ RightTransitive (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)
        (X.line.arc 0 s).vert 0 s := by
  have h30 := f112ll_hyp30 hF hm hn h1 h2
  have hloc : ∀ v a b, (f112Gold L1 L2 S).treeGraph.Adj v a →
      (f112Gold L1 L2 S).treeGraph.Adj v b →
      ∃ g ∈ MulAction.stabilizer ↥(f112EOdd L1 L2 S) v, g • a = b :=
    fun v a b ha hb => h30.locTrans ha hb
  rcases singularity_dichotomy h30.isTree h30.adj_smul hloc h30.edgeTrans h30.preservesParts
    hs with ⟨hev, -⟩ | ⟨-, o, ho⟩
  · exact absurd hev (Nat.not_even_iff_odd.mpr hodd)
  have key : ∀ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      Even ((f112Gold L1 L2 S).treeGraph.dist o (X.vert 0)) →
      ¬ RightTransitive (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)
        (X.line.arc 0 s).vert 0 s := by
    intro X h0
    refine (ho s le_rfl (X.line.arc 0 s)).1 ?_
    have h := X.odd_dist_vert_of_even o hodd h0
    simpa [Line.arc] using h
  have hadj := adj_baseA_baseB (f112Gold L1 L2 S)
  rcases Nat.even_or_odd ((f112Gold L1 L2 S).treeGraph.dist o (baseA (f112Gold L1 L2 S))) with
    hα | hα
  · obtain ⟨X, hX0, hX1⟩ := f112ll_exists_setup_baseEdge hF hm hn h1 h2
    exact ⟨X, Or.inl ⟨hX0, hX1⟩, key X (hX0 ▸ hα)⟩
  · have hβ : Even ((f112Gold L1 L2 S).treeGraph.dist o (baseB (f112Gold L1 L2 S))) := by
      obtain ⟨k, hk⟩ := hα
      rcases IsTree.dist_adj_cases h30.isTree (r := o) hadj with h | h
      · exact ⟨k + 1, by omega⟩
      · exact ⟨k, by omega⟩
    obtain ⟨Y, hY0, hY1⟩ := f112ll_exists_setup_baseEdge_swap hF hm hn h1 h2
    exact ⟨Y, Or.inr ⟨hY0, hY1⟩, key Y (hY0 ▸ hβ)⟩

private theorem f112ll_n_base {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    X.n 0 = m ∧ X.n 1 = n := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  constructor
  · rw [Setup.n, hX0]
    simpa using f112_nOf_alpha_of_isL2Quot hR (by omega) h1 (1 : (f112Gold L1 L2 S).Universal)
  · rw [Setup.n, hX1]
    simpa using f112_nOf_beta_of_isL2Quot hR (by omega) h2 (1 : (f112Gold L1 L2 S).Universal)

theorem f112ll_rows_of_sec4Row {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hg2 : ∀ f, G2qVertexData (X.L 0) (X.L 1) X.S f → m = n ∧ G2qLocalData L1 L2 S n)
    (hg2' : ∀ f, G2qVertexData (X.L 1) (X.L 0) X.S f → m = n ∧ G2qLocalData L2 L1 S n)
    (hrow : X.Sec4Row ∨ X.swap.Sec4Row) :
    (m = n ∧ (L3qLocalData L1 L2 S n ∨ Sp4qLocalData L1 L2 S n ∨
        G2qLocalData L1 L2 S n ∨ G2qLocalData L2 L1 S n)) ∨
      (m = 3 * n ∧ D4qLocalData L1 L2 S n) ∨ (n = 3 * m ∧ D4qLocalData L2 L1 S m) ∨
      (n = 2 * m ∧ U4qLocalData L1 L2 S m) ∨ (m = 2 * n ∧ U4qLocalData L2 L1 S n) := by
  obtain ⟨hX0n, hX1n⟩ := f112ll_n_base hF hm hn h1 h2 hX0 hX1
  rcases hrow with h | h
  · rcases h with ⟨-, hd⟩ | ⟨-, hd⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · obtain ⟨hmn', hD⟩ := f112ll_sp4qLocalData_of_tree hF hm hn h1 h2 hX0 hX1
        (by rw [hX0n]; exact hm) hd
      exact Or.inl ⟨hmn', Or.inr (Or.inl hD)⟩
    · exact Or.inr (Or.inl (f112ll_d4qLocalData_of_tree hF hm hn h1 h2 hX0 hX1 hd))
    · obtain ⟨hmn', hD⟩ := hg2 _ hd
      exact Or.inl ⟨hmn', Or.inr (Or.inr (Or.inl hD))⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (f112ll_u4qLocalData_of_tree hF hm hn h1 h2 hX0 hX1 hd))))
  · rw [Setup.sec4Row_swap_iff] at h
    rcases h with ⟨-, hd⟩ | ⟨-, hd⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · obtain ⟨hmn', hD⟩ := f112ll_sp4qLocalData_of_tree hF hm hn h1 h2 hX0 hX1
        (by rw [hX1n]; exact hn) hd.symm
      exact Or.inl ⟨hmn', Or.inr (Or.inl hD)⟩
    · exact Or.inr (Or.inr (Or.inl (f112ll_d4qLocalData_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd)))
    · obtain ⟨hmn', hD⟩ := hg2' _ hd
      exact Or.inl ⟨hmn', Or.inr (Or.inr (Or.inr hD))⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (f112ll_u4qLocalData_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd))))

theorem f112ll_odd_of_sec4 {L1 L2 S : Subgroup H} {m n s : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hs : IsSingularity (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) s) (hodd : Odd s)
    (hhyp : ∀ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      ¬ RightTransitive (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)
        (X.line.arc 0 s).vert 0 s → ∃ k : ℕ, X.Sec4Hyp s (2 * k))
    (hsec4 : ∀ (X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)) (r : ℕ),
      X.Sec4Hyp s r → X.Sec4Row ∨ X.swap.Sec4Row)
    (hg2 : ∀ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      X.vert 0 = baseA (f112Gold L1 L2 S) → X.vert 1 = baseB (f112Gold L1 L2 S) →
        ∀ f, G2qVertexData (X.L 0) (X.L 1) X.S f → m = n ∧ G2qLocalData L1 L2 S n)
    (hg2' : ∀ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      X.vert 0 = baseA (f112Gold L1 L2 S) → X.vert 1 = baseB (f112Gold L1 L2 S) →
        ∀ f, G2qVertexData (X.L 1) (X.L 0) X.S f → m = n ∧ G2qLocalData L2 L1 S n) :
    (m = n ∧ (L3qLocalData L1 L2 S n ∨ Sp4qLocalData L1 L2 S n ∨
        G2qLocalData L1 L2 S n ∨ G2qLocalData L2 L1 S n)) ∨
      (m = 3 * n ∧ D4qLocalData L1 L2 S n) ∨ (n = 3 * m ∧ D4qLocalData L2 L1 S m) ∨
      (n = 2 * m ∧ U4qLocalData L1 L2 S m) ∨ (m = 2 * n ∧ U4qLocalData L2 L1 S n) := by
  obtain ⟨X, hXbase, hX⟩ := f112ll_exists_setup_rightSingular hF hm hn h1 h2 hs hodd
  obtain ⟨k, H⟩ := hhyp X hX
  have hrow := hsec4 X (2 * k) H
  rcases hXbase with ⟨hX0, hX1⟩ | ⟨hX0, hX1⟩
  · exact f112ll_rows_of_sec4Row hF hm hn h1 h2 hX0 hX1 (hg2 X hX0 hX1) (hg2' X hX0 hX1) hrow
  · have hZ0 : X.swap.vert 0 = baseA (f112Gold L1 L2 S) := by simpa using hX1
    have hZ1 : X.swap.vert 1 = baseB (f112Gold L1 L2 S) := by simpa using hX0
    refine f112ll_rows_of_sec4Row hF hm hn h1 h2 hZ0 hZ1 (hg2 X.swap hZ0 hZ1)
      (hg2' X.swap hZ0 hZ1) ?_
    rcases hrow with h | h
    · exact Or.inr ((Setup.sec4Row_swap_swap_iff X).mpr h)
    · exact Or.inl h

end CFSG.Quasithin.F112R.St84

end
