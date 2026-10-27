module

public import CFSG.Quasithin.Recognition.St84.Sec4Switch
public import CFSG.Quasithin.Recognition.St84.Sec48E
public import CFSG.Quasithin.Recognition.St84.Sec4Move
public import CFSG.Quasithin.Recognition.St84.Sec4Extra

import CFSG.Quasithin.Recognition.St84.Sec4HypExists

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

theorem false_of_comm_eq_bot
    {r : ℕ} (H : X.Sec4Hyp s r) (hn : X.n 0 = X.n 1)
    {d : ℕ} (hd : X.HasB 1 d) (hR : ⁅X.Z 1, X.Z (d + 1)⁆ = ⊥) : False := by
  rcases Nat.even_or_odd (d + 1) with heven | hodd
  · exact Setup.Comm48.false (X := X) (s := s) (r := r) (d := d)
      { hyp := H, hasB := hd, even := heven, comm := hR } hn
  · obtain ⟨hr, d', hd', heven', hcomm'⟩ :=
      Setup.comm_eq_bot_switch X H hd hodd hR
    exact Setup.Comm48.false (X := X.swap) (s := s) (r := r) (d := d')
      { hyp := Setup.Sec4Hyp.swap X H hr, hasB := hd', even := heven', comm := hcomm' }
      (by simpa using hn.symm)

end Setup

theorem sec4_A5A5
    (hc : CharTwoStab (V := V) (G := G))
    (X : Setup Γ G) (hn : ∀ v, nOf Γ v = 2) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Odd (Nat.card X.GT)) :
    (s = 5 ∧ X.TreeSp44Data) ∨
      (s = 7 ∧ ((X.TreeG24Data ∧ X.TreeG24Extra ∧ X.TreeG24Transfer) ∨
        (X.swap.TreeG24Data ∧ X.swap.TreeG24Extra ∧ X.swap.TreeG24Transfer))) := by
  classical
  obtain ⟨m, H⟩ := X.exists_sec4Hyp hc (fun v => (hn v).ge) hs hodd h5 hX hGT
  rcases Setup.comm_Z_one_or_swap X H with
    ⟨d, hd, hR⟩ | ⟨hr, d, hd, hR, hR1⟩
  ·
    obtain ⟨d₀, hd₀⟩ := Setup.exists_hasB X H 0
    by_cases hbot : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ = ⊥
    · exact (Setup.false_of_comm_eq_bot X H
        ((hn (X.vert 0)).trans (hn (X.vert 1)).symm) hd hbot).elim
    · rcases Setup.s46_extra X H (fun i => hn (X.vert i)) hd₀ hd hR hbot with
        ⟨hs5, dA⟩ | ⟨hs7, dA⟩
      · exact Or.inl ⟨hs5, dA⟩
      · exact Or.inr ⟨hs7, Or.inl dA⟩
  ·
    have H' : X.swap.Sec4Hyp s (2 * m) := Setup.Sec4Hyp.swap X H hr
    obtain ⟨d₀, hd₀⟩ := Setup.exists_hasB X.swap H' 0
    rcases Setup.s46_extra X.swap H' (fun i => hn (X.swap.vert i)) hd₀ hd hR hR1 with
        ⟨hs5, dA⟩ | ⟨hs7, dA⟩
    · exact Or.inl ⟨hs5, Setup.TreeSp44Data.congr (X := X.swap.swap) (Y := X)
        (by simp) (by simp) (Setup.TreeSp44Data.swap (X := X.swap) dA)⟩
    · exact Or.inr ⟨hs7, Or.inr dA⟩

theorem sec4_A5A5_all
    (hc : CharTwoStab (V := V) (G := G))
    (X : Setup Γ G) (hn : ∀ v, nOf Γ v = 2) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Odd (Nat.card X.GT)) (Y : Setup Γ G) :
    (s = 5 ∧ Y.TreeSp44Data) ∨
      (s = 7 ∧ ((Y.TreeG24Data ∧ Y.TreeG24Extra ∧ Y.TreeG24Transfer) ∨
        (Y.swap.TreeG24Data ∧ Y.swap.TreeG24Extra ∧ Y.swap.TreeG24Transfer))) := by
  obtain ⟨g, -, hg⟩ := X.hyp.edgeTrans (X.vert 0) (X.vert 1) (Y.vert 0) (Y.vert 1)
    (by simpa using X.adj 0) (by simpa using Y.adj 0)
  have hmain := sec4_A5A5 hc X hn hs hodd h5 hX hGT
  rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases hmain with ⟨hs5, d⟩ | ⟨hs7, ⟨d, e, c⟩ | ⟨d, e, c⟩⟩
    · exact Or.inl ⟨hs5, Setup.TreeSp44Data.smul g h0 h1 d⟩
    · exact Or.inr ⟨hs7, Or.inl ⟨Setup.TreeG24Data.smul g h0 h1 d,
        Setup.TreeG24Extra.smul g h0 h1 e, Setup.TreeG24Transfer.smul g h0 h1 c⟩⟩
    · exact Or.inr ⟨hs7, Or.inr ⟨Setup.TreeG24Data.smul g h1 h0 d,
        Setup.TreeG24Extra.smul g h1 h0 e, Setup.TreeG24Transfer.smul g h1 h0 c⟩⟩
  · rcases hmain with ⟨hs5, d⟩ | ⟨hs7, ⟨d, e, c⟩ | ⟨d, e, c⟩⟩
    · exact Or.inl ⟨hs5,
        Setup.TreeSp44Data.smul g h1 h0 (Setup.TreeSp44Data.swap (X := X) d)⟩
    · exact Or.inr ⟨hs7, Or.inr ⟨Setup.TreeG24Data.smul g h0 h1 d,
        Setup.TreeG24Extra.smul g h0 h1 e, Setup.TreeG24Transfer.smul g h0 h1 c⟩⟩
    · exact Or.inr ⟨hs7, Or.inl ⟨Setup.TreeG24Data.smul g h1 h0 d,
        Setup.TreeG24Extra.smul g h1 h0 e, Setup.TreeG24Transfer.smul g h1 h0 c⟩⟩

end CFSG.Quasithin.St84
