module

public import CFSG.LocalAnalysis.StandardType.PhanELocalParts
public import CFSG.LocalAnalysis.StandardType.PhanELocalProd

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

namespace PhanCode

@[expose] def IsIrr2 : PhanCode → Prop
  | a2chamber | a2panel | a2coll | a2pol | exchA1A1 => True
  | _ => False

@[expose] def IsIrr3 : PhanCode → Prop
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p
    | exchA2A1 => True
  | _ => False

theorem rank_pos (c : PhanCode) : 0 < c.rank := by
  induction c <;> simp [rank] <;> omega

theorem encard_univ_ι (c : PhanCode) : (Set.univ : Set c.ι).encard = (c.rank : ℕ∞) := by
  induction c with
  | prod c c' ihc ihc' =>
    show (Set.univ : Set (c.ι ⊕ c'.ι)).encard = ((c.rank + c'.rank : ℕ) : ℕ∞)
    rw [Set.encard_univ, ENat.card_sum, ← Set.encard_univ, ← Set.encard_univ, ihc, ihc']
    push_cast
    rfl
  | _ => simp [ι, rank, Set.encard_univ, ENat.card_sum]

end PhanCode

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem flagSys_one_adj (x y : FlagK K (1 + 1)) (i : Fin 1) : (flagSys K 1).adj i x y := by
  intro j hj
  have hi : i.val = 0 := Fin.val_eq_zero i
  rw [hi] at hj
  rcases Nat.lt_or_ge j 2 with h | h
  · have h0 : j = 0 := by omega
    subst h0
    rw [Submodule.finrank_eq_zero.1 (x.dim 0 (by omega)),
      Submodule.finrank_eq_zero.1 (y.dim 0 (by omega))]
  · rw [x.top j h, y.top j h]

theorem rank_one_connected (A : Set (FlagK K (1 + 1))) :
    ((flagSys K 1).restrict A).Connected :=
  fun x y => ⟨[((0 : Fin 1), y)], ⟨flagSys_one_adj K x.1 y.1 0, trivial⟩, rfl⟩

theorem PhanCode.connected_of_rank_one (c : PhanCode) (hc : c.rank = 1) :
    ((c.sys K).restrict (c.set K f)).Connected := by
  cases c with
  | prod c c' => have := rank_pos c; have := rank_pos c'; simp [rank] at hc; omega
  | _ => first | (simp [rank] at hc; done) | exact rank_one_connected K _

theorem phanModelsRank2_of_irr
    (h : ∀ c : PhanCode, c.IsIrr2 → ((c.sys K).restrict (c.set K f)).Connected) :
    PhanModelsRank2 K f := by
  intro c hc
  cases c with
  | prod c c' =>
    have h1 := PhanCode.rank_pos c
    have h2 := PhanCode.rank_pos c'
    simp only [PhanCode.rank] at hc
    exact connected_prod_restrict (PhanCode.connected_of_rank_one K f c (by omega))
      (PhanCode.connected_of_rank_one K f c' (by omega))
  | _ => first | exact h _ trivial | (simp [PhanCode.rank] at hc; done)

theorem phanModelsRank3_of_irr (h2 : PhanModelsRank2 K f)
    (h : ∀ c : PhanCode, c.IsIrr3 → ((c.sys K).restrict (c.set K f)).Connected ∧
      ((c.sys K).restrict (c.set K f)).SimplyTwoConnected) : PhanModelsRank3 K f := by
  intro c hc
  cases c with
  | prod c c' =>
    have h1 := PhanCode.rank_pos c
    have h1' := PhanCode.rank_pos c'
    simp only [PhanCode.rank] at hc
    have hconn : ∀ d : PhanCode, d.rank ≤ 2 → ((d.sys K).restrict (d.set K f)).Connected := by
      intro d hd
      have := PhanCode.rank_pos d
      rcases (by omega : d.rank = 1 ∨ d.rank = 2) with h | h
      exacts [PhanCode.connected_of_rank_one K f d h, h2 d h]
    refine ⟨connected_prod_restrict (hconn c (by omega)) (hconn c' (by omega)), ?_⟩
    refine simplyTwoConnected_prod_restrict (c.sys K) (c'.sys K) _ _ ?_ ?_
    · rw [PhanCode.encard_univ_ι]; exact_mod_cast (by omega : c.rank ≤ 2)
    · rw [PhanCode.encard_univ_ι]; exact_mod_cast (by omega : c'.rank ≤ 2)
  | _ => first | exact h _ trivial | (simp [PhanCode.rank] at hc; done)

end CFSG.ClassicalInvolution.Phan.PhanE

end
