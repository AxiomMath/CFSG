module

public import CFSG.LocalAnalysis.StandardType.GGHalfE6CertDefs

public section

namespace CFSG.StandardType

@[expose] def ggHalfEntries : GGHalfBlk → List (ℕ × ℕ × List ℤ)
  | .L => [
    (0, 1, [1, 2, 2, 3, 2, 1]),
    (0, 2, [0, 1, 0, 1, 0, 0]),
    (0, 3, [0, 1, 0, 1, 1, 0]),
    (0, 4, [0, 1, 0, 0, 0, 0]),
    (0, 5, [0, 1, 0, 1, 1, 1]),
    (1, 0, [-1, -2, -2, -3, -2, -1]),
    (1, 2, [-1, -1, -2, -2, -2, -1]),
    (1, 3, [-1, -1, -2, -2, -1, -1]),
    (1, 4, [-1, -1, -2, -3, -2, -1]),
    (1, 5, [-1, -1, -2, -2, -1, 0]),
    (2, 0, [0, -1, 0, -1, 0, 0]),
    (2, 1, [1, 1, 2, 2, 2, 1]),
    (2, 3, [0, 0, 0, 0, 1, 0]),
    (2, 4, [0, 0, 0, -1, 0, 0]),
    (2, 5, [0, 0, 0, 0, 1, 1]),
    (3, 0, [0, -1, 0, -1, -1, 0]),
    (3, 1, [1, 1, 2, 2, 1, 1]),
    (3, 2, [0, 0, 0, 0, -1, 0]),
    (3, 4, [0, 0, 0, -1, -1, 0]),
    (3, 5, [0, 0, 0, 0, 0, 1]),
    (4, 0, [0, -1, 0, 0, 0, 0]),
    (4, 1, [1, 1, 2, 3, 2, 1]),
    (4, 2, [0, 0, 0, 1, 0, 0]),
    (4, 3, [0, 0, 0, 1, 1, 0]),
    (4, 5, [0, 0, 0, 1, 1, 1]),
    (5, 0, [0, -1, 0, -1, -1, -1]),
    (5, 1, [1, 1, 2, 2, 1, 0]),
    (5, 2, [0, 0, 0, 0, -1, -1]),
    (5, 3, [0, 0, 0, 0, 0, -1]),
    (5, 4, [0, 0, 0, -1, -1, -1])]
  | .K => [
    (2, 3, [0, 0, 0, 0, 1, 0]),
    (2, 4, [0, 0, 0, -1, 0, 0]),
    (2, 5, [0, 0, 0, 0, 1, 1]),
    (2, 6, [0, 0, -1, -1, 0, 0]),
    (2, 7, [-1, 0, -1, -1, 0, 0]),
    (3, 2, [0, 0, 0, 0, -1, 0]),
    (3, 4, [0, 0, 0, -1, -1, 0]),
    (3, 5, [0, 0, 0, 0, 0, 1]),
    (3, 6, [0, 0, -1, -1, -1, 0]),
    (3, 7, [-1, 0, -1, -1, -1, 0]),
    (4, 2, [0, 0, 0, 1, 0, 0]),
    (4, 3, [0, 0, 0, 1, 1, 0]),
    (4, 5, [0, 0, 0, 1, 1, 1]),
    (4, 6, [0, 0, -1, 0, 0, 0]),
    (4, 7, [-1, 0, -1, 0, 0, 0]),
    (5, 2, [0, 0, 0, 0, -1, -1]),
    (5, 3, [0, 0, 0, 0, 0, -1]),
    (5, 4, [0, 0, 0, -1, -1, -1]),
    (5, 6, [0, 0, -1, -1, -1, -1]),
    (5, 7, [-1, 0, -1, -1, -1, -1]),
    (6, 2, [0, 0, 1, 1, 0, 0]),
    (6, 3, [0, 0, 1, 1, 1, 0]),
    (6, 4, [0, 0, 1, 0, 0, 0]),
    (6, 5, [0, 0, 1, 1, 1, 1]),
    (6, 7, [-1, 0, 0, 0, 0, 0]),
    (7, 2, [1, 0, 1, 1, 0, 0]),
    (7, 3, [1, 0, 1, 1, 1, 0]),
    (7, 4, [1, 0, 1, 0, 0, 0]),
    (7, 5, [1, 0, 1, 1, 1, 1]),
    (7, 6, [1, 0, 0, 0, 0, 0])]
  | .M => [
    (2, 3, [1, 2, 2, 3, 2, 1]),
    (2, 4, [0, 1, 0, 0, 0, 0]),
    (2, 5, [0, 1, 0, 1, 1, 1]),
    (2, 6, [1, 1, 1, 1, 1, 1]),
    (2, 7, [0, 1, 1, 1, 1, 1]),
    (3, 2, [-1, -2, -2, -3, -2, -1]),
    (3, 4, [-1, -1, -2, -3, -2, -1]),
    (3, 5, [-1, -1, -2, -2, -1, 0]),
    (3, 6, [0, -1, -1, -2, -1, 0]),
    (3, 7, [-1, -1, -1, -2, -1, 0]),
    (4, 2, [0, -1, 0, 0, 0, 0]),
    (4, 3, [1, 1, 2, 3, 2, 1]),
    (4, 5, [0, 0, 0, 1, 1, 1]),
    (4, 6, [1, 0, 1, 1, 1, 1]),
    (4, 7, [0, 0, 1, 1, 1, 1]),
    (5, 2, [0, -1, 0, -1, -1, -1]),
    (5, 3, [1, 1, 2, 2, 1, 0]),
    (5, 4, [0, 0, 0, -1, -1, -1]),
    (5, 6, [1, 0, 1, 0, 0, 0]),
    (5, 7, [0, 0, 1, 0, 0, 0]),
    (6, 2, [-1, -1, -1, -1, -1, -1]),
    (6, 3, [0, 1, 1, 2, 1, 0]),
    (6, 4, [-1, 0, -1, -1, -1, -1]),
    (6, 5, [-1, 0, -1, 0, 0, 0]),
    (6, 7, [-1, 0, 0, 0, 0, 0]),
    (7, 2, [0, -1, -1, -1, -1, -1]),
    (7, 3, [1, 1, 1, 2, 1, 0]),
    (7, 4, [0, 0, -1, -1, -1, -1]),
    (7, 5, [0, 0, -1, 0, 0, 0]),
    (7, 6, [1, 0, 0, 0, 0, 0])]

@[expose] def ggHalfM0 : GGHalfE6Model where
  frame b c d := fun i =>
    ((ggHalfEntries b).find? fun e => e.1 = c.val ∧ e.2.1 = d.val).elim 0 fun e => e.2.2.getD i.val 0

open CFSG.Blueprint.Chevalley

private def mkVec (l : List ℤ) : GGE6Root := fun i => l.getD i.val 0

private instance decidableLab (b : GGHalfBlk) (a : Fin 8) : Decidable (b.Lab a) := by
  cases b <;> unfold GGHalfBlk.Lab <;> infer_instance

private instance : Fintype GGHalfBlk where
  elems := {.L, .K, .M}
  complete := by intro x; cases x <;> simp

private lemma memY_of_frame {b : GGHalfBlk} {c d : Fin 8}
    (hc : b.Lab c) (hd : b.Lab d) (hcd : c ≠ d) :
    ggHalfM0.frame b c d ∈ ggHalfM0.Y b :=
  ⟨c, d, hc, hd, hcd, rfl⟩

private lemma memY_of_frame_eq {b : GGHalfBlk} {c d : Fin 8} {r : GGE6Root}
    (hc : b.Lab c) (hd : b.Lab d) (hcd : c ≠ d) (heq : ggHalfM0.frame b c d = r) :
    r ∈ ggHalfM0.Y b := by
  rw [← heq]; exact memY_of_frame hc hd hcd

private theorem mem_rootFinset_of_root {v : GGE6Root} {k : ℕ} (hk : k < 72)
    (h : e6Certificate.root k = v) : v ∈ rootFinset .E6 := by
  rw [rootFinset, List.mem_toFinset, List.mem_map]
  refine ⟨k, List.mem_range.mpr ?_, h⟩
  show k < 72
  exact hk

private lemma vec_ne_of_ne (a b : GGE6Root) (i : Fin (Tag.rank .E6)) (h : a i ≠ b i) :
    a ≠ b :=
  fun hab => h (congrFun hab i)

private lemma der_base_of {b : GGHalfBlk} {r : GGE6Root} (hr : r ∈ ggHalfM0.Y b)
    {j : Fin (Tag.rank .E6)}
    (hi : r = GGHalfE6Model.simpleRoot j ∨ r = -GGHalfE6Model.simpleRoot j) :
    GGHalfE6Model.Der ggHalfM0 b r :=
  GGHalfE6Model.Der.base hr hi

private lemma der_refl_of {b : GGHalfBlk} {g h r ng : GGE6Root}
    (hg : GGHalfE6Model.Der ggHalfM0 b g) (hng : GGHalfE6Model.Der ggHalfM0 b ng)
    (hng_eq : ng = -g) (hh : GGHalfE6Model.Der ggHalfM0 b h)
    (hhg : h ≠ g) (hhn : h ≠ ng) (hr : r ∈ ggHalfM0.Y b) (heq : ggE6Refl g h = r) :
    GGHalfE6Model.Der ggHalfM0 b r := by
  rw [hng_eq] at hng
  rw [hng_eq] at hhn
  subst heq
  exact GGHalfE6Model.Der.refl hg hng hh hhg hhn hr

private lemma der_transfer_of {b c : GGHalfBlk} {r : GGE6Root}
    (hb : GGHalfE6Model.Der ggHalfM0 b r) (hc : r ∈ ggHalfM0.Y c) :
    GGHalfE6Model.Der ggHalfM0 c r :=
  GGHalfE6Model.Der.transfer hb hc

private lemma der_transportH_of {b c : GGHalfBlk} {r s : GGE6Root}
    (hK : ∀ t ∈ ggHalfM0.Y .K, GGHalfE6Model.Der ggHalfM0 .K t)
    (hb : GGHalfE6Model.Der ggHalfM0 b r)
    (hbc : (b = .L ∧ c = .M ∧ ggHalfM0.wh r ∈ ggHalfM0.Y .M) ∨
           (b = .M ∧ c = .L ∧ ggHalfM0.wh r ∈ ggHalfM0.Y .L))
    (heq : ggHalfM0.wh r = s) : GGHalfE6Model.Der ggHalfM0 c s := by
  subst heq
  exact GGHalfE6Model.Der.transportH hK hb hbc

private theorem frameOK_L_1 :
    ∀ c d : Fin 8, (GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d) →
      ggHalfM0.frame .L c d ∈ rootFinset .E6 := by decide +kernel
private theorem frameOK_L_2 :
    ∀ c d : Fin 8, (GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d) →
      ggHalfM0.frame .L d c = -ggHalfM0.frame .L c d := by decide +kernel
private theorem frameOK_L_3 :
    ∀ c d e : Fin 8,
      (GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ GGHalfBlk.L.Lab e ∧ c ≠ d ∧ d ≠ e ∧ c ≠ e) →
        ggHalfM0.frame .L c d + ggHalfM0.frame .L d e = ggHalfM0.frame .L c e := by decide +kernel
private theorem frameOK_L_4 :
    ∀ i j k l : Fin 8,
      (GGHalfBlk.L.Lab i ∧ GGHalfBlk.L.Lab j ∧ GGHalfBlk.L.Lab k ∧ GGHalfBlk.L.Lab l ∧
        i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i)) →
      ggHalfM0.frame .L i j + ggHalfM0.frame .L k l ≠ 0 := by decide +kernel
private theorem frameOK_L_5 :
    ∀ i j k l : Fin 8,
      (GGHalfBlk.L.Lab i ∧ GGHalfBlk.L.Lab j ∧ GGHalfBlk.L.Lab k ∧ GGHalfBlk.L.Lab l ∧
        i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i) ∧ j ≠ k ∧ i ≠ l) →
      ggHalfM0.frame .L i j + ggHalfM0.frame .L k l ∉ rootFinset .E6 := by decide +kernel

private theorem frameOK_K_1 :
    ∀ c d : Fin 8, (GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ c ≠ d) →
      ggHalfM0.frame .K c d ∈ rootFinset .E6 := by decide +kernel
private theorem frameOK_K_2 :
    ∀ c d : Fin 8, (GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ c ≠ d) →
      ggHalfM0.frame .K d c = -ggHalfM0.frame .K c d := by decide +kernel
private theorem frameOK_K_3 :
    ∀ c d e : Fin 8,
      (GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ GGHalfBlk.K.Lab e ∧ c ≠ d ∧ d ≠ e ∧ c ≠ e) →
        ggHalfM0.frame .K c d + ggHalfM0.frame .K d e = ggHalfM0.frame .K c e := by decide +kernel
private theorem frameOK_K_4 :
    ∀ i j k l : Fin 8,
      (GGHalfBlk.K.Lab i ∧ GGHalfBlk.K.Lab j ∧ GGHalfBlk.K.Lab k ∧ GGHalfBlk.K.Lab l ∧
        i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i)) →
      ggHalfM0.frame .K i j + ggHalfM0.frame .K k l ≠ 0 := by decide +kernel
private theorem frameOK_K_5 :
    ∀ i j k l : Fin 8,
      (GGHalfBlk.K.Lab i ∧ GGHalfBlk.K.Lab j ∧ GGHalfBlk.K.Lab k ∧ GGHalfBlk.K.Lab l ∧
        i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i) ∧ j ≠ k ∧ i ≠ l) →
      ggHalfM0.frame .K i j + ggHalfM0.frame .K k l ∉ rootFinset .E6 := by decide +kernel

private theorem frameOK_M_1 :
    ∀ c d : Fin 8, (GGHalfBlk.M.Lab c ∧ GGHalfBlk.M.Lab d ∧ c ≠ d) →
      ggHalfM0.frame .M c d ∈ rootFinset .E6 := by decide +kernel
private theorem frameOK_M_2 :
    ∀ c d : Fin 8, (GGHalfBlk.M.Lab c ∧ GGHalfBlk.M.Lab d ∧ c ≠ d) →
      ggHalfM0.frame .M d c = -ggHalfM0.frame .M c d := by decide +kernel
private theorem frameOK_M_3 :
    ∀ c d e : Fin 8,
      (GGHalfBlk.M.Lab c ∧ GGHalfBlk.M.Lab d ∧ GGHalfBlk.M.Lab e ∧ c ≠ d ∧ d ≠ e ∧ c ≠ e) →
        ggHalfM0.frame .M c d + ggHalfM0.frame .M d e = ggHalfM0.frame .M c e := by decide +kernel
private theorem frameOK_M_4 :
    ∀ i j k l : Fin 8,
      (GGHalfBlk.M.Lab i ∧ GGHalfBlk.M.Lab j ∧ GGHalfBlk.M.Lab k ∧ GGHalfBlk.M.Lab l ∧
        i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i)) →
      ggHalfM0.frame .M i j + ggHalfM0.frame .M k l ≠ 0 := by decide +kernel
private theorem frameOK_M_5 :
    ∀ i j k l : Fin 8,
      (GGHalfBlk.M.Lab i ∧ GGHalfBlk.M.Lab j ∧ GGHalfBlk.M.Lab k ∧ GGHalfBlk.M.Lab l ∧
        i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i) ∧ j ≠ k ∧ i ≠ l) →
      ggHalfM0.frame .M i j + ggHalfM0.frame .M k l ∉ rootFinset .E6 := by decide +kernel

private theorem frameOK_L : ggHalfM0.FrameOK .L := by
  unfold GGHalfE6Model.FrameOK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c d hc hd hcd; exact frameOK_L_1 c d ⟨hc, hd, hcd⟩
  · intro c d hc hd hcd; exact frameOK_L_2 c d ⟨hc, hd, hcd⟩
  · intro c d e hc hd he hcd hde hce; exact frameOK_L_3 c d e ⟨hc, hd, he, hcd, hde, hce⟩
  · intro i j k l hi hj hk hl hij hkl hne
    exact frameOK_L_4 i j k l ⟨hi, hj, hk, hl, hij, hkl, hne⟩
  · intro i j k l hi hj hk hl hij hkl hne hjk hil
    exact frameOK_L_5 i j k l ⟨hi, hj, hk, hl, hij, hkl, hne, hjk, hil⟩

private theorem frameOK_K : ggHalfM0.FrameOK .K := by
  unfold GGHalfE6Model.FrameOK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c d hc hd hcd; exact frameOK_K_1 c d ⟨hc, hd, hcd⟩
  · intro c d hc hd hcd; exact frameOK_K_2 c d ⟨hc, hd, hcd⟩
  · intro c d e hc hd he hcd hde hce; exact frameOK_K_3 c d e ⟨hc, hd, he, hcd, hde, hce⟩
  · intro i j k l hi hj hk hl hij hkl hne
    exact frameOK_K_4 i j k l ⟨hi, hj, hk, hl, hij, hkl, hne⟩
  · intro i j k l hi hj hk hl hij hkl hne hjk hil
    exact frameOK_K_5 i j k l ⟨hi, hj, hk, hl, hij, hkl, hne, hjk, hil⟩

private theorem frameOK_M : ggHalfM0.FrameOK .M := by
  unfold GGHalfE6Model.FrameOK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c d hc hd hcd; exact frameOK_M_1 c d ⟨hc, hd, hcd⟩
  · intro c d hc hd hcd; exact frameOK_M_2 c d ⟨hc, hd, hcd⟩
  · intro c d e hc hd he hcd hde hce; exact frameOK_M_3 c d e ⟨hc, hd, he, hcd, hde, hce⟩
  · intro i j k l hi hj hk hl hij hkl hne
    exact frameOK_M_4 i j k l ⟨hi, hj, hk, hl, hij, hkl, hne⟩
  · intro i j k l hi hj hk hl hij hkl hne hjk hil
    exact frameOK_M_5 i j k l ⟨hi, hj, hk, hl, hij, hkl, hne, hjk, hil⟩

private theorem perp_L_ip :
    ∀ c d : Fin 8, (GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d) →
      ggE6ip (ggHalfM0.frame .L c d) (![-1,0,0,0,0,0] : GGE6Root) = 0 := by decide +kernel
private theorem perp_L_back :
    ∀ r ∈ rootFinset .E6, ggE6ip r (![-1,0,0,0,0,0] : GGE6Root) = 0 →
      (∃ c d : Fin 8, GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d ∧
        ggHalfM0.frame .L c d = r) := by decide +kernel
private theorem perp_L : ggHalfM0.Perp .L := by
  refine ⟨(![-1,0,0,0,0,0] : GGE6Root),
    mem_rootFinset_of_root (k := 6) (by decide) (by funext x; fin_cases x <;> decide), ?_⟩
  intro r
  constructor
  · intro hr
    obtain ⟨c, d, hc, hd, hcd, hr'⟩ := hr
    exact ⟨by rw [← hr']; exact frameOK_L_1 c d ⟨hc, hd, hcd⟩,
      by rw [← hr']; exact perp_L_ip c d ⟨hc, hd, hcd⟩⟩
  · intro h
    exact perp_L_back r h.1 h.2

private theorem perp_K_ip :
    ∀ c d : Fin 8, (GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ c ≠ d) →
      ggE6ip (ggHalfM0.frame .K c d) (![1,2,2,3,2,1] : GGE6Root) = 0 := by decide +kernel
private theorem perp_K_back :
    ∀ r ∈ rootFinset .E6, ggE6ip r (![1,2,2,3,2,1] : GGE6Root) = 0 →
      (∃ c d : Fin 8, GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ c ≠ d ∧
        ggHalfM0.frame .K c d = r) := by decide +kernel
private theorem perp_K : ggHalfM0.Perp .K := by
  refine ⟨(![1,2,2,3,2,1] : GGE6Root),
    mem_rootFinset_of_root (k := 70) (by decide) (by funext x; fin_cases x <;> decide), ?_⟩
  intro r
  constructor
  · intro hr
    obtain ⟨c, d, hc, hd, hcd, hr'⟩ := hr
    exact ⟨by rw [← hr']; exact frameOK_K_1 c d ⟨hc, hd, hcd⟩,
      by rw [← hr']; exact perp_K_ip c d ⟨hc, hd, hcd⟩⟩
  · intro h
    exact perp_K_back r h.1 h.2

private theorem perp_M_ip :
    ∀ c d : Fin 8, (GGHalfBlk.M.Lab c ∧ GGHalfBlk.M.Lab d ∧ c ≠ d) →
      ggE6ip (ggHalfM0.frame .M c d) (![0,0,0,0,1,0] : GGE6Root) = 0 := by decide +kernel
private theorem perp_M_back :
    ∀ r ∈ rootFinset .E6, ggE6ip r (![0,0,0,0,1,0] : GGE6Root) = 0 →
      (∃ c d : Fin 8, GGHalfBlk.M.Lab c ∧ GGHalfBlk.M.Lab d ∧ c ≠ d ∧
        ggHalfM0.frame .M c d = r) := by decide +kernel
private theorem perp_M : ggHalfM0.Perp .M := by
  refine ⟨(![0,0,0,0,1,0] : GGE6Root),
    mem_rootFinset_of_root (k := 4) (by decide) (by funext x; fin_cases x <;> decide), ?_⟩
  intro r
  constructor
  · intro hr
    obtain ⟨c, d, hc, hd, hcd, hr'⟩ := hr
    exact ⟨by rw [← hr']; exact frameOK_M_1 c d ⟨hc, hd, hcd⟩,
      by rw [← hr']; exact perp_M_ip c d ⟨hc, hd, hcd⟩⟩
  · intro h
    exact perp_M_back r h.1 h.2

private theorem overlap_frame1 :
    ∀ c d : Fin 8, (2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d) →
      ggHalfM0.frame .L c d = ggHalfM0.frame .K c d := by decide +kernel
private theorem overlap_frame2 :
    ∀ c d : Fin 8, (2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d) →
      ggHalfM0.frame .M c d = ggHalfM0.frame .L (ggHalfSigma c) (ggHalfSigma d) := by decide +kernel
private theorem overlap_frame3 :
    ∀ c d : Fin 8, (4 ≤ c.val ∧ 4 ≤ d.val ∧ c ≠ d) →
      ggHalfM0.frame .M c d = ggHalfM0.frame .K (ggHalfPi d) (ggHalfPi c) := by decide +kernel

private theorem overlap_LK_fwd :
    ∀ c d e f : Fin 8,
      (GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d ∧ GGHalfBlk.K.Lab e ∧ GGHalfBlk.K.Lab f ∧
        e ≠ f ∧ ggHalfM0.frame .L c d = ggHalfM0.frame .K e f) →
      (∃ c' d' : Fin 8, 2 ≤ c'.val ∧ c'.val < 6 ∧ 2 ≤ d'.val ∧ d'.val < 6 ∧ c' ≠ d' ∧
        ggHalfM0.frame .L c' d' = ggHalfM0.frame .L c d) := by decide +kernel
private theorem overlap_LK_bwd :
    ∀ c d : Fin 8, (2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d) →
      (∃ e f : Fin 8, GGHalfBlk.K.Lab e ∧ GGHalfBlk.K.Lab f ∧ e ≠ f ∧
        ggHalfM0.frame .K e f = ggHalfM0.frame .L c d) := by decide +kernel
private theorem overlap_LK :
    ggHalfM0.Y .L ∩ ggHalfM0.Y .K =
      {r | ∃ c d : Fin 8, 2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d ∧
        ggHalfM0.frame .L c d = r} := by
  ext r
  constructor
  · rintro ⟨⟨c, d, hc, hd, hcd, hrL⟩, ⟨e, f, he, hf, hef, hrK⟩⟩
    obtain ⟨c', d', h1, h2, h3, h4, hcd', hf'⟩ :=
      overlap_LK_fwd c d e f ⟨hc, hd, hcd, he, hf, hef, by rw [hrL, ← hrK]⟩
    exact ⟨c', d', h1, h2, h3, h4, hcd', by rw [hf', hrL]⟩
  · rintro ⟨c, d, h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨c, d, h2, h4, h5, h6⟩, ?_⟩
    obtain ⟨e, f, he, hf, hef, hf'⟩ := overlap_LK_bwd c d ⟨h1, h2, h3, h4, h5⟩
    exact ⟨e, f, he, hf, hef, by rw [hf', h6]⟩

private theorem overlap_LM_fwd :
    ∀ c d e f : Fin 8,
      (GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d ∧ GGHalfBlk.M.Lab e ∧ GGHalfBlk.M.Lab f ∧
        e ≠ f ∧ ggHalfM0.frame .L c d = ggHalfM0.frame .M e f) →
      (∃ c' d' : Fin 8, 2 ≤ c'.val ∧ c'.val < 6 ∧ 2 ≤ d'.val ∧ d'.val < 6 ∧ c' ≠ d' ∧
        ggHalfM0.frame .M c' d' = ggHalfM0.frame .L c d) := by decide +kernel
private theorem overlap_LM_bwd :
    ∀ c d : Fin 8, (2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d) →
      (∃ e f : Fin 8, GGHalfBlk.L.Lab e ∧ GGHalfBlk.L.Lab f ∧ e ≠ f ∧
        ggHalfM0.frame .L e f = ggHalfM0.frame .M c d) := by decide +kernel
private theorem overlap_LM :
    ggHalfM0.Y .L ∩ ggHalfM0.Y .M =
      {r | ∃ c d : Fin 8, 2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d ∧
        ggHalfM0.frame .M c d = r} := by
  ext r
  constructor
  · rintro ⟨⟨c, d, hc, hd, hcd, hrL⟩, ⟨e, f, he, hf, hef, hrM⟩⟩
    obtain ⟨c', d', h1, h2, h3, h4, hcd', hf'⟩ :=
      overlap_LM_fwd c d e f ⟨hc, hd, hcd, he, hf, hef, by rw [hrL, ← hrM]⟩
    exact ⟨c', d', h1, h2, h3, h4, hcd', by rw [hf', hrL]⟩
  · rintro ⟨c, d, h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ⟨c, d, h1, h3, h5, h6⟩⟩
    obtain ⟨e, f, he, hf, hef, hf'⟩ := overlap_LM_bwd c d ⟨h1, h2, h3, h4, h5⟩
    exact ⟨e, f, he, hf, hef, by rw [hf', h6]⟩

private theorem overlap_MK_fwd :
    ∀ c d e f : Fin 8,
      (GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ c ≠ d ∧ GGHalfBlk.M.Lab e ∧ GGHalfBlk.M.Lab f ∧
        e ≠ f ∧ ggHalfM0.frame .K c d = ggHalfM0.frame .M e f) →
      (∃ c' d' : Fin 8, 4 ≤ c'.val ∧ 4 ≤ d'.val ∧ c' ≠ d' ∧
        ggHalfM0.frame .M c' d' = ggHalfM0.frame .K c d) := by decide +kernel
private theorem overlap_MK_bwd :
    ∀ c d : Fin 8, (4 ≤ c.val ∧ 4 ≤ d.val ∧ c ≠ d) →
      (∃ e f : Fin 8, GGHalfBlk.K.Lab e ∧ GGHalfBlk.K.Lab f ∧ e ≠ f ∧
        ggHalfM0.frame .K e f = ggHalfM0.frame .M c d) := by decide +kernel
private theorem overlap_KM :
    ggHalfM0.Y .K ∩ ggHalfM0.Y .M =
      {r | ∃ c d : Fin 8, 4 ≤ c.val ∧ 4 ≤ d.val ∧ c ≠ d ∧ ggHalfM0.frame .M c d = r} := by
  ext r
  constructor
  · rintro ⟨⟨c, d, hc, hd, hcd, hrK⟩, ⟨e, f, he, hf, hef, hrM⟩⟩
    obtain ⟨c', d', h1, h2, h3, h4⟩ :=
      overlap_MK_fwd c d e f ⟨hc, hd, hcd, he, hf, hef, by rw [hrK, ← hrM]⟩
    exact ⟨c', d', h1, h2, h3, by rw [h4, hrK]⟩
  · rintro ⟨c, d, h1, h2, h3, h4⟩
    refine ⟨?_, ⟨c, d, le_trans (by decide : (2:ℕ) ≤ 4) h1, le_trans (by decide : (2:ℕ) ≤ 4) h2, h3, h4⟩⟩
    obtain ⟨e, f, he, hf, hef, hf'⟩ := overlap_MK_bwd c d ⟨h1, h2, h3⟩
    exact ⟨e, f, he, hf, hef, by rw [hf', h4]⟩

private theorem overlap : ggHalfM0.Overlap := by
  unfold GGHalfE6Model.Overlap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d h1 h2 h3 h4 h5; exact overlap_frame1 c d ⟨h1, h2, h3, h4, h5⟩
  · intro c d h1 h2 h3 h4 h5; exact overlap_frame2 c d ⟨h1, h2, h3, h4, h5⟩
  · intro c d h1 h2 h3; exact overlap_frame3 c d ⟨h1, h2, h3⟩
  · exact overlap_LK
  · exact overlap_LM
  · exact overlap_KM

private theorem weyl_1 :
    ∀ c d : Fin 8, (2 ≤ c.val ∧ 2 ≤ d.val ∧ c ≠ d) →
      ggHalfM0.frame .M c d = ggHalfM0.wg (ggHalfM0.frame .K c d) := by decide +kernel
private theorem weyl_2 :
    ∀ c d : Fin 8, (2 ≤ c.val ∧ 2 ≤ d.val ∧ c ≠ d) →
      ggHalfM0.frame .M c d = ggHalfM0.wh (ggHalfM0.frame .L (ggHalfS d) (ggHalfS c)) := by
  decide +kernel
private theorem weyl : ggHalfM0.Weyl := by
  unfold GGHalfE6Model.Weyl
  refine ⟨?_, ?_⟩
  · intro c d h1 h2 h3; exact weyl_1 c d ⟨h1, h2, h3⟩
  · intro c d h1 h2 h3; exact weyl_2 c d ⟨h1, h2, h3⟩

private theorem pairs_common :
    ∀ i j : Fin (Tag.rank .E6),
      ∃ b : GGHalfBlk, GGHalfE6Model.simpleRoot i ∈ ggHalfM0.Y b ∧
        GGHalfE6Model.simpleRoot j ∈ ggHalfM0.Y b := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.M, memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.M, memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.M, memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.M, memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.K, memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩
  · exact ⟨.L, memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide), memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)⟩

private def ggHalfLList : List GGE6Root :=
  [(mkVec [0,1,0,0,0,0]),
   (mkVec [0,-1,0,0,0,0]),
   (mkVec [0,0,0,1,0,0]),
   (mkVec [0,0,0,-1,0,0]),
   (mkVec [0,0,0,0,1,0]),
   (mkVec [0,0,0,0,-1,0]),
   (mkVec [0,0,0,0,0,1]),
   (mkVec [0,0,0,0,0,-1]),
   (mkVec [0,0,0,0,-1,-1]),
   (mkVec [0,0,0,0,1,1]),
   (mkVec [0,1,0,1,0,0]),
   (mkVec [0,-1,0,-1,0,0]),
   (mkVec [0,0,0,1,1,0]),
   (mkVec [0,0,0,-1,-1,0]),
   (mkVec [0,0,0,-1,-1,-1]),
   (mkVec [0,0,0,1,1,1]),
   (mkVec [0,-1,0,-1,-1,-1]),
   (mkVec [0,1,0,1,1,1]),
   (mkVec [0,-1,0,-1,-1,0]),
   (mkVec [0,1,0,1,1,0]),
   (mkVec [1,1,2,2,1,0]),
   (mkVec [-1,-1,-2,-3,-2,-1]),
   (mkVec [1,1,2,2,1,1]),
   (mkVec [1,1,2,2,2,1]),
   (mkVec [-1,-1,-2,-2,-2,-1]),
   (mkVec [-1,-1,-2,-2,-1,0]),
   (mkVec [-1,-1,-2,-2,-1,-1]),
   (mkVec [1,1,2,3,2,1]),
   (mkVec [1,2,2,3,2,1]),
   (mkVec [-1,-2,-2,-3,-2,-1])]

private def ggHalfKList : List GGE6Root :=
  [(mkVec [1,0,0,0,0,0]),
   (mkVec [-1,0,0,0,0,0]),
   (mkVec [0,0,1,0,0,0]),
   (mkVec [0,0,-1,0,0,0]),
   (mkVec [0,0,0,1,0,0]),
   (mkVec [0,0,0,-1,0,0]),
   (mkVec [0,0,0,0,1,0]),
   (mkVec [0,0,0,0,-1,0]),
   (mkVec [0,0,0,0,0,1]),
   (mkVec [0,0,0,0,0,-1]),
   (mkVec [0,0,0,0,1,1]),
   (mkVec [0,0,0,-1,-1,0]),
   (mkVec [0,0,0,1,1,0]),
   (mkVec [0,0,0,0,-1,-1]),
   (mkVec [0,0,0,-1,-1,-1]),
   (mkVec [0,0,0,1,1,1]),
   (mkVec [1,0,1,0,0,0]),
   (mkVec [0,0,1,1,0,0]),
   (mkVec [0,0,-1,-1,-1,0]),
   (mkVec [0,0,-1,-1,0,0]),
   (mkVec [-1,0,-1,0,0,0]),
   (mkVec [0,0,1,1,1,0]),
   (mkVec [0,0,1,1,1,1]),
   (mkVec [-1,0,-1,-1,-1,-1]),
   (mkVec [0,0,-1,-1,-1,-1]),
   (mkVec [1,0,1,1,1,1]),
   (mkVec [-1,0,-1,-1,-1,0]),
   (mkVec [1,0,1,1,1,0]),
   (mkVec [-1,0,-1,-1,0,0]),
   (mkVec [1,0,1,1,0,0])]

private def ggHalfMList : List GGE6Root :=
  [(mkVec [1,0,0,0,0,0]),
   (mkVec [-1,0,0,0,0,0]),
   (mkVec [0,1,0,0,0,0]),
   (mkVec [0,-1,0,0,0,0]),
   (mkVec [0,0,1,0,0,0]),
   (mkVec [0,0,-1,0,0,0]),
   (mkVec [0,0,0,-1,-1,-1]),
   (mkVec [-1,0,-1,0,0,0]),
   (mkVec [0,0,0,1,1,1]),
   (mkVec [1,0,1,0,0,0]),
   (mkVec [0,0,-1,-1,-1,-1]),
   (mkVec [0,0,1,1,1,1]),
   (mkVec [0,-1,0,-1,-1,-1]),
   (mkVec [0,1,0,1,1,1]),
   (mkVec [-1,0,-1,-1,-1,-1]),
   (mkVec [1,0,1,1,1,1]),
   (mkVec [0,1,1,1,1,1]),
   (mkVec [0,-1,-1,-1,-1,-1]),
   (mkVec [1,1,1,1,1,1]),
   (mkVec [-1,-1,-1,-1,-1,-1]),
   (mkVec [1,1,1,2,1,0]),
   (mkVec [1,1,2,3,2,1]),
   (mkVec [1,1,2,2,1,0]),
   (mkVec [-1,-1,-2,-3,-2,-1]),
   (mkVec [-1,-1,-1,-2,-1,0]),
   (mkVec [0,1,1,2,1,0]),
   (mkVec [0,-1,-1,-2,-1,0]),
   (mkVec [-1,-1,-2,-2,-1,0]),
   (mkVec [1,2,2,3,2,1]),
   (mkVec [-1,-2,-2,-3,-2,-1])]

private theorem derL_decode :
    ∀ t ∈ rootFinset .E6,
      (∃ c d : Fin 8, GGHalfBlk.L.Lab c ∧ GGHalfBlk.L.Lab d ∧ c ≠ d ∧
        ggHalfM0.frame .L c d = t) → t ∈ ggHalfLList := by decide +kernel

private theorem derK_decode :
    ∀ t ∈ rootFinset .E6,
      (∃ c d : Fin 8, GGHalfBlk.K.Lab c ∧ GGHalfBlk.K.Lab d ∧ c ≠ d ∧
        ggHalfM0.frame .K c d = t) → t ∈ ggHalfKList := by decide +kernel

private theorem derM_decode :
    ∀ t ∈ rootFinset .E6,
      (∃ c d : Fin 8, GGHalfBlk.M.Lab c ∧ GGHalfBlk.M.Lab d ∧ c ≠ d ∧
        ggHalfM0.frame .M c d = t) → t ∈ ggHalfMList := by decide +kernel

private theorem ggHalfDer0 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [1,0,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨0, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer1 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [-1,0,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨0, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer2 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,0,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨0, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer3 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,0,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .M) (c := ⟨6, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨0, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer4 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,1,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨1, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer5 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,-1,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨0, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨1, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer6 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,1,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨1, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer7 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,-1,0,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .M) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨1, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer8 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,1,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨2, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer9 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,-1,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨2, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer10 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,0,1,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨2, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer11 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,0,-1,0,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨2, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer12 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,1,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨3, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer13 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,-1,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨3, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer14 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,1,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨3, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer15 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,-1,0,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨3, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer16 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,0,1,0]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨4, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer17 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,0,-1,0]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨4, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer18 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,0,1,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨4, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer19 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,0,-1,0]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨4, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer20 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,0,0,1]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨5, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer21 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,0,0,-1]) :=
  der_base_of ((memY_of_frame_eq (b := .L) (c := ⟨5, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨5, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer22 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,0,0,1]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨5, by decide⟩) (Or.inl (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer23 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,0,0,-1]) :=
  der_base_of ((memY_of_frame_eq (b := .K) (c := ⟨5, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (j := ⟨5, by decide⟩) (Or.inr (by funext x; fin_cases x <;> decide))

private theorem ggHalfDer24 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,0,-1,-1]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [0,0,0,0,-1,0])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer21 ggHalfDer20 (by funext x; fin_cases x <;> decide) ggHalfDer17 (vec_ne_of_ne (mkVec [0,0,0,0,-1,0]) (mkVec [0,0,0,0,0,-1]) ⟨4, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,0,-1,0]) (mkVec [0,0,0,0,0,1]) ⟨4, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨5, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer25 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,0,1,1]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [0,0,0,0,1,0])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer21 ggHalfDer20 (by funext x; fin_cases x <;> decide) ggHalfDer16 (vec_ne_of_ne (mkVec [0,0,0,0,1,0]) (mkVec [0,0,0,0,0,-1]) ⟨4, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,0,1,0]) (mkVec [0,0,0,0,0,1]) ⟨4, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer26 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,1,0,1,0,0]) :=
  der_refl_of (g := (mkVec [0,1,0,0,0,0])) (h := (mkVec [0,0,0,1,0,0])) (ng := (mkVec [0,-1,0,0,0,0])) ggHalfDer4 ggHalfDer5 (by funext x; fin_cases x <;> decide) ggHalfDer12 (vec_ne_of_ne (mkVec [0,0,0,1,0,0]) (mkVec [0,1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,0,0]) (mkVec [0,-1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer27 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,-1,0,-1,0,0]) :=
  der_refl_of (g := (mkVec [0,1,0,0,0,0])) (h := (mkVec [0,0,0,-1,0,0])) (ng := (mkVec [0,-1,0,0,0,0])) ggHalfDer4 ggHalfDer5 (by funext x; fin_cases x <;> decide) ggHalfDer13 (vec_ne_of_ne (mkVec [0,0,0,-1,0,0]) (mkVec [0,1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,0,0]) (mkVec [0,-1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨0, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer28 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,1,1,0]) :=
  der_refl_of (g := (mkVec [0,0,0,0,-1,0])) (h := (mkVec [0,0,0,1,0,0])) (ng := (mkVec [0,0,0,0,1,0])) ggHalfDer17 ggHalfDer16 (by funext x; fin_cases x <;> decide) ggHalfDer12 (vec_ne_of_ne (mkVec [0,0,0,1,0,0]) (mkVec [0,0,0,0,-1,0]) ⟨3, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,0,0]) (mkVec [0,0,0,0,1,0]) ⟨3, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer29 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,-1,-1,0]) :=
  der_refl_of (g := (mkVec [0,0,0,0,-1,0])) (h := (mkVec [0,0,0,-1,0,0])) (ng := (mkVec [0,0,0,0,1,0])) ggHalfDer17 ggHalfDer16 (by funext x; fin_cases x <;> decide) ggHalfDer13 (vec_ne_of_ne (mkVec [0,0,0,-1,0,0]) (mkVec [0,0,0,0,-1,0]) ⟨3, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,0,0]) (mkVec [0,0,0,0,1,0]) ⟨3, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer30 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,0,1,1]) :=
  der_transfer_of ggHalfDer25 ((memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer31 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,-1,-1,0]) :=
  der_transfer_of ggHalfDer29 ((memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer32 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,1,1,0]) :=
  der_transfer_of ggHalfDer28 ((memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer33 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,0,-1,-1]) :=
  der_transfer_of ggHalfDer24 ((memY_of_frame_eq (b := .K) (c := ⟨5, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer34 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,-1,-1,-1]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [0,0,0,-1,-1,0])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer23 ggHalfDer22 (by funext x; fin_cases x <;> decide) ggHalfDer31 (vec_ne_of_ne (mkVec [0,0,0,-1,-1,0]) (mkVec [0,0,0,0,0,-1]) ⟨3, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,-1,0]) (mkVec [0,0,0,0,0,1]) ⟨3, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨5, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer35 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,0,1,1,1]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [0,0,0,1,1,0])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer23 ggHalfDer22 (by funext x; fin_cases x <;> decide) ggHalfDer32 (vec_ne_of_ne (mkVec [0,0,0,1,1,0]) (mkVec [0,0,0,0,0,-1]) ⟨3, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,1,0]) (mkVec [0,0,0,0,0,1]) ⟨3, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer36 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [1,0,1,0,0,0]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [1,0,0,0,0,0])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer8 ggHalfDer9 (by funext x; fin_cases x <;> decide) ggHalfDer0 (vec_ne_of_ne (mkVec [1,0,0,0,0,0]) (mkVec [0,0,1,0,0,0]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [1,0,0,0,0,0]) (mkVec [0,0,-1,0,0,0]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer37 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,1,1,0,0]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [0,0,0,1,0,0])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer8 ggHalfDer9 (by funext x; fin_cases x <;> decide) ggHalfDer14 (vec_ne_of_ne (mkVec [0,0,0,1,0,0]) (mkVec [0,0,1,0,0,0]) ⟨2, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,0,0]) (mkVec [0,0,-1,0,0,0]) ⟨2, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer38 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,-1,-1,-1,0]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [0,0,0,-1,-1,0])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer8 ggHalfDer9 (by funext x; fin_cases x <;> decide) ggHalfDer31 (vec_ne_of_ne (mkVec [0,0,0,-1,-1,0]) (mkVec [0,0,1,0,0,0]) ⟨2, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,-1,0]) (mkVec [0,0,-1,0,0,0]) ⟨2, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer39 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,-1,-1,0,0]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [0,0,0,-1,0,0])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer8 ggHalfDer9 (by funext x; fin_cases x <;> decide) ggHalfDer15 (vec_ne_of_ne (mkVec [0,0,0,-1,0,0]) (mkVec [0,0,1,0,0,0]) ⟨2, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,0,0]) (mkVec [0,0,-1,0,0,0]) ⟨2, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer40 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [-1,0,-1,0,0,0]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [-1,0,0,0,0,0])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer8 ggHalfDer9 (by funext x; fin_cases x <;> decide) ggHalfDer1 (vec_ne_of_ne (mkVec [-1,0,0,0,0,0]) (mkVec [0,0,1,0,0,0]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [-1,0,0,0,0,0]) (mkVec [0,0,-1,0,0,0]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨4, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer41 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,1,1,1,0]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [0,0,0,1,1,0])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer8 ggHalfDer9 (by funext x; fin_cases x <;> decide) ggHalfDer32 (vec_ne_of_ne (mkVec [0,0,0,1,1,0]) (mkVec [0,0,1,0,0,0]) ⟨2, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,1,0]) (mkVec [0,0,-1,0,0,0]) ⟨2, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer42 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,-1,-1,-1]) :=
  der_transfer_of ggHalfDer34 ((memY_of_frame_eq (b := .L) (c := ⟨5, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer43 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,0,0,1,1,1]) :=
  der_transfer_of ggHalfDer35 ((memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer44 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,0,0,-1,-1,-1]) :=
  der_transfer_of ggHalfDer34 ((memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer45 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,0,-1,0,0,0]) :=
  der_transfer_of ggHalfDer40 ((memY_of_frame_eq (b := .M) (c := ⟨6, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer46 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,0,0,1,1,1]) :=
  der_transfer_of ggHalfDer35 ((memY_of_frame_eq (b := .M) (c := ⟨4, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer47 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,0,1,0,0,0]) :=
  der_transfer_of ggHalfDer36 ((memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer48 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,0,-1,-1,-1,-1]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [0,0,0,-1,-1,-1])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer10 ggHalfDer11 (by funext x; fin_cases x <;> decide) ggHalfDer44 (vec_ne_of_ne (mkVec [0,0,0,-1,-1,-1]) (mkVec [0,0,1,0,0,0]) ⟨2, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,-1,-1]) (mkVec [0,0,-1,0,0,0]) ⟨2, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer49 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,0,1,1,1,1]) :=
  der_refl_of (g := (mkVec [0,0,1,0,0,0])) (h := (mkVec [0,0,0,1,1,1])) (ng := (mkVec [0,0,-1,0,0,0])) ggHalfDer10 ggHalfDer11 (by funext x; fin_cases x <;> decide) ggHalfDer46 (vec_ne_of_ne (mkVec [0,0,0,1,1,1]) (mkVec [0,0,1,0,0,0]) ⟨2, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,1,1]) (mkVec [0,0,-1,0,0,0]) ⟨2, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨4, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer50 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,-1,0,-1,-1,-1]) :=
  der_refl_of (g := (mkVec [0,1,0,0,0,0])) (h := (mkVec [0,0,0,-1,-1,-1])) (ng := (mkVec [0,-1,0,0,0,0])) ggHalfDer6 ggHalfDer7 (by funext x; fin_cases x <;> decide) ggHalfDer44 (vec_ne_of_ne (mkVec [0,0,0,-1,-1,-1]) (mkVec [0,1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,-1,-1]) (mkVec [0,-1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer51 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,1,0,1,1,1]) :=
  der_refl_of (g := (mkVec [0,1,0,0,0,0])) (h := (mkVec [0,0,0,1,1,1])) (ng := (mkVec [0,-1,0,0,0,0])) ggHalfDer6 ggHalfDer7 (by funext x; fin_cases x <;> decide) ggHalfDer46 (vec_ne_of_ne (mkVec [0,0,0,1,1,1]) (mkVec [0,1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,1,1]) (mkVec [0,-1,0,0,0,0]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer52 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,0,-1,-1,-1,-1]) :=
  der_refl_of (g := (mkVec [-1,0,-1,0,0,0])) (h := (mkVec [0,0,0,-1,-1,-1])) (ng := (mkVec [1,0,1,0,0,0])) ggHalfDer45 ggHalfDer47 (by funext x; fin_cases x <;> decide) ggHalfDer44 (vec_ne_of_ne (mkVec [0,0,0,-1,-1,-1]) (mkVec [-1,0,-1,0,0,0]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,-1,-1,-1]) (mkVec [1,0,1,0,0,0]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨6, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer53 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,0,1,1,1,1]) :=
  der_refl_of (g := (mkVec [-1,0,-1,0,0,0])) (h := (mkVec [0,0,0,1,1,1])) (ng := (mkVec [1,0,1,0,0,0])) ggHalfDer45 ggHalfDer47 (by funext x; fin_cases x <;> decide) ggHalfDer46 (vec_ne_of_ne (mkVec [0,0,0,1,1,1]) (mkVec [-1,0,-1,0,0,0]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,1,1,1]) (mkVec [1,0,1,0,0,0]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨4, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer54 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,-1,0,-1,-1,-1]) :=
  der_transfer_of ggHalfDer50 ((memY_of_frame_eq (b := .L) (c := ⟨5, by decide⟩) (d := ⟨0, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer55 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,1,0,1,1,1]) :=
  der_transfer_of ggHalfDer51 ((memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer56 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,1,1,1,1]) :=
  der_transfer_of ggHalfDer49 ((memY_of_frame_eq (b := .K) (c := ⟨6, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer57 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [-1,0,-1,-1,-1,-1]) :=
  der_transfer_of ggHalfDer52 ((memY_of_frame_eq (b := .K) (c := ⟨5, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer58 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [0,0,-1,-1,-1,-1]) :=
  der_transfer_of ggHalfDer48 ((memY_of_frame_eq (b := .K) (c := ⟨5, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer59 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [1,0,1,1,1,1]) :=
  der_transfer_of ggHalfDer53 ((memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer60 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,-1,0,-1,-1,0]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [0,-1,0,-1,-1,-1])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer21 ggHalfDer20 (by funext x; fin_cases x <;> decide) ggHalfDer54 (vec_ne_of_ne (mkVec [0,-1,0,-1,-1,-1]) (mkVec [0,0,0,0,0,-1]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,-1,0,-1,-1,-1]) (mkVec [0,0,0,0,0,1]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨0, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer61 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [0,1,0,1,1,0]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [0,1,0,1,1,1])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer21 ggHalfDer20 (by funext x; fin_cases x <;> decide) ggHalfDer55 (vec_ne_of_ne (mkVec [0,1,0,1,1,1]) (mkVec [0,0,0,0,0,-1]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,1,0,1,1,1]) (mkVec [0,0,0,0,0,1]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer62 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [-1,0,-1,-1,-1,0]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [-1,0,-1,-1,-1,-1])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer23 ggHalfDer22 (by funext x; fin_cases x <;> decide) ggHalfDer57 (vec_ne_of_ne (mkVec [-1,0,-1,-1,-1,-1]) (mkVec [0,0,0,0,0,-1]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [-1,0,-1,-1,-1,-1]) (mkVec [0,0,0,0,0,1]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨3, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer63 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [1,0,1,1,1,0]) :=
  der_refl_of (g := (mkVec [0,0,0,0,0,-1])) (h := (mkVec [1,0,1,1,1,1])) (ng := (mkVec [0,0,0,0,0,1])) ggHalfDer23 ggHalfDer22 (by funext x; fin_cases x <;> decide) ggHalfDer59 (vec_ne_of_ne (mkVec [1,0,1,1,1,1]) (mkVec [0,0,0,0,0,-1]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [1,0,1,1,1,1]) (mkVec [0,0,0,0,0,1]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer64 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [-1,0,-1,-1,0,0]) :=
  der_refl_of (g := (mkVec [-1,0,-1,-1,-1,-1])) (h := (mkVec [0,0,0,0,1,1])) (ng := (mkVec [1,0,1,1,1,1])) ggHalfDer57 ggHalfDer59 (by funext x; fin_cases x <;> decide) ggHalfDer30 (vec_ne_of_ne (mkVec [0,0,0,0,1,1]) (mkVec [-1,0,-1,-1,-1,-1]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,0,1,1]) (mkVec [1,0,1,1,1,1]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨2, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer65 :
    GGHalfE6Model.Der ggHalfM0 .K (mkVec [1,0,1,1,0,0]) :=
  der_refl_of (g := (mkVec [-1,0,-1,-1,-1,-1])) (h := (mkVec [0,0,0,0,-1,-1])) (ng := (mkVec [1,0,1,1,1,1])) ggHalfDer57 ggHalfDer59 (by funext x; fin_cases x <;> decide) ggHalfDer33 (vec_ne_of_ne (mkVec [0,0,0,0,-1,-1]) (mkVec [-1,0,-1,-1,-1,-1]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,0,0,0,-1,-1]) (mkVec [1,0,1,1,1,1]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .K) (c := ⟨7, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer66 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,1,1,1,1,1]) :=
  der_refl_of (g := (mkVec [0,0,1,1,1,1])) (h := (mkVec [0,1,0,0,0,0])) (ng := (mkVec [0,0,-1,-1,-1,-1])) ggHalfDer49 ggHalfDer48 (by funext x; fin_cases x <;> decide) ggHalfDer6 (vec_ne_of_ne (mkVec [0,1,0,0,0,0]) (mkVec [0,0,1,1,1,1]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,1,0,0,0,0]) (mkVec [0,0,-1,-1,-1,-1]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer67 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,-1,-1,-1,-1,-1]) :=
  der_refl_of (g := (mkVec [0,0,1,1,1,1])) (h := (mkVec [0,-1,0,0,0,0])) (ng := (mkVec [0,0,-1,-1,-1,-1])) ggHalfDer49 ggHalfDer48 (by funext x; fin_cases x <;> decide) ggHalfDer7 (vec_ne_of_ne (mkVec [0,-1,0,0,0,0]) (mkVec [0,0,1,1,1,1]) ⟨1, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,-1,0,0,0,0]) (mkVec [0,0,-1,-1,-1,-1]) ⟨1, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer68 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,1,1,1,1,1]) :=
  der_refl_of (g := (mkVec [-1,0,-1,-1,-1,-1])) (h := (mkVec [0,1,0,0,0,0])) (ng := (mkVec [1,0,1,1,1,1])) ggHalfDer52 ggHalfDer53 (by funext x; fin_cases x <;> decide) ggHalfDer6 (vec_ne_of_ne (mkVec [0,1,0,0,0,0]) (mkVec [-1,0,-1,-1,-1,-1]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,1,0,0,0,0]) (mkVec [1,0,1,1,1,1]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer69 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,-1,-1,-1,-1,-1]) :=
  der_refl_of (g := (mkVec [-1,0,-1,-1,-1,-1])) (h := (mkVec [0,-1,0,0,0,0])) (ng := (mkVec [1,0,1,1,1,1])) ggHalfDer52 ggHalfDer53 (by funext x; fin_cases x <;> decide) ggHalfDer7 (vec_ne_of_ne (mkVec [0,-1,0,0,0,0]) (mkVec [-1,0,-1,-1,-1,-1]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [0,-1,0,0,0,0]) (mkVec [1,0,1,1,1,1]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .M) (c := ⟨6, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDerK :
    ∀ t ∈ ggHalfM0.Y .K, GGHalfE6Model.Der ggHalfM0 .K t := by
  intro t ht
  obtain ⟨c, d, hc, hd, hcd, htr⟩ := ht
  have hroot : t ∈ rootFinset .E6 := by
    rw [← htr]
    exact frameOK_K_1 c d ⟨hc, hd, hcd⟩
  have hmem : t ∈ ggHalfKList := derK_decode t hroot ⟨c, d, hc, hd, hcd, htr⟩
  rcases List.mem_cons.mp hmem with h_0 | hmem
  · subst h_0; exact ggHalfDer0
  rcases List.mem_cons.mp hmem with h_1 | hmem
  · subst h_1; exact ggHalfDer1
  rcases List.mem_cons.mp hmem with h_2 | hmem
  · subst h_2; exact ggHalfDer8
  rcases List.mem_cons.mp hmem with h_3 | hmem
  · subst h_3; exact ggHalfDer9
  rcases List.mem_cons.mp hmem with h_4 | hmem
  · subst h_4; exact ggHalfDer14
  rcases List.mem_cons.mp hmem with h_5 | hmem
  · subst h_5; exact ggHalfDer15
  rcases List.mem_cons.mp hmem with h_6 | hmem
  · subst h_6; exact ggHalfDer18
  rcases List.mem_cons.mp hmem with h_7 | hmem
  · subst h_7; exact ggHalfDer19
  rcases List.mem_cons.mp hmem with h_8 | hmem
  · subst h_8; exact ggHalfDer22
  rcases List.mem_cons.mp hmem with h_9 | hmem
  · subst h_9; exact ggHalfDer23
  rcases List.mem_cons.mp hmem with h_10 | hmem
  · subst h_10; exact ggHalfDer30
  rcases List.mem_cons.mp hmem with h_11 | hmem
  · subst h_11; exact ggHalfDer31
  rcases List.mem_cons.mp hmem with h_12 | hmem
  · subst h_12; exact ggHalfDer32
  rcases List.mem_cons.mp hmem with h_13 | hmem
  · subst h_13; exact ggHalfDer33
  rcases List.mem_cons.mp hmem with h_14 | hmem
  · subst h_14; exact ggHalfDer34
  rcases List.mem_cons.mp hmem with h_15 | hmem
  · subst h_15; exact ggHalfDer35
  rcases List.mem_cons.mp hmem with h_16 | hmem
  · subst h_16; exact ggHalfDer36
  rcases List.mem_cons.mp hmem with h_17 | hmem
  · subst h_17; exact ggHalfDer37
  rcases List.mem_cons.mp hmem with h_18 | hmem
  · subst h_18; exact ggHalfDer38
  rcases List.mem_cons.mp hmem with h_19 | hmem
  · subst h_19; exact ggHalfDer39
  rcases List.mem_cons.mp hmem with h_20 | hmem
  · subst h_20; exact ggHalfDer40
  rcases List.mem_cons.mp hmem with h_21 | hmem
  · subst h_21; exact ggHalfDer41
  rcases List.mem_cons.mp hmem with h_22 | hmem
  · subst h_22; exact ggHalfDer56
  rcases List.mem_cons.mp hmem with h_23 | hmem
  · subst h_23; exact ggHalfDer57
  rcases List.mem_cons.mp hmem with h_24 | hmem
  · subst h_24; exact ggHalfDer58
  rcases List.mem_cons.mp hmem with h_25 | hmem
  · subst h_25; exact ggHalfDer59
  rcases List.mem_cons.mp hmem with h_26 | hmem
  · subst h_26; exact ggHalfDer62
  rcases List.mem_cons.mp hmem with h_27 | hmem
  · subst h_27; exact ggHalfDer63
  rcases List.mem_cons.mp hmem with h_28 | hmem
  · subst h_28; exact ggHalfDer64
  rcases List.mem_cons.mp hmem with h_29 | hnil
  · subst h_29; exact ggHalfDer65
  · exact (List.not_mem_nil hnil).elim

private theorem ggHalfDer70 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,1,1,2,1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer26 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨7, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer71 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,1,2,3,2,1]) :=
  der_transportH_of ggHalfDerK ggHalfDer55 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨4, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer72 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,1,2,2,1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer4 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨5, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer73 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,-1,-2,-3,-2,-1]) :=
  der_transportH_of ggHalfDerK ggHalfDer54 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨3, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer74 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,-1,-1,-2,-1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer27 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨3, by decide⟩) (d := ⟨7, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer75 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,1,1,2,1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer61 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨6, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer76 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [0,-1,-1,-2,-1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer60 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨3, by decide⟩) (d := ⟨6, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer77 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,-1,-2,-2,-1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer5 (Or.inl ⟨rfl, rfl, (memY_of_frame_eq (b := .M) (c := ⟨3, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer78 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [1,1,2,2,1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer6 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨5, by decide⟩) (d := ⟨1, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer79 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [-1,-1,-2,-3,-2,-1]) :=
  der_transportH_of ggHalfDerK ggHalfDer50 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨1, by decide⟩) (d := ⟨4, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer80 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [1,1,2,2,1,1]) :=
  der_transportH_of ggHalfDerK ggHalfDer68 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨3, by decide⟩) (d := ⟨1, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer81 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [1,1,2,2,2,1]) :=
  der_transportH_of ggHalfDerK ggHalfDer66 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨2, by decide⟩) (d := ⟨1, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer82 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [-1,-1,-2,-2,-2,-1]) :=
  der_transportH_of ggHalfDerK ggHalfDer67 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨1, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer83 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [-1,-1,-2,-2,-1,0]) :=
  der_transportH_of ggHalfDerK ggHalfDer7 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨1, by decide⟩) (d := ⟨5, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer84 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [-1,-1,-2,-2,-1,-1]) :=
  der_transportH_of ggHalfDerK ggHalfDer69 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨1, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer85 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [1,1,2,3,2,1]) :=
  der_transportH_of ggHalfDerK ggHalfDer51 (Or.inr ⟨rfl, rfl, (memY_of_frame_eq (b := .L) (c := ⟨4, by decide⟩) (d := ⟨1, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))⟩) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer86 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [1,2,2,3,2,1]) :=
  der_refl_of (g := (mkVec [0,1,0,1,0,0])) (h := (mkVec [1,1,2,2,2,1])) (ng := (mkVec [0,-1,0,-1,0,0])) ggHalfDer26 ggHalfDer27 (by funext x; fin_cases x <;> decide) ggHalfDer81 (vec_ne_of_ne (mkVec [1,1,2,2,2,1]) (mkVec [0,1,0,1,0,0]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [1,1,2,2,2,1]) (mkVec [0,-1,0,-1,0,0]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨0, by decide⟩) (d := ⟨1, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer87 :
    GGHalfE6Model.Der ggHalfM0 .L (mkVec [-1,-2,-2,-3,-2,-1]) :=
  der_refl_of (g := (mkVec [0,1,0,1,0,0])) (h := (mkVec [-1,-1,-2,-2,-2,-1])) (ng := (mkVec [0,-1,0,-1,0,0])) ggHalfDer26 ggHalfDer27 (by funext x; fin_cases x <;> decide) ggHalfDer82 (vec_ne_of_ne (mkVec [-1,-1,-2,-2,-2,-1]) (mkVec [0,1,0,1,0,0]) ⟨0, by decide⟩ (by decide)) (vec_ne_of_ne (mkVec [-1,-1,-2,-2,-2,-1]) (mkVec [0,-1,0,-1,0,0]) ⟨0, by decide⟩ (by decide)) ((memY_of_frame_eq (b := .L) (c := ⟨1, by decide⟩) (d := ⟨0, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide))) (by funext x; fin_cases x <;> decide)

private theorem ggHalfDer88 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [1,2,2,3,2,1]) :=
  der_transfer_of ggHalfDer86 ((memY_of_frame_eq (b := .M) (c := ⟨2, by decide⟩) (d := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem ggHalfDer89 :
    GGHalfE6Model.Der ggHalfM0 .M (mkVec [-1,-2,-2,-3,-2,-1]) :=
  der_transfer_of ggHalfDer87 ((memY_of_frame_eq (b := .M) (c := ⟨3, by decide⟩) (d := ⟨2, by decide⟩) (by decide) (by decide) (by decide) (by funext x; fin_cases x <;> decide)))

private theorem der_all :
    (∀ r ∈ ggHalfM0.Y .L, GGHalfE6Model.Der ggHalfM0 .L r) ∧
    (∀ r ∈ ggHalfM0.Y .K, GGHalfE6Model.Der ggHalfM0 .K r) ∧
    (∀ r ∈ ggHalfM0.Y .M, GGHalfE6Model.Der ggHalfM0 .M r) := by
  refine ⟨?_, ggHalfDerK, ?_⟩
  ·
    intro t ht
    obtain ⟨c, d, hc, hd, hcd, htr⟩ := ht
    have hroot : t ∈ rootFinset .E6 := by
      rw [← htr]
      exact frameOK_L_1 c d ⟨hc, hd, hcd⟩
    have hmem : t ∈ ggHalfLList := derL_decode t hroot ⟨c, d, hc, hd, hcd, htr⟩
    rcases List.mem_cons.mp hmem with h_0 | hmem
    · subst h_0; exact ggHalfDer4
    rcases List.mem_cons.mp hmem with h_1 | hmem
    · subst h_1; exact ggHalfDer5
    rcases List.mem_cons.mp hmem with h_2 | hmem
    · subst h_2; exact ggHalfDer12
    rcases List.mem_cons.mp hmem with h_3 | hmem
    · subst h_3; exact ggHalfDer13
    rcases List.mem_cons.mp hmem with h_4 | hmem
    · subst h_4; exact ggHalfDer16
    rcases List.mem_cons.mp hmem with h_5 | hmem
    · subst h_5; exact ggHalfDer17
    rcases List.mem_cons.mp hmem with h_6 | hmem
    · subst h_6; exact ggHalfDer20
    rcases List.mem_cons.mp hmem with h_7 | hmem
    · subst h_7; exact ggHalfDer21
    rcases List.mem_cons.mp hmem with h_8 | hmem
    · subst h_8; exact ggHalfDer24
    rcases List.mem_cons.mp hmem with h_9 | hmem
    · subst h_9; exact ggHalfDer25
    rcases List.mem_cons.mp hmem with h_10 | hmem
    · subst h_10; exact ggHalfDer26
    rcases List.mem_cons.mp hmem with h_11 | hmem
    · subst h_11; exact ggHalfDer27
    rcases List.mem_cons.mp hmem with h_12 | hmem
    · subst h_12; exact ggHalfDer28
    rcases List.mem_cons.mp hmem with h_13 | hmem
    · subst h_13; exact ggHalfDer29
    rcases List.mem_cons.mp hmem with h_14 | hmem
    · subst h_14; exact ggHalfDer42
    rcases List.mem_cons.mp hmem with h_15 | hmem
    · subst h_15; exact ggHalfDer43
    rcases List.mem_cons.mp hmem with h_16 | hmem
    · subst h_16; exact ggHalfDer54
    rcases List.mem_cons.mp hmem with h_17 | hmem
    · subst h_17; exact ggHalfDer55
    rcases List.mem_cons.mp hmem with h_18 | hmem
    · subst h_18; exact ggHalfDer60
    rcases List.mem_cons.mp hmem with h_19 | hmem
    · subst h_19; exact ggHalfDer61
    rcases List.mem_cons.mp hmem with h_20 | hmem
    · subst h_20; exact ggHalfDer78
    rcases List.mem_cons.mp hmem with h_21 | hmem
    · subst h_21; exact ggHalfDer79
    rcases List.mem_cons.mp hmem with h_22 | hmem
    · subst h_22; exact ggHalfDer80
    rcases List.mem_cons.mp hmem with h_23 | hmem
    · subst h_23; exact ggHalfDer81
    rcases List.mem_cons.mp hmem with h_24 | hmem
    · subst h_24; exact ggHalfDer82
    rcases List.mem_cons.mp hmem with h_25 | hmem
    · subst h_25; exact ggHalfDer83
    rcases List.mem_cons.mp hmem with h_26 | hmem
    · subst h_26; exact ggHalfDer84
    rcases List.mem_cons.mp hmem with h_27 | hmem
    · subst h_27; exact ggHalfDer85
    rcases List.mem_cons.mp hmem with h_28 | hmem
    · subst h_28; exact ggHalfDer86
    rcases List.mem_cons.mp hmem with h_29 | hnil
    · subst h_29; exact ggHalfDer87
    · exact (List.not_mem_nil hnil).elim
  ·
    intro t ht
    obtain ⟨c, d, hc, hd, hcd, htr⟩ := ht
    have hroot : t ∈ rootFinset .E6 := by
      rw [← htr]
      exact frameOK_M_1 c d ⟨hc, hd, hcd⟩
    have hmem : t ∈ ggHalfMList := derM_decode t hroot ⟨c, d, hc, hd, hcd, htr⟩
    rcases List.mem_cons.mp hmem with h_0 | hmem
    · subst h_0; exact ggHalfDer2
    rcases List.mem_cons.mp hmem with h_1 | hmem
    · subst h_1; exact ggHalfDer3
    rcases List.mem_cons.mp hmem with h_2 | hmem
    · subst h_2; exact ggHalfDer6
    rcases List.mem_cons.mp hmem with h_3 | hmem
    · subst h_3; exact ggHalfDer7
    rcases List.mem_cons.mp hmem with h_4 | hmem
    · subst h_4; exact ggHalfDer10
    rcases List.mem_cons.mp hmem with h_5 | hmem
    · subst h_5; exact ggHalfDer11
    rcases List.mem_cons.mp hmem with h_6 | hmem
    · subst h_6; exact ggHalfDer44
    rcases List.mem_cons.mp hmem with h_7 | hmem
    · subst h_7; exact ggHalfDer45
    rcases List.mem_cons.mp hmem with h_8 | hmem
    · subst h_8; exact ggHalfDer46
    rcases List.mem_cons.mp hmem with h_9 | hmem
    · subst h_9; exact ggHalfDer47
    rcases List.mem_cons.mp hmem with h_10 | hmem
    · subst h_10; exact ggHalfDer48
    rcases List.mem_cons.mp hmem with h_11 | hmem
    · subst h_11; exact ggHalfDer49
    rcases List.mem_cons.mp hmem with h_12 | hmem
    · subst h_12; exact ggHalfDer50
    rcases List.mem_cons.mp hmem with h_13 | hmem
    · subst h_13; exact ggHalfDer51
    rcases List.mem_cons.mp hmem with h_14 | hmem
    · subst h_14; exact ggHalfDer52
    rcases List.mem_cons.mp hmem with h_15 | hmem
    · subst h_15; exact ggHalfDer53
    rcases List.mem_cons.mp hmem with h_16 | hmem
    · subst h_16; exact ggHalfDer66
    rcases List.mem_cons.mp hmem with h_17 | hmem
    · subst h_17; exact ggHalfDer67
    rcases List.mem_cons.mp hmem with h_18 | hmem
    · subst h_18; exact ggHalfDer68
    rcases List.mem_cons.mp hmem with h_19 | hmem
    · subst h_19; exact ggHalfDer69
    rcases List.mem_cons.mp hmem with h_20 | hmem
    · subst h_20; exact ggHalfDer70
    rcases List.mem_cons.mp hmem with h_21 | hmem
    · subst h_21; exact ggHalfDer71
    rcases List.mem_cons.mp hmem with h_22 | hmem
    · subst h_22; exact ggHalfDer72
    rcases List.mem_cons.mp hmem with h_23 | hmem
    · subst h_23; exact ggHalfDer73
    rcases List.mem_cons.mp hmem with h_24 | hmem
    · subst h_24; exact ggHalfDer74
    rcases List.mem_cons.mp hmem with h_25 | hmem
    · subst h_25; exact ggHalfDer75
    rcases List.mem_cons.mp hmem with h_26 | hmem
    · subst h_26; exact ggHalfDer76
    rcases List.mem_cons.mp hmem with h_27 | hmem
    · subst h_27; exact ggHalfDer77
    rcases List.mem_cons.mp hmem with h_28 | hmem
    · subst h_28; exact ggHalfDer88
    rcases List.mem_cons.mp hmem with h_29 | hnil
    · subst h_29; exact ggHalfDer89
    · exact (List.not_mem_nil hnil).elim

theorem ggHalfM0_good : ggHalfM0.Good := by
  refine ⟨frameOK_L, frameOK_K, frameOK_M, perp_L, perp_K, perp_M, overlap, weyl,
    pairs_common, ?_⟩
  intro b
  cases b
  · exact der_all.1
  · exact der_all.2.1
  · exact der_all.2.2

end CFSG.StandardType

end
