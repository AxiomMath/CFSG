module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

private def qTwoLMFrameC_card_sumZeroEquiv (m p : ℕ) :
    ↥(sumZero (m + 1) p) ≃ (Fin m → Multiplicative (ZMod p)) where
  toFun g := fun i => (g : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc i)
  invFun g := ⟨Fin.lastCases (Multiplicative.ofAdd (-∑ i : Fin m, Multiplicative.toAdd (g i)))
    (fun i => g i), by
      rw [mem_sumZero, Fin.sum_univ_castSucc]
      simp [Fin.lastCases_castSucc, Fin.lastCases_last, Finset.sum_neg_distrib]⟩
  left_inv g := by
    refine Subtype.ext (funext fun i => ?_)
    have h : ∑ i : Fin (m + 1),
        Multiplicative.toAdd ((g : Fin (m + 1) → Multiplicative (ZMod p)) i) = 0 :=
      mem_sumZero.mp g.2
    rw [Fin.sum_univ_castSucc] at h
    refine Fin.lastCases ?_ (fun j => ?_) i
    · dsimp only
      rw [Fin.lastCases_last]
      change Multiplicative.ofAdd (-∑ i : Fin m, Multiplicative.toAdd
          ((g : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc i))) =
        (g : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.last m)
      rw [← eq_neg_of_add_eq_zero_right h, ofAdd_toAdd]
    · dsimp only
      rw [Fin.lastCases_castSucc]
  right_inv g := by
    funext i
    dsimp only
    rw [Fin.lastCases_castSucc]

private theorem qTwoLMFrameC_card_sumZero_gen (m p : ℕ) :
    Nat.card ↥(sumZero m p) = p ^ (m - 1) := by
  rcases m with _ | n
  · rw [Nat.zero_sub, pow_zero]
    have htop : sumZero 0 p = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [mem_sumZero]
      simp
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_fin, pow_zero]
  · rw [Nat.card_congr (qTwoLMFrameC_card_sumZeroEquiv n p)]
    have hcard : Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    rw [hcard, Nat.add_sub_cancel]

theorem qTwoLMFrameC_card_sumZero (m : ℕ) : Nat.card ↥(sumZero m 3) = 3 ^ (m - 1) :=
  qTwoLMFrameC_card_sumZero_gen m 3

section Frame

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {m : ℕ}
  {V VT : Type} [Group V] [Group VT]

theorem qTwoLMFrameC_card_T (F : QTwoFrame m V VT Bs L x) (hVT : IsAugModel m VT F.permVT) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ (m - 1) := by
  obtain ⟨e, -⟩ := hVT.ex
  rw [← Nat.card_congr F.thetaT.toEquiv, ← Nat.card_congr e.toEquiv]
  exact qTwoLMFrameC_card_sumZero m

theorem qTwoLMFrameC_card_W (F : QTwoFrame m V VT Bs L x) (hV : IsAugModel m V F.permV) :
    Nat.card ↥(ggGamma L F.hN).range = 3 ^ (m - 1) := by
  obtain ⟨e, -⟩ := hV.ex
  rw [← Nat.card_congr F.theta.toEquiv, ← Nat.card_congr e.toEquiv]
  exact qTwoLMFrameC_card_sumZero m

theorem qTwoLMFrameC_card_Bs (F : QTwoFrame m V VT Bs L x) (hm : 1 ≤ m)
    (hV : IsAugModel m V F.permV) : Nat.card ↥Bs = 3 ^ m := by
  have hker : (ggGamma L F.hN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, F.ker b, Subgroup.mem_subgroupOf]
  have hcard_ker : Nat.card ↥(ggGamma L F.hN).ker = 3 := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr F.hx)).toEquiv,
      Nat.card_zpowers, F.hord]
  have hcard := Subgroup.card_ker_mul_card_range (ggGamma L F.hN)
  rw [hcard_ker, qTwoLMFrameC_card_W F hV] at hcard
  rw [← hcard, mul_comm 3 (3 ^ (m - 1)), ← pow_succ, Nat.sub_add_cancel hm]

end Frame

end CFSG.StandardType.QTwo

end
