module

public import CFSG.RankThree.PartOne.K133Spor.Bridge
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.Sporadic.Bridge.HNSurj

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms TauCeti
  CFSG.RankThree.PartOne.S13K

@[expose] def HNKleinPlaneFree : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* NativeSporadic.Carrier .HN) →
    ∀ (D V : Subgroup T), IsElementaryAbelian 5 D → Nat.card D = 25 → IsElementaryAbelian 2 V →
      Nat.card V = 4 → ¬ ∀ d ∈ D, ∀ v ∈ V, d * v = v * d

theorem hn_card_outer_aux :
    Nat.card (Outer (NativeSporadic.Carrier .HN)) = 2 :=
  CFSG.Sporadic.HNSchreier.card_outer_HN

theorem hn_card_aux :
    Nat.card (NativeSporadic.Carrier .HN) = 273030912000000 :=
  CFSG.Sporadic.HNSchreier.card_HN

theorem not_sq_dvd_card_HN_aux {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ 273030912000000 := by
  have hs : Nat.Coprime p (2 ^ 14 * 3 ^ 6 * 5 ^ 6) :=
    CFSG.RankThree.PartOne.coprime_two_three_five_pow hp hp3 hp5 14 6 6
  have hN : (273030912000000 : ℕ) = (2 ^ 14 * 3 ^ 6 * 5 ^ 6) * 1463 := by norm_num
  rw [hN]
  exact CFSG.RankThree.PartOne.not_sq_dvd_mul_of_coprime hp hs (B := 38) (by norm_num)
    (by decide +kernel) (by norm_num)

theorem goodResV_hn
    (hK : HNKleinPlaneFree) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (e : X ≃* NativeSporadic.Carrier .HN) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) : GoodResV p X := by
  have hout : Nat.card (Outer X) = 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hn_card_outer_aux
  by_cases hp5 : p = 5
  · subst hp5
    have hnd : ¬ 5 ∣ Nat.card (Outer X) := by rw [hout]; norm_num
    have hZ : Subgroup.center X = ⊥ := CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab
    intro Ē hE hc ⟨Cb, hCĒ, hCc, Kb, hKs, hKn, hpK, ⟨V, hVK, hVel, hVc⟩, hfix⟩
    exfalso
    have : Fact (Nat.Prime 5) := ⟨hp⟩
    have hC : IsElementaryAbelian 5 Cb := isElementaryAbelian_of_le hE hCĒ
    obtain ⟨C, hCe, hCcard, hCmap⟩ := exists_pullback_inner hZ hC
      (hCĒ.trans (le_inner_of_isPGroup_of_not_dvd_outer hp hnd (IsElementaryAbelian.isPGroup 5 Ē)))
    refine hK X ⟨e⟩ C V hCe (hCcard.trans hCc) hVel hVc fun c hc' v hv => ?_
    have h1 := hfix (MulAut.conj c) (by rw [hCmap]; exact Subgroup.mem_map_of_mem _ hc') v (hVK hv)
    rw [MulAut.conj_apply] at h1
    calc c * v = c * v * c⁻¹ * c := by group
      _ = v * c := by rw [h1]
  · refine (goodRes_of_not_sq_dvd ?_).toGoodResV
    have hcardX : Nat.card X = 273030912000000 := by
      rw [Nat.card_congr e.toEquiv]
      exact hn_card_aux
    exact CFSG.RankThree.PartOne.not_sq_dvd_card_mulAut_of_outer_le hnab (MulEquiv.refl X)
      (N := 273030912000000) (k := 2) hcardX (by rw [hout]) hp (by omega)
      (not_sq_dvd_card_HN_aux hp (by omega) hp5)

theorem kf133ResMaxAt_leaf6_hn
    (hK : HNKleinPlaneFree)
    (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) : KF133ResMaxAt (leaf6 .HN) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨e0⟩ := hX
  have : IsSimpleGroup SporadicName.HN.Group := e0.symm.isSimpleGroup
  obtain ⟨e1⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  exact goodResV_hn hK hne (e0.trans e1.symm) hp h5

end CFSG.RankThree.PartOne.K133
