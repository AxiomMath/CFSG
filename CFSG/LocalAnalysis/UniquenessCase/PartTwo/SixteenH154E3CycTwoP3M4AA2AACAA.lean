module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrameA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoGood
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoMaster
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP3M4AA2AACAA_normal_sylow_selfCentralizing
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 4)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (h3 : D.sig = {3}) :
    ∃ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV ∧
      Mbar D.M V₀ V hV ≤ Subgroup.normalizer (P : Set (MulAut (Vtil V₀ V hV))) ∧
      ¬ 3 ∣ P.relIndex (Mbar D.M V₀ V hV) ∧
      IsPGroup 3 P ∧
      IsElemAbelianOfRank 3 3 ↥P ∧
      Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓ Mbar D.M V₀ V hV ≤ P := by
  subst hp3
  have h3mem : 3 ∈ D.sig := by rw [h3]; exact Set.mem_singleton 3
  obtain ⟨g, hg⟩ := hLp.1.exists_generator
  have hLz : lBar V₀ V hV L = Subgroup.zpowers (g : MulAut (Vtil V₀ V hV)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← hk]
      simpa using (g ^ k).2
  have hZord : orderOf (g : MulAut (Vtil V₀ V hV)) = 3 := by
    rw [Subgroup.orderOf_coe g, orderOf_eq_card_of_forall_mem_zpowers hg, hLp.2]
  have hZM : (g : MulAut (Vtil V₀ V hV)) ∈ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.hyp151.le g.2
  unfold Conc4_136 at hc
  obtain ⟨t, -, -, -, -, hconc⟩ := hc
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hLp.2]
    exact ⟨1, by norm_num⟩
  have hfixbot : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) = ⊥ := by
    have hb := s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
    rwa [wTil, lBar] at hb
  have hcard : Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 2 ^ 4 := by
    change Nat.card ↥(wTil V₀ V hV L) = 2 ^ 4
    rw [card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V hV) (wTil V₀ V hV L), hm]
  obtain ⟨ψ, F⟩ := s16h_e3_CycTwoFrameA_frame (s15_Infra_vtil_sq_eq_one V₀ V hV)
    (A := Mbar D.M V₀ V hV) (Lb := lBar V₀ V hV L)
    (z := (g : MulAut (Vtil V₀ V hV))) (t := t)
    hZM hZord hLz hconc
    (by simpa [s15, lBar] using hs2) hfixbot hcard
  obtain ⟨u₀, hu₀, hu₁, hK⟩ := s16h_e3_CycTwoGood_vector D S hr3 hV h h3mem hW
  have h2 : 2 ≤ CFSG.Open.pRank 3
      (autSub (s16h_CycN (Mbar D.M V₀ V hV) (g : MulAut (Vtil V₀ V hV)))
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))) := by
    have h2' := s16h_e3_CycTwoRank_two_le D S hr3 hV h h3mem hs2.le hW
    rw [hLz] at h2'
    change 2 ≤ CFSG.Open.pRank 3 (autSub (Mbar D.M V₀ V hV ⊓
      Subgroup.normalizer (Subgroup.zpowers (g : MulAut (Vtil V₀ V hV)) : Set _))
      (wTil V₀ V hV L))
    exact h2'
  exact s16h_e3_CycTwoMaster F (by simpa [wTil, lBar] using hu₀) hu₁ hK h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
