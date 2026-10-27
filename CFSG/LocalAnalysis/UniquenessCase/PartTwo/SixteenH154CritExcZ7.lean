module

public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s16h_commute_zpowers {W : Type} [CommGroup W] {g i : MulAut W}
    (hgi : g * i = i * g) {y : MulAut W} (hy : y ∈ Subgroup.zpowers i) :
    g * y = y * g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (show Commute g i from hgi).zpow_right n

private lemma s16h_apply_commSub_zpowers_mem {W : Type} [CommGroup W] {g i : MulAut W}
    (hgi : g * i = i * g) {w : W}
    (hw : w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) :
    g w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers i) := by
  refine Subgroup.closure_induction (p := fun c _ =>
      g c ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨y, hy, u, -, rfl⟩
    have hyg : g * y = y * g := s16h_commute_zpowers hgi hy
    have h1 : g (y u) = y (g u) := by rw [← MulAut.mul_apply, hyg, MulAut.mul_apply]
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨y, hy, g u, Subgroup.mem_top _, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem s16h_three_le_rk_of_normalizes_Z7 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsCyclicOrd ↥L 7)
    (hfpf : ∀ w : W, (∀ l ∈ L, l w = w) → w = 1) (hrk : rk W = 6)
    {i : MulAut W} (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1)
    (hn : i ∈ normalizer (L : Set (MulAut W))) :
    3 ≤ rk ↥(commSub ⊤ (zpowers i)) := by
  classical
  obtain ⟨g, hg⟩ := hL.1.exists_generator
  let x : MulAut W := (g : MulAut W)
  have hxL : x ∈ L := g.2
  have hzp : Subgroup.zpowers x = L := by
    ext y
    constructor
    · intro hy
      exact Subgroup.zpowers_le.mpr hxL hy
    · intro hy
      have hy' : (⟨y, hy⟩ : ↥L) ∈ Subgroup.zpowers g := hg ⟨y, hy⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy'
      exact ⟨n, by
        have h := congrArg (fun z : ↥L => (z : MulAut W)) hn
        simpa [x] using h⟩
  have hord : orderOf x = 7 := by
    rw [← Nat.card_zpowers, hzp, hL.2]
  have hx7 : x ^ 7 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one x
  have hfpfx : ∀ w : W, x w = w → w = 1 := by
    intro w hw
    apply hfpf w
    intro l hl
    rw [← hzp] at hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    have hw' : x⁻¹ w = w := by
      have h := congrArg (fun z => x⁻¹ z) hw
      rw [MulAut.inv_apply_self] at h
      exact h.symm
    exact zpow_induction_right (g := x) (P := fun z => z w = w) rfl
      (fun a ha => by rw [MulAut.mul_apply, hw, ha])
      (fun a ha => by rw [MulAut.mul_apply, hw', ha]) n
  have hi_inv : i⁻¹ = i := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two]; exact hi2
  have hii : i * i = 1 := by rw [← pow_two]; exact hi2
  have hmem : i * x * i⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hn x).mp hxL
  rw [← hzp] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hconj1 : i * (i * x * i⁻¹) * i⁻¹ = x := by
    calc i * (i * x * i⁻¹) * i⁻¹ = (i * i) * x * (i⁻¹ * i⁻¹) := by group
      _ = x := by rw [hii, hi_inv, hii]; group
  have hstep : i * x ^ k * i⁻¹ = (x ^ k) ^ k := by
    rw [← conj_zpow, hk]
  have hxkk : x ^ (k * k) = x := by
    have h1 : (x ^ k) ^ k = x := by
      rw [hstep.symm, hk]
      exact hconj1
    rwa [← zpow_mul] at h1
  have hxone : x ^ (k * k - 1) = 1 := by
    have h := congrArg (fun y : MulAut W => y * x⁻¹) hxkk
    rw [mul_inv_cancel] at h
    rw [← zpow_neg_one, ← zpow_add] at h
    simpa [sub_eq_add_neg] using h
  have hdvd : (7 : ℤ) ∣ k * k - 1 := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hxone
    rw [hord] at h
    simpa using h
  have hmod : k * k ≡ 1 [ZMOD 7] := by
    rw [Int.modEq_iff_dvd]
    have hneg : (7 : ℤ) ∣ -(k * k - 1) := dvd_neg.mpr hdvd
    rwa [show (1 : ℤ) - k * k = -(k * k - 1) by ring]
  have hz : (k : ZMod 7) * (k : ZMod 7) = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (k * k) 1 7).mpr hmod
    push_cast at h
    simpa using h
  have hself : (k : ZMod 7) = 1 ∨ (k : ZMod 7) = -1 := mul_self_eq_one_iff.mp hz
  have h_comm_or_inv : i * x * i⁻¹ = x ∨ i * x * i⁻¹ = x⁻¹ := by
    rcases hself with hk1 | hkneg
    · left
      rw [← hk]
      have hgoal : x ^ k = x ^ (1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq, hord]
        exact (ZMod.intCast_eq_intCast_iff k 1 7).mp (by simpa using hk1)
      simpa using hgoal
    · right
      rw [← hk]
      have hgoal : x ^ k = x ^ (-1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq, hord]
        exact (ZMod.intCast_eq_intCast_iff k (-1) 7).mp (by simpa using hkneg)
      simpa using hgoal
  rcases h_comm_or_inv with hcomm | hinv
  · have hxi : x * i = i * x := by
      have h := congrArg (fun y : MulAut W => y * i) hcomm
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h.symm
    have hxi' : x⁻¹ * i = i * x⁻¹ := by
      have h := congrArg Inv.inv hxi
      rw [mul_inv_rev, mul_inv_rev, hi_inv] at h
      exact h.symm
    have hne : commSub (⊤ : Subgroup W) (Subgroup.zpowers i) ≠ ⊥ := by
      intro hbot
      apply hi1
      ext w
      have hle : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers i) :=
        commSub_eq_bot_iff.mp hbot
      have hw : w ∈ fixV (Subgroup.zpowers i) := hle (Subgroup.mem_top w)
      rwa [mem_fixV_zpowers_iff] at hw
    have hrkpos : 0 < rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) :=
      Nat.pos_of_ne_zero (fun h0 => hne ((rk_eq_zero_iff hW).mp h0))
    have hfixx : fixV (Subgroup.zpowers x) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      rw [mem_fixV_zpowers_iff] at hv
      exact hfpfx v hv
    have hfix : commSub (⊤ : Subgroup W) (Subgroup.zpowers i) ⊓
        fixV (Subgroup.zpowers x) = ⊥ := by
      rw [hfixx, inf_bot_eq]
    have hW_inv : ∀ y ∈ Subgroup.zpowers x, ∀ w ∈ commSub (⊤ : Subgroup W)
        (Subgroup.zpowers i), y w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers i) := by
      intro y hy w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (zpow_induction_right (g := x) (P := fun z => ∀ w ∈
          commSub (⊤ : Subgroup W) (Subgroup.zpowers i), z w ∈
          commSub (⊤ : Subgroup W) (Subgroup.zpowers i))
        (fun w hw => by simpa using hw)
        (fun a ha w hw => by
          rw [MulAut.mul_apply]
          exact ha (x w) (s16h_apply_commSub_zpowers_mem hxi (w := w) hw))
        (fun a ha w hw => by
          rw [MulAut.mul_apply]
          exact ha (x⁻¹ w) (s16h_apply_commSub_zpowers_mem hxi' (w := w) hw))
        n) w hw
    have horder2 : orderOf (2 : ZMod 7) = 3 := by
      have h1 : (2 : ZMod 7) ^ 3 = 1 := by decide
      have h2 : ∀ m, m < 3 → 0 < m → (2 : ZMod 7) ^ m ≠ 1 := by
        intro m hm3 hm0
        interval_cases m <;> decide
      exact (orderOf_eq_iff (n := 3) (by norm_num)).mpr ⟨h1, h2⟩
    have hY : IsPGroup 7 ↥(Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
    have hdvd3 : 3 ∣ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) := by
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hdvd := CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot (V := W) (p := 7)
        hW (Y := Subgroup.zpowers x) hY hW_inv hfix
      rwa [horder2] at hdvd
    exact Nat.le_of_dvd hrkpos hdvd3
  · have hix : i * x = x⁻¹ * i := by
      have h := congrArg (fun y : MulAut W => y * i) hinv
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    have hx_expr : x = i * x⁻¹ * i := by
      have h := congrArg (fun y : MulAut W => i * y) hix
      rw [← mul_assoc, hii, one_mul] at h
      rwa [← mul_assoc] at h
    have hxi : x * i = i * x⁻¹ := by
      conv_lhs => rw [hx_expr]
      rw [mul_assoc, hii, mul_one]
    let j : MulAut W := x * i
    have hj2 : j * j = 1 := by
      show (x * i) * (x * i) = 1
      calc (x * i) * (x * i) = x * (i * x) * i := by group
        _ = x * (x⁻¹ * i) * i := by rw [hix]
        _ = (x * x⁻¹) * (i * i) := by group
        _ = 1 := by rw [mul_inv_cancel, hii, mul_one]
    have hji : j * i = x := by
      show (x * i) * i = x
      rw [mul_assoc, hii, mul_one]
    have hdisj : fixV (Subgroup.zpowers i) ⊓ fixV (Subgroup.zpowers j) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      rw [Subgroup.mem_inf, mem_fixV_zpowers_iff, mem_fixV_zpowers_iff] at hv
      obtain ⟨hvi, hvj⟩ := hv
      have hxv : x v = v := by
        have h1 : (j * i) v = v := by rw [MulAut.mul_apply, hvi, hvj]
        rwa [hji] at h1
      exact hfpfx v hxv
    have hsum := rk_sup_add_rk_inf (fixV (Subgroup.zpowers i))
      (fixV (Subgroup.zpowers j))
    rw [hdisj, rk_bot, add_zero] at hsum
    have hle : rk ↥(fixV (Subgroup.zpowers i) ⊔ fixV (Subgroup.zpowers j)) ≤ rk W := by
      have hp := rk_mono (H := fixV (Subgroup.zpowers i) ⊔ fixV (Subgroup.zpowers j))
        (K := (⊤ : Subgroup W)) le_top
      rwa [rk_top] at hp
    have hCiCj : rk ↥(fixV (Subgroup.zpowers i)) + rk ↥(fixV (Subgroup.zpowers j)) ≤ 6 := by
      rw [← hsum]
      exact hle.trans (le_of_eq hrk)
    have hki := rk_commSub_add_rk_inf_fixV (V := W) (g := i) (W := (⊤ : Subgroup W))
      (fun _ _ _ _ => Subgroup.mem_top _)
    rw [top_inf_eq, rk_top, hrk] at hki
    have hkj := rk_commSub_add_rk_inf_fixV (V := W) (g := j) (W := (⊤ : Subgroup W))
      (fun _ _ _ _ => Subgroup.mem_top _)
    rw [top_inf_eq, rk_top, hrk] at hkj
    have hki_le : rk ↥(commSub ⊤ (Subgroup.zpowers i)) ≤ rk ↥(fixV (Subgroup.zpowers i)) :=
      rk_mono (by
        have h := commV_zpowers_le_fixV_of_involution hW hi2
        rwa [commV_eq_commSub] at h)
    have hkj_le : rk ↥(commSub ⊤ (Subgroup.zpowers j)) ≤ rk ↥(fixV (Subgroup.zpowers j)) :=
      rk_mono (by
        have h := commV_zpowers_le_fixV_of_involution hW hj2
        rwa [commV_eq_commSub] at h)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
