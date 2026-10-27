module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut
public import CFSG.Walter.Bender1970.S38.SmallQ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_TwoD_commSub_commSub_of_comm {W : Type*} [CommGroup W]
    {A B : Subgroup (MulAut W)} (hAB : ⁅A, B⁆ = ⊥)
    (h : commSub (commSub ⊤ A) B = ⊥) :
    commSub (commSub ⊤ B) A = ⊥ := by
  rw [commSub_eq_bot_iff]
  intro c hc
  rw [mem_fixV]
  intro a ha
  have hP : commHom a c = 1 := by
    refine Subgroup.closure_induction (p := fun c _ => commHom a c = 1) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨b, hb, w, -, rfl⟩
      have hcomm : a * b = b * a :=
        commutatorElement_eq_one_iff_mul_comm.1
          (Subgroup.mem_bot.1 (hAB ▸ Subgroup.commutator_mem_commutator ha hb))
      have hgen : commHom b (commHom a w) ∈ commSub (commSub ⊤ A) B :=
        Subgroup.subset_closure ⟨b, hb, commHom a w,
          Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩, rfl⟩
      have hEq : commHom a (b w * w⁻¹) = commHom b (commHom a w) := by
        simpa only [commHom_apply] using commHom_comm hcomm w
      rw [hEq]
      exact Subgroup.mem_bot.1 (h ▸ hgen)
    · exact map_one _
    · intro x y _ _ hx hy
      rw [map_mul, hx, hy, mul_one]
    · intro x _ hx
      rw [map_inv, hx, inv_one]
  rw [commHom_apply] at hP
  exact mul_inv_eq_one.1 hP

private theorem s15_TwoD_commSub_tilde_conj (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} (hgM : g ∈ D.M)
    (hgn : g ∉ nBar D.M V₀ V hV L) :
    commSub (commSub ⊤ (barSub V₀ V hV (conjSubgroup L g))) (barSub V₀ V hV L) = ⊥ := by
  have hc := s15_Kbar_commute_conj h (m := (1 : G)) (m' := g) D.M.one_mem hgM
    (by simpa using hgn)
  rw [conjSubgroup_one] at hc
  exact s15_TwoD_commSub_commSub_of_comm hc.1 hc.2

private theorem s15_TwoD_conj_fixV_lStar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {m : D.M}
    (hm : (m : G) ∉ nBar D.M V₀ V hV L) :
    imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) (m : G)) ≤
      fixV (lStar D.M V₀ V hV L) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hms : (m : G) ∈ stabTil V₀ V := hMs m.2
  have h01 : V₀ ≤ v1Sub D.M V₀ V hV L := s15_Infra_le_v1Sub D.M V₀ V hV L
  set B : Subgroup (Vtil V₀ V hV) :=
    commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G))) with hB
  have hWpre : conjSubgroup (wSub V₀ V hV L) (m : G) = preTil V₀ V hV B := by
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV hms]
    show wSub V₀ V hV (conjSubgroup L (m : G)) = preTil V₀ V hV B
    simp only [wSub, wTil, hB]
  rw [hWpre, s15_T7_imgTil_preTil_eq_map V₀ (v1Sub D.M V₀ V hV L) V hV h01]
  intro q hq
  rw [mem_fixV]
  intro φ hφ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
  obtain ⟨g, hgL, hgφ⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L φ).1 hφ
  have hg0 : (g : G) ∈ stabTil V₀ V := h.le.trans hMs hgL
  have hxfix : actTil V₀ V hV ⟨(g : G), hg0⟩ x = x := by
    have h1 : B ≤ fixV (barSub V₀ V hV L) :=
      commSub_eq_bot_iff.mp (s15_TwoD_commSub_tilde_conj D h hV (g := (m : G)) m.2 hm)
    exact mem_fixV.mp (h1 hx) (actTil V₀ V hV ⟨(g : G), hg0⟩)
      (actTil_mem_barSub V₀ V hV hgL hg0)
  calc φ (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV h01 x)
      = actTil (v1Sub D.M V₀ V hV L) V hV g
          (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV h01 x) := by rw [hgφ]
    _ = s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV h01
          (actTil V₀ V hV ⟨(g : G), hg0⟩ x) :=
        (s15_T7_kappa_act V₀ (v1Sub D.M V₀ V hV L) V hV h01 hg0 g.2 x).symm
    _ = s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV h01 x := by rw [hxfix]

private theorem s15_TwoD_mem_fixV_zpowers {W : Type*} [CommGroup W] {φ : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers φ) ↔ φ v = v := by
  constructor
  · intro h
    exact mem_fixV.mp h φ (Subgroup.mem_zpowers φ)
  · intro h
    rw [mem_fixV]
    intro x hx
    let H : Subgroup (MulAut W) :=
      { carrier := {x | x v = v}
        one_mem' := rfl
        mul_mem' := by
          intro a b ha hb
          show (a * b) v = v
          rw [MulAut.mul_apply, hb, ha]
        inv_mem' := by
          intro a ha
          show a.symm v = v
          have := congrArg (fun w => a.symm w) ha
          simpa using this.symm }
    have hH : Subgroup.zpowers φ ≤ H := Subgroup.zpowers_le.mpr h
    exact hH hx

private theorem s15_TwoD_lStar_centSub_wStar (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) :
    lStar D.M V₀ V hV L ⊓ centSub (wStar D.M V₀ V hV L) = ⊥ := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨hφL, hφfix⟩ := Subgroup.mem_inf.1 hφ
  have hspan : sSup (wStarConj D.M V₀ V hV L) = ⊤ :=
    (fifteen_two_directSum D h1217 h hV hL).2
  have hle : (⊤ : Subgroup (vStar D.M V₀ V hV L)) ≤ fixV (Subgroup.zpowers φ) := by
    rw [← hspan]
    refine sSup_le fun U hU => ?_
    rw [s15_Two_wStarConj_eq_range D.M V₀ V L hV] at hU
    obtain ⟨m, rfl⟩ := hU
    change imgTil (v1Sub D.M V₀ V hV L) V hV
      (conjSubgroup (wSub V₀ V hV L) (m : G)) ≤ fixV (Subgroup.zpowers φ)
    by_cases hm : (m : G) ∈ nBar D.M V₀ V hV L
    · have hKm : barSub V₀ V hV (conjSubgroup L (m : G)) = barSub V₀ V hV L :=
        (s15_Infra_mem_nBar_iff h.hyp125 hV m.2).1 hm
      have hWm : conjSubgroup (wSub V₀ V hV L) (m : G) = wSub V₀ V hV L := by
        rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m.2)]
        show wSub V₀ V hV (conjSubgroup L (m : G)) = wSub V₀ V hV L
        simp only [wSub, wTil, hKm]
      have hUeq : imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (m : G)) = wStar D.M V₀ V hV L := by
        rw [hWm]; rfl
      rw [hUeq]
      intro u hu
      rw [s15_TwoD_mem_fixV_zpowers]
      exact mem_centSub.1 hφfix u hu
    · intro u hu
      rw [s15_TwoD_mem_fixV_zpowers]
      exact mem_fixV.mp (s15_TwoD_conj_fixV_lStar D h hV hm hu) φ hφL
  have hφ1 : φ = 1 := by
    refine MulEquiv.ext fun v => ?_
    exact mem_fixV.mp (hle (Subgroup.mem_top v)) φ (Subgroup.mem_zpowers φ)
  rw [Subgroup.mem_bot]
  exact hφ1

private theorem s15_TwoD_card_lStar_dvd_six (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2) :
    Nat.card ↥(lStar D.M V₀ V hV L) ∣ 6 := by
  have hfaith := s15_TwoD_lStar_centSub_wStar D h1217 h hV hL
  have hstab := s15_T7_lStar_le_stabSub D h
  have hcard : Nat.card ↥(lStar D.M V₀ V hV L) =
      Nat.card ↥(autSub (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) := by
    have h1 := card_autSub_mul (A := lStar D.M V₀ V hV L)
      (U := wStar D.M V₀ V hV L) hstab
    rw [hfaith, Subgroup.card_bot, mul_one] at h1
    exact h1.symm
  rw [hcard]
  have hsq : ∀ w : ↥(wStar D.M V₀ V hV L), w ^ 2 = 1 := by
    intro w
    refine Subtype.ext ?_
    simpa using s15_LP_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV w.1
  have hcardW : Nat.card ↥(wStar D.M V₀ V hV L) = 4 := by
    rw [card_eq_two_pow_mSub (U := wStar D.M V₀ V hV L)
      (isPGroup_two_of_sq_eq_one hsq)]
    show 2 ^ rk ↥(wStar D.M V₀ V hV L) = 4
    rw [show rk ↥(wStar D.M V₀ V hV L) = 2 from hγ]
    norm_num
  have hcardMulAut : Nat.card (MulAut ↥(wStar D.M V₀ V hV L)) = 6 :=
    (CFSG.Walter.card_mulAut_of_elementary (Q := ↥(wStar D.M V₀ V hV L)) hsq).1 hcardW
  have hdvd := Subgroup.card_subgroup_dvd_card
    (autSub (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
  rwa [hcardMulAut] at hdvd

private theorem s15_TwoD_card_lBar_eq_lStar (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    Nat.card ↥(barSub V₀ V hV L) = Nat.card ↥(lStar D.M V₀ V hV L) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hLs : L ≤ stabTil V₀ V := h.le.trans hMs
  have hLs₁ : L ≤ stabTil (v1Sub D.M V₀ V hV L) V := h.le.trans (s15_T7_le_stabTil_v1Sub h)
  let ψ₀ : ↥L →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hLs)
  let ψ₁ : ↥L →* MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV) :=
    (actTil (v1Sub D.M V₀ V hV L) V hV).comp (Subgroup.inclusion hLs₁)
  have hr₀ : ψ₀.range = barSub V₀ V hV L := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLs x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  have hr₁ : ψ₁.range = barSub (v1Sub D.M V₀ V hV L) V hV L := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLs₁ x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  have hker₀ : ψ₀.ker = (F11.CTilde D.M V₀ V).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hx
      exact ⟨h.le x.2, hLs x.2,
        by simpa [ψ₀, MonoidHom.comp_apply, Subgroup.inclusion] using hx⟩
    · rintro ⟨-, hh, h1⟩
      simpa [ψ₀, MonoidHom.comp_apply, Subgroup.inclusion] using h1
  have hker₁ : ψ₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hx
      exact ⟨h.le x.2, hLs₁ x.2,
        by simpa [ψ₁, MonoidHom.comp_apply, Subgroup.inclusion] using hx⟩
    · rintro ⟨-, hh, h1⟩
      simpa [ψ₁, MonoidHom.comp_apply, Subgroup.inclusion] using h1
  have hker : ψ₀.ker = ψ₁.ker := by
    rw [hker₀, hker₁, ← fifteen_two_cent D h1217 h hV]
  have h0 : Nat.card ψ₀.ker * Nat.card ↥(barSub V₀ V hV L) = Nat.card ↥L := by
    rw [← hr₀]; exact Subgroup.card_ker_mul_card_range ψ₀
  have h1 : Nat.card ψ₁.ker *
      Nat.card ↥(barSub (v1Sub D.M V₀ V hV L) V hV L) = Nat.card ↥L := by
    rw [← hr₁]; exact Subgroup.card_ker_mul_card_range ψ₁
  have hmul : Nat.card ψ₀.ker * Nat.card ↥(barSub V₀ V hV L) =
      Nat.card ψ₀.ker * Nat.card ↥(barSub (v1Sub D.M V₀ V hV L) V hV L) := by
    rw [h0, ← h1, hker]
  have hgoal : Nat.card ↥(barSub V₀ V hV L) =
      Nat.card ↥(barSub (v1Sub D.M V₀ V hV L) V hV L) :=
    Nat.mul_left_cancel (Nat.card_pos (α := ψ₀.ker)) hmul
  rw [hgoal]
  rfl

private theorem s15_TwoD_eq_three_of_dvd_six {n : ℕ} (h : n ∣ 6) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h6 : n ≠ 6) : n = 3 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  interval_cases n
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl
  · norm_num at h
  · norm_num at h
  · exact absurd rfl h6

theorem s15_TwoD_card_eq_three (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V hV L = 2) : Nat.card ↥(barSub V₀ V hV L) = 3 := by
  have hdvd : Nat.card ↥(barSub V₀ V hV L) ∣ 6 := by
    rw [s15_TwoD_card_lBar_eq_lStar D h1217 h hV]
    exact s15_TwoD_card_lStar_dvd_six D h1217 h hV hL hγ
  have hntq := s15_Kbar_no_two_quotient h
  have h1 : Nat.card ↥(barSub V₀ V hV L) ≠ 1 := by
    intro hn
    exact hL (Subgroup.card_eq_one.mp hn)
  have h2 : Nat.card ↥(barSub V₀ V hV L) ≠ 2 := by
    intro hn
    have hidx : (⊥ : Subgroup ↥(barSub V₀ V hV L)).index = 2 ^ 1 := by
      rw [Subgroup.index_bot, hn]; norm_num
    have hbot : (⊥ : Subgroup ↥(barSub V₀ V hV L)) = ⊤ :=
      hntq ⊥ inferInstance ⟨1, hidx⟩
    have hcard := congrArg (fun H : Subgroup ↥(barSub V₀ V hV L) => Nat.card ↥H) hbot
    rw [Subgroup.card_bot, Subgroup.card_top] at hcard
    omega
  have h6 : Nat.card ↥(barSub V₀ V hV L) ≠ 6 := by
    intro hn
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hn]; norm_num)
    let N : Subgroup ↥(barSub V₀ V hV L) := Subgroup.zpowers x
    have hNcard : Nat.card ↥N = 3 := by rw [Nat.card_zpowers, hx3]
    have hmul := Subgroup.index_mul_card N
    rw [hNcard, hn] at hmul
    have hNidx : N.index = 2 := by omega
    haveI hNn : N.Normal := Subgroup.normal_of_index_eq_two hNidx
    have hNtop : N = ⊤ := hntq N hNn ⟨1, by rw [hNidx]; norm_num⟩
    have hcard := congrArg (fun H : Subgroup ↥(barSub V₀ V hV L) => Nat.card ↥H) hNtop
    rw [hNcard, Subgroup.card_top] at hcard
    omega
  exact s15_TwoD_eq_three_of_dvd_six hdvd h1 h2 h6

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
