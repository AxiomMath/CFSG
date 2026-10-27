module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_exists_Eb_of_blockBound_one_two (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 2) {q : ℕ}
    (hq : q ∈ D.sig) (h3 : 3 ≤ CFSG.Open.pRank q D.M)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian q E ∧
      q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V h.hyp151.isElemAbelian
        (centSub (wTil V₀ V h.hyp151.isElemAbelian L))) := by
  have hpp := D.sig_prime q hq
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h3)
  have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs
    (hpp.1.odd_of_ne_two hpp.2) hEM hEab
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hEab hEn
  refine ⟨E, hEM, hEab, ?_⟩
  rw [hEcard, pow_one] at hcard
  have h2 : q * q ^ 2 ≤ q * Nat.card ↥(E ⊓ preBarSub D.M V₀ V h.hyp151.isElemAbelian
      (centSub (wTil V₀ V h.hyp151.isElemAbelian L))) := by
    calc q * q ^ 2 = q ^ 3 := by ring
      _ ≤ _ := hcard
  exact Nat.le_of_mul_le_mul_left h2 hpp.1.pos

theorem s16h_uniqueMax_of_blockBound_one_two (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 2) {q : ℕ} (hq : q ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨E, -, hEab, hEX⟩ := s16h_exists_Eb_of_blockBound_one_two D h hs hq h3 hBB
  exact s16h_uniqueMax_of_card_le D h61 h127 h hq h3 hEab hEX

private theorem s16h_card_map_mul_card_inf_ker_cond {H N : Type*} [Group H] [Group N]
    (f : H →* N) (E : Subgroup H) :
    Nat.card ↥(E.map f) * Nat.card ↥(E ⊓ f.ker) = Nat.card ↥E := by
  have h1 : Nat.card ↥(f.ker.subgroupOf E) * Nat.card ↥(E.map f) = Nat.card ↥E := by
    have h := Subgroup.card_ker_mul_card_range (f.domRestrict E)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
    exact h
  have h2 : Nat.card ↥(f.ker.subgroupOf E) = Nat.card ↥(E ⊓ f.ker) := by
    rw [← Subgroup.inf_subgroupOf_left (H := f.ker) (K := E)]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ f.ker ≤ E)).toEquiv
  rw [h2, mul_comm] at h1
  exact h1

private theorem s16h_card_inf_preBarSub_eq {M V₀ V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hEM : E ≤ M) (hEs : E ≤ stabTil V₀ V) (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) :
    Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar) =
      Nat.card ↥(barSub V₀ V hV E ⊓ Xbar) *
        Nat.card ↥((E.subgroupOf (stabTil V₀ V)) ⊓ (actTil V₀ V hV).ker) := by
  have h1 := s16h_card_map_mul_card_inf_ker_cond (actTil V₀ V hV)
    ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV))
  rw [Subgroup.map_inf_comap] at h1
  have hker : ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)) ⊓
      (actTil V₀ V hV).ker = (E.subgroupOf (stabTil V₀ V)) ⊓ (actTil V₀ V hV).ker := by
    rw [inf_assoc, inf_eq_right.2 (Subgroup.ker_le_comap (actTil V₀ V hV) Xbar)]
  rw [hker] at h1
  have hpre : E ⊓ preBarSub M V₀ V hV Xbar
      = ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)).map
          (stabTil V₀ V).subtype := by
    unfold preBarSub
    rw [← inf_assoc, inf_eq_left.2 hEM]
    rw [Subgroup.map_inf _ _ (stabTil V₀ V).subtype (Subgroup.subtype_injective _)]
    rw [Subgroup.map_subgroupOf_eq_of_le hEs]
  have hcard4 : Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar)
      = Nat.card ↥((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)) := by
    rw [hpre, Subgroup.card_map_of_injective (f := (stabTil V₀ V).subtype)
      (K := (E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV))
      (Subgroup.subtype_injective _)]
  rw [hcard4]
  exact h1.symm

private theorem s16h_conj_mem_centSub {W : Type*} [CommGroup W] {U : Subgroup W}
    {g φ : MulAut W} (hg : ∀ u ∈ U, g u ∈ U) (hg' : ∀ u ∈ U, g⁻¹ u ∈ U)
    (hφ : φ ∈ centSub U) : g * φ * g⁻¹ ∈ centSub U := by
  intro u hu
  rw [MulAut.mul_apply, MulAut.mul_apply, hφ (g⁻¹ u) (hg' u hu)]
  exact g.apply_symm_apply u

theorem s16h_uniqueMax_of_fix_two (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 2) {q : ℕ} (hq : q ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 2)
    (hFix : s16h_H5Fix (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hpp := D.sig_prime q hq
  haveI : Fact q.Prime := ⟨hpp.1⟩
  have hq2le : 2 ≤ q := hpp.1.two_le
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  intro w hw hw1
  by_cases hw0 : w ∈ V₀
  · exact s16c34_uniqueMax_cent_of_mem_v0 D h61 h.hyp16 hq h3 hw0 hw1
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  let Ū : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L
  let X : Subgroup G := preBarSub D.M V₀ V hV (centSub Ū)
  let wtil : Vtil V₀ V hV := mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩)
  have hwtil : wtil ∈ Ū := (mem_preTil_iff_of_mem V₀ V hV (wTil V₀ V hV L) hwV).1 hw
  have hwtil1 : wtil ≠ 1 := by
    intro h1
    apply hw0
    have h2 : (IntMod.mk hV ⟨w, hwV⟩ : IntMod V hV) ∈ modNull V₀ V hV :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h1
    exact (mem_modNull V₀ V hV _).1 h2
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h3)
  have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs
    (hpp.1.odd_of_ne_two hpp.2) hEM hE
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hE hEn
  have hqle : q ≤ Nat.card ↥(E ⊓ X) := by
    rw [hEcard] at hcard
    have h2 : q ^ 2 * q ≤ q ^ 2 * Nat.card ↥(E ⊓ X) := by
      calc q ^ 2 * q = q ^ 3 := by ring
        _ ≤ _ := hcard
    exact Nat.le_of_mul_le_mul_left h2 (pow_pos hpp.1.pos 2)
  by_cases hbig : q ^ 2 ≤ Nat.card ↥(E ⊓ X)
  · exact s16h_uniqueMax_of_card_le D h61 h127 h hq h3 hE hbig w hw hw1
  have hsmall : Nat.card ↥(E ⊓ X) < q ^ 2 := not_le.1 hbig
  have hEab' : IsElemAbelian q (E ⊓ X) := hE.mono inf_le_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).1 hEab'.isPGroup
  have hn_eq : n = 1 := by
    have h1 : q ≤ q ^ n := by rw [← hn]; exact hqle
    have h2 : q ^ n < q ^ 2 := by rw [← hn]; exact hsmall
    have hnpos : 0 < n := by
      by_contra h
      have h0 : n = 0 := by omega
      subst h0
      rw [pow_zero] at h1
      omega
    have hnlt : n < 2 := by
      by_contra h
      have h2n : 2 ≤ n := not_lt.1 h
      have hle := Nat.pow_le_pow_right hpp.1.pos h2n
      omega
    omega
  have hcardEq : Nat.card ↥(E ⊓ X) = q := by rw [hn, hn_eq, pow_one]
  have hne_bot : E ⊓ X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardEq
    omega
  obtain ⟨a₀, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne_bot
  let a : G := (a₀ : G)
  have haE : a ∈ E := (Subgroup.mem_inf.1 a₀.2).1
  have haX : a ∈ X := (Subgroup.mem_inf.1 a₀.2).2
  have ha1 : a ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  have hEs : E ≤ stabTil V₀ V := hEM.trans hMs
  let K : Subgroup (↥(stabTil V₀ V)) :=
    (E.subgroupOf (stabTil V₀ V)) ⊓ (actTil V₀ V hV).ker
  have hKer1 : Nat.card ↥(barSub V₀ V hV E) * Nat.card ↥K = Nat.card ↥E := by
    have hh := s16h_card_map_mul_card_inf_ker_cond (actTil V₀ V hV)
      (E.subgroupOf (stabTil V₀ V))
    have hcardE : Nat.card ↥(E.subgroupOf (stabTil V₀ V)) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEs).toEquiv
    rw [hcardE] at hh
    exact hh
  have hKer2 : Nat.card ↥(E ⊓ X) =
      Nat.card ↥(barSub V₀ V hV E ⊓ centSub Ū) * Nat.card ↥K :=
    s16h_card_inf_preBarSub_eq hV hEM hEs (centSub Ū)
  have hEq : q ^ 2 * Nat.card ↥(barSub V₀ V hV E ⊓ centSub Ū) =
      Nat.card ↥(barSub V₀ V hV E) := by
    apply Nat.mul_right_cancel (card_subgroup_pos K)
    calc (q ^ 2 * Nat.card ↥(barSub V₀ V hV E ⊓ centSub Ū)) * Nat.card ↥K
        = q ^ 2 * (Nat.card ↥(barSub V₀ V hV E ⊓ centSub Ū) * Nat.card ↥K) := by
          ring
      _ = q ^ 2 * Nat.card ↥(E ⊓ X) := by rw [← hKer2]
      _ = q ^ 2 * q := by rw [hcardEq]
      _ = q ^ 3 := by ring
      _ = Nat.card ↥E := hEcard.symm
      _ = Nat.card ↥(barSub V₀ V hV E) * Nat.card ↥K := hKer1.symm
  have hĒM : barSub V₀ V hV E ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hEM
  have hĒab : IsElemAbelian q (barSub V₀ V hV E) := s16h_barSub_isElemAbelian hV hE
  obtain ⟨g, hgL, bbar, hbbarE, hbbarC, hfix⟩ :=
    hFix (barSub V₀ V hV E) (le_inf hĒM hEn) hĒab (le_of_eq hEq) wtil hwtil hwtil1
  obtain ⟨ĝ, hĝL, hĝeq⟩ := (mem_barSub V₀ V hV L g).1 hgL
  obtain ⟨bhat, hbhatE, hbhateq⟩ := (mem_barSub V₀ V hV E bbar).1 hbbarE
  have hbX : (bhat : G) ∉ X := by
    intro hbX
    obtain ⟨-, h, hh⟩ := (mem_preBarSub D.M V₀ V hV (centSub Ū)).1 hbX
    have hcast : actTil V₀ V hV ⟨(bhat : G), h⟩ = bbar := by
      rw [show (⟨(bhat : G), h⟩ : ↥(stabTil V₀ V)) = bhat from Subtype.ext rfl, hbhateq]
    exact hbbarC (hcast ▸ hh)
  have hstabg : ∀ u ∈ Ū, g u ∈ Ū :=
    commSub_top_stable151b (X := barSub V₀ V hV L) (g := g)
      (fun x hx => (barSub V₀ V hV L).mul_mem
        ((barSub V₀ V hV L).mul_mem hgL hx) ((barSub V₀ V hV L).inv_mem hgL))
  have hstabgi : ∀ u ∈ Ū, g⁻¹ u ∈ Ū :=
    commSub_top_stable151b (X := barSub V₀ V hV L) (g := g⁻¹)
      (fun x hx => (barSub V₀ V hV L).mul_mem
        ((barSub V₀ V hV L).mul_mem ((barSub V₀ V hV L).inv_mem hgL) hx)
        ((barSub V₀ V hV L).inv_mem ((barSub V₀ V hV L).inv_mem hgL)))
  have hstabg' : ∀ u ∈ Ū, actTil V₀ V hV ĝ u ∈ Ū := by rw [hĝeq]; exact hstabg
  have hstabgi' : ∀ u ∈ Ū, (actTil V₀ V hV ĝ)⁻¹ u ∈ Ū := by rw [hĝeq]; exact hstabgi
  obtain ⟨haM, haStab, haC⟩ := (mem_preBarSub D.M V₀ V hV (centSub Ū)).1 haX
  let x' : G := (ĝ : G) * a * (ĝ : G)⁻¹
  let x'' : G := (ĝ : G) * (bhat : G) * (ĝ : G)⁻¹
  have hx'CE : x' ∈ F11.CElt D.M V₀ w := by
    have hx'stab : x' ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ĝ.2 haStab)
        ((stabTil V₀ V).inv_mem ĝ.2)
    have hx'M : x' ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (h.hyp151.le hĝL) haM)
        (D.M.inv_mem (h.hyp151.le hĝL))
    have hx'C : actTil V₀ V hV ⟨x', hx'stab⟩ ∈ centSub Ū := by
      have heq : (⟨x', hx'stab⟩ : ↥(stabTil V₀ V)) = ĝ * ⟨a, haStab⟩ * ĝ⁻¹ :=
        Subtype.ext (by simp [x'])
      rw [heq]
      simp only [map_mul, map_inv]
      exact s16h_conj_mem_centSub hstabg' hstabgi' haC
    exact s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hw
      ((mem_preBarSub D.M V₀ V hV (centSub Ū)).2 ⟨hx'M, hx'stab, hx'C⟩)
  have hx''CE : x'' ∈ F11.CElt D.M V₀ w := by
    have hx''stab : x'' ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ĝ.2 bhat.2)
        ((stabTil V₀ V).inv_mem ĝ.2)
    have hx''M : x'' ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (h.hyp151.le hĝL) (hEM hbhatE))
        (D.M.inv_mem (h.hyp151.le hĝL))
    have hact : actTil V₀ V hV ⟨x'', hx''stab⟩ = g * bbar * g⁻¹ := by
      have heq : (⟨x'', hx''stab⟩ : ↥(stabTil V₀ V)) = ĝ * bhat * ĝ⁻¹ :=
        Subtype.ext (by simp [x''])
      rw [heq]
      simp only [map_mul, map_inv]
      rw [hĝeq, hbhateq]
    refine ⟨hx''M, stabTil_le_normalizer₀ V₀ V hx''stab, ?_⟩
    have h1 : actTil V₀ V hV ⟨x'', hx''stab⟩ wtil = wtil := by rw [hact]; exact hfix
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  let H : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers (bhat : G)
  have hb_not_a : (bhat : G) ∉ Subgroup.zpowers a := fun hb =>
    hbX (Subgroup.zpowers_le.2 haX hb)
  have hbhat1 : (bhat : G) ≠ 1 := fun h1 => hb_not_a (h1.symm ▸ Subgroup.one_mem _)
  have hHab_card := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_mem_isElemAbelian hE haE hbhatE
    (orderOf_eq_prime (hE.2 a haE) ha1)
    (orderOf_eq_prime (hE.2 (bhat : G) hbhatE) hbhat1) hb_not_a
  have hHab : IsElemAbelian q H := hHab_card.1
  have hHge : q ^ 2 ≤ Nat.card ↥H := le_of_eq hHab_card.2.symm
  let P : Subgroup G := conjSubgroup H ((ĝ : G)⁻¹)
  have hPab : IsElemAbelian q P :=
    hHab.map (MulAut.conj ((ĝ : G)⁻¹)⁻¹).toMonoidHom
  have hPge : q ^ 2 ≤ Nat.card ↥P := by
    have hh := Subgroup.card_map_of_injective
      (f := (MulAut.conj ((ĝ : G)⁻¹)⁻¹).toMonoidHom) (K := H) (MulAut.conj _).injective
    exact hh.symm ▸ hHge
  have hPnc : ¬ IsCyclic ↥P :=
    s16c7_not_isCyclic_of_elemAbelian hpp.1 hPab hPge
  have hPle : P ≤ F11.CElt D.M V₀ w := by
    show H.map (MulAut.conj ((ĝ : G)⁻¹)⁻¹).toMonoidHom ≤ F11.CElt D.M V₀ w
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      show MulAut.conj ((ĝ : G)⁻¹)⁻¹ a ∈ F11.CElt D.M V₀ w
      rw [inv_inv, MulAut.conj_apply]
      exact hx'CE
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      show MulAut.conj ((ĝ : G)⁻¹)⁻¹ (bhat : G) ∈ F11.CElt D.M V₀ w
      rw [inv_inv, MulAut.conj_apply]
      exact hx''CE
  exact s16c34_uniqueMax_cent_of_cElt D h61 h127 h.hyp16 hq hPab.isPGroup hPnc hwV hw0 hPle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
