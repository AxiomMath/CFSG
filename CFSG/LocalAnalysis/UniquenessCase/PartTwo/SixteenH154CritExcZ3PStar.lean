module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3PStarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154PStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_not_mBarGT_of_bar_two (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D) (h111 : F11.R111 D)
    (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (h126 : R126 D) (h1211 : R1211_1 D) (h111W : W3Thm111 G) (h6161ii : W3Lem616_1ii G)
    (hσ : D.sig = D.sig1) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    (hcard : Nat.card ↥X = p ^ 2)
    (hirr : ∀ Y : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian)), Y ≤ X →
      barSub V₀ V h.hyp125.isElemAbelian D.T ≤ normalizer (Y : Set _) → Y = ⊥ ∨ Y = X) :
    ¬ MBarGT D.M V₀ V (D.k + 1) := by
  intro hm
  by_cases hbot : V₀ = ⊥
  · subst hbot
    have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
    have hMs : D.M ≤ stabTil ⊥ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    haveI hCT : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
    have hH11 : F11.Hyp11 D ⊥ V := Hyp125.hyp11 h127 h.hyp125
    have h1110 : R1110Core D := r1110Core_holds D hSig h61 h63 h77 h869 h111 h112 hThin hCyc
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨Xbar, hXbn, hXbe, hXbc, hXbcomm, hXble⟩ :=
      s16h_z3_exists_xbar_of_bar (h := h) hXn hXe hXd (n := 2) hcard
    haveI := hXbn
    have hXn' : D.M ≤ normalizer ((F11.barPreimage11 D.M ⊥ V Xbar : Subgroup G) : Set G) :=
      fun g hg => uc22p22u_mem_normalizer_barPreimage11 (M := D.M) (V₀ := ⊥) (V := V)
        (Xbar := Xbar) hg
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F11.O2p p D.M)
    set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)
      with hYdef
    have hPM : P ≤ D.M := (uc22p22u_sylow_O2p hp hp2 hP).1
    have hYpre : Y ≤ P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar := by
      rw [hYdef]
      exact (Subgroup.closure_le _).2 fun x hx => hx.1
    have hYX : Y ≤ F11.barPreimage11 D.M ⊥ V Xbar := hYpre.trans inf_le_right
    have hYP : Y ≤ P := hYpre.trans (inf_le_left.trans inf_le_left)
    have hYM : Y ≤ D.M := hYP.trans hPM
    have hYp : IsPGroup p ↥Y := hP.isPGroup.to_le hYP
    have hY11 : F11.InP11 D Y :=
      s16e_d3_inP11 D hSig hσ h1110 h77 hH11 hp hp2 (n := 2) (by norm_num) Xbar hXbn hXbe
        hXbc hXbcomm hP
    have hYnc : ¬ IsCyclic ↥Y := by
      obtain ⟨-, -, -, -, -, -, hnc, -⟩ := hY11
      exact hnc
    have hYleX : barSub ⊥ V hV Y ≤ X := (barSub_mono ⊥ V hV hYX).trans hXble
    set N₀ : Subgroup G := D.T ⊓ normalizer (P : Set G) with hN₀def
    have hN₀Y : N₀ ≤ normalizer (Y : Set G) := by
      have h := s11_TenP_inf_normalizer_le (M := D.M) (P := P)
        (X := F11.barPreimage11 D.M ⊥ V Xbar) (p := p) hXn'
      intro g hg
      exact (h ⟨D.sylowM.le hg.1, hg.2⟩).2
    have hN₀le : N₀ ≤ normalizer (Y : Set G) ⊓ normalizer (D.T : Set G) :=
      le_inf hN₀Y fun g hg => Subgroup.le_normalizer (H := D.T) hg.1
    have hOT : pCoreOf 2 D.M ≤ D.T := by
      obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
      have hle : (CFSG.pCore 2 ↥D.M).map D.M.subtype ≤
          (S : Subgroup ↥D.M).map D.M.subtype :=
        Subgroup.map_mono (CFSG.fitting_pCore_le_sylow S)
      rw [hS, Subgroup.map_subgroupOf_eq_of_le D.sylowM.le] at hle
      exact hle
    have hbarN₀ : barSub ⊥ V hV N₀ = barSub ⊥ V hV D.T := by
      apply le_antisymm
      · exact barSub_mono ⊥ V hV inf_le_left
      · intro φ hφ
        obtain ⟨g, hgT, rfl⟩ := (mem_barSub ⊥ V hV D.T φ).1 hφ
        have hgM : (g : G) ∈ D.M := D.sylowM.le hgT
        obtain ⟨u, huO, n, hnN, hgn⟩ :=
          s11_TenP_exists_mul (M := D.M) (P := P) hp hp2 hP (g : G) hgM
        have huM : u ∈ D.M := uc22p21c_pCoreOf_le D.M huO
        have hnM : n ∈ D.M := hnN.1
        have hu_stab : u ∈ stabTil ⊥ V := hMs huM
        have hn_stab : n ∈ stabTil ⊥ V := hMs hnM
        have hgn' : n = u⁻¹ * (g : G) := by rw [hgn]; group
        have hnT : n ∈ D.T := by
          rw [hgn']
          exact D.T.mul_mem (D.T.inv_mem (hOT huO)) hgT
        have hnN₀ : n ∈ N₀ := ⟨hnT, hnN.2⟩
        have hker : actTil ⊥ V hV ⟨u, hu_stab⟩ = 1 := by
          have hmem : actTil ⊥ V hV ⟨u, hu_stab⟩ ∈ barSub ⊥ V hV (pCoreOf 2 D.M) :=
            actTil_mem_barSub ⊥ V hV huO hu_stab
          rw [barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125] at hmem
          exact Subgroup.mem_bot.1 hmem
        have hprod : (g : stabTil ⊥ V) = ⟨u, hu_stab⟩ * ⟨n, hn_stab⟩ :=
          Subtype.ext (by
            change (g : G) = u * n
            exact hgn)
        rw [hprod, map_mul, hker, one_mul]
        exact actTil_mem_barSub ⊥ V hV hnN₀ hn_stab
    have hYnorm : barSub ⊥ V hV N₀ ≤ normalizer ((barSub ⊥ V hV Y : Subgroup _) : Set _) := by
      intro φ hφ
      rw [Subgroup.mem_normalizer_iff]
      intro ψ
      constructor
      · intro hψ
        obtain ⟨n, hnN, rfl⟩ := (mem_barSub ⊥ V hV N₀ φ).1 hφ
        exact s16h_z3_conj_mem_barSub hV hN₀Y hnN hψ
      · intro hψ
        obtain ⟨n, hnN, rfl⟩ := (mem_barSub ⊥ V hV N₀ φ).1 hφ
        have h := s16h_z3_conj_mem_barSub (N := N₀) (Y := Y) hV hN₀Y (n := n⁻¹)
          (by simpa using (N₀).inv_mem hnN) hψ
        have h1 : actTil ⊥ V hV (n⁻¹) = (actTil ⊥ V hV n)⁻¹ := map_inv _ _
        rw [h1, inv_inv] at h
        have heq : (actTil ⊥ V hV n)⁻¹ * (actTil ⊥ V hV n * ψ * (actTil ⊥ V hV n)⁻¹) *
            actTil ⊥ V hV n = ψ := by group
        rwa [heq] at h
    have hcardYge : p ^ 2 ≤ Nat.card ↥Y :=
      ((h1110 ⊥ V hH11 p hp hp2 P hP).2.2 2 (by norm_num) Xbar hXbn hXbe hXbc hXbcomm).2.2.1
    refine twelve_twelve D h63 h126 h1211 h111W h6161ii h.hyp125 hm Y ?_
    refine ⟨hY11, fun _ => ⟨p, hp, hYp, ?_⟩⟩
    by_cases hbig : p ^ 2 < Nat.card ↥Y
    · exact Or.inl hbig
    · refine Or.inr (Or.inr ?_)
      have hcardY : Nat.card ↥Y = p ^ 2 := le_antisymm (not_lt.1 hbig) hcardYge
      have hsplit := hirr (barSub ⊥ V hV Y) hYleX (by rw [← hbarN₀]; exact hYnorm)
      have hbarY : barSub ⊥ V hV Y = X := by
        rcases hsplit with hsplitbot | hsplitX
        · exfalso
          have hYct : Y ≤ F11.CTilde D.M ⊥ V :=
            s16h_z3_le_cTilde_of_barSub_eq_bot hV h.hyp125.pairFacts.le_normalizer hYM
              (hYM.trans hMs) hsplitbot
          haveI : IsCyclic ↥(P ⊓ F11.CTilde D.M ⊥ V) :=
            (h1110 ⊥ V hH11 p hp hp2 P hP).2.1.1
          exact hYnc (Subgroup.isCyclic_of_le (le_inf hYP hYct))
        · exact hsplitX
      have hYinfCT : Y ⊓ F11.CTilde D.M ⊥ V = ⊥ := by
        have hcf := s16h_z3_card_eq_barSub_mul hV hYM h.hyp125.pairFacts.le_normalizer
          (hYM.trans hMs)
        rw [hbarY, hcard, hcardY] at hcf
        have hmul : p ^ 2 * Nat.card ↥(Y ⊓ F11.CTilde D.M ⊥ V) = p ^ 2 * 1 := by
          rw [mul_one]
          exact hcf.symm
        exact Subgroup.eq_bot_of_card_eq (H := Y ⊓ F11.CTilde D.M ⊥ V)
          (Nat.mul_left_cancel (pow_pos hp.pos 2) hmul)
      intro U hUY hNU
      have hN₀U : N₀ ≤ normalizer (U : Set G) := hN₀le.trans hNU
      have hUnorm : barSub ⊥ V hV N₀ ≤
          normalizer ((barSub ⊥ V hV U : Subgroup _) : Set _) := by
        intro φ hφ
        rw [Subgroup.mem_normalizer_iff]
        intro ψ
        constructor
        · intro hψ
          obtain ⟨n, hnN, rfl⟩ := (mem_barSub ⊥ V hV N₀ φ).1 hφ
          exact s16h_z3_conj_mem_barSub hV hN₀U hnN hψ
        · intro hψ
          obtain ⟨n, hnN, rfl⟩ := (mem_barSub ⊥ V hV N₀ φ).1 hφ
          have h := s16h_z3_conj_mem_barSub (N := N₀) (Y := U) hV hN₀U (n := n⁻¹)
            (by simpa using (N₀).inv_mem hnN) hψ
          have h1 : actTil ⊥ V hV (n⁻¹) = (actTil ⊥ V hV n)⁻¹ := map_inv _ _
          rw [h1, inv_inv] at h
          have heq : (actTil ⊥ V hV n)⁻¹ * (actTil ⊥ V hV n * ψ * (actTil ⊥ V hV n)⁻¹) *
              actTil ⊥ V hV n = ψ := by group
          rwa [heq] at h
      have hUleX : barSub ⊥ V hV U ≤ X := (barSub_mono ⊥ V hV hUY).trans hYleX
      have hsplitU := hirr (barSub ⊥ V hV U) hUleX (by rw [← hbarN₀]; exact hUnorm)
      rcases hsplitU with hUbot | hUX
      · left
        have hUct : U ≤ F11.CTilde D.M ⊥ V :=
          s16h_z3_le_cTilde_of_barSub_eq_bot hV h.hyp125.pairFacts.le_normalizer
            (hUY.trans hYM) ((hUY.trans hYM).trans hMs) hUbot
        exact le_bot_iff.1 ((le_inf hUY hUct).trans (le_of_eq hYinfCT))
      · right
        have hcfU := s16h_z3_card_eq_barSub_mul hV (hUY.trans hYM)
          h.hyp125.pairFacts.le_normalizer ((hUY.trans hYM).trans hMs)
        have hUinf : U ⊓ F11.CTilde D.M ⊥ V = ⊥ :=
          le_bot_iff.1 ((le_inf (inf_le_left.trans hUY) inf_le_right).trans (le_of_eq hYinfCT))
        rw [hUX, hcard, hUinf, Subgroup.card_bot, mul_one] at hcfU
        exact Subgroup.eq_of_le_of_card_ge hUY (le_of_eq (hcardY.trans hcfU.symm))
  · exact s16h_not_mBarGT_of_bar D hSig h61 h63 h77 h869 h111 h112 hThin hCyc h127 h126 h1211
      h111W h6161ii hσ h hp hp2 hXn hXe hXd (n := 2) (by norm_num)
      (fun h0 => absurd h0 hbot) hcard hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
