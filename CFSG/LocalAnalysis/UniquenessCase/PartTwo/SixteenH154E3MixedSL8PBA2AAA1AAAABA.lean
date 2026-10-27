module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1AAAABAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_pRank_mbar_three
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig) :
    3 ≤ CFSG.Open.pRank 7 (Mbar D.M ⊥ V h.hyp151.isElemAbelian) := by
  have hV := h.hyp151.isElemAbelian
  have h7C : ¬ 7 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) :=
    s16h_sl28_seven_cTilde_no_seven D h hs2 hcomp hbad hrow h7
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 7) (k := 3) (H := D.M)
      (S.hx.three_le 7 h7)
  have hdisj : E ⊓ F11.CTilde D.M ⊥ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.1 hx
    have hx7 : x ^ 7 = 1 := hEab.2 x hxE
    have hdvd7 : orderOf x ∣ 7 := orderOf_dvd_of_pow_eq_one hx7
    have hdvdC : orderOf x ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) :=
      Subgroup.orderOf_dvd_natCard _ hxC
    rcases Nat.prime_seven.eq_one_or_self_of_dvd (orderOf x) hdvd7 with h1 | h1
    · exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.mp h1)
    · exact absurd (h1 ▸ hdvdC) h7C
  have hEs : E ≤ stabTil ⊥ V := hEM.trans hMs
  let f : ↥E →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hEs)
  have hfker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have haC : (a : G) ∈ F11.CTilde D.M ⊥ V := by
      refine (mem_cTilde_iff hV hnorm).2 ⟨hEM a.2, hEs a.2, ?_⟩
      change actTil ⊥ V hV (Subgroup.inclusion hEs a) = 1
      exact ha
    have haX : (a : G) ∈ E ⊓ F11.CTilde D.M ⊥ V := ⟨a.2, haC⟩
    rw [hdisj, Subgroup.mem_bot] at haX
    exact Subtype.ext haX
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfker
  have hH : f.range ≤ Mbar D.M ⊥ V hV := by
    rintro _ ⟨a, rfl⟩
    change actTil ⊥ V hV (Subgroup.inclusion hEs a) ∈ Mbar D.M ⊥ V hV
    rw [show Subgroup.inclusion hEs a = (⟨(a : G), hEs a.2⟩ : stabTil ⊥ V) from
      Subtype.ext rfl]
    exact actTil_mem_barSub ⊥ V hV (hEM a.2) (hEs a.2)
  exact CFSG.SectionRank.le_pRank_of_injective (p := 7) (by norm_num)
    (fun a b : ↥E => hEab.1.is_comm.comm a b)
    (fun a : ↥E => Subtype.ext (hEab.2 (a : G) a.2))
    hEcard f hfinj hH

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
