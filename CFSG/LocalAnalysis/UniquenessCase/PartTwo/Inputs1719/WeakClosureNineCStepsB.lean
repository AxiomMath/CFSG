module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCSteps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNEnd

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {ψ : ↥N →* X}
variable (c : Ctx V T N ψ)
variable {Lb : Subgroup X} {B : Type} [Group B] [Finite B] {π : ↥(tcN1 Lb (barSub ψ T)) →* B}
  {Es : Subgroup B} (cb : TCBar Lb (barSub ψ T) π Es)
include c cb

theorem false_of_Es (hO : OrbitStmt) {U : Subgroup G} {u : G} (w : Witness V T U u)
    (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) {Eb : Subgroup X}
    (hEbT1 : Eb ≤ tcT1 Lb (barSub ψ T)) (hTEb : barSub ψ T ≤ normalizer (Eb : Set X))
    (hUb : barSub ψ U ≤ Eb)
    (hΔ : ∀ g, conjSubgroup V g ≤ T → barSub ψ (conjSubgroup V g) ≤ centralizer (Eb : Set X))
    (hFEs : barSub π Eb = Es) (hEs : Es ≠ ⊥) : False := by
  obtain ⟨hEsD, -, -, hmovs, Ks, hKs, hgen⟩ := cb.facts.star hEs
  have hEbN1 : Eb ≤ tcN1 Lb (barSub ψ T) := hEbT1.trans le_sup_right
  have hL : ∀ g, conjSubgroup V g ≤ T → barSub ψ (conjSubgroup V g) ≤ normalizer (Lb : Set X) := by
    intro g hAT
    by_contra hmove
    set Ab := barSub ψ (conjSubgroup V g)
    have hAbT : Ab ≤ barSub ψ T := barSub_mono hAT
    have hAbel : IsElemAbelian 2 Ab := c.isElemAbelian_bar g
    have hE1 : barSub π (Ab ⊓ normalizer (Lb : Set X)) ≤
        barSub π (barSub ψ T) ⊓ centralizer (Es : Set B) := by
      refine le_inf (barSub_mono (inf_le_left.trans hAbT)) ?_
      rw [← hFEs]
      exact barSub_le_centralizer (inf_le_left.trans (hΔ g hAT))
    obtain ⟨H, Xh, hmov, hEsH, hEsX⟩ := hmovs _ hE1
      ((hAbel.mono inf_le_left).subgroupOf _ |>.map π)
    obtain ⟨Kb, Yb, hirr, hAK, hAO, hEbO, -⟩ := hO X Lb (barSub ψ T) B π Es cb Ab hAbT hAbel
      hmove H Xh 3 hmov Eb hEbT1 hTEb (hFEs ▸ hEsH) (hFEs ▸ hEsX)
    exact hAO (c.le_pCoreOf_of_kgroup w hAT hirr (Or.inl rfl) (Or.inr ⟨rfl, hUb.trans hEbO⟩) hAK)
  apply h2
  refine c.le_of_closing cb hgen (Subgroup.le_normalizer.trans
    (E3.normalizer_le_normalizer_wClos T)) fun K hK => ?_
  obtain ⟨Y, hY, hEsO, hDK⟩ := hKs K hK
  obtain ⟨Yb, hirr, -, -⟩ := cb.lift_twoPTwoIrred hY
  have hUO : barSub ψ U ≤ pCoreOf 2 (liftSub π K) := by
    refine (hUb.trans ?_).trans (liftSub_pCoreOf_le cb.ker K)
    exact (barSub_le_iff hEbN1).1 (hFEs ▸ hEsO)
  refine le_normalizer_wClos_T (c.le_normalizer_wClos w hirr (Or.inl rfl) (Or.inr ⟨rfl, hUO⟩))
    ?_
  rw [wClos_zero_eq_iSup c.elem]
  refine iSup₂_le fun g hg => ?_
  have hN1 := bar_le_tcN1 (barSub_mono hg) (hL g hg)
  have hK' : barSub π (barSub ψ (conjSubgroup V g)) ≤ K := by
    refine le_trans (le_inf (barSub_mono (barSub_mono hg)) ?_) hDK
    rw [← hFEs]
    exact barSub_le_centralizer (hΔ g hg)
  exact (barSub_le_iff (hg.trans c.TN)).1 ((barSub_le_iff hN1).1 hK')

theorem false_of_pair (hK : KillStmt) {U : Subgroup G} {u : G} (w : Witness V T U u)
    {g : G} (hUg : U = conjSubgroup V g) (hUQ : ¬ U ≤ pCoreOf 2 N) {Eb : Subgroup X}
    (hEbT1 : Eb ≤ tcT1 Lb (barSub ψ T))
    (hconj : ∀ t ∈ T, barSub ψ (conjSubgroup V (g * t⁻¹)) ≤ Eb)
    (hF2 : Nat.card (barSub π Eb) = 2)
    (hpair : ∀ x ∈ barSub π Eb, x ≠ 1 → PairProp914 (barSub π Lb) x) : False := by
  subst hUg
  have hUT : conjSubgroup V g ≤ T := w.le_T
  obtain ⟨t, ht, hne⟩ : ∃ t ∈ T, barSub π (barSub ψ (conjSubgroup V (g * t⁻¹))) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hUQ
    rw [← barSub_eq_bot_iff c.ker (hUT.trans c.TN), eq_bot_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_bot]
    refine cb.eq_one_of_centralizes ⟨a, hUT ha, rfl⟩ fun s hs => ?_
    obtain ⟨t, ht, rfl⟩ := hs
    exact c.mem_centralizer_conj_of_bar cb hUT ht
      ((hconj t ht).trans (hEbT1.trans inf_le_right)) (hcon t ht) ha
  set A := conjSubgroup V (g * t⁻¹)
  have hAT : A ≤ T := conj_mul_le_T hUT (inv_mem ht)
  have hAb : barSub ψ A ≤ tcT1 Lb (barSub ψ T) := (hconj t ht).trans hEbT1
  have hAF : barSub π (barSub ψ A) = barSub π Eb := by
    refine Subgroup.eq_of_le_of_card_ge (barSub_mono (hconj t ht)) ?_
    rw [hF2]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  obtain ⟨Hb, Rb, hF⟩ := hK X Lb (barSub ψ T) B π Es cb (barSub ψ A) hAb (c.isElemAbelian_bar _)
    (hAF ▸ hF2) (fun x hx hx1 => hpair x (hAF ▸ hx) hx1)
  exact c.false_of_fiveUseC w hAT hF

theorem false_of_not_le_Q (hO : OrbitStmt) (hK : KillStmt) {U : Subgroup G} {u : G}
    (w : Witness V T U u) (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G))
    (hUQ : ¬ U ≤ pCoreOf 2 N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, rfl⟩ := w.conj
  set W0 := E3.wClos V 0 T with hW0
  have hUΩ : conjSubgroup V h ≤ zOmega W0 := fun x hx =>
    ⟨conjSubgroup_le_wClos_zero w.le_T hx, w.cent_W0 hx,
      (isElemAbelian_conjSubgroup' c.elem h).2 x hx⟩
  have hΩT : zOmega W0 ≤ T := fun x hx => E3.wClos_le 0 T hx.1
  have hTW0 : T ≤ normalizer (W0 : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)
  have hTΩ : T ≤ normalizer (zOmega W0 : Set G) := NFW.le_normalizer_of_conj_mem fun t ht x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 (hTW0 ht) x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer (hTW0 ht)) x).1 hx.2.1,
      by rw [conj_pow, hx.2.2, mul_one, mul_inv_cancel]⟩
  set Eb := barSub ψ (zOmega W0) with hEb
  have hEbT : Eb ≤ barSub ψ T := barSub_mono hΩT
  have hTEb : barSub ψ T ≤ normalizer (Eb : Set X) := barSub_le_normalizer hTΩ
  have hEbel : IsElemAbelian 2 Eb := ((isElemAbelian_zOmega W0).subgroupOf N).map ψ
  have hUb : barSub ψ (conjSubgroup V h) ≤ Eb := barSub_mono hUΩ
  have hUbne : barSub ψ (conjSubgroup V h) ≠ ⊥ := fun hb =>
    hUQ ((barSub_eq_bot_iff c.ker (w.le_T.trans c.TN)).1 hb)
  have hEbT1 : Eb ≤ tcT1 Lb (barSub ψ T) :=
    le_inf hEbT (cb.le_normalizer_of_normal hEbT hTEb hEbel)
  have hFne : barSub π Eb ≠ ⊥ := fun hb =>
    hUbne (le_bot_iff.mp ((cb.eq_bot_of_barSub_eq_bot hEbT1 hTEb hb) ▸ hUb))
  have hΔ : ∀ g, conjSubgroup V g ≤ T → barSub ψ (conjSubgroup V g) ≤ centralizer (Eb : Set X) :=
    fun g hg => barSub_le_centralizer fun x hx => mem_centralizer_iff.mpr fun y hy =>
      ((mem_centralizer_iff.mp (hy.2.1)) x (conjSubgroup_le_wClos_zero hg hx)).symm
  have hconj : ∀ t ∈ T, barSub ψ (conjSubgroup V (h * t⁻¹)) ≤ Eb := by
    intro t ht
    refine barSub_mono ?_
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup,
      ← conjSubgroup_eq_iff_mem_normalizer.2 (inv_mem (hTΩ ht))]
    exact E3.conjSubgroup_mono_left _ hUΩ
  rcases cb.facts.normal (barSub π Eb) (barSub_mono hEbT) (barSub_le_normalizer hTEb)
      ((hEbel.subgroupOf _).map π) with hF0 | hFEs | ⟨hF2, hpair⟩
  · exact hFne hF0
  · exact c.false_of_Es cb hO w h2 hEbT1 hTEb hUb hΔ hFEs (hFEs ▸ hFne)
  · exact c.false_of_pair cb hK w rfl hUQ hEbT1 hconj hF2 hpair

end Ctx

theorem tcAbstract_of (hO : OrbitStmt) (hK : KillStmt) : TCAbstract := by
  intro G _ _ V T N hyp hTN hNM hstar X _ _ ψ hψ hker Lb B _ _ π Es cb
  have c : Ctx V T N ψ := ⟨hyp, hTN, hNM, hstar, hψ, hker⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨U, u, w⟩ := c.exists_witness hcon.1
  exact c.false_of_not_le_Q cb hO hK w hcon.2 (c.not_le_Q cb hO w hcon.2)

end CFSG.LocalAnalysis.WeakClosure81.TC914
