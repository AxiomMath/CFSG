module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNIrred
public import CFSG.LocalAnalysis.WeakClosure81.NineOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFW

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def zOmega (W : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ W ∧ x ∈ centralizer (W : Set G) ∧ x ^ 2 = 1}
  one_mem' := ⟨W.one_mem, Subgroup.one_mem _, one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨haW, haC, ha2⟩ ⟨hbW, hbC, hb2⟩
    refine ⟨W.mul_mem haW hbW, Subgroup.mul_mem _ haC hbC, ?_⟩
    have hab : Commute a b := (Subgroup.mem_centralizer_iff.1 hbC) a haW
    rw [hab.mul_pow, ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haW, haC, ha2⟩
    exact ⟨W.inv_mem haW, Subgroup.inv_mem _ haC, by rw [inv_pow, ha2, inv_one]⟩

omit [Finite G] in
theorem isElemAbelian_zOmega (W : Subgroup G) : IsElemAbelian 2 (zOmega W) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
  exact (Subgroup.mem_centralizer_iff.1 b.2.2.1) a a.2.1

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {π : ↥N →* X} {Lb : Subgroup X}
variable (c : Ctx V T N π Lb)
include c

theorem conj_le_Q_eq {U : Subgroup G} {u : G} (w : Witness V T U u)
    (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) {g₀ : G}
    (hB : conjSubgroup V g₀ ≤ pCoreOf 2 N) : conjSubgroup V g₀ = V := by
  by_contra hBV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, rfl⟩ := w.conj
  obtain ⟨g, hAT, hAQ⟩ := c.exists_conj_not_le h2
  set A := conjSubgroup V g with hAdef
  set Tb := barSub π T with hTb
  set Q := pCoreOf 2 N with hQ
  have hAN : A ≤ N := hAT.trans c.TN
  have hAbT : barSub π A ≤ Tb := barSub_mono hAT
  have hAbel : IsElemAbelian 2 (barSub π A) :=
    ((isElemAbelian_conjSubgroup' c.elem g).subgroupOf N).map π
  have hAb4 := c.four_le_card_barSub w hAT hAQ
  obtain ⟨Kb, Yb, p, hAK, hirr, hcore, hnorm, hp3⟩ := c.facts.table _ hAbT hAbel hAb4
  set K := liftSub π Kb with hK
  have hKN : K ≤ N := liftSub_le Kb
  have hS : liftSub π (Kb ⊓ Tb) = K ⊓ T := by rw [liftSub_inf, c.liftSub_barSub_T]
  obtain ⟨Y, hY, -, -⟩ := twoPTwoIrred_liftSub c.ker c.surj hirr
  rw [hS] at hY
  have h91 : Nine1Hyp V K (K ⊓ T) Y p := ⟨hY, hKN.trans c.NM⟩
  have hAK' : A ≤ K := (barSub_le_iff hAN).1 hAK
  have hAS : A ≤ K ⊓ T := le_inf hAK' hAT
  set C1T := E3.cClos V 1 T with hC1T
  have hC1TT : C1T ≤ T := inf_le_left
  have hTC1T : T ≤ normalizer (C1T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos T)
  have hAW1 : A ≤ E3.wClos V 1 T := c.conj_le_wClos_one hAT
  have hC1A : C1T ≤ centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 hx.2) a (hAW1 ha)
  have hC1Tb : barSub π C1T ≤ coreIn (Tb ⊓ centralizer (barSub π A : Set X)) Tb :=
    le_coreIn (barSub_mono hC1TT) (barSub_le_normalizer hTC1T)
      (le_inf (barSub_mono hC1TT) (barSub_le_centralizer hC1A))
  have hC1K : C1T ≤ K :=
    (barSub_le_iff (hC1TT.trans c.TN)).1 (hC1Tb.trans (hcore.trans inf_le_left))
  have hC1S : C1T ≤ E3.cClos V 1 (K ⊓ T) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨⟨hC1K hx, hx.1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 hx.2) z (E3.wClos_mono inf_le_right hz)
  have key : ∀ D : Subgroup G, T ≤ normalizer (D : Set G) → twoResidual K ≤ D →
      ∃ x ∈ D, orderOf x = 3 := by
    intro D hTD hKD
    rcases hp3 with rfl | hmax
    · obtain ⟨y, hy, hy3⟩ := exists_orderOf_three_twoResidual hY
      exact ⟨y, hKD hy, hy3⟩
    · exact c.exists_orderOf_three_of_maximal hmax hY hKN hTD hKD
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have hBM : conjSubgroup V g₀ ≤ normalizer (V : Set G) := hB.trans (c.Q_le_T.trans c.T_le_M)
  rcases nine_one c.hyp.hyp7 c.hyp.rk_gt h91 with h1 | h2' | h3
  ·
    apply hnorm (barSub π (E3.wClos V 0 (K ⊓ T)))
    · exact barSub_mono (conjSubgroup_le_wClos_zero hAS)
    · rw [← barSub_liftSub c.surj (Kb ⊓ Tb), hS]
      exact barSub_mono (E3.wClos_le 0 _)
    · refine sup_le ?_ ?_
      · rw [← barSub_liftSub c.surj Kb]
        exact barSub_le_normalizer h1
      · rintro tb ⟨htb, htbN⟩
        obtain ⟨t, htT, rfl⟩ := htb
        have htS : (t : G) ∈ normalizer ((K ⊓ T : Subgroup G) : Set G) := by
          rw [← hS]
          exact mem_normalizer_liftSub t.2 htbN
        exact mem_normalizer_barSub (E3.normalizer_le_normalizer_wClos _ htS)
  ·
    have hD : T ≤ normalizer ((N ⊓ centralizer (C1T : Set G) : Subgroup G) : Set G) :=
      fun t ht => mem_normalizer_inf (Subgroup.le_normalizer (c.TN ht))
        (mem_normalizer_centralizer (hTC1T ht))
    have hKD : twoResidual K ≤ N ⊓ centralizer (C1T : Set G) := by
      refine le_inf ((CFSG.Quasithin.twoResidual_le K).trans hKN) ?_
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2').trans
        (Subgroup.centralizer_le hC1S)
    obtain ⟨x, hxD, hx3⟩ := key _ hD hKD
    have huC : u ∈ C1T := Subgroup.mem_inf.2 ⟨w.le_T w.mem, w.cent_W1⟩
    have hxu : x * u = u * x := ((Subgroup.mem_centralizer_iff.1 hxD.2) u huC).symm
    exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one hxD.1 hxu hx3
  ·
    have hQK : Q ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_liftSub c.ker Kb)
        (hKN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    set D : Subgroup G := N ⊓ ⨅ (g' : G) (_ : conjSubgroup V g' ≤ Q ∧ conjSubgroup V g' ≠ V),
      centralizer (conjSubgroup V g' : Set G) with hD
    have hmemD : ∀ x : G, x ∈ D ↔ x ∈ N ∧ ∀ g' : G, conjSubgroup V g' ≤ Q →
        conjSubgroup V g' ≠ V → x ∈ centralizer (conjSubgroup V g' : Set G) := by
      intro x
      rw [hD, Subgroup.mem_inf, Subgroup.mem_iInf]
      simp only [Subgroup.mem_iInf, and_imp]
    have hTD : T ≤ normalizer (D : Set G) := by
      apply le_normalizer_of_conj_mem
      intro t ht x hx
      have htN : t ∈ N := c.TN ht
      rw [hmemD] at hx ⊢
      refine ⟨N.mul_mem (N.mul_mem htN hx.1) (N.inv_mem htN), fun g' hg'Q hg'V => ?_⟩
      have hQt : conjSubgroup Q t = Q :=
        conjSubgroup_eq_iff_mem_normalizer.2
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N htN)
      have h1Q : conjSubgroup V (g' * t) ≤ Q := by
        rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← hQt]
        exact E3.conjSubgroup_mono_left t hg'Q
      have h1V : conjSubgroup V (g' * t) ≠ V := by
        intro heq
        apply hg'V
        have h3 : conjSubgroup V t⁻¹ = V :=
          conjSubgroup_eq_iff_mem_normalizer.2 (inv_mem (c.T_le_M ht))
        rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup] at heq
        rw [← E3.conjSubgroup_conj_inv (conjSubgroup V g') t, heq, h3]
      have hxc := hx.2 (g' * t) h1Q h1V
      rw [Subgroup.mem_centralizer_iff] at hxc ⊢
      intro b hb
      have hb' : t⁻¹ * b * t ∈ conjSubgroup V (g' * t) := by
        rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, mem_conjSubgroup_iff]
        simpa [mul_assoc] using hb
      have h4 := hxc _ hb'
      calc b * (t * x * t⁻¹) = t * ((t⁻¹ * b * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * b * t)) * t⁻¹ := by rw [h4]
        _ = t * x * t⁻¹ * b := by group
    have hKD : twoResidual K ≤ D := by
      intro k hk
      rw [hmemD]
      refine ⟨hKN (CFSG.Quasithin.twoResidual_le K hk), fun g' hg'Q _ => ?_⟩
      have hc := h3.2 (conjSubgroup V g') ⟨g', rfl⟩ (hg'Q.trans hQK)
      exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc) hk
    obtain ⟨x, hxD, hx3⟩ := key D hTD hKD
    rw [hmemD] at hxD
    have hxB := hxD.2 g₀ hB hBV
    have hBne : conjSubgroup V g₀ ≠ ⊥ := by
      intro hb
      have h1 := c.card_V
      rw [← E3.card_conjSubgroup V g₀, hb, Subgroup.card_bot] at h1
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
    have hb1' : b ≠ 1 := fun h0 => hb1 (Subtype.ext h0)
    have hxb : x * b = b * x := ((Subgroup.mem_centralizer_iff.1 hxB) b hb).symm
    exact c.not_orderOf_three_of_commute hBM hBV hb hb1' hxD.1 hxb hx3

theorem false_of_witness {U : Subgroup G} {u : G} (w : Witness V T U u)
    (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : ∀ g₀ : G, conjSubgroup V g₀ ≤ pCoreOf 2 N → conjSubgroup V g₀ = V :=
    fun g₀ hB => c.conj_le_Q_eq w h2 hB
  obtain ⟨h, rfl⟩ := w.conj
  set W0 := E3.wClos V 0 T with hW0
  set Tb := barSub π T with hTb
  have hUQ : ¬ conjSubgroup V h ≤ pCoreOf 2 N := fun hle => w.ne (h7 h hle)
  have hU4 : 4 ≤ Nat.card (barSub π (conjSubgroup V h)) := c.four_le_card_barSub w w.le_T hUQ
  have hUΩ : conjSubgroup V h ≤ zOmega W0 := fun x hx =>
    ⟨conjSubgroup_le_wClos_zero w.le_T hx, w.cent_W0 hx,
      (isElemAbelian_conjSubgroup' c.elem h).2 x hx⟩
  have hΩT : zOmega W0 ≤ T := fun x hx => E3.wClos_le 0 T hx.1
  have hTW0 : T ≤ normalizer (W0 : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)
  have hTΩ : T ≤ normalizer (zOmega W0 : Set G) := le_normalizer_of_conj_mem fun t ht x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 (hTW0 ht) x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer (hTW0 ht)) x).1 hx.2.1,
      by rw [conj_pow, hx.2.2, mul_one, mul_inv_cancel]⟩
  have hΩW : zOmega W0 ≤ centralizer (W0 : Set G) := fun x hx => hx.2.1
  have hE4 : 4 ≤ Nat.card (barSub π (zOmega W0)) :=
    hU4.trans (Subgroup.card_le_of_le (barSub_mono hUΩ))
  obtain ⟨Ks, hKs, hgen⟩ := c.facts.close _ (barSub_mono hΩT) (barSub_le_normalizer hTΩ)
    (((isElemAbelian_zOmega W0).subgroupOf N).map π) hE4
  have hW0E : barSub π W0 ≤ Tb ⊓ centralizer (barSub π (zOmega W0) : Set X) :=
    le_inf (barSub_mono (E3.wClos_le 0 T))
      (barSub_le_centralizer (Subgroup.le_centralizer_iff.1 hΩW))
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have hK : ∀ Kb ∈ Ks, liftSub π Kb ≤ normalizer (W0 : Set G) := by
    intro Kb hKb
    obtain ⟨Yb, hirr, hEO, hCK⟩ := hKs Kb hKb
    set K := liftSub π Kb with hK
    have hKN : K ≤ N := liftSub_le Kb
    have hS : liftSub π (Kb ⊓ Tb) = K ⊓ T := by rw [liftSub_inf, c.liftSub_barSub_T]
    obtain ⟨Y, hY, -, -⟩ := twoPTwoIrred_liftSub c.ker c.surj hirr
    rw [hS] at hY
    have h91 : Nine1Hyp V K (K ⊓ T) Y 3 := ⟨hY, hKN.trans c.NM⟩
    have hUO : conjSubgroup V h ≤ pCoreOf 2 K :=
      ((barSub_le_iff (w.le_T.trans c.TN)).1 ((barSub_mono hUΩ).trans hEO)).trans
        (liftSub_pCoreOf_le c.ker Kb)
    have hUK : conjSubgroup V h ≤ K := hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    have hUS : conjSubgroup V h ≤ K ⊓ T := le_inf hUK w.le_T
    have hW0K : W0 ≤ K :=
      (barSub_le_iff ((E3.wClos_le 0 T).trans c.TN)).1 (hW0E.trans hCK)
    have hW0S : E3.wClos V 0 (K ⊓ T) = W0 := by
      apply le_antisymm (E3.wClos_mono inf_le_right)
      refine E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨?_, hA.2⟩
      exact (E3.le_wClos hA).trans (le_inf hW0K (E3.wClos_le 0 T))
    obtain ⟨y, hy, hy3⟩ := exists_orderOf_three_twoResidual hY
    have hyN : y ∈ N := hKN (CFSG.Quasithin.twoResidual_le K hy)
    rcases nine_one c.hyp.hyp7 c.hyp.rk_gt h91 with h1 | h2' | h3
    · rwa [hW0S] at h1
    · exfalso
      have huS : u ∈ E3.cClos V 1 (K ⊓ T) := by
        refine Subgroup.mem_inf.2 ⟨hUS w.mem, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.1 w.cent_W1) z (E3.wClos_mono inf_le_right hz)
      have hyc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2' hy
      have hyu : y * u = u * y := ((Subgroup.mem_centralizer_iff.1 hyc) u huS).symm
      exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one hyN hyu hy3
    · exfalso
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h3.2 _ ⟨h, rfl⟩ hUO) w.mem
      have hyu : y * u = u * y := (Subgroup.mem_centralizer_iff.1 hc) y hy
      exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one hyN hyu hy3
  apply h2
  have hQH : pCoreOf 2 N ≤ N ⊓ normalizer (W0 : Set G) :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 N) (c.Q_le_T.trans hTW0)
  have htop : (⊤ : Subgroup X) ≤ barSub π (N ⊓ normalizer (W0 : Set G)) := by
    rw [← hgen]
    refine sup_le (iSup₂_le fun Kb hKb => ?_) (barSub_mono (le_inf c.TN hTW0))
    rw [← barSub_liftSub c.surj Kb]
    exact barSub_mono (le_inf (liftSub_le Kb) (hK Kb hKb))
  have hN := liftSub_mono (π := π) htop
  rw [liftSub_top, liftSub_barSub c.ker hQH inf_le_left] at hN
  exact hN.trans inf_le_right

end Ctx

end CFSG.LocalAnalysis.WeakClosure81.NFW
