module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNIrred
public import CFSG.LocalAnalysis.WeakClosure81.NineOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {ψ : ↥N →* X}
variable (c : Ctx V T N ψ)
include c

omit [Finite X] c in
theorem exists_three_of_irr {Kb Yb : Subgroup X} {p : ℕ}
    (h3 : p = 3 ∨ ∀ J : Subgroup X, barSub ψ T ≤ normalizer (J : Set X) → Yb ≤ J →
      ∃ x ∈ J, orderOf x = 3)
    {Y : Subgroup G} (hY : TwoPTwoIrred (liftSub ψ Kb) (liftSub ψ Kb ⊓ T) Y p)
    (hYb : barSub ψ Y = Yb) {D : Subgroup G} (hTD : T ≤ normalizer (D : Set G))
    (hKD : twoResidual (liftSub ψ Kb) ≤ D) : ∃ x ∈ D, orderOf x = 3 := by
  rcases h3 with rfl | h3
  · obtain ⟨y, hy, hy3⟩ := exists_orderOf_three_twoResidual hY
    exact ⟨y, hKD hy, hy3⟩
  · have hYD : Y ≤ D := (le_twoResidual_of_isPGroup hY.prime hY.odd hY.sylowP.isPGroup
      hY.sylowP.le).trans hKD
    obtain ⟨x, hx, hx3⟩ := h3 (barSub ψ D) (barSub_le_normalizer hTD) (hYb ▸ barSub_mono hYD)
    exact exists_orderOf_eq_of_barSub hx hx3

omit [Finite G] [Finite X] in
theorem T_le_normalizer_inf_centralizer {Z : Subgroup G} (hTZ : T ≤ normalizer (Z : Set G)) :
    T ≤ normalizer ((N ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := fun _ ht =>
  mem_normalizer_inf (Subgroup.le_normalizer (c.TN ht)) (mem_normalizer_centralizer (hTZ ht))

@[expose] def centQ (V N : Subgroup G) : Subgroup G :=
  N ⊓ ⨅ (g' : G) (_ : conjSubgroup V g' ≤ pCoreOf 2 N ∧ conjSubgroup V g' ≠ V),
    centralizer (conjSubgroup V g' : Set G)

omit [Finite G] c in
theorem mem_centQ {x : G} : x ∈ centQ V N ↔ x ∈ N ∧ ∀ g' : G, conjSubgroup V g' ≤ pCoreOf 2 N →
    conjSubgroup V g' ≠ V → x ∈ centralizer (conjSubgroup V g' : Set G) := by
  rw [centQ, Subgroup.mem_inf, Subgroup.mem_iInf]
  simp only [Subgroup.mem_iInf, and_imp]

omit [Finite G] [Finite X] in
theorem T_le_normalizer_centQ : T ≤ normalizer (centQ V N : Set G) := by
  apply NFW.le_normalizer_of_conj_mem
  intro t ht x hx
  have htN : t ∈ N := c.TN ht
  rw [mem_centQ] at hx ⊢
  refine ⟨N.mul_mem (N.mul_mem htN hx.1) (N.inv_mem htN), fun g' hg'Q hg'V => ?_⟩
  have hQt : conjSubgroup (pCoreOf 2 N) t = pCoreOf 2 N :=
    conjSubgroup_eq_iff_mem_normalizer.2 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N htN)
  have h1Q : conjSubgroup V (g' * t) ≤ pCoreOf 2 N := by
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

omit [Finite X] in
theorem commutator_cClos_ne_bot {h u : G} (w : Witness V T (conjSubgroup V h) u)
    {Kb Yb : Subgroup X} {p : ℕ} {Y : Subgroup G}
    (hY : TwoPTwoIrred (liftSub ψ Kb) (liftSub ψ Kb ⊓ T) Y p) (hYb : barSub ψ Y = Yb)
    (h3 : p = 3 ∨ ∀ J : Subgroup X, barSub ψ T ≤ normalizer (J : Set X) → Yb ≤ J →
      ∃ x ∈ J, orderOf x = 3)
    (hU : conjSubgroup V h ≤ pCoreOf 2 N ∨
      (p = 3 ∧ conjSubgroup V h ≤ pCoreOf 2 (liftSub ψ Kb))) :
    ⁅twoResidual (liftSub ψ Kb), E3.cClos V 1 (liftSub ψ Kb ⊓ T)⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := liftSub ψ Kb with hK
  intro h2
  have hO2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  have hKN : K ≤ N := liftSub_le Kb
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have hW1S : E3.wClos V 1 (K ⊓ T) ≤ E3.wClos V 1 T := E3.wClos_mono inf_le_right
  rcases hU with hUQ | ⟨rfl, hUO⟩
  ·
    set Z := pCoreOf 2 N ⊓ centralizer (E3.wClos V 1 T : Set G) with hZ
    have hZS : Z ≤ E3.cClos V 1 (K ⊓ T) := fun z hz =>
      mem_inf.mpr ⟨⟨pCoreOf_le_liftSub c.ker Kb hz.1, c.Q_le_T hz.1⟩, centralizer_le hW1S hz.2⟩
    have hTZ : T ≤ normalizer (Z : Set G) := fun t ht => mem_normalizer_inf
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N (c.TN ht))
      (mem_normalizer_centralizer
        ((Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)) ht))
    obtain ⟨x, hxD, hx3⟩ := exists_three_of_irr h3 hY hYb
      (c.T_le_normalizer_inf_centralizer hTZ)
      (le_inf ((CFSG.Quasithin.twoResidual_le K).trans hKN) (hO2.trans (centralizer_le hZS)))
    exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one hxD.1
      ((Subgroup.mem_centralizer_iff.1 hxD.2) u ⟨hUQ w.mem, w.cent_W1⟩).symm hx3
  ·
    have huS : u ∈ E3.cClos V 1 (K ⊓ T) := mem_inf.mpr
      ⟨⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K (hUO w.mem), w.le_T w.mem⟩,
        centralizer_le hW1S w.cent_W1⟩
    obtain ⟨y, hy, hy3⟩ := exists_orderOf_three_twoResidual hY
    exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one
      (hKN (CFSG.Quasithin.twoResidual_le K hy))
      ((Subgroup.mem_centralizer_iff.1 (hO2 hy)) u huS).symm hy3

omit [Finite X] in
theorem not_nineOneThree {h u : G} (w : Witness V T (conjSubgroup V h) u)
    {Kb Yb : Subgroup X} {p : ℕ} {Y : Subgroup G}
    (hY : TwoPTwoIrred (liftSub ψ Kb) (liftSub ψ Kb ⊓ T) Y p) (hYb : barSub ψ Y = Yb)
    (h3 : p = 3 ∨ ∀ J : Subgroup X, barSub ψ T ≤ normalizer (J : Set X) → Yb ≤ J →
      ∃ x ∈ J, orderOf x = 3)
    (hU : conjSubgroup V h ≤ pCoreOf 2 N ∨
      (p = 3 ∧ conjSubgroup V h ≤ pCoreOf 2 (liftSub ψ Kb))) :
    ¬ NineOneThree V (liftSub ψ Kb) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := liftSub ψ Kb with hK
  intro h3'
  have hKN : K ≤ N := liftSub_le Kb
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  rcases hU with hUQ | ⟨rfl, hUO⟩
  ·
    have hQO : pCoreOf 2 N ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_liftSub c.ker Kb)
        (hKN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    have hKD : twoResidual K ≤ centQ V N := by
      intro k hk
      rw [mem_centQ]
      refine ⟨hKN (CFSG.Quasithin.twoResidual_le K hk), fun g' hg'Q _ => ?_⟩
      have hc := h3'.2 (conjSubgroup V g') ⟨g', rfl⟩ (hg'Q.trans hQO)
      exact Subgroup.le_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc) hk
    obtain ⟨x, hxD, hx3⟩ := exists_three_of_irr h3 hY hYb c.T_le_normalizer_centQ hKD
    rw [mem_centQ] at hxD
    exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one hxD.1
      ((Subgroup.mem_centralizer_iff.1 (hxD.2 h hUQ w.ne)) u w.mem).symm hx3
  ·
    obtain ⟨y, hy, hy3⟩ := exists_orderOf_three_twoResidual hY
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h3'.2 _ ⟨h, rfl⟩ hUO) w.mem
    exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one
      (hKN (CFSG.Quasithin.twoResidual_le K hy)) ((Subgroup.mem_centralizer_iff.1 hc) y hy) hy3

theorem le_normalizer_wClos {U : Subgroup G} {u : G} (w : Witness V T U u) {Kb Yb : Subgroup X}
    {p : ℕ} (hirr : TwoPTwoIrred Kb (Kb ⊓ barSub ψ T) Yb p)
    (h3 : p = 3 ∨ ∀ J : Subgroup X, barSub ψ T ≤ normalizer (J : Set X) → Yb ≤ J →
      ∃ x ∈ J, orderOf x = 3)
    (hU : U ≤ pCoreOf 2 N ∨ (p = 3 ∧ barSub ψ U ≤ pCoreOf 2 Kb)) :
    liftSub ψ Kb ≤ normalizer (E3.wClos V 0 (liftSub ψ Kb ⊓ T) : Set G) := by
  obtain ⟨h, rfl⟩ := w.conj
  have hS : liftSub ψ (Kb ⊓ barSub ψ T) = liftSub ψ Kb ⊓ T := by
    rw [liftSub_inf, c.liftSub_barSub_T]
  obtain ⟨Y, hY, hYb, -⟩ := twoPTwoIrred_liftSub c.ker c.surj hirr
  rw [hS] at hY
  have h91 : Nine1Hyp V (liftSub ψ Kb) (liftSub ψ Kb ⊓ T) Y p := ⟨hY, (liftSub_le Kb).trans c.NM⟩
  have hU' : conjSubgroup V h ≤ pCoreOf 2 N ∨
      (p = 3 ∧ conjSubgroup V h ≤ pCoreOf 2 (liftSub ψ Kb)) :=
    hU.imp_right fun ⟨hp, hUK⟩ => ⟨hp, ((barSub_le_iff (w.le_T.trans c.TN)).1 hUK).trans
      (liftSub_pCoreOf_le c.ker Kb)⟩
  rcases nine_one c.hyp.hyp7 c.hyp.rk_gt h91 with h1 | h2 | h3'
  · exact h1
  · exact absurd h2 (c.commutator_cClos_ne_bot w hY hYb h3 hU')
  · exact absurd h3' (c.not_nineOneThree w hY hYb h3 hU')

omit [Finite X] in
theorem conj_le_pCoreOf_of_le_normalizer {K : Subgroup G}
    (hK : K ≤ normalizer (E3.wClos V 0 (K ⊓ T) : Set G)) {g : G}
    (hA : conjSubgroup V g ≤ K ⊓ T) : conjSubgroup V g ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (conjSubgroup_le_wClos_zero hA).trans ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((E3.wClos_le 0 _).trans inf_le_left) hK
    (c.isPGroup_T.to_le ((E3.wClos_le 0 _).trans inf_le_right))

omit [Finite G] [Finite X] c in
theorem le_normalizer_wClos_T {K : Subgroup G}
    (hK : K ≤ normalizer (E3.wClos V 0 (K ⊓ T) : Set G)) (hW : E3.wClos V 0 T ≤ K) :
    K ≤ normalizer (E3.wClos V 0 T : Set G) := by
  have hW0S : E3.wClos V 0 (K ⊓ T) = E3.wClos V 0 T := by
    apply le_antisymm (E3.wClos_mono inf_le_right)
    refine E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨?_, hA.2⟩
    exact (E3.le_wClos hA).trans (le_inf hW (E3.wClos_le 0 T))
  rwa [hW0S] at hK

end Ctx

end CFSG.LocalAnalysis.WeakClosure81.TC914
