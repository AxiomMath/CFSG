module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCStmt

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {ψ : ↥N →* X}
variable (c : Ctx V T N ψ)
include c

omit [Finite G] [Finite X] c in
theorem conj_mul_le_T {g t : G} (hg : conjSubgroup V g ≤ T) (ht : t ∈ T) :
    conjSubgroup V (g * t) ≤ T := by
  rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup]
  have hTt : conjSubgroup T t = T := conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer ht)
  rw [← hTt]
  exact E3.conjSubgroup_mono_left t hg

omit [Finite X] in
theorem isElemAbelian_bar (g : G) : IsElemAbelian 2 (barSub ψ (conjSubgroup V g)) :=
  ((isElemAbelian_conjSubgroup' c.elem g).subgroupOf N).map ψ

theorem le_pCoreOf_of_kgroup {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) {Kb Yb : Subgroup X} {p : ℕ}
    (hirr : TwoPTwoIrred Kb (Kb ⊓ barSub ψ T) Yb p)
    (h3 : p = 3 ∨ ∀ J : Subgroup X, barSub ψ T ≤ normalizer (J : Set X) → Yb ≤ J →
      ∃ x ∈ J, orderOf x = 3)
    (hU : U ≤ pCoreOf 2 N ∨ (p = 3 ∧ barSub ψ U ≤ pCoreOf 2 Kb))
    (hAK : barSub ψ (conjSubgroup V g) ≤ Kb) :
    barSub ψ (conjSubgroup V g) ≤ pCoreOf 2 Kb := by
  have hK := c.le_normalizer_wClos w hirr h3 hU
  have hA := c.conj_le_pCoreOf_of_le_normalizer hK
    (le_inf ((barSub_le_iff (hAT.trans c.TN)).1 hAK) hAT)
  exact (barSub_mono hA).trans (c.barSub_pCoreOf_le Kb)

theorem le_of_closing {Lb : Subgroup X} {B : Type} [Group B] [Finite B]
    {π : ↥(tcN1 Lb (barSub ψ T)) →* B} {Es : Subgroup B} (cb : TCBar Lb (barSub ψ T) π Es)
    {Ks : Finset (Subgroup B)} (hgen : (⨆ K ∈ Ks, K) ⊔ barSub π (barSub ψ T) = ⊤)
    {M : Subgroup G} (hTM : T ≤ M) (hKM : ∀ K ∈ Ks, liftSub ψ (liftSub π K) ≤ M) :
    N ≤ M := by
  set J := M ⊓ N with hJ
  have hQJ : pCoreOf 2 N ≤ J :=
    le_inf (c.Q_le_T.trans hTM) (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
  have hTJ : barSub ψ T ≤ barSub ψ J := barSub_mono (le_inf hTM c.TN)
  have hLJ : Lb ≤ barSub ψ J := by
    refine (cb.Lb_le_of_closing hgen).trans (sup_le (iSup₂_le fun K hK => ?_) hTJ)
    rw [← barSub_liftSub c.surj (liftSub π K)]
    exact barSub_mono (le_inf (hKM K hK) (liftSub_le _))
  have hbar : barSub ψ J = ⊤ := by
    rw [eq_top_iff, ← cb.gen]
    refine sup_le (iSup₂_le fun s hs => ?_) hTJ
    intro x hx
    have hs' : s ∈ barSub ψ J := hTJ hs
    have h1 : s * x * s⁻¹ ∈ barSub ψ J := hLJ (mem_conjSubgroup_iff.mp hx)
    have := mul_mem (mul_mem (inv_mem hs') h1) hs'
    simpa [mul_assoc] using this
  have hN := liftSub_mono (π := ψ) hbar.ge
  rw [liftSub_top, liftSub_barSub c.ker hQJ inf_le_right] at hN
  exact hN.trans inf_le_left

variable {Lb : Subgroup X} {B : Type} [Group B] [Finite B] {π : ↥(tcN1 Lb (barSub ψ T)) →* B}
  {Es : Subgroup B} (cb : TCBar Lb (barSub ψ T) π Es)
include cb

omit c cb in
omit [Finite G] [Finite X] in
theorem le_normalizer_bot {Y : Type*} [Group Y] (H : Subgroup Y) :
    H ≤ normalizer ((⊥ : Subgroup Y) : Set Y) := by
  rw [(Subgroup.normalizer_eq_top_iff).mpr (inferInstance : (⊥ : Subgroup Y).Normal)]
  exact le_top

omit c cb in
omit [Finite G] [Finite X] in
theorem barSub_bot' {Y : Type} [Group Y] {M : Subgroup Y} {Z : Type} [Group Z] (f : ↥M →* Z) :
    barSub f (⊥ : Subgroup Y) = ⊥ := by
  rw [barSub, Subgroup.bot_subgroupOf, Subgroup.map_bot]

omit [Finite G] [Finite X] [Finite B] c cb in
theorem bar_le_tcN1 {A : Subgroup X} (hAT : A ≤ barSub ψ T) (hAL : A ≤ normalizer (Lb : Set X)) :
    A ≤ tcN1 Lb (barSub ψ T) := fun _ ha => mem_sup_right ⟨hAT ha, hAL ha⟩

theorem le_normalizer_of_le_Q (hO : OrbitStmt) {U : Subgroup G} {u : G} (w : Witness V T U u)
    (hUQ : U ≤ pCoreOf 2 N) {g : G} (hAT : conjSubgroup V g ≤ T) :
    barSub ψ (conjSubgroup V g) ≤ normalizer (Lb : Set X) := by
  by_contra hmove
  set Ab := barSub ψ (conjSubgroup V g)
  have hAbT : Ab ≤ barSub ψ T := barSub_mono hAT
  have hAbel : IsElemAbelian 2 Ab := c.isElemAbelian_bar g
  obtain ⟨H, Xh, p, hmov⟩ := cb.facts.mov (barSub π (Ab ⊓ normalizer (Lb : Set X)))
    (barSub_mono (inf_le_left.trans hAbT)) ((hAbel.mono inf_le_left).subgroupOf _ |>.map π)
  obtain ⟨Kb, Yb, hirr, hAK, hAO, -, h3⟩ := hO X Lb (barSub ψ T) B π Es cb Ab hAbT hAbel hmove
    H Xh p hmov ⊥ bot_le (le_normalizer_bot _) (by rw [barSub_bot']; exact bot_le) (by
      rw [barSub_bot']
      intro f hf x _
      rw [mem_bot.mp hf]
      simp)
  exact hAO (c.le_pCoreOf_of_kgroup w hAT hirr h3 (Or.inl hUQ) hAK)

theorem bar_eq_bot_or_Es (hO : OrbitStmt) {U : Subgroup G} {u : G} (w : Witness V T U u)
    (hUQ : U ≤ pCoreOf 2 N) {g : G} (hAT : conjSubgroup V g ≤ T) :
    barSub π (barSub ψ (conjSubgroup V g)) = ⊥ ∨ barSub π (barSub ψ (conjSubgroup V g)) = Es := by
  by_contra hne
  rw [not_or] at hne
  set Ab := barSub ψ (conjSubgroup V g)
  have hAbT : Ab ≤ barSub ψ T := barSub_mono hAT
  have hAbN := bar_le_tcN1 hAbT (c.le_normalizer_of_le_Q cb hO w hUQ hAT)
  rcases cb.facts.fix (barSub π Ab) (barSub_mono hAbT)
    ((c.isElemAbelian_bar g).subgroupOf _ |>.map π) hne.1 with ⟨K, Y, p, hw⟩ | heq
  · obtain ⟨Yb, hirr, hAK, hAO, h3⟩ := cb.fix_lift hAbN hw
    exact hAO (c.le_pCoreOf_of_kgroup w hAT hirr h3 (Or.inl hUQ) hAK)
  · exact hne.2 heq

omit [Finite G] [Finite B] in
theorem mem_centralizer_conj_of_bar {g t : G} (hAT : conjSubgroup V g ≤ T) (ht : t ∈ T)
    (hL : barSub ψ (conjSubgroup V (g * t⁻¹)) ≤ normalizer (Lb : Set X))
    (hbot : barSub π (barSub ψ (conjSubgroup V (g * t⁻¹))) = ⊥) {a : G}
    (ha : a ∈ conjSubgroup V g) :
    ψ ⟨a, c.TN (hAT ha)⟩ ∈ centralizer (conjSubgroup Lb (ψ ⟨t, c.TN ht⟩) : Set X) := by
  have hA'T : conjSubgroup V (g * t⁻¹) ≤ T := conj_mul_le_T hAT (inv_mem ht)
  have hy : t * a * t⁻¹ ∈ conjSubgroup V (g * t⁻¹) := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, mem_conjSubgroup_iff]
    simpa [mul_assoc] using ha
  have hyN : t * a * t⁻¹ ∈ N := c.TN (hA'T hy)
  have hyb : ψ ⟨t * a * t⁻¹, hyN⟩ ∈ barSub ψ (conjSubgroup V (g * t⁻¹)) :=
    mem_barSub_of_mem hyN hy
  have hyN1 := bar_le_tcN1 (barSub_mono hA'T) hL hyb
  have h1 : π ⟨_, hyN1⟩ = 1 := by
    have := mem_barSub_of_mem (π := π) hyN1 hyb
    rwa [hbot, mem_bot] at this
  rw [TCBar.mem_centralizer_conj_iff]
  have h2 : ψ ⟨t * a * t⁻¹, hyN⟩ ∈ centralizer (Lb : Set X) := (cb.mem_of_ker h1).2
  have e : ψ ⟨t * a * t⁻¹, hyN⟩ = ψ ⟨t, c.TN ht⟩ * ψ ⟨a, c.TN (hAT ha)⟩ * (ψ ⟨t, c.TN ht⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rwa [e] at h2

theorem not_le_Q (hO : OrbitStmt) {U : Subgroup G} {u : G} (w : Witness V T U u)
    (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) : ¬ U ≤ pCoreOf 2 N := by
  intro hUQ
  obtain ⟨g, hAT, hAQ⟩ := c.exists_conj_not_le h2
  have hL : ∀ g', conjSubgroup V g' ≤ T →
      barSub ψ (conjSubgroup V g') ≤ normalizer (Lb : Set X) :=
    fun g' hg' => c.le_normalizer_of_le_Q cb hO w hUQ hg'
  by_cases hEs : Es = ⊥
  ·
    apply hAQ
    rw [← barSub_eq_bot_iff c.ker (hAT.trans c.TN), eq_bot_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_bot]
    refine cb.eq_one_of_centralizes ⟨a, hAT ha, rfl⟩ fun s hs => ?_
    obtain ⟨t, ht, rfl⟩ := hs
    have hbot : barSub π (barSub ψ (conjSubgroup V (g * (t : G)⁻¹))) = ⊥ := by
      rcases c.bar_eq_bot_or_Es cb hO w hUQ (conj_mul_le_T hAT (inv_mem ht)) with h | h
      · exact h
      · exact h.trans hEs
    exact c.mem_centralizer_conj_of_bar cb hAT ht (hL _ (conj_mul_le_T hAT (inv_mem ht)))
      hbot ha
  ·
    obtain ⟨hEsD, -, hEsel, -, Ks, hKs, hgen⟩ := cb.facts.star hEs
    have hEsC : Es ≤ barSub π (barSub ψ T) ⊓ centralizer (Es : Set B) := by
      refine le_inf hEsD fun x hx => mem_centralizer_iff.mpr fun y hy => ?_
      have := hEsel.1
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Es) ⟨x, hx⟩)
    have hΔ : ∀ K ∈ Ks, ∀ g', conjSubgroup V g' ≤ T →
        conjSubgroup V g' ≤ liftSub ψ (liftSub π K) := by
      intro K hK g' hg'
      obtain ⟨-, -, -, hDK⟩ := hKs K hK
      have hN1 := bar_le_tcN1 (barSub_mono hg') (hL g' hg')
      have hK' : barSub π (barSub ψ (conjSubgroup V g')) ≤ K := by
        rcases c.bar_eq_bot_or_Es cb hO w hUQ hg' with h | h
        · rw [h]
          exact bot_le
        · rw [h]
          exact hEsC.trans hDK
      exact (barSub_le_iff (hg'.trans c.TN)).1 ((barSub_le_iff hN1).1 hK')
    apply h2
    refine c.le_of_closing cb hgen (Subgroup.le_normalizer.trans
      (E3.normalizer_le_normalizer_wClos T)) fun K hK => ?_
    obtain ⟨Y, hY, -, -⟩ := hKs K hK
    obtain ⟨Yb, hirr, -, -⟩ := cb.lift_twoPTwoIrred hY
    refine le_normalizer_wClos_T (c.le_normalizer_wClos w hirr (Or.inl rfl) (Or.inl hUQ)) ?_
    rw [wClos_zero_eq_iSup c.elem]
    exact iSup₂_le fun g' hg' => hΔ K hK g' hg'

end Ctx

end CFSG.LocalAnalysis.WeakClosure81.TC914
