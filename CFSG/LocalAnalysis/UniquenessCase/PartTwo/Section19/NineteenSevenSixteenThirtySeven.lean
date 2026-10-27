module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37Cnt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Conj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_seven_le_of_forall_centralizer_le {M V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hP : PairFacts M V₀ V) (S : OmegaModel (Vtil V₀ V hV))
    (hN : Mbar M V₀ V hV ≤ normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))))
    {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) {n : ℕ} (hn : n < 2 * m) {X : Subgroup G}
    (hXM : X ≤ M) (hX : IsElemAbelian 2 X) (hXcard : 2 * Nat.card ↥V₀ < Nat.card ↥X)
    (hXn : ∀ x ∈ X, E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ n)
    {N : Subgroup G} (hNc : ∀ x ∈ X, x ≠ 1 → centralizer ({x} : Set G) ≤ N) :
    V ≤ N := by
  classical
  have hMst : M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hXst : X ≤ stabTil V₀ V := hXM.trans hMst
  have hbarN : barSub V₀ V hV X ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hXM).trans hN
  have hord : ∀ g ∈ barSub V₀ V hV X, g * g = 1 := by
    intro g hg
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X g).1 hg
    rw [← map_mul]
    have hx2 : x * x = 1 := Subtype.ext (by
      have := hX.2 (x : G) hxX
      simpa [pow_two] using this)
    rw [hx2, map_one]
  have hfix : ∀ g ∈ barSub V₀ V hV X, g ≠ 1 →
      Nat.card S.K ^ 2 < Nat.card {v : Vtil V₀ V hV // g v = v} := by
    intro g hg _
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X g).1 hg
    exact card_fixed_gt_of_mQuot_le hP.le S hSK hn x.2 (hXn (x : G) hxX)
  have hbar2 : Nat.card ↥(barSub V₀ V hV X) ≤ 2 :=
    S.card_le_two_of_card_fixed_gt (barSub V₀ V hV X) hbarN hord hfix
  have hiso := s16c7_card_mul_card_preBarSub (V₀ := V₀) (V := V) (E := X) hV hXst
    (Q := ⊥) bot_le
  rw [Subgroup.card_bot, mul_one] at hiso
  have hCcard : Nat.card ↥V₀ < Nat.card ↥(preBarSub X V₀ V hV ⊥) := by
    have h1 : Nat.card ↥(preBarSub X V₀ V hV ⊥) * Nat.card ↥(barSub V₀ V hV X) ≤
        Nat.card ↥(preBarSub X V₀ V hV ⊥) * 2 := Nat.mul_le_mul_left _ hbar2
    omega
  intro v hv
  have hCN : ∀ c ∈ preBarSub X V₀ V hV ⊥, c * v * c⁻¹ * v⁻¹ ∈ V₀ := by
    intro c hc
    obtain ⟨-, hcs, hc'⟩ := (mem_preBarSub X V₀ V hV ⊥).1 hc
    have h1 : actTil V₀ V hV ⟨c, hcs⟩ = 1 := Subgroup.mem_bot.1 hc'
    exact (actTil_eq_one_iff V₀ V hV ⟨c, hcs⟩).1 h1 v hv
  obtain ⟨c, hcC, hc1, hcv⟩ := exists_ne_one_commute_of_card_lt hCN hCcard
  obtain ⟨hcX, -⟩ := (mem_preBarSub X V₀ V hV ⊥).1 hcC
  exact hNc c hcX hc1 (Subgroup.mem_centralizer_singleton_iff.2 hcv.symm)

theorem nineteen_seven_conjSubgroup_le_of_E {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hP : PairFacts M V₀ V) (S : OmegaModel (Vtil V₀ V hV))
    (hN : Mbar M V₀ V hV ≤ normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))))
    {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) (hm2 : 2 ≤ m) {n : ℕ} (hn : n < 2 * m) {g : G}
    (hU : E3.mQuot V (conjSubgroup M g⁻¹) ≤ n) {E : Subgroup G} (hEV : E ≤ V)
    (hEM : E ≤ conjSubgroup M g)
    (hEB : E ≤ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G))
    (hEcard : Nat.card ↥E = Nat.card ↥V₀ * Nat.card S.K)
    (hEc : ∀ x ∈ E, x ≠ 1 → centralizer ({x} : Set G) ≤ M) :
    conjSubgroup V g ≤ M := by
  classical
  let U : Subgroup G := V ⊓ conjSubgroup M g⁻¹
  have hXM : conjSubgroup E g⁻¹ ≤ M := by
    have h := E3.conjSubgroup_mono_left g⁻¹ hEM
    rwa [E3.conjSubgroup_conj_inv] at h
  have hX : IsElemAbelian 2 (conjSubgroup E g⁻¹) :=
    E3.isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono hEV hV) g⁻¹
  have hXcard : 2 * Nat.card ↥V₀ < Nat.card ↥(conjSubgroup E g⁻¹) := by
    rw [E3.card_conjSubgroup E g⁻¹, hEcard, hSK]
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hpos : 0 < Nat.card ↥V₀ := Nat.card_pos
    calc 2 * Nat.card ↥V₀ < 4 * Nat.card ↥V₀ := by omega
      _ = Nat.card ↥V₀ * 4 := by rw [Nat.mul_comm]
      _ ≤ Nat.card ↥V₀ * 2 ^ m := Nat.mul_le_mul_left _ h4
  have hU_eq : conjSubgroup U g = conjSubgroup V g ⊓ M := by
    dsimp only [U]
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj]
  have hXcenU : conjSubgroup E g⁻¹ ≤ centralizer (U : Set G) := by
    have hEcU : E ≤ centralizer (conjSubgroup U g : Set G) := by
      rw [hU_eq]
      exact hEB
    have h := E3.conjSubgroup_mono_left g⁻¹ hEcU
    rwa [E3.conjSubgroup_centralizer, E3.conjSubgroup_conj_inv] at h
  have hXn : ∀ x ∈ conjSubgroup E g⁻¹,
      E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ n := by
    intro x hx
    have hxcen : x ∈ centralizer (U : Set G) := hXcenU hx
    have hUle : U ≤ V ⊓ centralizer ({x} : Set G) := by
      intro u hu
      dsimp only [U] at hu
      exact ⟨(Subgroup.mem_inf.1 hu).1,
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxcen u hu)⟩
    have hUeq : E3.mQuot V U = E3.mQuot V (conjSubgroup M g⁻¹) := by
      unfold E3.mQuot
      dsimp only [U]
      rw [inf_comm, Subgroup.inf_relIndex_right]
    calc E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ E3.mQuot V U := E3.mQuot_mono hUle
      _ = E3.mQuot V (conjSubgroup M g⁻¹) := hUeq
      _ ≤ n := hU
  have hNc : ∀ x' ∈ conjSubgroup E g⁻¹, x' ≠ 1 →
      centralizer ({x'} : Set G) ≤ conjSubgroup M g⁻¹ := by
    intro x' hx' hx'1 z hz
    have hxE : g⁻¹ * x' * g ∈ E := E3.mem_conjSubgroup_inv_iff.1 hx'
    have hx1 : g⁻¹ * x' * g ≠ 1 := by
      intro h
      apply hx'1
      calc x' = g * (g⁻¹ * x' * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h]
        _ = 1 := by group
    have hzcomm : z * x' = x' * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    have hmem : g⁻¹ * z * g ∈ centralizer ({g⁻¹ * x' * g} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g⁻¹ * z * g) * (g⁻¹ * x' * g)
          = g⁻¹ * (z * x') * g := by group
        _ = g⁻¹ * (x' * z) * g := by rw [hzcomm]
        _ = (g⁻¹ * x' * g) * (g⁻¹ * z * g) := by group
    exact E3.mem_conjSubgroup_inv_iff.2 (hEc (g⁻¹ * x' * g) hxE hx1 hmem)
  have hVle : V ≤ conjSubgroup M g⁻¹ :=
    nineteen_seven_le_of_forall_centralizer_le (X := conjSubgroup E g⁻¹)
      (N := conjSubgroup M g⁻¹) hP S hN hSK hn hXM hX hXcard hXn hNc
  rw [← E3.conjSubgroup_inv_conj M g]
  exact (E3.conjSubgroup_le_conjSubgroup_iff (A := V)
    (B := conjSubgroup M g⁻¹) g).2 hVle

theorem nineteen_seven_exists_subgroup_of_line {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hP : PairFacts M V₀ V) (S : OmegaModel (Vtil V₀ V hV))
    (hc₀ : ∀ x ∈ V₀, x ≠ 1 → centralizer ({x} : Set G) ≤ M)
    (hcQ : ∀ x : IntMod V hV, S.Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ M)
    {B : Subgroup G} (hBst : B ≤ stabTil V₀ V)
    (hcB : ∀ v ∈ V, (∀ a ∈ B, ⁅v, a⁆ ∈ V₀) → v ∈ centralizer (B : Set G))
    {e : Vtil V₀ V hV} (hQ : S.Q e ≠ 0)
    (hfix : ∀ φ ∈ barSub V₀ V hV B, ∀ c : S.K, φ (S.smul c e) = S.smul c e) :
    ∃ E : Subgroup G, E ≤ V ∧ E ≤ centralizer (B : Set G) ∧
      Nat.card ↥E = Nat.card ↥V₀ * Nat.card S.K ∧
      ∀ x ∈ E, x ≠ 1 → centralizer ({x} : Set G) ≤ M := by
  have he1 : e ≠ 1 := fun h => hQ (by rw [h, S.Q_one])
  refine ⟨preTil V₀ V hV (S.line e), preTil_le V₀ V hV _, ?_, ?_, ?_⟩
  · intro x hx
    have hxV : x ∈ V := preTil_le V₀ V hV _ hx
    have hxl : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ S.line e :=
      (mem_preTil_iff_of_mem V₀ V hV _ hxV).1 hx
    obtain ⟨c, hc⟩ := hxl
    refine hcB x hxV (commutator_mem_V₀_of_fixes hBst
      (q := mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩)) (fun φ hφ => ?_) hxV rfl)
    rw [hc]
    exact hfix φ hφ c
  · rw [card_preTil hV hP.le, S.card_line he1]
  · intro x hx hx1
    have hxV : x ∈ V := preTil_le V₀ V hV _ hx
    by_cases hx0 : x ∈ V₀
    · exact hc₀ x hx0 hx1
    · have hxline : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ S.line e :=
        (mem_preTil_iff_of_mem V₀ V hV _ hxV).1 hx
      have hxi1 : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ≠ 1 := fun h =>
        hx0 ((mem_modNull V₀ V hV _).1
          ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h))
      exact hcQ (IntMod.mk hV ⟨x, hxV⟩) (S.Q_ne_zero_of_mem_line hQ hxline hxi1)

theorem nineteen_seven_false_of_inCalO2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h3 : R19_3At D V₀ V p L K hS.ctx) (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) {g : G} (hg : InCalO2 2 D.M V₀ V g)
    (hcase : ¬ OneFirst D.M V₀ V g) : False := by
  classical
  have hP : PairFacts D.M V₀ V := hS.ctx.hyp.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [hSK]; norm_num
  obtain ⟨b, hbB, hbC, hbn⟩ := exists_b_of_inCalO2 hV2 hg (Or.inr hcase)
  have hbM : b ∈ D.M := (Subgroup.mem_inf.1 hbB).2
  have hbs : b ∈ stabTil V₀ V := hMst hbM
  have hb1 : actTil V₀ V hV ⟨b, hbs⟩ ≠ 1 := fun h1 =>
    hbC ((mem_cTilde_iff hV hP.le_normalizer).2 ⟨hbM, hbs, h1⟩)
  set B : Subgroup G := conjSubgroup V g ⊓ D.M with hBdef
  have hi' : E3.mQuot (conjSubgroup V g) B ≤ 2 := by
    have h1 : E3.mQuot (conjSubgroup V g) B = E3.mQuot (conjSubgroup V g) D.M := by
      unfold E3.mQuot
      rw [hBdef, inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    exact hg.1.2.2.1
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) D.M :=
    ⟨inf_le_right, g, inf_le_left, rfl⟩
  have hBst : B ≤ stabTil V₀ V := inf_le_right.trans hMst
  have hbmem : actTil V₀ V hV ⟨b, hbs⟩ ∈ barSub V₀ V hV B := actTil_mem_barSub V₀ V hV hbB hbs
  have hA1 : barSub V₀ V hV B ≠ ⊥ := fun h0 => hb1 (Subgroup.mem_bot.1 (h0 ▸ hbmem))
  have hBcal : barSub V₀ V hV B ∈ calABar 2 D.M V₀ V hV :=
    nineteen_seven_barSub_mem_calABar D hV hS h3 h5 h61 hSg h1219 S hSω hSK
      (i := E3.mQuot (conjSubgroup V g) B) (k := 2) (by omega) hBγ hA1
  have hlt : ((E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have h35 := nineteen_seven_sixteen_thirtyFive D hV hS h5 h61 S hSω hSK
    exact lt_of_lt_of_le (by exact_mod_cast (by omega :
      E3.mQuot (conjSubgroup V g) B + mSub V₀ < 4 + mSub V₀)) h35.2
  obtain ⟨-, hcB, hMg⟩ := S18.twentyThree_one_of_inf D hS.ctx.hyp.hyp125 hBγ
    (inf_le_left : B ≤ conjSubgroup V g) hlt
    (nineteen_seven_inf_conj_eq_bot D hV hS h3 h5 hSg h1219 g)
  have hfixcard := card_fixed_gt_of_mQuot_le hP.le S hSK2 (by norm_num : 2 < 2 * 2) hbs hbn
  obtain ⟨e, hQ, hfixe⟩ := S.exists_fixed_line_of_mem_aSet
    (nineteen_seven_mbar_le_normalizer D hV hS S hSω) hBcal hbmem hb1 hfixcard
  obtain ⟨E, hEV, hEB, hEcard, hEc⟩ :=
    nineteen_seven_exists_subgroup_of_line hP S
      (fun x hx hx1 => centralizer_singleton_le_M_of_mem_V₀' D hS.ctx.hyp.hyp125 hx hx1)
      (fun x hx => nineteen_seven_centralizer_le_of_nonsingular D hV hS h5 h61 S hSω hSK hx)
      hBst hcB hQ hfixe
  have hEM : E ≤ conjSubgroup D.M g := fun x hx => hMg ⟨hEV hx, hEB hx⟩
  have hU : E3.mQuot V (conjSubgroup D.M g⁻¹) ≤ 2 :=
    ((oDual_iff_oFirst_inv 2 D.M V₀ V g).1 hg.1.2).2.1
  exact hg.1.1.1 (nineteen_seven_conjSubgroup_le_of_E hP S
    (nineteen_seven_mbar_le_normalizer D hV hS S hSω) hSK2 (le_refl 2) (by norm_num) hU
    hEV hEM hEB hEcard hEc)

theorem nineteen_seven_calO2_subset_calO1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h3 : R19_3At D V₀ V p L K hS.ctx) (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) :
    calO2 2 D.M V₀ V ⊆ calO1 2 D.M V₀ V := by
  intro X hX
  obtain ⟨g, hXg, hg⟩ := hX
  refine ⟨g, hXg, hg.1, ?_, ?_⟩
  · by_contra hOne
    exact nineteen_seven_false_of_inCalO2 D hV hS h3 h5 h61 hSg h1219 S hSω hSK hg hOne
  · by_contra hDual
    exact nineteen_seven_false_of_inCalO2 D hV hS h3 h5 h61 hSg h1219 S hSω hSK
      (inCalO2_inv hg) (fun h' => hDual ((oneDual_iff_oneFirst_inv D.M V₀ V g).2 h'))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
