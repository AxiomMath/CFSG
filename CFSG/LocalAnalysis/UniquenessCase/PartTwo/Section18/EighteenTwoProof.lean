module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.Quasithin.MS93.S38ESecMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.WeakClosure81.InFSqQuasisimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Fix
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eighteen_one_five_mem_centralizer (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hsmall : mSub V₀ ≤ 1) {i : ℕ} {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G}
    (hAg : A ≤ CFSG.Quasithin.conjSubgroup V g)
    (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) (hm : MBarGT D.M V₀ V (i + 1)) :
    ∀ v ∈ V, (∀ a ∈ A, ⁅v, a⁆ ∈ V₀) → v ∈ centralizer (A : Set G) := by
  intro v hvV hvA
  by_cases hg : g ∈ D.M
  · exact (twentyThree_one_of_inf D h hA hAg hi (fun hg' => absurd hg hg')).2.1 v hvV hvA
  by_cases hinf : V₀ ⊓ conjSubgroup V g = ⊥
  · exact (twentyThree_one_of_inf D h hA hAg hi (fun _ => hinf)).2.1 v hvV hvA
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    exact hinf (by rw [hbot]; simp)
  by_contra hvnot
  rw [Subgroup.mem_centralizer_iff] at hvnot
  push Not at hvnot
  obtain ⟨a, haA, hav⟩ := hvnot
  have hz0 : ⁅v, a⁆ ∈ V₀ := hvA a haA
  have hz1 : ⁅v, a⁆ ≠ 1 := by
    intro h
    exact hav (commutatorElement_eq_one_iff_mul_comm.1 h).symm
  have hmemA : A ≤ conjSubgroup V g ⊓ D.M := le_inf hAg hA.1
  have hmQ : E3.mQuot (conjSubgroup V g) A = i := mQuot_eq_of_mem_gammaSet hA hAg
  have hr : ((E3.mQuot (conjSubgroup V g) A + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    rw [hmQ]
    exact hi
  have hvpre : v ∈ preCTilde V₀ V A hV :=
    (mem_preCTilde_iff hV (h62.le_stabTil hmemA) hvV).2 hvA
  let w : G := g * v * g⁻¹
  have hwM : w ∈ D.M := by
    change g * v * g⁻¹ ∈ D.M
    exact mem_conjSubgroup_iff.1 (six_two_one h62 hmemA hr hvpre)
  have hvv : v * v = 1 := by simpa [pow_two] using hV.2 v hvV
  have hww : w * w = 1 := by
    change (g * v * g⁻¹) * (g * v * g⁻¹) = 1
    rw [show (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, hvv]
    group
  have hwwmod : CentralizesMod V₀ V (w * w) := by
    rw [hww]
    intro x hx
    simp
  have hnotcent : ¬ CentralizesMod V₀ V w := by
    intro hc
    have hxV : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 (hAg haA)
    have hmem : g * ⁅v, a⁆ * g⁻¹ ∈ V₀ := by
      have h := hc (g * a * g⁻¹) hxV
      rwa [show w * (g * a * g⁻¹) * w⁻¹ * (g * a * g⁻¹)⁻¹ = g * ⁅v, a⁆ * g⁻¹ by
        change (g * v * g⁻¹) * (g * a * g⁻¹) * (g * v * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ = _
        rw [commutatorElement_def]
        group] at h
    rcases h.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd (by rw [hbot]; simp) hinf
    · have hTI := h0.2.2.2.1
      have hN0 : Subgroup.normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D h0.1
      have hinter : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ ≠ ⊥ := by
        intro hbot
        have hmem' : g * ⁅v, a⁆ * g⁻¹ ∈
            V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ := by
          refine ⟨hmem, ?_⟩
          exact (CFSG.CGT.Timmesfeld75.mem_conjSubgroup).2 (by simpa [mul_assoc] using hz0)
        rw [hbot, Subgroup.mem_bot] at hmem'
        exact hz1 (by
          have := congrArg (fun t => g⁻¹ * t * g) hmem'
          simpa [mul_assoc] using this)
      have heq : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ = V₀ :=
        (hTI g).resolve_left hinter
      have hle : V₀ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ :=
        (le_of_eq heq.symm).trans inf_le_right
      have hcardC : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup g V₀) = Nat.card V₀ :=
        CFSG.CGT.Timmesfeld75.card_conjSubgroup g V₀
      have heqC : V₀ = CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardC)
      have hgN : g ∈ Subgroup.normalizer (V₀ : Set G) :=
        CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq.2 heqC.symm
      exact hg (hN0 ▸ hgN)
  set C : Subgroup G := A ⊓ Subgroup.centralizer ({v} : Set G) with hCdef
  have hCA : C ≤ A := inf_le_left
  have hcardC_le : Nat.card C ≤ Nat.card (centMod V₀ V w) := by
    let f : ↥C → ↥(centMod V₀ V w) := fun c =>
      ⟨g * (c : G) * g⁻¹, by
        have hcC : (c : G) ∈ A ⊓ Subgroup.centralizer ({v} : Set G) := c.2
        obtain ⟨hcA, hcent⟩ := Subgroup.mem_inf.1 hcC
        refine ⟨mem_conjSubgroup_iff.1 (hAg hcA), ?_⟩
        have hcomm : v * (c : G) = (c : G) * v :=
          Subgroup.mem_centralizer_iff.1 hcent v rfl
        have hone : w * (g * (c : G) * g⁻¹) * w⁻¹ * (g * (c : G) * g⁻¹)⁻¹ = 1 := by
          change (g * v * g⁻¹) * (g * (c : G) * g⁻¹) * (g * v * g⁻¹)⁻¹ *
            (g * (c : G) * g⁻¹)⁻¹ = 1
          rw [show (g * v * g⁻¹) * (g * (c : G) * g⁻¹) * (g * v * g⁻¹)⁻¹ *
              (g * (c : G) * g⁻¹)⁻¹ =
              g * (v * (c : G) * v⁻¹ * (c : G)⁻¹) * g⁻¹ by group]
          rw [show v * (c : G) * v⁻¹ * (c : G)⁻¹ = 1 by rw [hcomm]; group]
          group
        rw [hone]
        exact V₀.one_mem⟩
    refine Nat.card_le_card_of_injective f fun c₁ c₂ h => ?_
    have h1 : g * (c₁ : G) * g⁻¹ = g * (c₂ : G) * g⁻¹ := congrArg Subtype.val h
    have h2 : (c₁ : G) = (c₂ : G) := by
      have h3 := congrArg (fun t => g⁻¹ * t * g) h1
      simpa [mul_assoc] using h3
    exact Subtype.ext h2
  have hcardV0 : Nat.card V₀ = 2 := by
    have h1 : mSub V₀ = 1 := le_antisymm hsmall (one_le_mSub_of_ne_bot hP.elemAbelian₀ hV0ne)
    rw [card_eq_two_pow_mSub hP.elemAbelian₀.isPGroup, h1]
    norm_num
  obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥V₀)).1 hcardV0
  have hfixV₀ : ∀ a ∈ A, ∀ y ∈ V₀, (a : G) * y * (a : G)⁻¹ = y := by
    intro a ha y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      group
    · have haN : (a : G) ∈ Subgroup.normalizer (V₀ : Set G) := hP.le_normalizer₀ (hA.1 ha)
      have hy' : (a : G) * y * (a : G)⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.1 haN y).1 hy
      have hy'1 : (a : G) * y * (a : G)⁻¹ ≠ 1 := by
        intro h
        apply hy1
        have h3 := congrArg (fun t => (a : G)⁻¹ * t * (a : G)) h
        have h2 : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * (a : G) = y := by group
        rw [h2] at h3
        simpa using h3
      have e1 : (⟨(a : G) * y * (a : G)⁻¹, hy'⟩ : ↥V₀) = z :=
        huniq _ (fun h => hy'1 (congrArg (fun t : ↥V₀ => (t : G)) h))
      have e2 : (⟨y, hy⟩ : ↥V₀) = z :=
        huniq _ (fun h => hy1 (congrArg (fun t : ↥V₀ => (t : G)) h))
      exact congrArg (fun t : ↥V₀ => (t : G)) (e1.trans e2.symm)
  let φ : ↥A →* ↥V₀ :=
    { toFun := fun a => ⟨⁅v, (a : G)⁆, hvA (a : G) a.2⟩
      map_one' := Subtype.ext (by simp [commutatorElement_def])
      map_mul' := fun a b => Subtype.ext (by
        show ⁅v, ((a : G) * (b : G))⁆ = ⁅v, (a : G)⁆ * ⁅v, (b : G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        rw [show ⁅v, (a : G)⁆ * (a : G) * ⁅v, (b : G)⁆ * (a : G)⁻¹ =
          ⁅v, (a : G)⁆ * ((a : G) * ⁅v, (b : G)⁆ * (a : G)⁻¹) by group]
        rw [hfixV₀ (a : G) a.2 _ (hvA (b : G) b.2)]) }
  have hker : φ.ker = C.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : ((φ a : ↥V₀) : G) = 1 := by
        rw [h]
        rfl
      change ⁅v, (a : G)⁆ = 1 at h1
      refine ⟨a.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · rintro ⟨-, hcent⟩
      have h1 : v * (a : G) = (a : G) * v := Subgroup.mem_centralizer_iff.1 hcent v rfl
      refine Subtype.ext ?_
      change ⁅v, (a : G)⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.2 h1
  have hidx : C.relIndex A ≤ 2 := by
    have hrel : C.relIndex A = (C.subgroupOf A).index := by
      have h := Subgroup.relIndex_subgroupOf (H := C) (K := A) (L := A) le_rfl
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
      exact h.symm
    rw [hrel, ← hker, Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card ↥V₀ := by
          simpa using Subgroup.card_le_of_le (le_top : φ.range ≤ ⊤)
      _ = 2 := hcardV0
  have hmul : C.relIndex A * Nat.card C = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := A)
    rwa [inf_eq_left.mpr hCA] at h
  have hcardA : Nat.card A ≤ 2 * Nat.card C := by
    calc Nat.card A = C.relIndex A * Nat.card C := hmul.symm
      _ ≤ 2 * Nat.card C := Nat.mul_le_mul_right _ hidx
  have hVgP : IsPGroup 2 (conjSubgroup V g) :=
    hV.isPGroup.map (MulAut.conj g⁻¹).toMonoidHom
  have hVgcard : Nat.card (conjSubgroup V g) = 2 ^ i * Nat.card A := by
    have h := E3.card_eq_two_pow_mul hVgP hAg
    rwa [hmQ] at h
  have hVle : Nat.card V ≤ 2 ^ (i + 1) * Nat.card C := by
    calc Nat.card V = Nat.card (conjSubgroup V g) := (E3.card_conjSubgroup V g).symm
      _ = 2 ^ i * Nat.card A := hVgcard
      _ ≤ 2 ^ i * (2 * Nat.card C) := Nat.mul_le_mul_left _ hcardA
      _ = 2 ^ (i + 1) * Nat.card C := by rw [pow_succ]; ring
  have hGT := hm.1 w hwM hnotcent hwwmod
  have hdouble : 2 * Nat.card V ≤ Nat.card V := by
    calc 2 * Nat.card V ≤ 2 * (2 ^ (i + 1) * Nat.card C) := Nat.mul_le_mul_left 2 hVle
      _ = 2 ^ (i + 1 + 1) * Nat.card C := by rw [pow_succ']; ring
      _ ≤ 2 ^ (i + 1 + 1) * Nat.card (centMod V₀ V w) := Nat.mul_le_mul_left _ hcardC_le
      _ ≤ Nat.card V := hGT
  have hpos : 0 < Nat.card V := Nat.card_pos
  omega

theorem exists_mem_cClos_not_mem_V₀ (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hsmall : mSub V₀ ≤ 1) (hV₀ : V₀ ≠ ⊥) {n : ℕ}
    (hr : ((n + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) (hm : MBarGT D.M V₀ V (n + 1)) :
    ∃ v ∈ V, v ∉ V₀ ∧ v ∈ E3.cClos V n D.T := by
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hcardV0 : Nat.card V₀ = 2 := by
    have h1 : mSub V₀ = 1 := le_antisymm hsmall (one_le_mSub_of_ne_bot hP.elemAbelian₀ hV₀)
    rw [card_eq_two_pow_mSub hP.elemAbelian₀.isPGroup, h1]
    norm_num
  have hnt : Nontrivial (Vtil V₀ V hV) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hc := card_Vtil_eq V₀ V hV hP.le
    rw [hcardV0] at hc
    have hV4 : 4 ≤ Nat.card V := four_le_card_V_of_hyp125 D h
    omega
  have hTbar2 : IsPGroup 2 ↥(barSub V₀ V hV D.T) :=
    s15_LP_isPGroup_barSub hV D.sylowM.isPGroup
  have hfix : fixV (barSub V₀ V hV D.T) ≠ ⊥ :=
    @CFSG.Quasithin.MS93.S38E.fixV_ne_bot_of_isPGroup (Vtil V₀ V hV) _ _ hnt
      (s15_Infra_vtil_sq_eq_one V₀ V hV) (barSub V₀ V hV D.T) hTbar2
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hfix
  obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV (y : Vtil V₀ V hV)
  let v : G := x.val
  have hvV : v ∈ V := x.val_mem
  have hvpre : v ∈ preCTilde V₀ V D.T hV := by
    rw [preCTilde]
    exact (mem_preTil V₀ V hV _).2 ⟨x, rfl, by rw [hx]; exact y.2⟩
  have hv0 : v ∉ V₀ := by
    intro hv0
    apply hy1
    have h1 : mkTil V₀ V hV x = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 (by
        change x.val ∈ V₀
        exact hv0)
    rw [hx] at h1
    exact Subtype.ext h1
  have hDT : D.T ≤ stabTil V₀ V :=
    le_inf (D.sylowM.le.trans (le_of_eq h.normalizer_eq.symm))
      (D.sylowM.le.trans hP.le_normalizer₀)
  have hvT : ∀ t ∈ D.T, ⁅v, t⁆ ∈ V₀ := fun t ht =>
    (mem_preCTilde_iff hV hDT hvV).1 hvpre t ht
  have hwclos : E3.wClos V n D.T ≤ Subgroup.centralizer ({v} : Set G) := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hmQ⟩ := hA
    have hAM : A ≤ D.M := hAT.trans D.sylowM.le
    have hAgamma : A ∈ E3.gammaSet V n D.M := ⟨hAM, g, hAg, hmQ⟩
    have hvA : ∀ a ∈ A, ⁅v, a⁆ ∈ V₀ := fun a ha => hvT a (hAT ha)
    have hcent :=
      eighteen_one_five_mem_centralizer D h hsmall (i := n) hAgamma hAg hr hm v hvV hvA
    intro a ha
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.1 hcent a ha).symm
  refine ⟨v, hvV, hv0, ?_⟩
  refine ⟨s15_13A_le_T (D := D) h hvV, ?_⟩
  exact Subgroup.mem_centralizer_iff.2 fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (hwclos hx) v rfl).symm

theorem eighteen_two_of_calO_one
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (h126 : R126 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L) : (V₀ ≠ ⊥ → calO 1 D.M V₀ V = ∅) → R18_2At D V₀ V p L h := by
  intro hO1 hV₀ j Δ h12 hXT hO2 hcl
  classical
  have hV := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hmSub : mSub V₀ = 1 := mSub_eq_one h hV₀
  by_cases htop : fIndexMax Δ = ⊤
  · rw [htop, top_add]
    exact le_top
  set n : ℕ := (fIndexMax Δ).toNat with hn
  have hneq : fIndexMax Δ = (n : ℕ∞) := (ENat.coe_toNat htop).symm
  have hF : ∀ H ∈ Δ, InFSq n H := fIndexMax_le_iff.1 hneq.le
  rw [hneq]
  by_contra hle
  have hlt : n + 1 < mBar D.M V₀ V hV := by
    have h1 : ((n + 1 : ℕ) : ℕ∞) < (mBar D.M V₀ V hV : ℕ∞) := by
      push_cast
      exact not_le.1 hle
    exact_mod_cast h1
  have hXTn : ¬ InFSq 0 (UC22.conjClosure D.M L ⊔ D.T) :=
    not_inFSq_zero_of_isQuasisimple_bar2 (X := L)
      ((TwelveTwentyThree.le_conjClosure D.M L).trans le_sup_left) h.hL.1.2.2
  have hnpos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (h0 ▸ hF _ hXT) hXTn
    · exact h0
  have hm3 : 3 ≤ mBar D.M V₀ V hV := by omega
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have h11 : (mBar D.M V₀ V hV : ℕ∞) < rMV D.M V :=
    lt_rMV_of_hyp125 D hx h61 h127 h1114 h162 h.hyp125 hV₀
  have hconcl := concl18_1_2_of_calO_one D hx h61 h127 h1114 h162 h hV₀ (hO1 hV₀)
  have hno : ∀ k, k < mBar D.M V₀ V hV → ∀ g : G, ¬ InCalO1 k D.M V₀ V g := by
    intro k hk g hg
    have hmem : conjSubgroup V g ∈ calO k D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [hconcl k hk] at hmem
    exact hmem
  have hkm : D.k < mBar D.M V₀ V hV := by omega
  have hkr : ((0 + D.k : ℕ) : ℕ∞) < rMV D.M V := by
    have h1 : ((D.k : ℕ) : ℕ∞) < (mBar D.M V₀ V hV : ℕ∞) := by exact_mod_cast hkm
    simpa using h1.trans h11
  have hN : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    not_normalizer_wClos_le_of_no_calO1 D hx h61 h127 h1114 h126 h.hyp125 hV₀
      hkr (by simpa using hkm) (hno _ (by simpa using hkm))
  have hmGT : MBarGT D.M V₀ V (n + 1) := (h.hyp125.mBarGT_iff_lt_mBar (n + 1)).2 hlt
  have hr : ((n + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    rw [hmSub]
    have h1 : ((n + 1 : ℕ) : ℕ∞) < (mBar D.M V₀ V hV : ℕ∞) := by exact_mod_cast hlt
    exact h1.trans h11
  obtain ⟨v, hvV, hv0, hvc⟩ :=
    exists_mem_cClos_not_mem_V₀ D h.hyp125 h.small hV₀ (n := n) hr hmGT
  have hH6 : Hyp6H D.M V₀ V :=
    (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp125 hV₀).hyp6H
  have key : ∀ H ∈ Δ, H ≤ normalizer (E3.wClos V 0 D.T : Set G) ∨
      ⁅E3.cClos V n D.T, twoResidual H⁆ = ⊥ := by
    intro H hHΔ
    refine TwelveEighteen.twelve_eighteen_three_of_no_calO1 hH6 hV₀ (i := 0) (n := n) (k := n)
      (by omega) ?_ (by omega) (hno n (by omega))
      (TwelveShort.isSylowIn_of_le D (h12.delta_T H hHΔ)) (hF H hHΔ)
    have h1 : ((n : ℕ) : ℕ∞) < (mBar D.M V₀ V hV : ℕ∞) := by
      exact_mod_cast (by omega : n < mBar D.M V₀ V hV)
    exact h1.trans h11
  have hbarT : ∀ H ∈ Δ, ⁅E3.cClos V n D.T, twoResidual H⁆ = ⊥ →
      barSub V₀ V hV H = barSub V₀ V hV D.T := by
    intro H hHΔ hHC
    have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (h12.delta_T H hHΔ)
    have hHM : H ≤ D.M := h12.delta_le H hHΔ
    have hSM : twoResidual H ≤ D.M := (twoResidual_le H).trans hHM
    have hsup : D.T ⊔ twoResidual H = H :=
      sup_twoResidual_eq ⟨hTH.le, hTH.isPGroup, hTH.not_dvd_relIndex⟩
    have hMstab : D.M ≤ stabTil V₀ V :=
      le_stabTil hP.le_normalizer hP.le_normalizer₀
    have hstabS : twoResidual H ≤ stabTil V₀ V := hSM.trans hMstab
    have hstabT : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMstab
    have hfixne : fixV (barSub V₀ V hV (twoResidual H)) ≠ ⊥ := by
      intro hbot
      have hvpre : v ∈ preCTilde V₀ V (twoResidual H) hV := by
        rw [mem_preCTilde_iff hV hstabS hvV]
        intro d hd
        have hcent : E3.cClos V n D.T ≤ centralizer (twoResidual H : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 hHC
        have hcomm : d * v = v * d :=
          Subgroup.mem_centralizer_iff.1 (hcent hvc) d hd
        have h1 : ⁅v, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm
        rw [h1]
        exact V₀.one_mem
      have hvpre' : v ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (twoResidual H))) := hvpre
      rw [hbot, preTil_bot, inf_eq_right.mpr hP.le] at hvpre'
      exact hv0 hvpre'
    have hO2H : ((S17.oUpperTwo H).subgroupOf D.M).Normal := hO2 H hHΔ
    have hO2H' : ((twoResidual H).subgroupOf D.M).Normal := by
      rwa [oUpperTwo_eq_twoResidual] at hO2H
    have hMN : D.M ≤ normalizer (twoResidual H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).1 hO2H'
    have hconj : ConjGenerated D.M V₀ V :=
      (TwelveTwentyThree.ne_and_conjGenerated_of_hyp125 h.hyp125 hV₀).2
    have hfix : fixV (barSub V₀ V hV (twoResidual H)) = ⊤ := by
      have hnormal : ((barSub V₀ V hV (twoResidual H)).subgroupOf
          (Mbar D.M V₀ V hV)).Normal :=
        barSub_subgroupOf_mbar_normal hV hSM hMN
      have hstable : StableUnder (Mbar D.M V₀ V hV)
          (fixV (barSub V₀ V hV (twoResidual H))) := by
        refine stableUnder_fixV (fun y hy h hh => ?_)
        have hle : barSub V₀ V hV (twoResidual H) ≤ Mbar D.M V₀ V hV :=
          barSub_mono V₀ V hV hSM
        have hhmem : (⟨h, hle hh⟩ : Mbar D.M V₀ V hV) ∈
            (barSub V₀ V hV (twoResidual H)).subgroupOf (Mbar D.M V₀ V hV) :=
          Subgroup.mem_subgroupOf.2 hh
        have h1 := hnormal.conj_mem (⟨h, hle hh⟩ : Mbar D.M V₀ V hV) hhmem
          (⟨y, hy⟩ : Mbar D.M V₀ V hV)
        simpa using Subgroup.mem_subgroupOf.1 h1
      rcases eq_bot_or_eq_top_of_stable hV hP.le_normalizer hP.le_normalizer₀ hconj
        hstable with hbot | htop
      · exact absurd hbot hfixne
      · exact htop
    have hSbot : barSub V₀ V hV (twoResidual H) = ⊥ := by
      by_contra hne
      exact fixV_ne_top hne hfix
    calc barSub V₀ V hV H = barSub V₀ V hV (D.T ⊔ twoResidual H) := by
          conv_lhs => rw [← hsup]
      _ = barSub V₀ V hV D.T ⊔ barSub V₀ V hV (twoResidual H) :=
        s16c7_barSub_sup V₀ V hV hstabT hstabS
      _ = barSub V₀ V hV D.T := by rw [hSbot, sup_bot_eq]
  set K : Subgroup G := (⨆ H ∈ Δ, H) ⊓ normalizer (E3.wClos V 0 D.T : Set G) with hK
  have hTK : D.T ≤ K := by
    refine le_inf ?_ ?_
    · exact le_trans le_sup_right
        (le_iSup₂_of_le (f := fun H (_ : H ∈ Δ) => H) _ hXT le_rfl)
    · exact Subgroup.le_normalizer.trans
        (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) D.T)
  have hKA : K ≤ ⨆ H ∈ Δ, H := inf_le_left
  have hKN : K ≤ normalizer (E3.wClos V 0 D.T : Set G) := inf_le_right
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hbarA : barSub V₀ V hV (⨆ H ∈ Δ, H) = ⨆ H ∈ Δ, barSub V₀ V hV H := by
    calc barSub V₀ V hV (⨆ H ∈ Δ, H) =
        barSub V₀ V hV (⨆ H : Δ, (H : Subgroup G)) := by rw [iSup_subtype']
      _ = ⨆ H : Δ, barSub V₀ V hV (H : Subgroup G) :=
        barSub_iSup_of_le hV (K := fun H : Δ => (H : Subgroup G))
          (fun H => (h12.delta_le H H.2).trans hMstab)
      _ = ⨆ H ∈ Δ, barSub V₀ V hV H := by rw [iSup_subtype']
  have hKbar : barSub V₀ V hV K = ⨆ H ∈ Δ, barSub V₀ V hV H := by
    rw [hK]
    refine le_antisymm ((barSub_mono V₀ V hV inf_le_left).trans_eq hbarA) ?_
    refine iSup₂_le fun H hHΔ => ?_
    rcases key H hHΔ with hHN | hHC
    · have hHK : H ≤ K := le_inf (le_iSup₂_of_le H hHΔ le_rfl) hHN
      exact barSub_mono V₀ V hV hHK
    · rw [hbarT H hHΔ hHC]
      exact barSub_mono V₀ V hV hTK
  have hcalM : calMOf K = {D.M} := hcl K hTK hKA hKbar
  have hloc : IsTwoLocal (normalizer (E3.wClos V 0 D.T : Set G)) := by
    refine ⟨E3.wClos V 0 D.T, ?_, ?_, rfl⟩
    · exact E3.wClos_ne_bot hV (TwelveTwentyTwo.le_T_of_hyp125 h.hyp125)
        (lt_of_lt_of_le Nat.zero_lt_one
          (show 1 ≤ rk ↥V from one_le_mSub_of_ne_bot hV hP.ne_bot))
    · exact (TwelveTwentyTwo.isPGroup_T D).to_le (E3.wClos_le 0 D.T)
  exact hN (uc22p22p_le_of_uniqueMax hcalM hloc hKN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
