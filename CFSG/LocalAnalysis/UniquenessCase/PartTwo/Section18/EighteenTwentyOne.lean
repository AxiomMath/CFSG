module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneKHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenCaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.GammaTwoBarHyp18

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem four_mul_n_add_one_le_of_not_le_normalizer
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hr : ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V)
    {A : Subgroup G} (hA : A ∈ F12.Gam 0 D.T V)
    (hVA : ¬ V ≤ normalizer (A : Set G)) :
    4 * S17.nOf L + 1 ≤
      mSub V₀ + rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  obtain ⟨hAT, U, g, hUV, hcard, hAeq⟩ := hA
  have hcard' : Nat.card V = Nat.card U := by simpa using hcard
  have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (le_of_eq hcard')
  subst U
  have hAc : A = conjSubgroup V g⁻¹ := by
    rw [hAeq, conjSubgroup, inv_inv]
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  set C : Subgroup G := A ⊓ F11.CTilde D.M V₀ V with hCdef
  have hrk : rk ↥(barSub V₀ V hV A) = E3.mQuot A C :=
    CFSG.LocalAnalysis.WeakClosure81.rk_barSub_eq_mQuot_inf_cTilde hV
      h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hAM
  by_contra hlt
  push Not at hlt
  rw [hrk] at hlt
  have h62 := h.hyp125.hyp62
  have hD : C ≤ conjSubgroup V g⁻¹ ⊓ D.M :=
    le_inf (hAc ▸ inf_le_left) (inf_le_left.trans hAM)
  have hrlt : ((E3.mQuot (conjSubgroup V g⁻¹) C + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    rw [← hAc]
    calc ((E3.mQuot A C + mSub V₀ : ℕ) : ℕ∞) < ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) := by
          exact_mod_cast (by omega)
      _ ≤ rMV D.M V := hr
  have hU := CFSG.LocalAnalysis.WeakClosure81.six_two_one h62 hD hrlt
  have hpre : V ≤ CFSG.LocalAnalysis.WeakClosure81.preCTilde V₀ V C hV := by
    intro v hv
    rw [CFSG.LocalAnalysis.WeakClosure81.mem_preCTilde_iff hV (h62.le_stabTil hD) hv]
    intro d hd
    have hdC : CentralizesMod V₀ V d :=
      CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde hV
        h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hd.2
    have h1 : d * v * d⁻¹ * v⁻¹ ∈ V₀ := hdC v hv
    have h2 : ⁅v, d⁆ = (d * v * d⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact V₀.inv_mem h1
  apply hVA
  rw [hAc, ← E3.conjSubgroup_normalizer, h.hyp125.normalizer_eq]
  exact hpre.trans hU



theorem exists_offender_zero_or_two (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) :
    (∃ A ∈ F12.Gam 0 D.T V, barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) ∨
      (E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V ∧
        ∃ A ∈ F12.Gam 2 D.T V, barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  by_cases h0 : ∃ A ∈ F12.Gam 0 D.T V, barSub V₀ V hV A ≠ ⊥
  · exact Or.inl h0
  · right
    push Not at h0
    have hW0 : E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V := by
      refine E3.wClos_le_of_forall fun A hA => ?_
      have hAgam : A ∈ F12.Gam 0 D.T V := by
        rw [S17.gam_eq_gammaSet 0 D.T V hV]
        exact hA
      exact (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV
        h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
        (hAgam.1.trans D.sylowM.le)).1 (h0 A hAgam)
    exact ⟨hW0, exists_gammaTwo_barSub_ne_bot_of_hyp18 D V₀ V p L h hx h61 h126 h66 h127 h1114
      h111 h183 h1669⟩

theorem eq_bot_of_no_gammaZero_offender (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h183 : W3Thm183 G) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hW0 : E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V) (hV₀ : V₀ ≠ ⊥) : False := by
  have hm3 : MBarGT D.M V₀ V 3 :=
    h1669 (by
      have h2 : Nat.card V₀ ≤ 2 :=
        (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
      omega)
  have hm2 : MBarGT D.M V₀ V 2 := TwelveShort.mBarGT_mono hm3 (by omega)
  have hNW0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    normalizer_wClos_le_of_le_cTilde D (r129_1_of_r127 D h127) h61 hx.sig_nonempty
      hx.three_le h.hyp125 h.small hW0
  exact twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 h.hyp125 hV₀ hm2 hNW0

theorem comm_eq_bot_of_conj_le_M (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hW : ⁅E3.wClos V 0 D.T, V⁆ = ⊥) {g : G} (hg : conjSubgroup V g ≤ D.M) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isElemAbelian.isPGroup
  obtain ⟨m, hmM, hm⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM hg
    (E3.isPGroup_conjSubgroup hV2 g)
  have hle : conjSubgroup V (g * m) ≤ D.T := by
    rw [← conjSubgroup_conjSubgroup]
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have := hm _ hx
    simpa [mul_assoc] using this
  have hle0 : conjSubgroup V (g * m) ≤ E3.wClos V 0 D.T :=
    E3.le_wClos ⟨hle, g * m, le_rfl, E3.mQuot_self _⟩
  have h1 : ⁅V, conjSubgroup V (g * m)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.1 ((Subgroup.commutator_mono hle0 le_rfl).trans hW.le)
  have hVm : conjSubgroup V m⁻¹ = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (h.pairFacts.le_normalizer (by simpa using hmM))
  have h2 := E3.conjSubgroup_commutator V (conjSubgroup V (g * m)) m⁻¹
  rw [h1, E3.conjSubgroup_bot, hVm, conjSubgroup_conjSubgroup, mul_inv_cancel_right] at h2
  exact h2.symm

theorem preTil_fixV_le_conj_of_gamma (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {i k r n : ℕ} {A : Subgroup G} {g : G} (hA : A ∈ E3.gammaSet V i D.M)
    (hAg : A ≤ conjSubgroup V g) (hmQA : E3.mQuot (conjSubgroup V g) A = i)
    (hrankA : rk ↥(barSub V₀ V h.isElemAbelian A) = k)
    (hr : ((4 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V)
    {B : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hBA : B ≤ barSub V₀ V h.isElemAbelian A) (hB : rk ↥B = r)
    (hbound : i + (k - r) + mSub V₀ ≤ 4 * n)
    (hinf : g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥) :
    preTil V₀ V h.isElemAbelian (fixV B) ≤ conjSubgroup D.M g := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hM : D.M ≤ Subgroup.normalizer (V : Set G) := h.pairFacts.le_normalizer
  have hM₀ : D.M ≤ Subgroup.normalizer (V₀ : Set G) := h.pairFacts.le_normalizer₀
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hM hM₀
  let X : Subgroup G := preBarSub A V₀ V hV B
  have hXA : X ≤ A := inf_le_left
  have hXst : X ≤ stabTil V₀ V := (hXA.trans hA.1).trans hMst
  have hbarX : barSub V₀ V hV X = B := by
    rw [show X = preBarSub A V₀ V hV B from rfl, barSub_preBarSub]
    exact inf_eq_left.2 hBA
  have hAst : A ≤ stabTil V₀ V := hA.1.trans hMst
  have hmXA : E3.mQuot A X = k - r := by
    have h1 := mQuot_barSub_preBarSub_gen (V₀ := V₀) hV hAst (C := B) hBA
    rw [← h1]
    have h2 := E3.mQuot_add (bot_le : (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) ≤ B) hBA
    rw [E3.mQuot_bot_eq_rk, E3.mQuot_bot_eq_rk] at h2
    rw [hB, hrankA] at h2
    omega
  have hXgam : X ∈ E3.gammaSet V (i + (k - r)) D.M := by
    refine ⟨hXA.trans hA.1, g, hXA.trans hAg, ?_⟩
    rw [E3.mQuot_add hXA hAg, hmQA, hmXA]
    omega
  have hbound' : ((i + (k - r) + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have hle : ((i + (k - r) + mSub V₀ : ℕ) : ℕ∞) ≤ ((4 * n : ℕ) : ℕ∞) := by
      exact_mod_cast hbound
    exact lt_of_le_of_lt hle (lt_of_lt_of_le (by exact_mod_cast (by omega : 4 * n < 4 * n + 1)) hr)
  have h23 := twentyThree_one_of_inf D h hXgam (hXA.trans hAg) hbound' hinf
  have hpreC : preCTilde V₀ V X hV = V ⊓ Subgroup.centralizer (X : Set G) :=
    preCTilde_eq_inf_centralizer_of hV hXst h23.2.1
  have hpre : preCTilde V₀ V X hV = preTil V₀ V hV (fixV B) := by
    unfold preCTilde
    rw [hbarX]
  rw [← hpre, hpreC]
  exact h23.2.2

theorem exists_gam_of_conj_of_eq {V A : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hA : A = conjSubgroup V x) {j : ℕ} (hj : j ≤ mSub V) :
    ∃ B : Subgroup G, B ∈ F12.Gam j A V := by
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hcardV : Nat.card V = 2 ^ mSub V := card_eq_two_pow_mSub hV2
  have hex : ∃ U' : Subgroup G, U' ≤ V ∧ Nat.card V = 2 ^ j * Nat.card U' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥V) 2
      (n := mSub V - j) (by
        rw [hcardV]
        exact pow_dvd_pow 2 (Nat.sub_le _ _))
    refine ⟨K.map V.subtype, Subgroup.map_subtype_le K, ?_⟩
    rw [Subgroup.card_map_of_injective V.subtype_injective, hK, hcardV, ← pow_add]
    congr 1
    omega
  obtain ⟨U', hU'V, hU'card⟩ := hex
  refine ⟨U'.map (MulAut.conj x⁻¹).toMonoidHom,
    ⟨?_, U', x⁻¹, hU'V, hU'card, rfl⟩⟩
  rw [hA]
  exact Subgroup.map_mono hU'V

theorem calABar_of_gammaZero (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1 : P18_13_1 D V₀ V p L h)
    (h16 : R18_16_1At D V₀ V p L h) (h17 : R18_17_1At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) {n : ℕ} (hnof : S17.nOf L = n) (hn : 1 ≤ n)
    {A : Subgroup G} (hGam : A ∈ F12.Gam 0 D.M V)
    (hAbar : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥)
    (hjV : 2 * n - 1 ≤ mSub V) :
    barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar (2 * n) D.M V₀ V h.hyp125.isElemAbelian := by
  have hGam' := hGam
  obtain ⟨-, U, g, hUV, hcard, hAeq⟩ := hGam
  have hcard' : Nat.card V = Nat.card U := by simpa using hcard
  have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (le_of_eq hcard')
  subst U
  have hAeqC : A = conjSubgroup V g⁻¹ := by
    rw [hAeq, conjSubgroup, inv_inv]
  obtain ⟨B, hB⟩ := exists_gam_of_conj_of_eq h.hyp125.isElemAbelian hAeqC (j := 2 * n - 1) hjV
  have hδ : ((2 * n : ℕ) : ℕ∞) ≤ deltaInf D.M V := by simpa [hnof] using h17 h1
  have hr : ((2 * n - 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have h16' : ((4 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by simpa [hnof] using h16 h1
    have hsmall : mSub V₀ ≤ 1 := h.small
    have hle : ((2 * n - 1 + mSub V₀ : ℕ) : ℕ∞) < ((4 * n + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : 2 * n - 1 + mSub V₀ < 4 * n + 1)
    exact lt_of_lt_of_le hle h16'
  exact (h18 0 A hGam' hAbar (2 * n) hδ hr B hB).1



private theorem five_mul_ne_two_mul_mul {n k : ℕ} (hn : 0 < n) : 5 * n ≠ 2 * n * k := by
  intro h
  have h' : 5 * n = (2 * k) * n := by rw [h]; ring
  have h5 : 5 = 2 * k := Nat.eq_of_mul_eq_mul_right hn h'
  omega

theorem comm_mem_inf_conj (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {A : Subgroup G} {x : G} (hAM : A ≤ D.M) (hAeq : A = conjSubgroup V x)
    (hVM : V ≤ conjSubgroup D.M x) {a v : G} (ha : a ∈ A) (hv : v ∈ V) :
    ⁅a, v⁆ ∈ V ⊓ A := by
  have h62 : Hyp62 D.M V₀ V := Hyp125.hyp62 h
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [h62.normalizer_eq]
    exact hAM
  have hVA : V ≤ Subgroup.normalizer (A : Set G) := by
    rw [hAeq, ← E3.conjSubgroup_normalizer V x, h62.normalizer_eq]
    exact hVM
  exact CFSG.LocalAnalysis.RankThreeUC.commutator_le_inf_of_normalizer hAV hVA
    (Subgroup.commutator_mem_commutator ha hv)

section Certified


theorem sing_of_mem_conj (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h)
    (hSg : UC6S846.SigmaStd D) (h15 : R18_15At D V₀ V p L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hSUn : IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 n)
    (hNat : NatSUn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedSU 4 (2 ^ n) F))
    (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 4 → F))
    (hψ : NatCoordsSU4 (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n F ε ψ)
    {x v : G} (hxM : x ∉ D.M) (hxv : x * v * x⁻¹ ∈ V)
    (hvV : v ∈ V) (hv0 : v ∉ V₀) :
    (∑ i, (Multiplicative.toAdd (ψ (tilOf V₀ V h.hyp125.isElemAbelian v hvV))) i ^
      (2 ^ n + 1)) = 0 := by
  by_contra hns
  have hns' : (∑ i, (Multiplicative.toAdd (ψ (mkTil V₀ V h.hyp125.isElemAbelian
      (IntMod.mk h.hyp125.isElemAbelian ⟨v, hvV⟩)))) i ^ (2 ^ n + 1)) ≠ 0 := by
    simpa [tilOf] using hns
  have hv1 : v ≠ 1 := fun h1 => hv0 (h1 ▸ V₀.one_mem)
  have hx : x⁻¹ ∈ D.M :=
    mem_M_of_centralizer_le D h hSg h15 (g := x⁻¹) (by simpa using hxv) hv1
      (nonsingular_centralizer_le_case1 D h61 h h1742 h141 hn2 hSUn hNat hF ε ψ hψ
        (IntMod.mk h.hyp125.isElemAbelian ⟨v, hvV⟩) hv0 hns')
  exact hxM (by simpa using D.M.inv_mem hx)

theorem totally_singular_commV (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h)
    (hSg : UC6S846.SigmaStd D) (h15 : R18_15At D V₀ V p L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hSUn : IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 n)
    (hNat : NatSUn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedSU 4 (2 ^ n) F))
    (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 4 → F))
    (hψ : NatCoordsSU4 (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n F ε ψ)
    {A : Subgroup G} {x : G} (hAeq : A = conjSubgroup V x) (hxM : x ∉ D.M)
    (hVM : V ≤ conjSubgroup D.M x) :
    ∀ w ∈ commV (barSub V₀ V h.hyp125.isElemAbelian A),
      (∑ i, (Multiplicative.toAdd (ψ w)) i ^ (2 ^ n + 1)) = 0 := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  intro w hw
  have hVA : V ≤ normalizer (A : Set G) := by
    rw [hAeq, ← E3.conjSubgroup_normalizer V x, h.hyp125.hyp62.normalizer_eq]
    exact hVM
  have hw' : w ∈ imgTil V₀ V hV (A ⊓ V) :=
    commSub_barSub_le_imgTil hV hVA (by rwa [← commV_eq_commSub])
  obtain ⟨u, hu, rfl⟩ := (mem_imgTil V₀ V hV (A ⊓ V) w).1 hw'
  by_cases hu0 : u.val ∈ V₀
  · have h1 : mkTil V₀ V hV u = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) u).2 hu0
    rw [h1, map_one, toAdd_one]
    simp
  · have huV : u.val ∈ V := (Subgroup.mem_inf.1 hu).2
    have hxv : x * u.val * x⁻¹ ∈ V := by
      rw [hAeq] at hu
      exact mem_conjSubgroup_iff.1 (Subgroup.mem_inf.1 hu).1
    have hres := sing_of_mem_conj D h h61 h1742 h141 hSg h15 hn2 hSUn hNat hF ε ψ hψ
      hxM hxv huV hu0
    have hueq : u = IntMod.mk hV ⟨u.val, huV⟩ := IntMod.val_injective rfl
    rw [hueq]
    exact hres


theorem one_sided_conj_structure (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h)
    (hSg : UC6S846.SigmaStd D) (h15 : R18_15At D V₀ V p L)
    (h16 : R18_16_1At D V₀ V p L h) (h17 : R18_17_1At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h)
    {n : ℕ} (hnof : S17.nOf L = n)
    (hSUn : IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 n)
    (hNat : NatSUn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 n)
    (hn2 : 2 ≤ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedSU 4 (2 ^ n) F))
    (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 4 → F))
    (hψ : NatCoordsSU4 (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n F ε ψ)
    {A : Subgroup G} {x : G} (hAeq : A = conjSubgroup V x) (hxM : x ∉ D.M)
    (hAM : A ≤ D.M) (hVM : V ≤ conjSubgroup D.M x)
    (hAbar : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) :
    (∃ (N B : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))),
        barSub V₀ V h.hyp125.isElemAbelian A ≤ N ∧
          N ≤ barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ∧
          IsElemAbelian2 N ∧ rk ↥N = 4 * n ∧ B ≤ N ∧ rk ↥B = n ∧
            rk ↥(fixV B) = 6 * n ∧
            (∀ y ∈ N, (y ∈ B ↔ ∀ z ∈ fixV B, y z = z)) ∧
          fixV (barSub V₀ V h.hyp125.isElemAbelian A) =
            commV (barSub V₀ V h.hyp125.isElemAbelian A) ∧
          rk ↥(fixV (barSub V₀ V h.hyp125.isElemAbelian A)) = 4 * n) ∧
      E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set G)) = 4 * n := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hHY : H ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.X_le_M
  have hYN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (H : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHY).1
      (barSub_subgroupOf_mbar_normal hV h.X_le_M
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
  have hP1 : P18_13_1 D V₀ V p L h := ⟨n, hSUn, hNat⟩
  have hrkV : mSub V = 8 * n + mSub V₀ := by
    have htop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 8 * n :=
      rk_top_eq_eight_mul_of_natSUn hNat
    have hadd := rk_top_vtil_add_mSub V₀ V hV h.hyp125.pairFacts.le
    rw [htop] at hadd
    exact hadd.symm
  have hjV : 2 * n - 1 ≤ mSub V := by omega
  have hAgam : A ∈ F12.Gam 0 D.M V :=
    ⟨hAM, V, x⁻¹, le_rfl, by simp, by rw [hAeq, conjSubgroup]⟩
  have hmemA : barSub V₀ V hV A ∈ calABar (2 * n) D.M V₀ V hV :=
    calABar_of_gammaZero D h hP1 h16 h17 h18 hnof (by omega) hAgam hAbar hjV
  have h2n : 2 * n ≤ rk ↥(barSub V₀ V hV A) := by
    by_contra hlt
    have hlt' : rk ↥(barSub V₀ V hV A) < 2 * n := by omega
    have hfix : fixV (barSub V₀ V hV A) = ⊤ := by
      have h := hmemA.2.2.2 (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) bot_le
        (by rw [E3.mQuot_bot_eq_rk]; exact hlt')
      rw [← h]
      ext v
      simp [fixV]
    apply hAbar
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have htop : fixV (Subgroup.zpowers y) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      have hsub : fixV (barSub V₀ V hV A) ≤ fixV (Subgroup.zpowers y) :=
        fun u hu z hz => hu z (Subgroup.zpowers_le.2 hy hz)
      exact hsub (by rw [hfix]; exact Subgroup.mem_top w)
    exact eq_one_of_fixV_eq_top htop
  have hAel : IsElemAbelian 2 A := by
    rw [hAeq]
    exact E3.isElemAbelian_conjSubgroup hV x
  have hAbarEl : IsElemAbelian2 (barSub V₀ V hV A) := isElemAbelian2_barSub hV hAel
  have hAleH : barSub V₀ V hV A ≤ H :=
    le_of_mem_aSet_of_natSUn hNat hYN (by simpa [calABar] using hmemA)
  have hsing : ∀ w ∈ commV (barSub V₀ V hV A),
      (∑ i, (Multiplicative.toAdd (ψ w)) i ^ (2 ^ n + 1)) = 0 :=
    totally_singular_commV D h h61 h1742 h141 hSg h15 hn2 hSUn hNat hF ε ψ hψ
      hAeq hxM hVM
  have hK2res := k_18_21_Q_unipotent_holds H (barSub V₀ V hV A) n hSUn hNat
    (by simpa [H] using hAleH) hAbarEl h2n F ε ψ hF hψ hsing
  obtain ⟨hfixA, hrkfixA, N, B, hAN, hNH, hNel, hrkN, hBN, hrkBn, hrkZ, hchar⟩ := hK2res
  have hInfx : V₀ ⊓ conjSubgroup V x = ⊥ :=
    inf_conjSubgroup_eq_bot_of_r18_15 hSg h h15 x hxM
  have hi : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have h16' : ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := h16 hP1
    have hsmall : mSub V₀ ≤ 1 := h.small
    have hle : ((0 + mSub V₀ : ℕ) : ℕ∞) ≤ ((4 * S17.nOf L : ℕ) : ℕ∞) := by
      rw [hnof]
      exact_mod_cast (by omega : 0 + mSub V₀ ≤ 4 * n)
    exact lt_of_le_of_lt hle (lt_of_lt_of_le (by exact_mod_cast (by omega :
      4 * S17.nOf L < 4 * S17.nOf L + 1)) h16')
  have h23 := twentyThree_one_of_inf D h.hyp125
    (by rw [← S17.gam_eq_gammaSet 0 D.M V hV]; exact hAgam) (by rw [hAeq]) hi
    (fun _ => hInfx)
  have hAst : A ≤ stabTil V₀ V :=
    hAM.trans (le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀)
  have hpreC : preCTilde V₀ V A hV = V ⊓ Subgroup.centralizer (A : Set G) :=
    preCTilde_eq_inf_centralizer_of hV hAst h23.2.1
  have hmV : E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set G)) = 4 * n := by
    rw [← hpreC]
    unfold preCTilde
    rw [mQuot_preTil]
    have h1 := rk_add_rkIdx (fixV (barSub V₀ V hV A))
    have h2 := rk_top_eq_eight_mul_of_natSUn hNat
    rw [rk_top] at h2
    omega
  exact ⟨⟨N, B, hAN, hNH, hNel, hrkN, hBN, hrkBn, hrkZ, hchar, hfixA, hrkfixA⟩, hmV⟩



theorem eighteen_twentyone (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h) (h15 : R18_15At D V₀ V p L)
    (hSg : UC6S846.SigmaStd D)
    (h16 : R18_16_1At D V₀ V p L h) (h17 : R18_17_1At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h)
    (hKi2 : K_18_21_i2) :
    R18_21At D V₀ V p L h := by
  intro hP
  obtain ⟨n, hSUn, hNat⟩ := hP
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hP1 : P18_13_1 D V₀ V p L h := ⟨n, hSUn, hNat⟩
  have hUX : IsU4 ↥(barSub V₀ V hV (UC22.conjClosure D.M L)) n := isU4_of_isSUn_four hSUn
  obtain ⟨-, hnof, hn1, -⟩ := isU4_barSub_cong h h1742 hUX
  have hn2 : 2 ≤ n := by omega
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hHY : H ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.X_le_M
  have hYN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (H : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHY).1
      (barSub_subgroupOf_mbar_normal hV h.X_le_M
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
  have hrkV : mSub V = 8 * n + mSub V₀ := by
    have htop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 8 * n :=
      rk_top_eq_eight_mul_of_natSUn hNat
    have hadd := rk_top_vtil_add_mSub V₀ V hV h.hyp125.pairFacts.le
    rw [htop] at hadd
    exact hadd.symm
  have hjV : 2 * n - 1 ≤ mSub V := by omega
  obtain ⟨F, hF, hFfin, hFcard, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  have hInf : ∀ {y : G}, y ∉ D.M → V₀ ⊓ conjSubgroup V y = ⊥ :=
    fun hy => inf_conjSubgroup_eq_bot_of_r18_15 hSg h h15 _ hy
  rcases exists_offender_zero_or_two D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669 with
      ⟨A, hA, hAbar⟩ | ⟨hW0, A, hA2, hAbar2⟩
  ·
    have hAkeep := hA
    obtain ⟨hAT, U, gg, hUV, hcard, hAeq⟩ := hA
    have hcard' : Nat.card V = Nat.card U := by simpa using hcard
    have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (le_of_eq hcard')
    subst U
    set x : G := gg⁻¹ with hxdef
    have hAeqC : A = conjSubgroup V x := by rw [hAeq, hxdef, conjSubgroup, inv_inv]
    have hAM : A ≤ D.M := hAT.trans D.sylowM.le
    have hxM : x ∉ D.M := by
      intro hxM'
      apply hAbar
      have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
        rw [h.hyp125.hyp62.normalizer_eq]
        exact hxM'
      have hAV : A = V := by
        rw [hAeqC, conjSubgroup_eq_iff_mem_normalizer.2 hxN]
      rw [hAV]
      exact barSub_self_eq_bot hV
    have hAgam : A ∈ F12.Gam 0 D.M V :=
      ⟨hAM, V, x⁻¹, le_rfl, by simp, by rw [hAeqC, conjSubgroup]⟩
    have hAgamE : A ∈ E3.gammaSet V 0 D.M := by
      rw [← S17.gam_eq_gammaSet 0 D.M V hV]
      exact hAgam
    by_cases hVM : V ≤ conjSubgroup D.M x
    ·
      have hA' := one_sided_conj_structure D h h61 h1742 h141 hSg h15 h16 h17 h18
        hnof hSUn hNat hn2 hFcard ε ψ hψ hAeqC hxM hAM hVM hAbar
      obtain ⟨⟨N, Bbar, hAN, hNH, hNel, hrkN, hBbarN, hrkBbar, hrkZbar, hchar,
        hfixA, hrkfixA⟩, hmV⟩ := hA'
      have hxM' : x⁻¹ ∉ D.M := fun hh => hxM (by simpa using D.M.inv_mem hh)
      have hAM' : conjSubgroup V x⁻¹ ≤ D.M := by
        intro v hv
        rw [mem_conjSubgroup_iff] at hv
        have h := hVM hv
        rw [mem_conjSubgroup_iff] at h
        simpa [show x * (x⁻¹ * v * x) * x⁻¹ = v by group] using h
      have hVM' : V ≤ conjSubgroup D.M x⁻¹ := by
        intro v hv
        rw [mem_conjSubgroup_iff]
        have hvA : x⁻¹ * v * x ∈ A := by
          rw [hAeqC, mem_conjSubgroup_iff]
          show x * (x⁻¹ * v * x) * x⁻¹ ∈ V
          simpa [show x * (x⁻¹ * v * x) * x⁻¹ = v by group] using hv
        simpa using hAM hvA
      have hAbar' : barSub V₀ V hV (conjSubgroup V x⁻¹) ≠ ⊥ := by
        intro hbot
        have hAV_bot : ⁅V, A⁆ ≠ ⊥ := by
          intro h0
          apply hAbar
          rw [barSub_eq_bot_iff hV h.hyp125.pairFacts.le_normalizer
            h.hyp125.pairFacts.le_normalizer₀ hAM]
          intro a ha
          refine (mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer).2
            ⟨hAM ha, hAM.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
              h.hyp125.pairFacts.le_normalizer₀) ha, ?_⟩
          rw [actTil_eq_one_iff]
          intro v hv
          have hcent : A ≤ Subgroup.centralizer (V : Set G) := by
            rw [Subgroup.commutator_comm] at h0
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0
          have hcomm : a * v = v * a :=
            (Subgroup.mem_centralizer_iff.1 (hcent ha) v hv).symm
          rw [show a * v * a⁻¹ * v⁻¹ = 1 from commutatorElement_eq_one_iff_mul_comm.2 hcomm]
          exact V₀.one_mem
        have hAV'_bot : ⁅V, conjSubgroup V x⁻¹⁆ ≠ ⊥ := by
          intro h0
          apply hAV_bot
          have h := E3.conjSubgroup_commutator V (conjSubgroup V x⁻¹) x
          rw [h0, E3.conjSubgroup_bot, conjSubgroup_conjSubgroup, inv_mul_cancel,
            conjSubgroup_one] at h
          rw [Subgroup.commutator_comm, hAeqC]
          exact h.symm
        have hA'V_bot : ⁅conjSubgroup V x⁻¹, V⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          have hst : a ∈ stabTil V₀ V :=
            hAM'.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
              h.hyp125.pairFacts.le_normalizer₀) ha
          have hmem : ⁅a, v⁆ ∈ conjSubgroup V x⁻¹ ⊓ V₀ := by
            constructor
            · have hvN : v ∈ Subgroup.normalizer (conjSubgroup V x⁻¹ : Set G) := by
                rw [← E3.conjSubgroup_normalizer V x⁻¹, h.hyp125.hyp62.normalizer_eq]
                exact hVM' hv
              have hmemA : v * a⁻¹ * v⁻¹ ∈ conjSubgroup V x⁻¹ :=
                (Subgroup.mem_normalizer_iff.1 hvN a⁻¹).1 ((conjSubgroup V x⁻¹).inv_mem ha)
              simpa [commutatorElement_def, mul_assoc] using
                (conjSubgroup V x⁻¹).mul_mem ha hmemA
            · have hact : actTil V₀ V hV ⟨a, hst⟩ ∈ barSub V₀ V hV (conjSubgroup V x⁻¹) :=
                actTil_mem_barSub V₀ V hV ha hst
              rw [hbot, Subgroup.mem_bot] at hact
              exact (actTil_eq_one_iff V₀ V hV ⟨a, hst⟩).1 hact v hv
          have hmem' : ⁅a, v⁆ ∈ V₀ ⊓ conjSubgroup V x⁻¹ :=
            ⟨(Subgroup.mem_inf.1 hmem).2, (Subgroup.mem_inf.1 hmem).1⟩
          rw [show V₀ ⊓ conjSubgroup V x⁻¹ = ⊥ from hInf hxM'] at hmem'
          have h1 : ⁅a, v⁆ = 1 := Subgroup.mem_bot.1 hmem'
          exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
        rw [Subgroup.commutator_comm] at hA'V_bot
        exact hAV'_bot hA'V_bot
      have hA'' := one_sided_conj_structure D h h61 h1742 h141 hSg h15 h16 h17 h18
        hnof hSUn hNat hn2 hFcard ε ψ hψ
        (by rfl : conjSubgroup V x⁻¹ = conjSubgroup V x⁻¹)
        hxM' hAM' hVM' hAbar'
      obtain ⟨⟨N', B', hA'N', hN'H, hN'el, hrkN', hB'N', hrkB'N', hrkZ'N', hchar'N,
        hfixA', hrkfixA'⟩, hmV'⟩ := hA''
      have hA'leH : barSub V₀ V hV (conjSubgroup V x⁻¹) ≤ H := hA'N'.trans hN'H
      have hsym : E3.mQuot (conjSubgroup V x) (conjSubgroup V x ⊓
          Subgroup.centralizer (V : Set G)) = 4 * n := by
        have h := E3.mQuot_conjSubgroup V
          (V ⊓ Subgroup.centralizer (conjSubgroup V x⁻¹ : Set G)) x
        have hU : conjSubgroup (V ⊓ Subgroup.centralizer (conjSubgroup V x⁻¹ : Set G)) x =
            conjSubgroup V x ⊓ Subgroup.centralizer (V : Set G) := by
          rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, conjSubgroup_conjSubgroup,
            inv_mul_cancel, conjSubgroup_one]
        rw [hU] at h
        rw [h]
        exact hmV'
      have hrkAbar : rk ↥(barSub V₀ V hV A) = 4 * n := by
        have h1 := rk_barSub_eq_mQuot_inf_cTilde (M := D.M) (V₀ := V₀) (V := V)
          (B := A) hV h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hAM
        rw [h1]
        have hCt : A ⊓ F11.CTilde D.M V₀ V = A ⊓ Subgroup.centralizer (V : Set G) := by
          apply le_antisymm
          · intro a ha
            obtain ⟨haA, haC⟩ := Subgroup.mem_inf.1 ha
            refine Subgroup.mem_inf.2 ⟨haA, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            obtain ⟨-, hst, hact⟩ := (mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer).1 haC
            have h1 : actTil V₀ V hV ⟨a, hst⟩ = 1 := hact
            have hcomm : ⁅a, v⁆ ∈ V₀ :=
              (actTil_eq_one_iff V₀ V hV ⟨a, hst⟩).1 h1 v hv
            have hcommA : ⁅a, v⁆ ∈ A :=
              (comm_mem_inf_conj D h.hyp125 hAM hAeqC hVM haA hv).2
            have hmem : ⁅a, v⁆ ∈ V₀ ⊓ A := ⟨hcomm, hcommA⟩
            rw [show V₀ ⊓ A = ⊥ by rw [hAeqC]; exact hInf hxM,
              Subgroup.mem_bot] at hmem
            exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
          · intro a ha
            obtain ⟨haA, haC⟩ := Subgroup.mem_inf.1 ha
            refine Subgroup.mem_inf.2 ⟨haA, ?_⟩
            refine (mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer).2
              ⟨hAM haA, hAM.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
                h.hyp125.pairFacts.le_normalizer₀) haA, ?_⟩
            rw [actTil_eq_one_iff]
            intro v hv
            have hcomm : a * v = v * a :=
              (Subgroup.mem_centralizer_iff.1 haC v hv).symm
            rw [show a * v * a⁻¹ * v⁻¹ = 1 from commutatorElement_eq_one_iff_mul_comm.2 hcomm]
            exact V₀.one_mem
        rw [hCt]
        rw [hAeqC]
        exact hsym
      have hAbar_eq_N : barSub V₀ V hV A = N := by
        refine Subgroup.eq_of_le_of_card_ge hAN ?_
        have hAbarEl : IsElemAbelian2 (barSub V₀ V hV A) := by
          have hAel : IsElemAbelian 2 A := by
            rw [hAeqC]
            exact E3.isElemAbelian_conjSubgroup hV x
          exact isElemAbelian2_barSub hV hAel
        rw [card_eq_two_pow_of_isPGroup (IsElemAbelian2.isPGroup hNel),
          card_eq_two_pow_of_isPGroup (IsElemAbelian2.isPGroup hAbarEl), hrkN, hrkAbar]
      let Dk : Subgroup G := A ⊓ F11.CTilde D.M V₀ V
      have hDkA : Dk ≤ A := inf_le_left
      have hrkDk : rk ↥Dk = 4 * n + mSub V₀ := by
        have h1 := rk_barSub_eq_mQuot_inf_cTilde (M := D.M) (V₀ := V₀) (V := V)
          (B := A) hV h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hAM
        have h2 := E3.mQuot_add (bot_le : (⊥ : Subgroup G) ≤ Dk) hDkA
        rw [E3.mQuot_bot_eq_rk, E3.mQuot_bot_eq_rk] at h2
        rw [← h1, hrkAbar] at h2
        have hrkA : rk ↥A = 8 * n + mSub V₀ := by
          have h : rk ↥A = rk ↥V := by
            rw [hAeqC]
            unfold rk
            rw [E3.card_conjSubgroup]
          rw [h]
          exact hrkV
        omega
      let Zbar : Subgroup (Vtil V₀ V hV) := fixV Bbar
      let Z : Subgroup G := preTil V₀ V hV Zbar
      let B : Subgroup G := preBarSub A V₀ V hV Bbar
      have hAst : A ≤ stabTil V₀ V :=
        hAM.trans (le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀)
      have hBbar : barSub V₀ V hV B = Bbar := by
        rw [show B = preBarSub A V₀ V hV Bbar from rfl, barSub_preBarSub]
        exact inf_eq_left.2 (by
          have h := hBbarN
          rw [← hAbar_eq_N] at h
          exact h)
      have hDk_le_B : Dk ≤ B := by
        intro a ha
        obtain ⟨haA, haC⟩ := Subgroup.mem_inf.1 ha
        refine (mem_preBarSub A V₀ V hV Bbar).2 ⟨haA, hAst haA, ?_⟩
        obtain ⟨-, hst, hact⟩ := (mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer).1 haC
        have h1 : actTil V₀ V hV ⟨a, hAst haA⟩ = 1 := by
          rw [show (⟨a, hAst haA⟩ : ↥(stabTil V₀ V)) = ⟨a, hst⟩ from Subtype.ext rfl]
          exact hact
        rw [h1]
        exact Bbar.one_mem
      have hrkB : rk ↥B = 5 * n + mSub V₀ := by
        have h1 := rk_barSub_eq_mQuot_inf_cTilde (M := D.M) (V₀ := V₀) (V := V)
          (B := B) hV h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
          (inf_le_left.trans hAM)
        have hBK : B ⊓ F11.CTilde D.M V₀ V = Dk := by
          apply le_antisymm
          · intro b hb
            obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.1 hb
            obtain ⟨hbA, -, -⟩ := (mem_preBarSub A V₀ V hV Bbar).1 hbB
            exact Subgroup.mem_inf.2 ⟨hbA, hbC⟩
          · intro b hb
            exact Subgroup.mem_inf.2 ⟨hDk_le_B hb, (Subgroup.mem_inf.1 hb).2⟩
        rw [hBK, hBbar, hrkBbar] at h1
        have h2 := E3.mQuot_add (bot_le : (⊥ : Subgroup G) ≤ Dk) hDk_le_B
        rw [E3.mQuot_bot_eq_rk, E3.mQuot_bot_eq_rk] at h2
        rw [hrkDk, ← h1] at h2
        omega
      have hB_eq : B = A ⊓ Subgroup.centralizer (Z : Set G) := by
        apply le_antisymm
        · intro b hb
          obtain ⟨hbA, hst, hbBbar⟩ := (mem_preBarSub A V₀ V hV Bbar).1 hb
          refine Subgroup.mem_inf.2 ⟨hbA, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have hzV : z ∈ V := preTil_le V₀ V hV Zbar hz
          have hzbar : mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩) ∈ Zbar :=
            (mem_preTil_iff_of_mem V₀ V hV Zbar hzV).1 hz
          have hBbarN' : Bbar ≤ barSub V₀ V hV A := by rwa [hAbar_eq_N]
          have hbN : actTil V₀ V hV ⟨b, hst⟩ ∈ N := by
            rw [← hAbar_eq_N]
            exact hBbarN' hbBbar
          have hfix := (hchar _ hbN).1 hbBbar _ hzbar
          rw [actTil_mk, mkTil_eq_iff] at hfix
          have hcommA : ⁅b, z⁆ ∈ A :=
            (comm_mem_inf_conj D h.hyp125 hAM hAeqC hVM hbA hzV).2
          have hmem : ⁅b, z⁆ ∈ V₀ ⊓ A := by
            refine ⟨?_, hcommA⟩
            rwa [commutatorElement_def]
          rw [show V₀ ⊓ A = ⊥ by rw [hAeqC]; exact hInf hxM,
            Subgroup.mem_bot] at hmem
          exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
        · intro b hb
          obtain ⟨hbA, hbC⟩ := Subgroup.mem_inf.1 hb
          refine (mem_preBarSub A V₀ V hV Bbar).2 ⟨hbA, hAst hbA, ?_⟩
          have hbN : actTil V₀ V hV ⟨b, hAst hbA⟩ ∈ N := by
            rw [← hAbar_eq_N]
            exact actTil_mem_barSub V₀ V hV hbA (hAst hbA)
          refine (hchar _ hbN).2 fun zbar hzbar => ?_
          obtain ⟨xx, rfl⟩ := mkTil_surjective V₀ V hV zbar
          rw [actTil_mk, mkTil_eq_iff]
          have hz : xx.val ∈ Z := (mem_preTil_iff_of_mem V₀ V hV Zbar xx.val_mem).2 hzbar
          have hcent : b * xx.val = xx.val * b :=
            (Subgroup.mem_centralizer_iff.1 hbC xx.val hz).symm
          have h3 : b * xx.val * b⁻¹ * xx.val⁻¹ = 1 := by
            calc b * xx.val * b⁻¹ * xx.val⁻¹ = (xx.val * b) * b⁻¹ * xx.val⁻¹ := by
                  rw [hcent]
              _ = 1 := by group
          rw [actStab_apply_val, h3]
          exact V₀.one_mem
      let Z' : Subgroup G := conjSubgroup Z x⁻¹
      have hZleV : Z ≤ V := preTil_le V₀ V hV Zbar
      have hZ'leA' : Z' ≤ conjSubgroup V x⁻¹ :=
        E3.conjSubgroup_mono_left x⁻¹ hZleV
      have hZ'leM : Z' ≤ D.M := hZ'leA'.trans hAM'
      have hBconj : conjSubgroup B x⁻¹ = V ⊓ Subgroup.centralizer (Z' : Set G) := by
        rw [hB_eq, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
        have hAV : conjSubgroup A x⁻¹ = V := by
          rw [hAeqC, E3.conjSubgroup_conj_inv V x]
        rw [hAV]
      have hmZ : E3.mQuot V Z = 2 * n := by
        have hZ'eq : Z = preTil V₀ V hV Zbar := rfl
        rw [hZ'eq, mQuot_preTil]
        have hZ : rk Zbar = 6 * n := hrkZbar
        have h1 := rk_add_rkIdx Zbar
        have h2 := rk_top_eq_eight_mul_of_natSUn hNat
        rw [rk_top] at h2
        omega
      have hZ'Γ : Z' ∈ E3.gammaSet V (2 * n) D.M := by
        refine ⟨hZ'leM, x⁻¹, hZ'leA', ?_⟩
        have h := E3.mQuot_conjSubgroup V Z x⁻¹
        rw [h]
        exact hmZ
      have hZ'st : Z' ≤ stabTil V₀ V :=
        hZ'leM.trans (le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀)
      have hboundZ : ((2 * n + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
        have h16' : ((4 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by simpa [hnof] using h16 hP1
        have hsmall : mSub V₀ ≤ 1 := h.small
        have hle : ((2 * n + mSub V₀ : ℕ) : ℕ∞) < ((4 * n + 1 : ℕ) : ℕ∞) := by
          exact_mod_cast (by omega : 2 * n + mSub V₀ < 4 * n + 1)
        exact lt_of_lt_of_le hle h16'
      have h23Z := twentyThree_one_of_inf D h.hyp125 hZ'Γ hZ'leA' hboundZ
        (fun _ => hInf hxM')
      have hpreZ : V ⊓ Subgroup.centralizer (Z' : Set G) =
          preTil V₀ V hV (fixV (barSub V₀ V hV Z')) := by
        rw [← preCTilde_eq_inf_centralizer_of hV hZ'st h23Z.2.1]
        rfl
      have hBrank : rk ↥B = mSub V₀ + rk ↥(fixV (barSub V₀ V hV Z')) := by
        have h1 : mSub (conjSubgroup B x⁻¹) =
            mSub V₀ + rk ↥(fixV (barSub V₀ V hV Z')) := by
          rw [hBconj, hpreZ, s16c4_mSub_preTil hV h.hyp125.pairFacts.le]
        have h2 : rk ↥B = rk ↥(conjSubgroup B x⁻¹) := by
          rw [E3.rk_conjSubgroup]
        rw [h2]
        exact h1
      have hZ'leH : barSub V₀ V hV Z' ≤ H :=
        (barSub_mono V₀ V hV hZ'leA').trans hA'leH
      obtain ⟨kk, hkk⟩ := exists_rk_fixV_eq_two_mul_mul_of_natSUn hNat hZ'leH
      have h5 : 5 * n + mSub V₀ = mSub V₀ + 2 * n * kk := by
        rw [← hrkB, hBrank, hkk]
      have h5' : 5 * n = 2 * n * kk := by omega
      exact five_mul_ne_two_mul_mul (by omega) h5'
    ·
      have hVA : ¬ V ≤ Subgroup.normalizer (A : Set G) := by
        rw [hAeqC, ← E3.conjSubgroup_normalizer V x, h.hyp125.hyp62.normalizer_eq]
        exact hVM
      have hbound := four_mul_n_add_one_le_of_not_le_normalizer (D := D) h
        (by simpa [hnof] using h16 hP1) hAkeep hVA
      have hmemA : barSub V₀ V hV A ∈ calABar (2 * n) D.M V₀ V hV :=
        calABar_of_gammaZero D h hP1 h16 h17 h18 hnof (by omega) hAgam hAbar hjV
      have hmemA2 : barSub V₀ V hV A ∈ E3.aSet (2 * n - 2) (Mbar D.M V₀ V hV) :=
        E3.aSet_anti (by omega : 2 * n - 2 ≤ 2 * n) (Mbar D.M V₀ V hV) hmemA
      have hrankA : 4 * n - 1 ≤ rk ↥(barSub V₀ V hV A) := by
        have hsmall : mSub V₀ ≤ 1 := h.small
        omega
      obtain ⟨hAleH, hrkA_le, ⟨a₁, a₂, ha₁, ha₂, hc₁, hf₁, hc₂, hf₂, hfixne, hfixsup⟩, -⟩ :=
        hKi2 H (Mbar D.M V₀ V hV) (barSub V₀ V hV A) n hn2 hSUn hNat hHY hYN hmemA2 hrankA
      by_cases hV0 : V₀ = ⊥
      · subst hV0
        have hms : mSub (⊥ : Subgroup G) = 0 := by rw [mSub, CFSG.Quasithin.rk_bot]
        rw [hms, Nat.zero_add] at hbound
        omega
      · have hm1 : mSub V₀ = 1 := by
          have hle := h.small
          have hne : mSub V₀ ≠ 0 := by
            intro h0
            apply hV0
            have hcard : Nat.card V₀ = 1 := by
              rw [card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup, h0]
              norm_num
            exact (Subgroup.card_eq_one).1 hcard
          omega
        have hrank4 : rk ↥(barSub V₀ V hV A) = 4 * n := by omega
        have hAbarEl : IsElemAbelian2 (barSub V₀ V hV A) := by
          have hAel : IsElemAbelian 2 A := by
            rw [hAeqC]
            exact E3.isElemAbelian_conjSubgroup hV x
          exact isElemAbelian2_barSub hV hAel
        have hsq1 : a₁ * a₁ = 1 := hAbarEl.2 a₁ ha₁
        have hsq2 : a₂ * a₂ = 1 := hAbarEl.2 a₂ ha₂
        have hne1 : a₁ ≠ 1 := by
          intro h1
          have h0 : rk ↥(commV (Subgroup.zpowers a₁)) = 0 := by
            rw [h1, Subgroup.zpowers_one_eq_bot, CFSG.Quasithin.FixVLat.commV_bot,
              CFSG.Quasithin.rk_bot]
          omega
        have hne2 : a₂ ≠ 1 := by
          intro h1
          have h0 : rk ↥(commV (Subgroup.zpowers a₂)) = 0 := by
            rw [h1, Subgroup.zpowers_one_eq_bot, CFSG.Quasithin.FixVLat.commV_bot,
              CFSG.Quasithin.rk_bot]
          omega
        have ho1 : orderOf a₁ = 2 := by
          have hdvd : orderOf a₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using hsq1)
          rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hne1
          · exact h
        have ho2 : orderOf a₂ = 2 := by
          have hdvd : orderOf a₂ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using hsq2)
          rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hne2
          · exact h
        have hrk1 : rk ↥(Subgroup.zpowers a₁) = 1 := by
          unfold rk
          rw [Nat.card_zpowers, ho1]
          norm_num [padicValNat]
        have hrk2 : rk ↥(Subgroup.zpowers a₂) = 1 := by
          unfold rk
          rw [Nat.card_zpowers, ho2]
          norm_num [padicValNat]
        have hPt1 : preTil V₀ V hV (fixV (Subgroup.zpowers a₁)) ≤ conjSubgroup D.M x :=
          preTil_fixV_le_conj_of_gamma (D := D) (h := h.hyp125) (n := n) (i := 0)
            (k := 4 * n) (r := 1) (A := A) (g := x) hAgamE (by rw [hAeqC])
            (by rw [← hAeqC]; exact E3.mQuot_self _) (by rw [hrank4])
            (by simpa [hnof] using h16 hP1)
            (Subgroup.zpowers_le.2 ha₁) hrk1 (by omega) (fun _ => hInf hxM)
        have hPt2 : preTil V₀ V hV (fixV (Subgroup.zpowers a₂)) ≤ conjSubgroup D.M x :=
          preTil_fixV_le_conj_of_gamma (D := D) (h := h.hyp125) (n := n) (i := 0)
            (k := 4 * n) (r := 1) (A := A) (g := x) hAgamE (by rw [hAeqC])
            (by rw [← hAeqC]; exact E3.mQuot_self _) (by rw [hrank4])
            (by simpa [hnof] using h16 hP1)
            (Subgroup.zpowers_le.2 ha₂) hrk2 (by omega) (fun _ => hInf hxM)
        have hVsup : V = preTil V₀ V hV (fixV (Subgroup.zpowers a₁)) ⊔
            preTil V₀ V hV (fixV (Subgroup.zpowers a₂)) := by
          rw [← TwelveSeventeen.preTil_sup V₀ V hV, hfixsup, preTil_top]
        exact hVM (by rw [hVsup]; exact sup_le hPt1 hPt2)
  ·
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      have hW : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        have hCt : F11.CTilde D.M ⊥ V = D.M ⊓ Subgroup.centralizer (V : Set G) :=
          UC22.uc22p22u_cTilde_bot D.M V
        rw [hCt] at hW0
        exact hW0.trans inf_le_right
      obtain ⟨hAT, U, gg, hUV, hcard, hAeq⟩ := hA2
      set x : G := gg⁻¹ with hxdef
      have hAgA : A ≤ conjSubgroup V x := by
        rw [hAeq, hxdef, conjSubgroup, inv_inv]
        exact Subgroup.map_mono hUV
      have hAM : A ≤ D.M := hAT.trans D.sylowM.le
      have hMst : D.M ≤ stabTil (⊥ : Subgroup G) V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
      have hAst : A ≤ stabTil (⊥ : Subgroup G) V := hAM.trans hMst
      have hcardA : Nat.card ↥A = Nat.card ↥U := by
        rw [hAeq]
        exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj gg))
      have hmQA : E3.mQuot (conjSubgroup V x) A = 2 := by
        have hVg : Nat.card ↥(conjSubgroup V x) = Nat.card ↥V := E3.card_conjSubgroup V x
        have hrel : A.relIndex (conjSubgroup V x) = 4 := by
          have hmul := Subgroup.relIndex_mul_card (H := A) (K := conjSubgroup V x)
          rw [inf_eq_left.2 hAgA, hVg, hcard, ← hcardA,
            show (2 : ℕ) ^ 2 = 4 by norm_num] at hmul
          have hpos : 0 < Nat.card ↥A := Nat.card_pos
          exact Nat.eq_of_mul_eq_mul_right hpos hmul
        unfold E3.mQuot
        rw [hrel, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
      have hVleM : V ≤ conjSubgroup D.M x := by
        by_contra hVMg
        have hrankGeo : 4 * n - 1 ≤ rk ↥(barSub (⊥ : Subgroup G) V hV A) := by
          by_contra hlt
          have hlt' : rk ↥(barSub (⊥ : Subgroup G) V hV A) ≤ 4 * n - 2 := by omega
          let Dk : Subgroup G := A ⊓ F11.CTilde D.M ⊥ V
          have hDkA : Dk ≤ A := inf_le_left
          have hDkM : Dk ≤ D.M := hDkA.trans hAM
          have hVpre : V ≤ preCTilde (⊥ : Subgroup G) V Dk hV := by
            intro v hv
            rw [mem_preCTilde_iff hV (hDkM.trans hMst) hv]
            intro d hd
            have hdC : d ∈ Subgroup.centralizer (V : Set G) := by
              have h1 := (Subgroup.mem_inf.1 hd).2
              rw [UC22.uc22p22u_cTilde_bot D.M V] at h1
              exact h1.2
            rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
            exact Subgroup.mem_centralizer_iff.1 hdC v hv
          have hmQDk : E3.mQuot (conjSubgroup V x) Dk =
              2 + rk ↥(barSub (⊥ : Subgroup G) V hV A) := by
            have h3 := rk_barSub_eq_mQuot_inf_cTilde (V₀ := ⊥) (V := V) (M := D.M) (B := A)
              hV h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hAM
            rw [E3.mQuot_add hDkA hAgA, hmQA, ← h3]
            ring
          have hr : ((E3.mQuot (conjSubgroup V x) Dk + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) <
              rMV D.M V := by
            have h0 : mSub (⊥ : Subgroup G) = 0 := by rw [mSub, CFSG.Quasithin.rk_bot]
            rw [h0, Nat.add_zero, hmQDk]
            have hle : 2 + rk ↥(barSub (⊥ : Subgroup G) V hV A) ≤ 4 * n := by omega
            have h16' : ((4 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by simpa [hnof] using h16 hP1
            have hlt2 : ((4 * n : ℕ) : ℕ∞) < ((4 * n + 1 : ℕ) : ℕ∞) := by
              exact_mod_cast (by omega : 4 * n < 4 * n + 1)
            exact lt_of_le_of_lt (by exact_mod_cast hle) (hlt2.trans_le h16')
          have hD : Dk ≤ conjSubgroup V x ⊓ D.M := le_inf (hDkA.trans hAgA) hDkM
          exact hVMg (hVpre.trans (six_two_one (Hyp125.hyp62 h.hyp125) hD hr))
        have hmSubV : 2 * n ≤ mSub V := by
          have := hrkV
          omega
        obtain ⟨B0, hB0⟩ := eighteen_twenty_exists_gamma (A := A) (U := U) (V := V) (g := gg)
          hV hUV hcard hAeq (j := 2 * n) (by omega) (by
            have := hrkV; omega)
        have hδ : ((2 * n : ℕ) : ℕ∞) ≤ deltaInf D.M V := by simpa [hnof] using h17 hP1
        have hm0 : mSub (⊥ : Subgroup G) = 0 := by rw [mSub, CFSG.Quasithin.rk_bot]
        have hr' : ((2 * n - 1 + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
          rw [hm0, Nat.add_zero]
          have h16b : ((4 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by simpa [hnof] using h16 hP1
          exact lt_of_lt_of_le (by exact_mod_cast (by omega : 2 * n - 1 < 4 * n + 1)) h16b
        have hAgam : A ∈ F12.Gam 2 D.M V := ⟨hAM, U, gg, hUV, hcard, hAeq⟩
        have hmemAbar2 : barSub (⊥ : Subgroup G) V hV A ∈ calABar (2 * n - 2) D.M ⊥ V hV :=
          (h18 2 A hAgam hAbar2 (2 * n) hδ hr' B0 hB0).1
        obtain ⟨hAleH2, hk_le, ⟨a₁, a₂, ha₁, ha₂, hc₁, hf₁, hc₂, hf₂, hfixne, hfixsup⟩,
          hroot⟩ :=
          hKi2 H (Mbar D.M (⊥ : Subgroup G) V hV) _ n hn2 hSUn hNat hHY hYN
            (by simpa [calABar] using hmemAbar2) hrankGeo
        have hAgamE : A ∈ E3.gammaSet V 2 D.M := by
          rw [← S17.gam_eq_gammaSet 2 D.M V hV]
          exact hAgam
        have h16' : ((4 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by simpa [hnof] using h16 hP1
        have hinfx : x ∉ D.M → (⊥ : Subgroup G) ⊓ conjSubgroup V x = ⊥ := by
          intro _; simp
        have hAbarEl : IsElemAbelian2 (barSub (⊥ : Subgroup G) V hV A) := by
          have hUel : IsElemAbelian 2 U := hV.mono hUV
          have hAeqU : A = conjSubgroup U gg⁻¹ := by
            rw [hAeq, conjSubgroup, inv_inv]
          have hAel : IsElemAbelian 2 A := by
            rw [hAeqU]
            exact E3.isElemAbelian_conjSubgroup hUel gg⁻¹
          exact isElemAbelian2_barSub hV hAel
        by_cases hrk4 : rk ↥(barSub (⊥ : Subgroup G) V hV A) = 4 * n
        · obtain ⟨N, B1, B2, hAeqN, hNH, hNel, hrkN, hB1N, hB2N, hrkB1, hrkB2, hf1, hf2, hfixne2,
            hfixsup2⟩ := hroot hrk4
          have hB1A : B1 ≤ barSub (⊥ : Subgroup G) V hV A := by rw [hAeqN]; exact hB1N
          have hB2A : B2 ≤ barSub (⊥ : Subgroup G) V hV A := by rw [hAeqN]; exact hB2N
          have hP1 := preTil_fixV_le_conj_of_gamma (D := D) (h := h.hyp125) (n := n) (i := 2)
            (k := 4 * n) (r := n) (A := A) (g := x) hAgamE hAgA hmQA (by rw [hrk4]) h16'
            hB1A hrkB1 (by rw [hm0]; omega) hinfx
          have hP2 := preTil_fixV_le_conj_of_gamma (D := D) (h := h.hyp125) (n := n) (i := 2)
            (k := 4 * n) (r := n) (A := A) (g := x) hAgamE hAgA hmQA (by rw [hrk4]) h16'
            hB2A hrkB2 (by rw [hm0]; omega) hinfx
          have hVeq : V = preTil (⊥ : Subgroup G) V hV (fixV B1) ⊔
              preTil (⊥ : Subgroup G) V hV (fixV B2) := by
            rw [← TwelveSeventeen.preTil_sup, hfixsup2, preTil_top]
          exact hVMg (by rw [hVeq]; exact sup_le hP1 hP2)
        · have hrkl : rk ↥(barSub (⊥ : Subgroup G) V hV A) ≤ 4 * n - 1 := by omega
          have hsq1 : a₁ * a₁ = 1 := hAbarEl.2 a₁ ha₁
          have hsq2 : a₂ * a₂ = 1 := hAbarEl.2 a₂ ha₂
          have hne1 : a₁ ≠ 1 := by
            intro h1
            have h0 : rk ↥(commV (Subgroup.zpowers a₁)) = 0 := by
              rw [h1, Subgroup.zpowers_one_eq_bot, CFSG.Quasithin.FixVLat.commV_bot,
                CFSG.Quasithin.rk_bot]
            rw [hc₁] at h0
            omega
          have hne2 : a₂ ≠ 1 := by
            intro h1
            have h0 : rk ↥(commV (Subgroup.zpowers a₂)) = 0 := by
              rw [h1, Subgroup.zpowers_one_eq_bot, CFSG.Quasithin.FixVLat.commV_bot,
                CFSG.Quasithin.rk_bot]
            rw [hc₂] at h0
            omega
          have ho1 : orderOf a₁ = 2 := by
            have hdvd : orderOf a₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using hsq1)
            rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
            · exact absurd (orderOf_eq_one_iff.mp h) hne1
            · exact h
          have ho2 : orderOf a₂ = 2 := by
            have hdvd : orderOf a₂ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using hsq2)
            rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
            · exact absurd (orderOf_eq_one_iff.mp h) hne2
            · exact h
          have hrk1 : rk ↥(Subgroup.zpowers a₁) = 1 := by
            unfold rk
            rw [Nat.card_zpowers, ho1]
            norm_num [padicValNat]
          have hrk2 : rk ↥(Subgroup.zpowers a₂) = 1 := by
            unfold rk
            rw [Nat.card_zpowers, ho2]
            norm_num [padicValNat]
          have hP1 := preTil_fixV_le_conj_of_gamma (D := D) (h := h.hyp125) (n := n) (i := 2)
            (k := rk ↥(barSub (⊥ : Subgroup G) V hV A)) (r := 1) (A := A) (g := x)
            hAgamE hAgA hmQA rfl h16' (Subgroup.zpowers_le.2 ha₁) hrk1
            (by rw [hm0]; omega) hinfx
          have hP2 := preTil_fixV_le_conj_of_gamma (D := D) (h := h.hyp125) (n := n) (i := 2)
            (k := rk ↥(barSub (⊥ : Subgroup G) V hV A)) (r := 1) (A := A) (g := x)
            hAgamE hAgA hmQA rfl h16' (Subgroup.zpowers_le.2 ha₂) hrk2
            (by rw [hm0]; omega) hinfx
          have hVeq : V = preTil (⊥ : Subgroup G) V hV (fixV (Subgroup.zpowers a₁)) ⊔
              preTil (⊥ : Subgroup G) V hV (fixV (Subgroup.zpowers a₂)) := by
            rw [← TwelveSeventeen.preTil_sup, hfixsup, preTil_top]
          exact hVMg (by rw [hVeq]; exact sup_le hP1 hP2)
      have hcomm_eq : ⁅V, conjSubgroup V x⁆ = ⊥ := by
        have hxg : conjSubgroup V x⁻¹ ≤ D.M := by
          have h := E3.conjSubgroup_mono_left x⁻¹ hVleM
          rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
        have h := comm_eq_bot_of_conj_le_M (D := D) h.hyp125 hW hxg
        have h2 := E3.conjSubgroup_commutator V (conjSubgroup V x⁻¹) x
        rw [h, E3.conjSubgroup_bot, conjSubgroup_conjSubgroup, inv_mul_cancel,
          conjSubgroup_one] at h2
        rw [Subgroup.commutator_comm]
        exact h2.symm
      exact hAbar2 (by
        rw [barSub_eq_bot_iff hV h.hyp125.pairFacts.le_normalizer
          h.hyp125.pairFacts.le_normalizer₀ hAM, UC22.uc22p22u_cTilde_bot]
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm_eq
        intro a ha
        refine Subgroup.mem_inf.2 ⟨hAM ha, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (Subgroup.mem_centralizer_iff.1 (hcomm_eq hv) a (hAgA ha)).symm)
    · exact eq_bot_of_no_gammaZero_offender D V₀ V p L h hx h61 h66 h127 h1114 h183 h1669
        hW0 hV0

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
