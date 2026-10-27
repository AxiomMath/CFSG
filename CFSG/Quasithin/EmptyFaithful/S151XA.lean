module

public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Ctx15128 (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) : Prop where
  ctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂
  h17 : Lemma15117Concl T M Z₁
  h18 : Lemma15118Concl T Mc M Z₁
  h19 : Lemma15119Used T Mc M Z₁ V₂
  hL : IsL1519 Mc Z₁ L
  h22 : Lemma15122Concl T Mc M Z₁ L
  h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L
  h25 : Lemma15125Concl T Z₁ V₁ L
  h26 : Lemma15126Concl L
  h27 : Lemma15127Concl Z₂ L

structure Ctx15129 (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) : Prop where
  base : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L
  h28 : Lemma15128Concl T Mc Z₁ Z₂ L

@[expose] def IsSFlag (S U : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) : Prop :=
  Nat.card ↥U = 2 ^ n ∧ ∀ k : ℕ, 1 ≤ k → k < n → W k ≤ U ∧ Nat.card ↥(W k) = 2 ^ k ∧
    S ≤ Subgroup.normalizer (W k : Set G) ∧ (k + 1 < n → W k ≤ W (k + 1))

@[expose] def flagParab (X : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) (i : ℕ) : Subgroup G :=
  X ⊓ ⨅ j ∈ {j : ℕ | 1 ≤ j ∧ j < n ∧ j ≠ i}, Subgroup.normalizer (W j : Set G)

omit [Finite G] in
theorem flagParab_le (X : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) (i : ℕ) :
    flagParab X n W i ≤ X := inf_le_left

structure FlagData15129 (T Mc M Z₁ Z₂ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) : Prop where
  four : Ce15Four T Mc M
  n_eq : n = 4 ∨ n = 5
  normalizes : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)
  flag : IsSFlag (s1516 T Z₁) (uLOf1527 Z₂ L) n W
  w1 : W 1 = zUOf1528 Z₂ L
  w2 : W 2 = V₂

@[expose] def pPar15129 (T Z₁ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) (i : ℕ) : Subgroup G :=
  flagParab (L ⊔ s1516 T Z₁) n W i

@[expose] def kPar15129 (T Z₁ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) : Subgroup G :=
  oTwoUpper (pPar15129 T Z₁ L n W 1) ⊔ oTwoUpper (pPar15129 T Z₁ L n W 2)

@[expose] def Input15129CaseFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Four T Mc M

@[expose] def Input15129Flag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Four T Mc M →
    ∃ (n : ℕ) (W : ℕ → Subgroup G), FlagData15129 T Mc M Z₁ Z₂ V₂ L n W

@[expose] def Input15129ZDiagonal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Six T Mc M 3 → Nat.card (quasithinOmegaOneCenter T) = 4

@[expose] def Input15129ZOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → Nat.card (quasithinOmegaOneCenter T) = 2

theorem caseFour15129_of (nZD : Input15129ZDiagonal) (nZO : Input15129ZOrder) :
    Input15129CaseFour := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc
  rcases hc.base.h24.one with h | h
  · exact h
  · exfalso
    have h1 := nZD G T Mc M Z₁ Z₂ V₁ V₂ L hc h
    have h2 := nZO G T Mc M Z₁ Z₂ V₁ V₂ L hc
    omega

theorem s_le_normalizer_v2_15129 {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (hsmall : Ce15Small T Mc M) (h7 : ¬ Ce15Seven T Mc M) :
    s1516 T Z₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hno
    have hTS : T ≤ s1516 T Z₁ := fun y hy => by
      by_contra hy'
      exact hno ⟨y, hy, hy'⟩
    have h1 : (s1516 T Z₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hTS
    have h2 := hS.index_two hsmall h7
    omega
  intro s hs
  have hsT : s ∈ T := s1516_le T Z₁ hs
  have htsT : t * s ∈ T := T.mul_mem htT hsT
  have htsS : t * s ∉ s1516 T Z₁ := fun h => htS (by
    simpa using (s1516 T Z₁).mul_mem h ((s1516 T Z₁).inv_mem hs))
  have h1 := hS.swap_small hsmall h7 t htT htS
  have h2 := hS.swap_small hsmall h7 (t * s) htsT htsS
  rw [conjByElt_mul1516] at h2
  have h3 : conjByElt s V₂ = V₂ := conjByElt_injective1516 t (h2.trans h1.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3

omit [Finite G] in
private theorem commutator_le_of_index_two15129 {V₂ Z₂ Y : Subgroup G}
    (hidx : (Z₂.subgroupOf V₂).index = 2) (hYV : Y ≤ Subgroup.normalizer (V₂ : Set G))
    (hYZ : Y ≤ Subgroup.normalizer (Z₂ : Set G)) : ⁅V₂, Y⁆ ≤ Z₂ := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨v, hv, y, hy, rfl⟩
  have hw : y * v * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hYV hy) v).mp hv
  have hiff : v ∈ Z₂ ↔ y * v * y⁻¹ ∈ Z₂ := Subgroup.mem_normalizer_iff.mp (hYZ hy) v
  have hab : (⟨v, hv⟩ : ↥V₂) * (⟨y * v * y⁻¹, hw⟩ : ↥V₂)⁻¹ ∈ Z₂.subgroupOf V₂ := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
    exact hiff
  have hab' : v * (y * v * y⁻¹)⁻¹ ∈ Z₂ := hab
  have hc : ⁅v, y⁆ = v * (y * v * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  show ⁅v, y⁆ ∈ Z₂
  rw [hc]
  exact hab'

private theorem conjClosure_eq_of_commutator15129 {Y V₂ Z₂ : Subgroup G} (hZV : Z₂ ≤ V₂)
    (hV2c : Nat.card V₂ = 4) (hZ2c : Nat.card Z₂ = 2)
    (hYV : Y ≤ Subgroup.normalizer (V₂ : Set G)) (hcomm : ⁅V₂, Y⁆ = V₂) :
    conjClosure Z₂ Y = V₂ := by
  have hXV : conjClosure Z₂ Y ≤ V₂ := conjClosure_le fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.mp (hYV hh) z).mp (hZV hz)
  have hZX : Z₂ ≤ conjClosure Z₂ Y := le_conjClosure Z₂ Y
  by_contra hne
  have hXc : Nat.card ↥(conjClosure Z₂ Y) = 2 := by
    have hdvd1 : Nat.card ↥(conjClosure Z₂ Y) ∣ 4 := by
      have := Subgroup.card_dvd_of_le hXV
      rwa [hV2c] at this
    have hdvd2 : 2 ∣ Nat.card ↥(conjClosure Z₂ Y) := by
      have := Subgroup.card_dvd_of_le hZX
      rwa [hZ2c] at this
    have hle4 : Nat.card ↥(conjClosure Z₂ Y) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd1
    have hne4 : Nat.card ↥(conjClosure Z₂ Y) ≠ 4 := fun h4 =>
      hne (Subgroup.eq_of_le_of_card_ge hXV (by rw [h4, hV2c]))
    have hpos : 0 < Nat.card ↥(conjClosure Z₂ Y) := Nat.card_pos
    omega
  have hXZ : conjClosure Z₂ Y = Z₂ :=
    (Subgroup.eq_of_le_of_card_ge hZX (by rw [hXc, hZ2c])).symm
  have hYZ : Y ≤ Subgroup.normalizer (Z₂ : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have := mem_conjClosure hy hz
      rwa [hXZ] at this
    · intro hz
      have := mem_conjClosure (Y.inv_mem hy) hz
      rw [hXZ] at this
      simpa [mul_assoc] using this
  have hidx : (Z₂.subgroupOf V₂).index = 2 := by
    have h1 := Subgroup.card_mul_index (Z₂.subgroupOf V₂)
    have h2 : Nat.card ↥(Z₂.subgroupOf V₂) = 2 := by
      rw [← hZ2c]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
    rw [h2, hV2c] at h1
    omega
  have hle := commutator_le_of_index_two15129 hidx hYV hYZ
  rw [hcomm] at hle
  have h4 := Subgroup.card_le_of_le hle
  omega

theorem v2UL15129 :
    ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
      Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Four T Mc M → V₂ ≤ uLOf1527 Z₂ L := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hfour
  have hS := hc.base.ctx.setting
  have h7 : ¬ Ce15Seven T Mc M := not_seven_of_four_or_six (Or.inl hfour)
  obtain ⟨⟨-, -, hYcomm, hYN⟩, -⟩ := hS.y_facts (Or.inl hfour)
  obtain ⟨-, hV2c, -, hZ2c⟩ := hS.ranks_four hfour
  have hZV : Z₂ ≤ V₂ := hS.z2_le_v2 h7
  have hYL : oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ L :=
    (oPrimeResidualOf_mono1516 3 (inf_le_right : M ⊓ g1_1516 Z₁ ≤ g1_1516 Z₁)).trans
      hc.base.h25.one.symm.le
  have hX := conjClosure_eq_of_commutator15129 hZV hV2c hZ2c hYN hYcomm
  have hV2U : V₂ ≤ uOf1527 Z₂ L := by
    rw [← hX]
    exact conjClosure_le fun h hh z hz => mem_conjClosure (hYL hh) hz
  unfold uLOf1527
  calc V₂ = ⁅V₂, oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁)⁆ := hYcomm.symm
    _ ≤ ⁅uOf1527 Z₂ L, L⁆ := Subgroup.commutator_mono hV2U hYL

@[expose] def Input15129FlagLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S UL : Subgroup G), IsNaturalUL L UL →
    S ≤ Subgroup.normalizer (L : Set G) → S ≤ Subgroup.normalizer (UL : Set G) → IsPGroup 2 S →
    IsSylowTwoOf (S ⊓ L) L →
    ∃ (n : ℕ) (W : ℕ → Subgroup G), (n = 4 ∨ n = 5) ∧ IsSFlag S UL n W ∧
      ∀ k : ℕ, 1 ≤ k → k < n → ∀ X : Subgroup G, X ≤ UL → S ≤ Subgroup.normalizer (X : Set G) →
        Nat.card ↥X = 2 ^ k → X = W k

omit [Finite G] in
private theorem le_normalizer_conjClosure_of_le15129 {Z H X : Subgroup G}
    (hZ : X ≤ Subgroup.normalizer (Z : Set G)) (hH : X ≤ Subgroup.normalizer (H : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ conjClosure Z H, x * y * x⁻¹ ∈ conjClosure Z H := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hy
      have h1 : x * h * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hH hx) h).mp hh
      have h2 : x * z * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ hx) z).mp hz
      have := mem_conjClosure h1 h2
      simpa [mul_assoc] using this
    | one => simp
    | mul y y' _ _ ihy ihy' => simpa [mul_assoc] using (conjClosure Z H).mul_mem ihy ihy'
    | inv y _ ih => simpa [mul_assoc] using (conjClosure Z H).inv_mem ih
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this

omit [Finite G] in
private theorem le_normalizer_commutator_of_le15129 {A B X : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hA' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx)
  have hB' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)
  rw [Subgroup.map_commutator, hA', hB']

theorem flag15129_of (nFL : Input15129FlagLocal) : Input15129Flag := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hfour
  have hV2UL := v2UL15129 G T Mc M Z₁ Z₂ V₁ V₂ L hc hfour
  have hq := hc.base.ctx.qtfe
  have hM := hc.base.ctx.mf
  have hS := hc.base.ctx.setting
  have hSV2 := s_le_normalizer_v2_15129 hS (Or.inl hfour) (not_seven_of_four_or_six (Or.inl hfour))
  have hL1520 : IsL1520 T Mc Z₁ L :=
    hc.base.hL.isL1520 hc.base.h18.four (hS.pCore_g1_ne_bot hq hM)
  have hSylL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.base.h18.four hL1520
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have h := normalizer_le_normalizer_oPrimeResidualOf1516 3 (g1_1516 Z₁)
    rw [← hc.base.h25.one] at h
    exact (s1516_le_g1 T Z₁).trans (Subgroup.le_normalizer.trans h)
  have h7 : ¬ Ce15Seven T Mc M := not_seven_of_four_or_six (Or.inl hfour)
  have hdiag := (hS.diagonal (Or.inl hfour) h7).2
  have hSZ2 : s1516 T Z₁ ≤ Subgroup.normalizer (Z₂ : Set G) := by
    intro x hx
    have hx' : x ∈ T ⊓ Subgroup.centralizer (Z₂ : Set G) := by rw [← hdiag]; exact hx
    exact Subgroup.centralizer_le_normalizer _ hx'.2
  have hSU : s1516 T Z₁ ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G) :=
    le_normalizer_conjClosure_of_le15129 hSZ2 hSN
  have hSCL : s1516 T Z₁ ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    hSN.trans (normalizer_le_normalizer_centralizer L)
  have hSUC : s1516 T Z₁ ≤
      Subgroup.normalizer ((uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hSU hx, hSCL hx⟩
  have hSUL : s1516 T Z₁ ≤ Subgroup.normalizer (uLOf1527 Z₂ L : Set G) :=
    le_normalizer_commutator_of_le15129 hSU hSN
  have hSZU : s1516 T Z₁ ≤ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) := by
    unfold zUOf1528
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hSZ2 hx, hSUC hx⟩, hSUL hx⟩
  obtain ⟨n, W, hn, hflag, huniq⟩ := nFL G L (s1516 T Z₁) (uLOf1527 Z₂ L) hc.h28.1 hSN hSUL
    hc.base.h18.four.2.1 hSylL
  refine ⟨n, W, ⟨hfour, hn, hSN, hflag, ?_, ?_⟩⟩
  · have hZU : Nat.card ↥(zUOf1528 Z₂ L) = 2 ^ 1 := by simpa using hc.h28.2.1
    have hle : zUOf1528 Z₂ L ≤ uLOf1527 Z₂ L := by unfold zUOf1528; exact inf_le_right
    exact (huniq 1 le_rfl (by rcases hn with h | h <;> omega) (zUOf1528 Z₂ L) hle hSZU hZU).symm
  · have h4 : Nat.card ↥V₂ = 2 ^ 2 := by simpa using (hS.ranks_four hfour).2.1
    exact (huniq 2 (by omega) (by rcases hn with h | h <;> omega) V₂ hV2UL hSV2 h4).symm

@[expose] def Input15129P0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    ¬ pPar15129 T Z₁ L n W 1 ≤ Subgroup.normalizer (W 1 : Set G) ∧
      pCoreOf 2 (pPar15129 T Z₁ L n W 1) = s1516 T Z₁ ⊓ Subgroup.centralizer (V₂ : Set G) ∧
      oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ oPrimeResidualOf 3 (pPar15129 T Z₁ L n W 1)

@[expose] def Input15129CS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Four T Mc M →
    s1516 T Z₁ ⊓ Subgroup.centralizer (V₂ : Set G) = T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)

omit [Finite G] in
private theorem conjAct_coe15129 (W : Subgroup G) (g : Subgroup.normalizer (W : Set G)) (w : W) :
    ((conjAct W g w : W) : G) = g * w * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl g) w

theorem cs15129 : Input15129CS := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hfour
  have hM := hc.base.ctx.mf
  have hS := hc.base.ctx.setting
  have h7 : ¬ Ce15Seven T Mc M := not_seven_of_four_or_six (Or.inl hfour)
  have hsmall : Ce15Small T Mc M := Or.inl hfour
  have hTM : T ≤ M := hM.1.1.2
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans (le_normalizer_V154 T Mc M)
  have hZ1V : Z₁ ≤ V154 T Mc M := hS.z1_le.trans inf_le_left
  have hV2V : V₂ ≤ V154 T Mc M := hS.v2_le
  apply le_antisymm
  · rintro x ⟨hxS, hxV2⟩
    have hxT : x ∈ T := s1516_le T Z₁ hxS
    refine ⟨hxT, ?_⟩
    obtain ⟨-, -, hsup, -⟩ := hS.decomp_other h7
    obtain ⟨e⟩ := hfour.2.2
    have hcomm : ∀ a b : G, a ∈ T → b ∈ T → ∀ v : G, v ∈ V154 T Mc M →
        a * (b * v * b⁻¹) * a⁻¹ = b * (a * v * a⁻¹) * b⁻¹ := by
      intro a b ha hb v hv
      have hpa : conjAct (V154 T Mc M) ⟨a, hTN ha⟩ ∈ autOn T (V154 T Mc M) :=
        Subgroup.mem_map.mpr ⟨⟨a, hTN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have hpb : conjAct (V154 T Mc M) ⟨b, hTN hb⟩ ∈ autOn T (V154 T Mc M) :=
        Subgroup.mem_map.mpr ⟨⟨b, hTN hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      have h1 : (⟨_, hpa⟩ * ⟨_, hpb⟩ : ↥(autOn T (V154 T Mc M))) = ⟨_, hpb⟩ * ⟨_, hpa⟩ := by
        apply e.injective
        rw [map_mul, map_mul]
        exact mul_comm _ _
      have h2 : conjAct (V154 T Mc M) ⟨a, hTN ha⟩ * conjAct (V154 T Mc M) ⟨b, hTN hb⟩ =
          conjAct (V154 T Mc M) ⟨b, hTN hb⟩ * conjAct (V154 T Mc M) ⟨a, hTN ha⟩ :=
        congrArg Subtype.val h1
      have h3 := congrArg (fun p : MulAut ↥(V154 T Mc M) => ((p ⟨v, hv⟩ : ↥(V154 T Mc M)) : G)) h2
      simpa [MulAut.mul_apply, conjAct_coe15129] using h3
    obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
      by_contra hno
      have hTS : T ≤ s1516 T Z₁ := fun y hy => by
        by_contra hy'
        exact hno ⟨y, hy, hy'⟩
      have h1 : (s1516 T Z₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hTS
      have h2 := hS.index_two hsmall h7
      omega
    have hswap := hS.swap_small hsmall h7 t htT htS
    have hxV1 : ∀ u ∈ V₁, u ∈ Subgroup.centralizer ({x} : Set G) := by
      intro u hu
      rw [← hswap] at hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      have hxv : x * v * x⁻¹ = v := by
        have := Subgroup.mem_centralizer_iff.mp hxV2 v hv
        rw [← this]; group
      have h1 := hcomm x t hxT htT v (hV2V hv)
      rw [hxv] at h1
      have hmem : t * v * t⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc t * v * t⁻¹ * x = (x * (t * v * t⁻¹) * x⁻¹) * x := by rw [h1]
          _ = x * (t * v * t⁻¹) := by group
      exact hmem
    have hxV2' : ∀ v ∈ V₂, v ∈ Subgroup.centralizer ({x} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxV2 v hv
    have hle : V154 T Mc M ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hsup]
      exact sup_le (fun u hu => hxV1 u hu) (fun v hv => hxV2' v hv)
    show x ∈ Subgroup.centralizer (V154 T Mc M : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  · rintro x ⟨hxT, hxV⟩
    have hxZ1 : x ∈ Subgroup.centralizer (Z₁ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ1V) hxV
    exact ⟨⟨hxT, hxZ1⟩, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV2V) hxV⟩

@[expose] def Input15129EndNode : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    ∀ t ∈ T, conjByElt t (oTwoUpper (pPar15129 T Z₁ L n W 2)) = oTwoUpper (pPar15129 T Z₁ L n W 2) ∨
      conjByElt t (oTwoUpper (pPar15129 T Z₁ L n W 2)) = oTwoUpper (pPar15129 T Z₁ L n W (n - 1))

@[expose] def Input15129Rank2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    pCoreOf 2 (oTwoUpper (pPar15129 T Z₁ L n W (n - 1))) ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 1) ∧
      ¬ pCoreOf 2 (oTwoUpper (pPar15129 T Z₁ L n W 2)) ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 1) ∧
      perfectCore (kPar15129 T Z₁ L n W) = kPar15129 T Z₁ L n W

@[expose] def Input15129MSHyp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    (∀ C : Subgroup G, C ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 2) → C ≠ ⊥ →
        (C.subgroupOf (pCoreOf 2 (pPar15129 T Z₁ L n W 2))).Characteristic →
        ¬ kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2) ≤ Subgroup.normalizer (C : Set G)) →
    IsMSPair (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
        (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) ∧
      kPar15129 T Z₁ L n W ∈ cComp (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2)) ∧
      ((kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2) : Subgroup G) : Set G) =
        (kPar15129 T Z₁ L n W : Set G) * (pCoreOf 2 (pPar15129 T Z₁ L n W 2) : Set G) ∧
      ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥(kPar15129 T Z₁ L n W) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ^ m ∧ IsModO2Surj (kPar15129 T Z₁ L n W) α

@[expose] def Input15129MFrattini : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    ∀ m ∈ M, ∃ x ∈ T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1),
      ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G), m = x * c

end CFSG.Quasithin
