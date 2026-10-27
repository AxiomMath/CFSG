module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem521
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs2
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.Quasithin.Vol2.Ch6NatFacts
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise commutatorElement

section NatFix

theorem sl2_mul_self_eq_one_of_fix {K : Type} [Field K] (h2 : (2 : K) = 0)
    (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (hAv : A.mulVec v = v) : A * A = 1 := by
  have hz : (A - 1).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, hAv, Matrix.one_mulVec, sub_self]
  have hd : (A - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hz⟩
  rw [Matrix.det_fin_two] at hd hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by
    decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hd
  have htr : A 0 0 + A 1 1 = 0 := by linear_combination -hd + hdet + h2
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by linear_combination A 0 0 * htr - hdet - h2
  have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by linear_combination A 0 1 * htr
  have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by linear_combination A 1 0 * htr
  have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by linear_combination A 1 1 * htr - hdet - h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]

variable {G : Type} [Group G] {L W : Subgroup G} {n : ℕ}

theorem NatL2Data.two_eq_zero (D : NatL2Data L W n) : (2 : D.K) = 0 := by
  have := Fintype.ofFinite D.K
  have hn : n ≠ 0 := by
    rintro rfl
    have : Nat.card D.K = 1 := by simpa using D.card
    exact (Finite.one_lt_card (α := D.K)).ne' this
  have h := FiniteField.cast_card_eq_zero D.K
  rw [← Nat.card_eq_fintype_card, D.card] at h
  push_cast at h
  exact (pow_eq_zero_iff hn).mp h

theorem IsNatModCh5.mem_centralizer_of_fix (h : IsNatModCh5 L W n) {d w : G} (hd : d ∈ L)
    (hd3 : d ^ 3 = 1) (hw : w ∈ W) (hw1 : w ≠ 1) (hdw : d * w * d⁻¹ = w) :
    d ∈ Subgroup.centralizer (W : Set G) := by
  let D := h.data
  let g : Subgroup.normalizer (W : Set G) := ⟨d, h.1 hd⟩
  obtain ⟨A, hA⟩ := D.exists_matrix_of_mem g hd
  have hv : Multiplicative.toAdd (D.E ⟨w, hw⟩) ≠ 0 := by
    intro h0
    apply hw1
    have h1 : D.E ⟨w, hw⟩ = 1 := toAdd_eq_zero.mp h0
    have h2 : (⟨w, hw⟩ : ↥W) = 1 := (map_eq_one_iff D.E D.E.injective).mp h1
    exact congrArg Subtype.val h2
  have hgw : conjAct W g ⟨w, hw⟩ = ⟨w, hw⟩ :=
    Subtype.ext (by rw [conjAct_apply_coe]; exact hdw)
  have hAv : (A : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd (D.E ⟨w, hw⟩)) =
      Multiplicative.toAdd (D.E ⟨w, hw⟩) := by
    rw [← hA, ← D.toAdd_E_conj, hgw]
  have hA2 := sl2_mul_self_eq_one_of_fix D.two_eq_zero (A : Matrix (Fin 2) (Fin 2) D.K) A.2 hv hAv
  have key : ∀ y, (A : Matrix (Fin 2) (Fin 2) D.K).mulVec
      ((A : Matrix (Fin 2) (Fin 2) D.K).mulVec y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa [g] using hd3)
  apply D.mem_centralizer_of_conj_eq g
  intro x
  have h3 := D.conj_eq_of_mem_centralizer (g ^ 3) (by rw [hg3]; exact Subgroup.one_mem _) x
  rw [D.conj_pow, show (D.conj g)^[3] x = D.conj g (D.conj g (D.conj g x)) from rfl, hA, hA, hA,
    key] at h3
  rw [hA]
  exact h3

theorem isNatModCh5_of_isNatQuotCh5 (h : IsNatQuotCh5 L W n)
    (hC : W ⊓ Subgroup.centralizer (L : Set G) = ⊥) : IsNatModCh5 L W n := by
  obtain ⟨hLW, hc, hB⟩ := h
  refine ⟨hLW, hc, ?_⟩
  have h0 : (Subgroup.centralizer (L : Set G)).subgroupOf W = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm, hC]
  rwa [h0] at hB

end NatFix

section General

variable {G : Type} [Group G]

omit [Group G] in
theorem card_of_lieModel_L2 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 2 2 n) : Nat.card X = 2 ^ n * (4 ^ n - 1) := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have hodd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
      have : (2 ^ n - 1) % 2 = 1 := by omega
      rw [Nat.gcd_rec, this]
      rfl
    have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hodd, h4]
    simp
  all_goals exact absurd h0 (by norm_num)

theorem eq_one_of_mem_of_pow_three {P : Subgroup G} (hP : IsPGroup 2 P) {d : G} (hd : d ∈ P)
    (hd3 : d ^ 3 = 1) : d = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨d, hd⟩
  have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf d ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hd3)
  have h3 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact h2

theorem comm_of_mem_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

variable [Finite G]

theorem exists_mem_centralizer_of_isPGroup {T W : Subgroup G} (hT : IsPGroup 2 T) (hWT : W ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have : (W.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWT).mpr hTW
  have hne : W.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hW
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hWT hx⟩ : ↥T) ∈ W.subgroupOf T := hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨⟨⟨x, hxT⟩, hxW, hxZ⟩, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨x, hxW, fun h1 => hx1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
  exact (congrArg Subtype.val this)

theorem exists_mem_omegaOneCenter {T V W : Subgroup G} (hT : IsPGroup 2 T)
    (hV : IsElemAbelian 2 V) (hWV : W ≤ V) (hVT : V ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    ∃ z ∈ W, z ≠ 1 ∧ z ∈ quasithinOmegaOneCenter T := by
  obtain ⟨z, hzW, hz1, hzC⟩ := exists_mem_centralizer_of_isPGroup hT (hWV.trans hVT) hTW hW
  exact ⟨z, hzW, hz1,
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hVT (hWV hzW), hzC, hV.2 z (hWV hzW)⟩⟩

omit [Finite G] in
theorem mem_centralizerModO2_of_quotConjAut_eq_one {X : Subgroup G}
    {g : ↥(Subgroup.normalizer (X : Set G))} (hg : quotConjAut X g = 1) :
    (g : G) ∈ centralizerModO2 X :=
  ⟨g.2, normalizer_le_normalizer_pCoreOf 2 X g.2,
    fun u hu => commutator_mem_of_quotConjAut_eq_one hg ⟨u, hu⟩⟩

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem card_quot_dvd_card_autOn (h : Hyp5_0_1 G T M L n)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ Nat.card ↥(autOn L V) := by
  have hC := h.inf_centralizer_le hLV hVL
  have he : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    exact map_subtype_subgroupOf' (CFSG.Open.pCore 2 ↥L)
  rw [card_autOn_eq_relIndex hLV, ← Subgroup.index, ← he, Subgroup.relIndex]
  exact Subgroup.index_dvd_of_le fun x hx => hC hx

theorem n_eq_two_of_isBarS5 (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    (hS5 : IsBarS5 L T V) : n = 2 := by
  have hred := hV.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have h1 := h.card_quot_dvd_card_autOn hLV hV.2.2
  have h2 : Nat.card ↥(autOn L V) ∣ Nat.card ↥(autOn (L ⊔ T) V) :=
    Subgroup.card_dvd_of_le (autOn_le_autOn V le_sup_left)
  obtain ⟨e⟩ := hS5
  have h3 : Nat.card ↥(autOn (L ⊔ T) V) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  rw [card_of_lieModel_L2 (by have := h.two_le; omega) h.lie] at h1
  have hd := (h1.trans h2)
  rw [h3] at hd
  have h2n := h.two_le
  have hle : 2 ^ n * (4 ^ n - 1) ≤ 120 := Nat.le_of_dvd (by norm_num) hd
  have h7 : n < 7 := by
    by_contra hcon
    have ha : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb : 1 ≤ 4 ^ n - 1 := by
      have : 4 ≤ 4 ^ n := by
        calc 4 = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ 7 ≤ 2 ^ n * (4 ^ n - 1) := by
      calc 2 ^ 7 ≤ 2 ^ n := ha
        _ = 2 ^ n * 1 := by ring
        _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul_left _ hb
    omega
  interval_cases n
  · rfl
  all_goals norm_num at hd

theorem V_le_T (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V) : V ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hP : V ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1 (isPGroup_of_isElemAbelian hred.2.2.1)
  exact hP.trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (h.isSylowTwoOf le_sup_right))

theorem conj_ne_of_isNatModCh5 (h : Hyp5_0_1 G T M L n) {W : Subgroup G} {k : ℕ}
    (hW : IsNatModCh5 L W k) {d w : G} (hd : d ∈ L) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hw : w ∈ W) (hw1 : w ≠ 1) : d * w * d⁻¹ ≠ w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdw
  have hc := hW.mem_centralizer_of_fix hd hd3 hw hw1 hdw
  have hWne : ⁅W, L⁆ ≠ ⊥ := by
    rw [hW.commutator_eq]
    intro hb
    rw [hb, Subgroup.mem_bot] at hw
    exact hw1 hw
  have hle := h.inf_centralizer_le hW.1 hWne
  exact hd1 (eq_one_of_mem_of_pow_three (pCoreOf_isPGroup 2 L) (hle ⟨hd, hc⟩) hd3)

end Hyp5_0_1

theorem stmt5_1_19_of_inputs (h513 : Stmt5_1_3) (h515 : Stmt5_1_15) (h516 : Stmt5_1_16)
    (h518 : Stmt5_1_18) (h5114 : Stmt5_1_14_first) (hF : L2TorusFact)
    (hOrth : OrthTorusFixFact) (hA9 : L34AutNoNineFact) : Stmt5_1_19 := by
  intro G _ _ T M L V H B D n hyp hN hV hK hnot D₃ hD₃ h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  obtain ⟨hDcyc, hDcard⟩ := hh.isCyclic_card_of_isHall hF hN.2.1
  by_cases hD₃M : D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  swap
  · rcases h515 G T M L V H B D n hyp hN hV hK with h1 | h2 | h3' | h4
    · exact absurd (hD₃.trans h1) hD₃M
    · exact Or.inl ⟨hD₃M, Or.inl h2⟩
    · exact Or.inl ⟨hD₃M, Or.inr h3'⟩
    · exact Or.inr (Or.inl ⟨h4.1, h4.2.1, hD₃M⟩)
  obtain ⟨hD₃B, hZD₃⟩ := h518 G T M L V H B D n hyp hN hV hK D₃ hD₃ h3 hD₃M
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n hyp hN hV hK).2.2
  have hDB : n = 2 → D = B := by
    intro hn2
    rw [← hD₃B]
    refine (Subgroup.eq_of_le_of_card_ge hD₃ ?_).symm
    rw [hDcard, h3, hn2]
    norm_num
  obtain ⟨d, hdD₃, hd1⟩ := exists_ne_one_of_card_prime Nat.prime_three h3
  have hd3 := pow_three_of_mem_of_card_three h3 hdD₃
  have hdD : d ∈ D := hD₃ hdD₃
  have hdBorel : d ∈ borelL T L := hN.2.1.1 hdD
  have hdL : d ∈ L := hdBorel.1
  have hdfix : ∀ z ∈ quasithinOmegaOneCenter T, d * z * d⁻¹ = z := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (D₃ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZD₃ hz
    rw [Subgroup.mem_centralizer_iff.mp hzC d hdD₃, mul_assoc, mul_inv_cancel, mul_one]
  have hred := hV.isTwoReducedIn
  have hT2 : IsPGroup 2 T := hh.sylow.1
  have hVT : V ≤ T := hh.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVne : V ≠ ⊥ := by
    intro hb
    apply hV.2.2
    rw [hb, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv]
    simp
  obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl hVT hTV hVne
  rcases h513 G T M L V n hh hV with hc1 | hc2 | hc3 | hc4 | hc5
  ·
    exfalso
    obtain ⟨W₁, W₂, hLW₁, hLW₂, hinf, hsup, hN₁, hN₂⟩ := hc1
    have hW₂N : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
      intro y hy
      apply mem_normalizer_of_forall_conj_mem'
      intro x hx
      have hxV : x ∈ V := hsup ▸ Subgroup.mem_sup_left hx
      have hyV : y ∈ V := hsup ▸ Subgroup.mem_sup_right hy
      rw [comm_of_mem_of_isElemAbelian hred.2.2.1 hyV hxV, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    have hset : ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hW₂N
    have hzm : z ∈ (W₁ : Set G) * (W₂ : Set G) := by
      rw [← hset, hsup]
      exact hzV
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Set.mem_mul.mp hzm
    have hc₁ : d * w₁ * d⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hLW₁ hdL) w₁).mp hw₁
    have hc₂ : d * w₂ * d⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hLW₂ hdL) w₂).mp hw₂
    have hprod : (d * w₁ * d⁻¹) * (d * w₂ * d⁻¹) = w₁ * w₂ := by
      rw [← hdfix _ hzZ]
      group
    have hu : (w₁⁻¹ * (d * w₁ * d⁻¹)) = w₂ * (d * w₂ * d⁻¹)⁻¹ := by
      have e : w₁⁻¹ * (d * w₁ * d⁻¹) * (d * w₂ * d⁻¹) = w₂ := by
        rw [mul_assoc, hprod]
        group
      exact eq_mul_inv_of_mul_eq e
    have hmem : w₁⁻¹ * (d * w₁ * d⁻¹) ∈ W₁ ⊓ W₂ :=
      ⟨W₁.mul_mem (W₁.inv_mem hw₁) hc₁, hu ▸ W₂.mul_mem hw₂ (W₂.inv_mem hc₂)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hfix₁ : d * w₁ * d⁻¹ = w₁ := by
      have := congrArg (w₁ * ·) hmem
      simpa using this
    have hfix₂ : d * w₂ * d⁻¹ = w₂ := by
      rw [hmem] at hu
      have := congrArg (· * (d * w₂ * d⁻¹)) hu
      simp only [one_mul, inv_mul_cancel_right] at this
      exact this
    by_cases hw₁1 : w₁ = 1
    · have hw₂1 : w₂ ≠ 1 := by
        intro hw
        apply hz1
        rw [hw₁1, hw, one_mul]
      exact hh.conj_ne_of_isNatModCh5 hN₂ hdL hd3 hd1 hw₂ hw₂1 hfix₂
    · exact hh.conj_ne_of_isNatModCh5 hN₁ hdL hd3 hd1 hw₁ hw₁1 hfix₁
  ·
    exfalso
    exact hnot ⟨hc2.1, Or.inl ⟨hc2.2.1, Or.inr hc2.2.2⟩, hDB hc2.1⟩
  ·
    exfalso
    set W := ⁅V, L⁆ with hWdef
    have hWV : W ≤ V := by
      rw [hWdef, Subgroup.commutator_le]
      intro v hv l hl
      have : l * v⁻¹ * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
      have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact V.mul_mem hv this
    have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
      le_normalizer_commutator_of hTV hh.T_le_normalizer
    have hTC : T ≤ Subgroup.normalizer
        ((W ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      intro t ht
      apply mem_normalizer_of_forall_conj_mem'
      intro c hc
      obtain ⟨hcW, hcL⟩ := Subgroup.mem_inf.mp hc
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hTW ht) c).mp hcW, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : t⁻¹ * l * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hh.T_le_normalizer (T.inv_mem ht)) l).mp hl
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hcL _ hl'
      calc l * (t * c * t⁻¹) = t * ((t⁻¹ * l * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * l * t)) * t⁻¹ := by rw [hcomm]
        _ = t * c * t⁻¹ * l := by group
    have hC : W ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      by_contra hne
      obtain ⟨c, hc, hc1, hcZ⟩ :=
        exists_mem_omegaOneCenter hT2 hred.2.2.1 (inf_le_left.trans hWV) hVT hTC hne
      have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hcZ, hc.2⟩
      rw [hZL, Subgroup.mem_bot] at this
      exact hc1 this
    have hWnat := isNatModCh5_of_isNatQuotCh5 hc3 hC
    obtain ⟨z', hz'W, hz'1, hz'Z⟩ :=
      exists_mem_omegaOneCenter hT2 hred.2.2.1 hWV hVT hTW hV.2.2
    exact hh.conj_ne_of_isNatModCh5 hWnat hdL hd3 hd1 hz'W hz'1 (hdfix z' hz'Z)
  ·
    obtain ⟨m, hnm, -⟩ := id hc4
    by_cases hn2 : n = 2
    · exfalso
      exact hnot ⟨hn2, Or.inr (hn2 ▸ hc4), hDB hn2⟩
    have h2n := hh.two_le
    have hmodd : ¬ Even m := by
      intro hme
      have hS : IsSylowTwoOf (T ⊓ L) L :=
        A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left
          hh.sup_le_normalizer
      have hCV : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
        (pCoreOf_isPGroup 2 L).to_le (hh.inf_centralizer_le hLV hV.2.2)
      have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
      have hzC : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (fun x hx => hx.1)
          (quasithinOmegaOneCenter_le_inf T hzZ).2
      exact hz1 (hOrth G L V (T ⊓ L) m d z (hnm ▸ hc4) hme hS hCV hdBorel hord hzV hzC
        (hdfix z hzZ))
    have hmod : n % 4 = 2 := by
      rcases Nat.even_or_odd m with hme | ⟨k, hk⟩
      · exact absurd hme hmodd
      · omega
    have hgt : 2 < n := by omega
    have hDM : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
      rcases h515 G T M L V H B D n hyp hN hV hK with h1 | h2 | h3' | h4
      · exact h1
      · exact absurd h2.1 hn2
      · exfalso; rcases h3'.1 with h | h <;> omega
      · exfalso; rcases h4.1 with h | h <;> omega
    have h3n : ¬ 3 ∣ n := by
      intro h3n
      have h6 : 2 * 3 ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) (by omega) h3n
      obtain ⟨k, hk⟩ := h6
      have h9 : 9 ∣ Nat.card D := by
        rw [hDcard, hk, show 2 * 3 * k = 6 * k by ring, pow_mul]
        have h63 : 2 ^ 6 - 1 ∣ (2 ^ 6) ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow _ _ k
        rw [one_pow] at h63
        exact (show 9 ∣ 2 ^ 6 - 1 by norm_num).trans h63
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥D)
      have hgord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
      have hg0 : orderOf g ≠ 0 := by
        rw [hgord]
        exact Nat.card_pos.ne'
      set x := g ^ (orderOf g / 9) with hxdef
      have hxord : orderOf x = 9 := orderOf_pow_orderOf_div hg0 (hgord ▸ h9)
      have hxM : (x : G) ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hDM x.2
      let y : ↥(Subgroup.normalizer (oTwoUpper H : Set G)) := ⟨x, hxM⟩
      have hy9 : quotConjAut (oTwoUpper H) y ^ 9 = 1 := by
        rw [← map_pow]
        have : y ^ 9 = 1 := by
          apply Subtype.ext
          simp only [y, Subgroup.coe_pow, Subgroup.coe_one]
          have := pow_orderOf_eq_one x
          rw [hxord] at this
          exact congrArg Subtype.val this
        rw [this, map_one]
      have hy3 := hA9 _ hK _ hy9
      rw [← map_pow] at hy3
      have hmem := mem_centralizerModO2_of_quotConjAut_eq_one hy3
      have hx3 : orderOf ((x : G) ^ 3) = 3 := by
        rw [orderOf_pow' _ (by norm_num), Subgroup.orderOf_coe, hxord]
        norm_num
      have hdvd : 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) := by
        have := orderOf_dvd_natCard (⟨(x : G) ^ 3, by simpa [y] using hmem⟩ :
          ↥(centralizerModO2 (oTwoUpper H)))
        rwa [Subgroup.orderOf_mk, hx3] at this
      exact (h516 G T M L V H B D n hyp hN hV hK).1 hdvd
    exact Or.inr (Or.inr ⟨hmod, hgt, h3n, hD₃B, hD₃M, hc4⟩)
  ·
    exfalso
    obtain ⟨⟨-, hsplit⟩, hS5, hmod⟩ := hc5
    have hn2 := hh.n_eq_two_of_isBarS5 hV hS5
    have hCV : V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hcV, hcC⟩
      have hcT : c ∈ Subgroup.centralizer (T : Set G) :=
        Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_right hx) hcC
      have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx) hcC
      have hcZ : c ∈ quasithinOmegaOneCenter T :=
        mem_quasithinOmegaOneCenter_iff.mpr ⟨hVT hcV, hcT, hred.2.2.1.2 c hcV⟩
      have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hcZ, hcL⟩
      rwa [hZL] at this
    rw [hCV, sup_bot_eq] at hsplit
    rw [hsplit] at hmod
    exact hnot ⟨hn2, Or.inl ⟨hS5, Or.inl hmod⟩, hDB hn2⟩

end CFSG.Quasithin.H13
