module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowS5
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Proof
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowMain

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped IsMulCommutative

theorem card_of_isSylowTwoOf_l2 {G : Type} [Group G] [Finite G] {A K : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (hA : IsSylowTwoOf A K) :
    Nat.card A = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAK, hA2, hidx⟩ := hA
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
  have h := (A.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hk, hK] at h
  have hodd : Odd (A.subgroupOf K).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
  rw [hk, (two_pow_mul_odd_inj hodd (odd_two_pow_pow_sub_one hn (by norm_num)) h).1]

namespace LowData

variable {V : Type} [CommGroup V] [Finite V] {X K A : Subgroup (MulAut V)} {I : Subgroup V}
  {n : ℕ}

theorem sum_of_two (hF : L2FFModuleFact) (h42 : AsB42) (d : LowData V X K A I n) :
    (∃ W₁ W₂ : Subgroup V, (∀ k ∈ K, ∀ w ∈ W₁, k w ∈ W₁) ∧ (∀ k ∈ K, ∀ w ∈ W₂, k w ∈ W₂) ∧
      W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ ∧ BinaryNaturalSL K W₁ ⊥ 2 n ∧
        BinaryNaturalSL K W₂ ⊥ 2 n) ∨
    (n = 2 ∧ Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧
      ∃ W₁ W₂ : Subgroup V, (∀ x ∈ X, ∀ w ∈ W₁, x w ∈ W₁) ∧ (∀ x ∈ X, ∀ w ∈ W₂, x w ∈ W₂) ∧
        W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ ∧ SymmetricNatural X W₁ ⊥ 5 ∧
          SymmetricNatural X W₂ ⊥ 5) := by
  have h := d.set
  have hn1 : 1 ≤ n := by have := h.two_le; omega
  obtain ⟨hAX, -, hA2⟩ := d.isA2
  rcases nat_or_s5 hF h42 d with ⟨hI, hQ, hS⟩ | ⟨hn2, hX, hI, hQ, hAK, hAI⟩
  · left
    have hAc := card_of_isSylowTwoOf_l2 hn1 h.card hS
    have hrk : rk A = n := by
      have h1 := card_eq_two_pow_of_isPGroup hA2.isPGroup
      rw [hAc] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm
    have hr : rkIdx (fixV A) ≤ 2 * n := by
      rw [← hrk]
      exact d.r
    exact nat_sum_of_nat_nat h.sq hn1 d.fix hS.1 hA2 hAc hr hI hQ
  · right
    have hK60 : Nat.card K = 60 := by
      have h60 := h.card
      rw [hn2] at h60
      simpa using h60
    exact ⟨hn2, hX, s5_sum_of_s5_s5 h.sq h.le h.normal hK60 hX hI hQ hAX hA2 hAK hAI d.r⟩

end LowData

section Map

variable {G : Type} [Group G] {Y V : Subgroup G}

theorem realizes_map_subtype [IsMulCommutative ↥V] {D : FFModel}
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) {W : Subgroup ↥V}
    [IsMulCommutative ↥(W.map V.subtype)] (hW : ∀ k ∈ autOn Y V, ∀ w ∈ W, k w ∈ W)
    (h : D.Realizes (autOn Y V) W ⊥) : D.Realizes (autOn Y (W.map V.subtype)) ⊤ ⊥ := by
  have hsub : (W.map V.subtype).subgroupOf V = W :=
    Subgroup.comap_map_eq_self_of_injective V.subtype_injective W
  rw [← hsub] at h
  exact FFModel.Realizes.restrict hYV (le_normalizer_map_of_invariant hYV hW)
    (Subgroup.map_subtype_le W) h

end Map

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem l2Set [IsMulCommutative ↥V] (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V) :
    L2Set ↥V (autOn (L ⊔ T) V) (autOn L V) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hYV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hYV
  have hVL : ⁅V, L⁆ ≠ ⊥ := hV.2.2
  have hn := InternalSec.autOn_normal_of (U := V) h.sup_le_normalizer
  obtain ⟨eLV⟩ := h.nonempty_autOn_equiv_of_le hV le_rfl hYV hVL
  obtain ⟨eL⟩ := nonempty_equiv_psl_of_lieModel (by have := h.two_le; omega) h.lie
  have hsimple : IsSimpleGroup ↥(autOn L V) := by
    have := h.isSimple
    exact eLV.isSimpleGroup
  refine ⟨fun v => Subtype.ext (by simpa using hVel.2 v v.2), h.two_le,
    InternalSec.autOn_le_autOn_of_le le_sup_left, ?_, ?_,
    h.pCoreOf_autOn_eq_bot_of_le hV le_rfl hYV hVL, ⟨eLV.trans eL⟩, ?_,
    h.isQuasisimple_autOn_of_le hV le_rfl hYV hVL, h.sqtkGroup_autOn_of_le hV le_rfl hYV hVL,
    hsimple⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hn x hx k
    · intro hk
      have := hn x⁻¹ ((autOn (L ⊔ T) V).inv_mem hx) _ hk
      simpa [mul_assoc] using this
  · refine InternalSec.autOn_two_of hLV fun y hy => ?_
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 h.T_le_normalizer y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  · rw [Nat.card_congr eLV.toEquiv]
    exact h.card_quot

end Hyp5_0_1

theorem stmt5_1_3_low_of (hF : L2FFModuleFact) (h42 : AsB42) : Stmt5_1_3_low := by
  intro G _ _ T M L V I n h hV _ hC hq hI hTI hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hYV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hYV
  let _ : IsMulCommutative ↥V := hVel.1
  set X := autOn (L ⊔ T) V
  set K := autOn L V with hKdef
  have hset : L2Set ↥V X K n := h.l2Set hV
  have hfix : fixV K = ⊥ := by
    rw [hKdef, fixV_autOn hLV, eq_bot_iff]
    intro v hv
    have : (v : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv⟩
    rw [hC, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hq' : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) := by exact_mod_cast hq
  obtain ⟨A, hA, -, hrA⟩ := kq_le_iff.mp hq'
  have hr : rkIdx (fixV A) ≤ 2 * rk A := by
    have h1 := hA.rAV_mul
    have h2 : (rkIdx (fixV A) : ℚ) ≤ 2 * rk A := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_right hrA (Nat.cast_nonneg _)
    exact_mod_cast h2
  have hIV : I ≤ V := hI.1
  have hLI : L ≤ Subgroup.normalizer (I : Set G) := hI.2.2.1
  have hI'map : (I.subgroupOf V).map V.subtype = I := Subgroup.map_subgroupOf_eq_of_le hIV
  have hVLV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hcommV : commV K = ⁅V, L⁆.subgroupOf V := by
    apply Subgroup.map_injective V.subtype_injective
    rw [hKdef, map_commV_autOn hLV, Subgroup.map_subgroupOf_eq_of_le hVLV]
  have hIC : I ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    le_bot_iff.mp (hC ▸ inf_le_inf_right _ hIV)
  have hd : LowData ↥V X K A (I.subgroupOf V) n := by
    refine ⟨hset, hfix, hA, hr, ?_, ?_, ?_, ?_, ?_⟩
    ·
      have hY : L ⊔ T ≤ Subgroup.normalizer ((V ⊓ I : Subgroup G) : Set G) := by
        rw [inf_eq_right.mpr hIV]
        exact sup_le hLI hTI
      exact InternalSec.autOn_le_stabSub hY
    ·
      intro J hJ _ hJI
      have hJmap : J.map V.subtype ≤ I := by
        rw [← hI'map]
        exact Subgroup.map_mono hJI
      rcases hI.2.2.2.2.2.1 (J.map V.subtype) (by rw [hIC]; exact bot_le) hJmap
          (le_normalizer_map_of_invariant hLV hJ) with h1 | h1
      · left
        rw [hIC] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective J V.subtype_injective).mp h1
      · right
        rw [← Subgroup.comap_map_eq_self_of_injective V.subtype_injective J, h1]
        rfl
    ·
      intro h1
      apply hI.2.1
      rw [← hI'map, h1, Subgroup.map_bot]
    ·
      have hIL : I ≤ ⁅V, L⁆ :=
        calc I = ⁅I, L⁆ := hI.2.2.2.1.symm
          _ ≤ ⁅V, L⁆ := Subgroup.commutator_mono hIV le_rfl
      rw [hcommV]
      exact Subgroup.comap_mono hIL
    ·
      intro h1
      apply hIU
      rw [← hI'map, h1, hcommV, Subgroup.map_subgroupOf_eq_of_le hVLV]
  have hinf : ∀ W₁ W₂ : Subgroup ↥V, W₁ ⊓ W₂ = ⊥ →
      W₁.map V.subtype ⊓ W₂.map V.subtype = ⊥ := by
    intro W₁ W₂ h12
    rw [← Subgroup.map_inf_eq _ _ _ V.subtype_injective, h12, Subgroup.map_bot]
  have hsup : ∀ W₁ W₂ : Subgroup ↥V, W₁ ⊔ W₂ = ⊤ → W₁.map V.subtype ⊔ W₂.map V.subtype = V := by
    intro W₁ W₂ h12
    rw [← Subgroup.map_sup, h12, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rcases hd.sum_of_two hF h42 with ⟨W₁, W₂, h1, h2, h12, h12', hW₁, hW₂⟩ |
      ⟨hn2, hX, W₁, W₂, h1, h2, h12, h12', hW₁, hW₂⟩
  ·
    left
    have hW : ∀ W : Subgroup ↥V, (∀ k ∈ K, ∀ w ∈ W, k w ∈ W) → BinaryNaturalSL K W ⊥ 2 n →
        IsNatModCh5 L (W.map V.subtype) n := by
      intro W hWK hnat
      obtain ⟨F, _, _, hFc, hR⟩ := hnat
      let hWc : IsMulCommutative ↥(W.map V.subtype) :=
        (isElemAbelian_mono hVel (Subgroup.map_subtype_le W)).1
      exact ⟨le_normalizer_map_of_invariant hLV hWK, hWc, F, inferInstance, inferInstance, hFc,
        realizes_map_subtype hLV hWK hR⟩
    exact ⟨W₁.map V.subtype, W₂.map V.subtype, le_normalizer_map_of_invariant hLV h1,
      le_normalizer_map_of_invariant hLV h2, hinf W₁ W₂ h12, hsup W₁ W₂ h12', hW W₁ h1 hW₁,
      hW W₂ h2 hW₂⟩
  ·
    right
    have hW : ∀ W : Subgroup ↥V, (∀ x ∈ X, ∀ w ∈ W, x w ∈ W) → SymmetricNatural X W ⊥ 5 →
        IsS5ModCh5 L T (W.map V.subtype) := by
      intro W hWX hsym
      let hWc : IsMulCommutative ↥(W.map V.subtype) :=
        (isElemAbelian_mono hVel (Subgroup.map_subtype_le W)).1
      exact ⟨le_normalizer_map_of_invariant hYV hWX, hWc, realizes_map_subtype hYV hWX hsym⟩
    exact ⟨hn2, hX, W₁.map V.subtype, W₂.map V.subtype, le_normalizer_map_of_invariant hYV h1,
      le_normalizer_map_of_invariant hYV h2, hinf W₁ W₂ h12, hsup W₁ W₂ h12', hW W₁ h1 hW₁,
      hW W₂ h2 hW₂⟩

theorem stmt5_1_3_qhat_of_asB51
    (hD : D310L2Fact) (hF : Vol2.Ch10.SecA.Facts10_1) (h45 : AsB45)
    (h16 : ASInputs.AS_I_1_6) (h51 : AsB51) (h42 : AsB42) : Stmt5_1_3_qhat :=
  stmt5_1_3_qhat_of hD hF h45 h16 (stmt5_1_3_low_of (l2FFModuleFact_of h51) h42)

end CFSG.Quasithin.H13
