module

public import CFSG.Quasithin.Background.E3Offender
public import CFSG.Quasithin.Background.E3Transport

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section ValHom

variable {G : Type u} [Group G] {V : Subgroup G}

@[expose] def valHom (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem valHom_apply (hV : IsElemAbelian 2 V) (v : IntMod V hV) : valHom hV v = v.val := rfl

theorem valHom_injective (hV : IsElemAbelian 2 V) : Function.Injective (valHom hV) :=
  fun _ _ h => IntMod.val_injective h

theorem map_valHom_le (hV : IsElemAbelian 2 V) (W : Subgroup (IntMod V hV)) :
    W.map (valHom hV) ≤ V := by
  rintro _ ⟨w, -, rfl⟩
  exact w.val_mem

theorem mem_fixV_iff_preI (hV : IsElemAbelian 2 V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) {X : Subgroup (MulAut (IntMod V hV))}
    (hX : X ≤ autI hV A) (v : IntMod V hV) :
    v ∈ fixV X ↔ v.val ∈ Subgroup.centralizer (preI hV A hAN X : Set G) := by
  have hpre : autI hV (preI hV A hAN X) = X := autI_preI hV hX
  conv_lhs => rw [← hpre]
  exact mem_fixV_autI hV ((preI_le hV).trans hAN) v

end ValHom

section Offender2

variable {G : Type u} [Group G] [Finite G] {V T : Subgroup G}

theorem rkIdx_eq_mQuot_map (hV : IsElemAbelian 2 V) (W : Subgroup (IntMod V hV)) :
    rkIdx W = mQuot V (W.map (valHom hV)) := by
  unfold rkIdx mQuot
  congr 1
  have h1 := Subgroup.card_mul_index W
  have h2 := Subgroup.relIndex_mul_card (H := W.map (valHom hV)) (K := V)
  rw [inf_eq_left.2 (map_valHom_le hV W),
    Subgroup.card_map_of_injective (valHom_injective hV)] at h2
  have hpos : 0 < Nat.card W := Nat.card_pos
  have h3 : Nat.card (IntMod V hV) = Nat.card V := rfl
  rw [h3] at h1
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, mul_comm]
  exact h2.symm

theorem e3_32 (hV : IsElemAbelian 2 V) {g : G} (hg : IsWOffenderAt T V g) {k : ℕ}
    (hk : (k : ℕ∞) + wParam T V + 1 ≤ rParam V) :
    (gammaCheck k (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map
        (valHom hV) ≤ V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hAN : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (V : Set G) := inf_le_right
  have hVg2 : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  rw [Subgroup.map_le_iff_le_comap]
  unfold gammaCheck
  refine iSup_le fun X => iSup_le fun hX => iSup_le fun hXk => ?_
  intro v hv
  rw [Subgroup.mem_comap, valHom_apply]
  refine Subgroup.mem_inf.2 ⟨v.val_mem, ?_⟩
  by_contra hvN
  have hBA : preI hV _ hAN X ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) := preI_le hV
  have hC : ¬ V ⊓ Subgroup.centralizer (preI hV _ hAN X : Set G) ≤
      Subgroup.normalizer (conjSubgroup V g : Set G) := by
    intro h
    exact hvN (h (Subgroup.mem_inf.2 ⟨v.val_mem, (mem_fixV_iff_preI hV hAN hX v).1 hv⟩))
  have h1 := e3_4_one hBA hC
  have hadd := mQuot_add (V := conjSubgroup V g) (preI_le hV :
    preI hV _ hAN X ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) inf_le_left
  rw [← mQuot_autI_preI hV hAN hX] at hadd
  have hb := hg.2
  have h2 : ((k + mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) + 1 : ℕ) : ℕ∞) ≤ rParam V := by
    push_cast
    rw [← hb]
    exact hk
  have h3 : rParam V ≤ ((mQuot (conjSubgroup V g) (preI hV _ hAN X) : ℕ) : ℕ∞) := h1
  have h4 := h2.trans h3
  have h5 : k + mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) + 1 ≤
      mQuot (conjSubgroup V g) (preI hV _ hAN X) := by exact_mod_cast h4
  omega

omit [Finite G] in
theorem wParam_eq_top_of_le_centralizer (h : T ≤ Subgroup.centralizer (V : Set G)) :
    wParam T V = ⊤ :=
  le_antisymm le_top (le_iInf₂ fun _ hj =>
    absurd (le_inf (wClos_le _ T) ((wClos_le _ T).trans h)) hj)

theorem min_le_mQuot_conj_inf_normalizer (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {h : G}
    (hnc : ⁅V, conjSubgroup V h⁆ ≠ ⊥) :
    min (wParam T V) (rParam V) ≤
      ((mQuot (conjSubgroup V h) (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) : ℕ) :
        ℕ∞) := by
  by_contra hlt
  push Not at hlt
  set A₀ := conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G) with hA₀
  set j := mQuot (conjSubgroup V h) A₀ with hj
  have hjw : (j : ℕ∞) < wParam T V := lt_of_lt_of_le hlt (min_le_left _ _)
  have hjr : (j : ℕ∞) < rParam V := lt_of_lt_of_le hlt (min_le_right _ _)
  have hw : 0 < wParam T V := lt_of_le_of_lt zero_le hjw
  have hWj : wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    have : wParam T V ≤ (j : ℕ∞) := iInf₂_le j hcon
    exact absurd hjw (not_lt.2 this)
  have hTN : IsSylowIn 2 T (Subgroup.normalizer (V : Set G)) :=
    B6.isSylowTwoOf_mono hT.sylow hT.normal le_top
  have hA₀2 : IsPGroup 2 ↥A₀ :=
    (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) h).to_le inf_le_left
  obtain ⟨n, hn, hle⟩ := exists_le_conj_of_isSylowIn hTN
    (inf_le_right : A₀ ≤ Subgroup.normalizer (V : Set G)) hA₀2
  have h1 : conjSubgroup A₀ n⁻¹ ≤ T := by
    have := conjSubgroup_mono_left n⁻¹ hle
    rwa [conjSubgroup_conj_inv] at this
  have hmem : conjSubgroup A₀ n⁻¹ ∈ gammaSet V j T := by
    refine ⟨h1, h * n⁻¹, ?_, ?_⟩
    · rw [← conjSubgroup_conjSubgroup]
      exact conjSubgroup_mono_left n⁻¹ inf_le_left
    · rw [← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
  have h2 : conjSubgroup A₀ n⁻¹ ≤ Subgroup.centralizer (V : Set G) :=
    ((le_wClos hmem).trans hWj).trans inf_le_right
  have hnV : conjSubgroup V n = V := conjSubgroup_eq_iff_mem_normalizer.2 hn
  have h3 : A₀ ≤ Subgroup.centralizer (V : Set G) := by
    have := conjSubgroup_mono_left n h2
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, conjSubgroup_centralizer,
      hnV] at this
  have h4 : A₀ = conjSubgroup V h ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (le_inf inf_le_left h3)
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  have hVN : ¬ V ≤ Subgroup.normalizer (conjSubgroup V h : Set G) := fun hVN =>
    hnc (commutator_eq_bot_iff_le_centralizer'.2
      ((e3_25_centralizer_iff_normalizer hV hT hw h).2 hVN))
  have h5 := e3_4_two hVN
  rw [← h4] at h5
  exact absurd (lt_of_lt_of_le hjr h5) (lt_irrefl _)

theorem min_le_mQuot_inf_normalizer_conj (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {g : G}
    (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    min (wParam T V) (rParam V) ≤
      ((mQuot V (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) : ℕ) : ℕ∞) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hnc' : ⁅conjSubgroup V g, conjSubgroup (conjSubgroup V g) g⁻¹⁆ ≠ ⊥ := by
    rw [conjSubgroup_conj_inv, Subgroup.commutator_comm]
    exact hnc
  have h := min_le_mQuot_conj_inf_normalizer hVg (hypE322_conj hT g) hnc'
  rwa [wParam_conj, rParam_conj, conjSubgroup_conj_inv] at h

theorem wParam_eq_top_of_pRank_eq_zero (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    (h0 : CFSG.Open.pRank 2 (autI hV ⊤) = 0) : wParam T V = ⊤ := by
  have hTp : IsPGroup 2 T := hT.sylow.isPGroup
  have hX2 : IsPGroup 2 (autI hV T) := isPGroup_autI hV hT.normal hTp
  have hbot : autI hV T = ⊥ := by
    by_contra hne
    obtain ⟨t, htT, hto⟩ := exists_orderOf_two_of_isPGroup hX2 hne
    have hE : IsElemAbelian 2 (Subgroup.zpowers t) := by
      refine ⟨inferInstance, ?_⟩
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hto,
        pow_orderOf_eq_one, one_zpow]
    have hle : Subgroup.zpowers t ≤ autI hV ⊤ :=
      Subgroup.zpowers_le.2 (autI_mono hV le_top htT)
    have hcard : Nat.card (Subgroup.zpowers t) = 2 ^ 1 := by
      rw [Nat.card_zpowers, hto, pow_one]
    have := le_pRank Nat.prime_two hle hE hcard
    omega
  exact wParam_eq_top_of_le_centralizer ((autI_eq_bot_iff hV hT.normal).1 hbot)

theorem e3_31_one_core (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g)
    (hEq : rParam V = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V) :
    rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) =
        CFSG.Open.pRank 2 (autI hV ⊤) ∧
      rParam V = ((mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓
          Subgroup.centralizer (V : Set G)) : ℕ) : ℕ∞) := by
  have h1 := e3_28_one hV hT h24 hg
  rw [mQuot_conj_inf_centralizer hV g] at h1
  have h2 := rk_autI_le_pRank (V := V) hV (g := g)
  have hb := hg.2
  rw [hb] at hEq
  rw [hEq] at h1
  have h3 : CFSG.Open.pRank 2 (autI hV ⊤) + mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ≤
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) +
        rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) := by
    exact_mod_cast h1
  have h4 : rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) =
      CFSG.Open.pRank 2 (autI hV ⊤) := by omega
  refine ⟨h4, ?_⟩
  rw [mQuot_conj_inf_centralizer hV g, h4, hb] at *
  rw [hEq, add_comm]
  push_cast
  rfl

theorem e3_31_one_pos (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g)
    (hEq : rParam V = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V) :
    0 < rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) := by
  rw [(e3_31_one_core hV hT h24 hg hEq).1]
  by_contra h0
  have h00 : CFSG.Open.pRank 2 (autI hV ⊤) = 0 := Nat.eq_zero_of_not_pos h0
  have h := wParam_eq_top_of_pRank_eq_zero hV hT h00
  rw [hg.2] at h
  exact ENat.natCast_ne_top _ h

theorem e3_31_one_le (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g)
    (hEq : rParam V = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V) :
    (gammaCheck (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map (valHom hV) ≤
      V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  apply e3_32 hV hg
  obtain ⟨-, h2⟩ := e3_31_one_core hV hT h24 hg hEq
  have hpos := e3_31_one_pos hV hT h24 hg hEq
  rw [h2, mQuot_conj_inf_centralizer hV g, hg.2]
  exact_mod_cast (by omega : (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
    + mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) + 1 ≤
    mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) +
      rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))))

theorem e3_31_two_ge (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g)
    (hEq : rParam V = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V) :
    wParam T V ≤ ((rkIdx (gammaCheck
      (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) : ℕ) : ℕ∞) := by
  have hW := e3_31_one_le hV hT h24 hg hEq
  have h1 := min_le_mQuot_inf_normalizer_conj hV hT hg.1
  have hmin : min (wParam T V) (rParam V) = wParam T V :=
    min_eq_left (by rw [hEq]; exact le_add_self)
  rw [hmin] at h1
  refine h1.trans ?_
  rw [rkIdx_eq_mQuot_map hV]
  exact_mod_cast mQuot_mono hW

theorem e3_31_two_eq (hV : IsElemAbelian 2 V) {g : G} (hVg : IsElemAbelian 2 (conjSubgroup V g))
    (hT : HypE322 T V) (h24 : HypE324 T V hV) (hg : IsWOffenderAt T V g)
    (hEq : rParam V = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V)
    (hweq : wParam T V = ((rkIdx (gammaCheck
      (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) : ℕ) : ℕ∞)) :
    0 < wParam T V ∧
      (gammaCheck (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map (valHom hV) =
        V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ∧
      IsWOffenderAt (conjSubgroup T g) (conjSubgroup V g) g⁻¹ ∧
      rk ↥(autI hVg (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G))) =
        CFSG.Open.pRank 2 (autI hV ⊤) := by
  have hW := e3_31_one_le hV hT h24 hg hEq
  set Wm := (gammaCheck (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
    (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map (valHom hV) with hWm
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have h1 := min_le_mQuot_inf_normalizer_conj hV hT hg.1
  have hmin : min (wParam T V) (rParam V) = wParam T V :=
    min_eq_left (by rw [hEq]; exact le_add_self)
  rw [hmin, hweq, rkIdx_eq_mQuot_map hV] at h1
  have hca : mQuot V Wm = mQuot V (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) := by
    have h2 := mQuot_mono (V := V) hW
    have h3 : mQuot V Wm ≤ mQuot V (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) := by
      exact_mod_cast h1
    omega
  have hweq' : wParam T V = ((mQuot V Wm : ℕ) : ℕ∞) := by
    rw [hweq, rkIdx_eq_mQuot_map hV]
  have hpos : 0 < wParam T V := by
    rcases eq_or_ne (wParam T V) 0 with h0 | hne
    · exfalso
      rw [h0] at hweq'
      have hm0 : mQuot V Wm = 0 := by exact_mod_cast hweq'.symm
      have hWV : Wm = V := (mQuot_eq_zero_iff hV2 (map_valHom_le hV _)).1 hm0
      apply e3_28_four_left hV hT h24 hg
      intro v hv
      have : v ∈ Wm := hWV ▸ hv
      exact (hW this).2
    · exact pos_iff_ne_zero.2 hne
  have hWmN : Wm = V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge hW ?_
    have e1 := card_eq_two_pow_mul hV2 (map_valHom_le hV _ : Wm ≤ V)
    have e2 := card_eq_two_pow_mul hV2 (inf_le_left : V ⊓ Subgroup.normalizer
      (conjSubgroup V g : Set G) ≤ V)
    rw [hca] at e1
    have := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) _)
      (e1.symm.trans e2)
    exact this.ge
  have hoff : IsWOffenderAt (conjSubgroup T g) (conjSubgroup V g) g⁻¹ := by
    refine ⟨?_, ?_⟩
    · rw [conjSubgroup_conj_inv, Subgroup.commutator_comm]
      exact hg.1
    · rw [wParam_conj, conjSubgroup_conj_inv, hweq', hca]
  refine ⟨hpos, hWmN, hoff, ?_⟩
  have hEq' : rParam (conjSubgroup V g) =
      ((CFSG.Open.pRank 2 (autI hVg ⊤) : ℕ) : ℕ∞) + wParam (conjSubgroup T g) (conjSubgroup V g) := by
    rw [rParam_conj, pRank_autI_conj hV g hVg, wParam_conj]
    exact hEq
  have hcore := (e3_31_one_core hVg (hypE322_conj hT g) (hypE324_conj hV g hVg h24) hoff hEq').1
  rw [conjSubgroup_conj_inv, pRank_autI_conj hV g hVg] at hcore
  exact hcore

omit [Finite G] in
theorem mQuot_bot_eq_rk (X : Subgroup G) : mQuot X ⊥ = rk ↥X := by
  unfold mQuot rk
  rw [Subgroup.relIndex_bot_left]

theorem e3_33_one (hV : IsElemAbelian 2 V) {g : G} (hg : IsWOffenderAt T V g)
    (hws : wParam T V < (sParam hV : ℕ∞)) :
    V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) :
        Set G) = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ∧
      V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) < V := by
  have hb : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      sParam hV := by
    have := hg.2 ▸ hws
    exact_mod_cast this
  refine ⟨e3_10_one hV hb, lt_of_le_of_ne inf_le_left fun h => hg.1 ?_⟩
  have hVC : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
    h.symm.le.trans inf_le_right
  exact commutator_eq_bot_iff_le_centralizer'.2 hVC

theorem e3_33_two (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {g : G} (hg : IsWOffenderAt T V g)
    (h0w : 0 < wParam T V) :
    V < V ⊔ conjSubgroup V g ∧
      V ⊔ conjSubgroup V g ≤ Subgroup.centralizer
        ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) ∧
      ¬ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) :
        Subgroup G) : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hn := e3_28_four_right hV hT hg h0w
  have hVU : V ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) :
      Subgroup G) : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun u hu =>
      (B2F.isElemAbelian_comm hV (Subgroup.mem_inf.1 hu).1 hv)
  have hVgU : conjSubgroup V g ≤ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.2 fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2 x hx).symm
  refine ⟨lt_of_le_of_ne le_sup_left fun h => hn ?_, sup_le hVU hVgU, fun h => hn (hVgU.trans h)⟩
  exact (le_sup_right.trans h.symm.le).trans (Subgroup.le_normalizer)

theorem e3_33_three (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {g : G} (hg : IsWOffenderAt T V g)
    (h0w : 0 < wParam T V) :
    rParam V ≤ mQuot V (V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) := by
  have hn := e3_28_four_right hV hT hg h0w
  have h := e3_4_two (V := conjSubgroup V g) (g := g⁻¹) (by rwa [conjSubgroup_conj_inv])
  rwa [rParam_conj, conjSubgroup_conj_inv] at h

theorem e3_33_four (hV : IsElemAbelian 2 V) {g : G} (hg : IsWOffenderAt T V g)
    (hws : wParam T V < (sParam hV : ℕ∞)) :
    autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ∈
        aSet (sParam hV - mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) (autI hV ⊤) ∧
      sParam hV - mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ≤
        rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) ∧
      1 ≤ sParam hV - mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) := by
  have hb : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      sParam hV := by
    have := hg.2 ▸ hws
    exact_mod_cast this
  have hmem := e3_10_two hV hb hg.1
  refine ⟨hmem, ?_, by omega⟩
  have := le_mQuot_bot_of_mem_aSet hmem
  rwa [mQuot_bot_eq_rk] at this

end Offender2

end E3

end CFSG.Quasithin
