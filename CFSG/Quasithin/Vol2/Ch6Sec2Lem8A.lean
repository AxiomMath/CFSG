module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem conjSub_eq_conjSubgroup_ch62 (g : G) (X : Subgroup G) :
    conjSub g X = conjSubgroup X g⁻¹ := by
  ext x
  rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]

omit [Finite G] in
theorem conjSubgroup_eq_conjSub_ch62 (X : Subgroup G) (g : G) :
    conjSubgroup X g = conjSub g⁻¹ X := by
  rw [conjSub_eq_conjSubgroup_ch62, inv_inv]

omit [Finite G] in
theorem relIndex_conjSub_ch62 (k : G) (Y X : Subgroup G) :
    (conjSub k Y).relIndex (conjSub k X) = Y.relIndex X :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k).injective

omit [Finite G] in
theorem mQuot_conjSub_ch62 (k : G) (X Y : Subgroup G) :
    mQuot (conjSub k X) (conjSub k Y) = mQuot X Y := by
  unfold mQuot
  rw [relIndex_conjSub_ch62]

omit [Finite G] in
theorem conjSub_inf_centralizer_singleton_ch62 (g x : G) (X : Subgroup G) :
    conjSub g (X ⊓ Subgroup.centralizer ({x} : Set G)) =
      conjSub g X ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_inf, mem_conjSub, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [h2]
      _ = y * (g * x * g⁻¹) := by group
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * y * g * x := by group

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_conjSub_V (g : G) : Nat.card (conjSub g V) = 16 := by
  rw [CosetGeom.card_conjSub, h.natural.card_eq]
  norm_num

theorem card_fix_le_four (h432 : Stmt4_3_2) {x : G} (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxC : x ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 4 := by
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.normal (h.normalizer_V_le h432 hxN)
  have := h.data.card_fixed_le_two_pow ⟨x, hxN⟩ hxL hxC
  simpa using this

theorem card_fix_conj_le_four (h432 : Stmt4_3_2) (g : G) {x : G}
    (hxN : x ∈ Subgroup.normalizer (conjSub g V : Set G))
    (hxC : x ∉ Subgroup.centralizer (conjSub g V : Set G)) :
    Nat.card ↥(conjSub g V ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 4 := by
  have hxN' : g⁻¹ * x * g ∈ Subgroup.normalizer (V : Set G) := by
    rw [CFSG.Quasithin.conjSub_normalizer] at hxN
    exact mem_conjSub.mp hxN
  have hxC' : g⁻¹ * x * g ∉ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hxC
    rw [CFSG.Quasithin.conjSub_centralizer]
    exact mem_conjSub.mpr hc
  have h1 := h.card_fix_le_four h432 hxN' hxC'
  have h2 := conjSub_inf_centralizer_singleton_ch62 g (g⁻¹ * x * g) V
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e] at h2
  rw [← h2, CosetGeom.card_conjSub]
  exact h1

theorem centralizer_le_normalizer_of_relIndex_le_two (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {Y : Subgroup G} (hYV : Y ≤ V)
    (hY : Y.relIndex V ≤ 2) :
    Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro c hc
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  have hpow := relIndex_eq_two_pow hV2 Y
  have hcases : Y.relIndex V = 1 ∨ Y.relIndex V = 2 := by
    rw [hpow] at hY ⊢
    rcases Nat.lt_or_ge (mQuot V Y) 1 with h0 | h0
    · left; rw [show mQuot V Y = 0 by omega, pow_zero]
    · right
      have : mQuot V Y ≤ 1 := by
        by_contra hgt
        have : 2 ^ 2 ≤ 2 ^ mQuot V Y := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [show mQuot V Y = 1 by omega, pow_one]
  rcases hcases with h1 | h2
  · have hYeq : Y = V := le_antisymm hYV (Subgroup.relIndex_eq_one.mp h1)
    rw [hYeq] at hc
    exact Subgroup.centralizer_le_normalizer _ hc
  · have hYc : Y ≤ conjSubgroup V c⁻¹ := by
      intro y hy
      rw [mem_conjSubgroup_iff, inv_inv]
      have := Subgroup.mem_centralizer_iff.mp hc y hy
      have e : c⁻¹ * y * c = y := by rw [mul_assoc, this, inv_mul_cancel_left]
      rw [e]
      exact hYV hy
    have h3 := h.lemma_6_2_5_six h331 h432 h615 h6110 hE612 hYV h2 hYc
    have h4 := conjSubgroup_eq_iff_mem_normalizer.mp h3
    simpa using Subgroup.inv_mem _ h4

theorem centralizer_le_normalizer_conj (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) (g : G) {Y : Subgroup G} (hYV : Y ≤ conjSub g V)
    (hY : Y.relIndex (conjSub g V) ≤ 2) :
    Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (conjSub g V : Set G) := by
  have hY' : conjSub g⁻¹ Y ≤ V := by
    have := conjSub_mono g⁻¹ hYV
    rwa [conjSub_conjSub_inv] at this
  have hrel : (conjSub g⁻¹ Y).relIndex V ≤ 2 := by
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) Y
      (conjSub g V) (MulAut.conj g⁻¹).injective
    have e : (conjSub g V).map (MulAut.conj g⁻¹).toMonoidHom = V := conjSub_conjSub_inv g V
    change (conjSub g⁻¹ Y).relIndex ((conjSub g V).map (MulAut.conj g⁻¹).toMonoidHom) = _ at this
    rw [e] at this
    rw [this]
    exact hY
  have h1 := h.centralizer_le_normalizer_of_relIndex_le_two h331 h432 h615 h6110 hE612 hY' hrel
  have h2 := conjSub_mono g h1
  rwa [← CFSG.Quasithin.conjSub_centralizer, conjSub_inv_conjSub,
    ← CFSG.Quasithin.conjSub_normalizer] at h2

theorem commutator_conj_eq_bot (h432 : Stmt4_3_2) (h627 : Stmt6_2_7) {x : G}
    (hx : conjSub x V ≤ Subgroup.normalizer (V : Set G)) : ⁅conjSub x V, V⁆ = ⊥ := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  have hW := (h627 G T M L V h).1
  have hP : conjSub x V ≤ ch6MV M V := le_inf (hx.trans (h.normalizer_V_le h432)) hx
  obtain ⟨m, hm, hPT⟩ := h.toHyp611.exists_conj_sylow hP (hV2.map _)
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm.2
  have h1 : conjSub (m⁻¹ * x) V ≤ T := by
    rw [conjSub_mul]
    have h2 : conjSub m⁻¹ (conjSub x V) ≤ conjSub m⁻¹ (T.map (MulAut.conj m).toMonoidHom) :=
      conjSub_mono _ hPT
    have e : conjSub m⁻¹ (T.map (MulAut.conj m).toMonoidHom) = T := conjSub_conjSub_inv m T
    rwa [e] at h2
  have h3 : conjSub (m⁻¹ * x) V ≤ Subgroup.centralizer (V : Set G) := by
    have hmem : conjSub (m⁻¹ * x) V ∈ gammaSet V 0 T := by
      refine ⟨h1, (m⁻¹ * x)⁻¹, ?_, ?_⟩
      · rw [conjSub_eq_conjSubgroup_ch62]
      · rw [conjSub_eq_conjSubgroup_ch62, mQuot_self]
    exact ((le_wClos hmem).trans hW).trans inf_le_right
  have h4 : conjSub x V ≤ Subgroup.centralizer (V : Set G) := by
    have h5 := conjSub_mono m h3
    rw [← conjSub_mul, mul_inv_cancel_left, ← CFSG.Quasithin.conjSub_centralizer,
      conjSub_eq_of_mem_normalizer' hmV] at h5
    exact h5
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h4

theorem commutator_conj_conj_eq_bot (h432 : Stmt4_3_2) (h627 : Stmt6_2_7) {x y : G}
    (hxy : conjSub x V ≤ Subgroup.normalizer (conjSub y V : Set G)) :
    ⁅conjSub x V, conjSub y V⁆ = ⊥ := by
  have h1 : conjSub (y⁻¹ * x) V ≤ Subgroup.normalizer (V : Set G) := by
    rw [conjSub_mul]
    have := conjSub_mono y⁻¹ hxy
    rwa [CFSG.Quasithin.conjSub_normalizer, conjSub_conjSub_inv] at this
  have h2 := h.commutator_conj_eq_bot h432 h627 h1
  have h3 := congrArg (conjSub y) h2
  rw [conjSub_commutator', ← conjSub_mul, mul_inv_cancel_left, CFSG.Quasithin.conjSub_bot] at h3
  exact h3

theorem exists_conj_sylow_ch62 {U : Subgroup G} (hU1 : U ≠ ⊥) (hUV : U ≤ V) :
    ∃ m ∈ ch6MV M V, IsSylowIn 2 (T ⊓ Subgroup.normalizer (conjSubgroup U m : Set G))
      (M ⊓ Subgroup.normalizer (conjSubgroup U m : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2 (bot_le : ⊥ ≤ M ⊓ Subgroup.normalizer (U : Set G))
    IsPGroup.of_bot
  obtain ⟨m, hm, hPT⟩ := h.toHyp611.exists_conj_sylow
    (hP.le.trans (h.toHyp611Nat.normalizer_le hU1 hUV)) hP.isPGroup
  refine ⟨m, hm, ?_⟩
  have hmM : m ∈ M := hm.1
  have hNM : M ⊓ Subgroup.normalizer (conjSubgroup U m : Set G) =
      conjSubgroup (M ⊓ Subgroup.normalizer (U : Set G)) m := by
    rw [conjSubgroup_inf M, conjSubgroup_normalizer U m,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hmM)]
  have hPm : conjSubgroup P m ≤ T := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hPT hx)
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have := congrArg (fun z => m⁻¹ * z * m) hyx
      simpa [mul_assoc] using this
    rw [← this]
    exact hy
  have hPm' : IsSylowIn 2 (conjSubgroup P m)
      (M ⊓ Subgroup.normalizer (conjSubgroup U m : Set G)) := by
    rw [hNM]
    refine ⟨conjSubgroup_mono_left m hP.le, hP.isPGroup.map _, ?_⟩
    rw [relIndex_conjSubgroup]
    exact hP.not_dvd_relIndex
  refine ⟨inf_le_inf_right _ h.T_le, h.sylow.1.to_le inf_le_left, fun h2 =>
    hPm'.not_dvd_relIndex (h2.trans (Subgroup.relIndex_dvd_of_le_left _ ?_))⟩
  exact le_inf hPm (hPm'.le.trans inf_le_right)

theorem exists_conj_fieldType_ch62 {U : Subgroup G} (hUV : U ≤ V) (hm : mQuot V U = 2)
    (hH : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ∃ m ∈ ch6MV M V, conjSubgroup U m ≤ V ∧ mQuot V (conjSubgroup U m) = 2 ∧
      ¬ Subgroup.centralizer (conjSubgroup U m : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      IsSylowIn 2 (T ⊓ Subgroup.normalizer (conjSubgroup U m : Set G))
        (M ⊓ Subgroup.normalizer (conjSubgroup U m : Set G)) := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  have hU1 : U ≠ ⊥ := by
    intro h0
    have h1 := card_eq_two_pow_mul hV2 hUV
    rw [hm, h0, Subgroup.card_bot, h.natural.card_eq] at h1
    norm_num at h1
  obtain ⟨m, hm', hSyl⟩ := h.exists_conj_sylow_ch62 hU1 hUV
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm'.2
  have hVm : conjSubgroup V m = V := conjSubgroup_eq_iff_mem_normalizer.mpr hmV
  refine ⟨m, hm', ?_, ?_, ?_, hSyl⟩
  · have := conjSubgroup_mono_left m hUV
    rwa [hVm] at this
  · rw [← hVm, mQuot_conjSubgroup]
    exact hm
  · intro hle
    apply hH
    have h1 := conjSubgroup_mono_left m⁻¹ hle
    rwa [conjSubgroup_centralizer, conjSubgroup_conj_inv, conjSubgroup_normalizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hmV)] at h1

theorem relIndex_le_two_of_fieldType (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {U : Subgroup G} (hUV : U ≤ V)
    (hm : mQuot V U = 2)
    (hH : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    {P : Subgroup G}
    (hP : P ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G))
    (hP2 : IsPGroup 2 P) : (Subgroup.centralizer (V : Set G)).relIndex P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm', hU'V, hm2', hH', hSyl⟩ := h.exists_conj_fieldType_ch62 hUV hm hH
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm'.2
  set U' := conjSubgroup U m with hU'
  obtain ⟨t, htT, ht, -, ⟨-, hRsyl, -⟩, -⟩ :=
    h.lemma_6_2_4_one_five h331 h432 h615 h6110 hE612 hU'V hm2' hH' hSyl
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have hRN : R ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (inf_le_left.trans h.toHyp611.T_le_normalizer)
      (Subgroup.zpowers_le.mpr (h.toHyp611.T_le_normalizer htT))
  have hRsyl' : IsSylowIn 2 R (Subgroup.centralizer (U' : Set G) ⊓
      Subgroup.normalizer (V : Set G)) :=
    E6.isSylowIn_of_le hRsyl (le_inf hRsyl.le hRN) inf_le_left
  have hP' : conjSub m⁻¹ P ≤ Subgroup.centralizer (U' : Set G) ⊓
      Subgroup.normalizer (V : Set G) := by
    have h1 := conjSub_mono m⁻¹ hP
    rw [conjSub_inf, ← CFSG.Quasithin.conjSub_centralizer, ← CFSG.Quasithin.conjSub_normalizer,
      conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hmV)] at h1
    rwa [hU', conjSubgroup_eq_conjSub_ch62]
  obtain ⟨c, hc, hPc⟩ := F7.isSylowTwoOf_exists_conj_le hRsyl' hP' (hP2.map _)
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := hc.2
  have hR2 : (Subgroup.centralizer (V : Set G)).relIndex R ≤ 2 := by
    have htQ : t ∉ ch6Q T V := fun h1 =>
      h.toHyp611Nat.not_mem_centralizer_of_fieldAut htT ht h1.2
    have ht2 : t * t ∈ ch6Q T V :=
      ⟨T.mul_mem htT htT, h.toHyp611Nat.sq_mem_centralizer_of_fieldAut htT ht⟩
    have htN : t ∈ Subgroup.normalizer (ch6Q T V : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htT,
        F7.normalizer_le_normalizer_centralizer V (h.toHyp611.T_le_normalizer htT)⟩
    have h1 := relIndex_sup_zpowers_eq_two_ch62 htN htQ ht2
    rw [sup_comm] at h1
    rw [← h1]
    exact Subgroup.relIndex_le_of_le_left inf_le_right (by rw [h1]; norm_num)
  have hk : c⁻¹ * m⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hcV) (Subgroup.inv_mem _ hmV)
  have hconj : (Subgroup.centralizer (V : Set G)).relIndex (conjSub (c⁻¹ * m⁻¹) P) =
      (Subgroup.centralizer (V : Set G)).relIndex P := by
    have h1 := Subgroup.relIndex_map_map_of_injective
      (f := (MulAut.conj (c⁻¹ * m⁻¹)).toMonoidHom) (Subgroup.centralizer (V : Set G)) P
      (MulAut.conj _).injective
    have e : (Subgroup.centralizer (V : Set G)).map (MulAut.conj (c⁻¹ * m⁻¹)).toMonoidHom =
        Subgroup.centralizer (V : Set G) := by
      change conjSub (c⁻¹ * m⁻¹) (Subgroup.centralizer (V : Set G)) = _
      rw [← CFSG.Quasithin.conjSub_centralizer, conjSub_eq_of_mem_normalizer' hk]
    change (Subgroup.centralizer (V : Set G)).relIndex
      ((P).map (MulAut.conj (c⁻¹ * m⁻¹)).toMonoidHom) = _
    calc (Subgroup.centralizer (V : Set G)).relIndex
          ((P).map (MulAut.conj (c⁻¹ * m⁻¹)).toMonoidHom) =
        ((Subgroup.centralizer (V : Set G)).map (MulAut.conj (c⁻¹ * m⁻¹)).toMonoidHom).relIndex
          ((P).map (MulAut.conj (c⁻¹ * m⁻¹)).toMonoidHom) := by rw [e]
      _ = _ := h1
  have hle : conjSub (c⁻¹ * m⁻¹) P ≤ R := by
    rw [conjSub_mul]
    have := conjSub_mono c⁻¹ hPc
    rwa [conjSub_conjSub_inv] at this
  rw [← hconj]
  exact (Subgroup.relIndex_le_of_le_right hle Subgroup.index_ne_zero_of_finite).trans hR2

theorem relIndex_le_two_of_fieldType_conj (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) (g : G) {U : Subgroup G}
    (hUV : U ≤ conjSub g V) (hm : mQuot (conjSub g V) U = 2)
    (hH : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (conjSub g V : Set G))
    {P : Subgroup G} (hP : P ≤ Subgroup.centralizer (U : Set G) ⊓
      Subgroup.normalizer (conjSub g V : Set G))
    (hP2 : IsPGroup 2 P) :
    (Subgroup.centralizer (conjSub g V : Set G)).relIndex P ≤ 2 := by
  have hgV : conjSub g⁻¹ (conjSub g V) = V := conjSub_conjSub_inv g V
  have hUV' : conjSub g⁻¹ U ≤ V := by
    have := conjSub_mono g⁻¹ hUV
    rwa [hgV] at this
  have hm' : mQuot V (conjSub g⁻¹ U) = 2 := by
    rw [← hgV, mQuot_conjSub_ch62]
    exact hm
  have hH' : ¬ Subgroup.centralizer (conjSub g⁻¹ U : Set G) ≤
      Subgroup.normalizer (V : Set G) := by
    intro hle
    apply hH
    have := conjSub_mono g hle
    rwa [← CFSG.Quasithin.conjSub_centralizer, conjSub_inv_conjSub,
      ← CFSG.Quasithin.conjSub_normalizer] at this
  have hP' : conjSub g⁻¹ P ≤ Subgroup.centralizer (conjSub g⁻¹ U : Set G) ⊓
      Subgroup.normalizer (V : Set G) := by
    have := conjSub_mono g⁻¹ hP
    rwa [conjSub_inf, ← CFSG.Quasithin.conjSub_centralizer,
      ← CFSG.Quasithin.conjSub_normalizer, hgV] at this
  have h1 := h.relIndex_le_two_of_fieldType h331 h432 h615 h6110 hE612 hUV' hm' hH' hP'
    (hP2.map _)
  rw [← relIndex_conjSub_ch62 g⁻¹, ← CFSG.Quasithin.conjSub_centralizer, hgV]
  exact h1

end Hyp6Sec2

end CFSG.Quasithin.H13
