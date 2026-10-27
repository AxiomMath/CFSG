module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem IsInvolutoryFieldAut.conjSubgroup_ch62 {t : G} (ht : IsInvolutoryFieldAut L t) (g : G) :
    IsInvolutoryFieldAut (conjSubgroup L g) (g⁻¹ * t * g) := by
  have hO : pCoreOf 2 (conjSubgroup L g) = conjSubgroup (pCoreOf 2 L) g :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g⁻¹) L
  obtain ⟨htN, ht2, htout⟩ := ht
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
    simpa [mul_assoc] using htN
  · rw [mem_conjSubgroup_iff] at hx
    rw [hO, mem_conjSubgroup_iff]
    have := ht2 _ hx
    convert this using 1
    simp only [sq]
    group
  · rintro ⟨y, hy, hyx⟩
    apply htout
    refine ⟨g * y * g⁻¹, mem_conjSubgroup_iff.mp hy, fun z hz => ?_⟩
    have hz' : g⁻¹ * z * g ∈ conjSubgroup L g := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hz
    have h2 := hyx _ hz'
    rw [hO, mem_conjSubgroup_iff] at h2
    convert h2 using 1
    group

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_fieldAut_of_fieldType (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {F : Subgroup G} (hFV : F ≤ V)
    (hm : mQuot V F = 2)
    (hH : ¬ Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ∃ t ∈ ch6MV M V, IsInvolutoryFieldAut L t ∧ t ∈ Subgroup.centralizer (F : Set G) := by
  obtain ⟨m, hm', hU'V, hm2', hH', hSyl⟩ := h.exists_conj_fieldType_ch62 hFV hm hH
  obtain ⟨t₀, ht₀T, ht₀, hUt, -⟩ :=
    h.lemma_6_2_4_one_five h331 h432 h615 h6110 hE612 hU'V hm2' hH' hSyl
  have hmL : m⁻¹ ∈ Subgroup.normalizer (L : Set G) := h.normal (M.inv_mem hm'.1)
  refine ⟨m⁻¹⁻¹ * t₀ * m⁻¹, ?_, ht₀.conj_ch6 hmL, ?_⟩
  · rw [inv_inv]
    have ht₀M : t₀ ∈ ch6MV M V := ⟨h.T_le ht₀T, h.toHyp611.T_le_normalizer ht₀T⟩
    exact (ch6MV M V).mul_mem ((ch6MV M V).mul_mem hm' ht₀M) ((ch6MV M V).inv_mem hm')
  · rw [inv_inv]
    refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hf' : m⁻¹ * f * m ∈ conjSubgroup F m := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hf
    rw [hUt] at hf'
    have hc := Subgroup.mem_centralizer_iff.mp hf'.2 t₀ rfl
    calc f * (m * t₀ * m⁻¹) = m * ((m⁻¹ * f * m) * t₀) * m⁻¹ := by group
      _ = m * (t₀ * (m⁻¹ * f * m)) * m⁻¹ := by rw [hc]
      _ = m * t₀ * m⁻¹ * f := by group

theorem isFieldType_one (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {F : Subgroup G} (hFV : F ≤ V)
    (hm : mQuot V F = 2)
    (hH : ¬ Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    IsFieldType M L V F 1 := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  obtain ⟨t, htM, ht, htF⟩ := h.exists_fieldAut_of_fieldType h331 h432 h615 h6110 hE612 hFV hm hH
  refine ⟨by rw [conjSubgroup_one]; exact hFV, ?_, t, by rw [conjSubgroup_one]; exact htM,
    by rw [conjSubgroup_one]; exact ht, htF⟩
  have h1 := card_eq_two_pow_mul hV2 hFV
  rw [hm, h.natural.card_eq] at h1
  norm_num at h1
  omega

theorem isFieldType_conj (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) (g : G) {F : Subgroup G}
    (hFV : F ≤ conjSubgroup V g) (hm : mQuot (conjSubgroup V g) F = 2)
    (hH : ¬ Subgroup.centralizer (F : Set G) ≤
      Subgroup.normalizer (conjSubgroup V g : Set G)) :
    IsFieldType M L V F g := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  set F' := conjSubgroup F g⁻¹ with hF'
  have hgV : conjSubgroup (conjSubgroup V g) g⁻¹ = V := conjSubgroup_conj_inv V g
  have hFV' : F' ≤ V := by
    have := conjSubgroup_mono_left g⁻¹ hFV
    rwa [hgV] at this
  have hm' : mQuot V F' = 2 := by rw [← hgV, mQuot_conjSubgroup]; exact hm
  have hH' : ¬ Subgroup.centralizer (F' : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro hle
    apply hH
    have := conjSubgroup_mono_left g hle
    rwa [conjSubgroup_centralizer, hF', conjSubgroup_inv_conj, conjSubgroup_normalizer] at this
  obtain ⟨t, htM, ht, htF⟩ :=
    h.exists_fieldAut_of_fieldType h331 h432 h615 h6110 hE612 hFV' hm' hH'
  refine ⟨hFV, ?_, g⁻¹ * t * g, ?_, ht.conjSubgroup_ch62 g, ?_⟩
  · have h1 := card_eq_two_pow_mul (isPGroup_conjSubgroup hV2 g) hFV
    rw [hm, card_conjSubgroup, h.natural.card_eq] at h1
    norm_num at h1
    omega
  · rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using htM
  · refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hf' : g * f * g⁻¹ ∈ F' := by
      rw [hF', mem_conjSubgroup_iff, inv_inv]
      simpa [mul_assoc] using hf
    have hc := Subgroup.mem_centralizer_iff.mp htF _ hf'
    calc f * (g⁻¹ * t * g) = g⁻¹ * ((g * f * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * f * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * t * g * f := by group

theorem le_pCoreOf_centralizer_of_fieldType (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {F : Subgroup G} (hFV : F ≤ V)
    (hm : mQuot V F = 2)
    (hH : ¬ Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ pCoreOf 2 (Subgroup.centralizer (F : Set G)) := by
  obtain ⟨m, hm', hU'V, hm2', hH', hSyl⟩ := h.exists_conj_fieldType_ch62 hFV hm hH
  obtain ⟨-, -, -, -, -, -, ⟨-, hUHO, -⟩, -⟩ :=
    h.lemma_6_2_4_one_five h331 h432 h615 h6110 hE612 hU'V hm2' hH' hSyl
  have h1 : V ≤ pCoreOf 2 (Subgroup.centralizer (conjSubgroup F m : Set G)) :=
    (le_conjClosure V _).trans hUHO
  have hVm : conjSubgroup V m⁻¹ = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hm'.2)
  have h2 := conjSubgroup_mono_left m⁻¹ h1
  rw [hVm] at h2
  have e : conjSubgroup (pCoreOf 2 (Subgroup.centralizer (conjSubgroup F m : Set G))) m⁻¹ =
      pCoreOf 2 (Subgroup.centralizer (F : Set G)) := by
    rw [conjSubgroup_eq_conjSub_ch62, inv_inv, ← pCoreOf_conjSub,
      ← CFSG.Quasithin.conjSub_centralizer, conjSubgroup_eq_conjSub_ch62, conjSub_inv_conjSub]
  rwa [e] at h2

theorem not_le_centralizer_pair626 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {x y : G}
    (hA : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2)
    (hU : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex (conjSub x V) = 2) :
    ¬ conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G) ≤
      Subgroup.centralizer (conjSub x V : Set G) := by
  intro hle
  have hXC : conjSub x V ≤ Subgroup.centralizer
      ((conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G) : Subgroup G) : Set G) :=
    fun v hv => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hle ha) v hv).symm
  have hXN := hXC.trans (h.centralizer_le_normalizer_conj h331 h432 h615 h6110 hE612 y
    inf_le_left (by rw [hA]))
  rw [inf_eq_left.mpr hXN, Subgroup.relIndex_self] at hU
  norm_num at hU

theorem fieldType_data_pair626 {x y : G}
    (hA : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2)
    (hU : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex (conjSub x V) = 2)
    (hA2 : (Subgroup.centralizer (conjSub x V : Set G)).relIndex
      (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) = 2) :
    mQuot (conjSub y V) ((conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) ⊓
        Subgroup.centralizer (conjSub x V : Set G)) = 2 ∧
      ¬ Subgroup.centralizer (((conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) ⊓
        Subgroup.centralizer (conjSub x V : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (conjSub y V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := conjSub x V with hX
  set Y := conjSub y V with hY
  set A := Y ⊓ Subgroup.normalizer (X : Set G) with hAdef
  set A₀ := A ⊓ Subgroup.centralizer (X : Set G) with hA₀
  have hY2 : IsPGroup 2 Y := B2F.isPGroup_of_isElemAbelian (h.isElemAbelian_conjSub_V y)
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.relIndex_mul_relIndex A₀ A Y inf_le_left inf_le_left
    rw [Subgroup.inf_relIndex_left, hA2, hA] at h1
    have h2 := relIndex_eq_two_pow hY2 A₀
    rw [← h1] at h2
    have : 2 ^ mQuot Y A₀ = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl this
  · have hXA₀ : X ≤ Subgroup.centralizer (A₀ : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm
    intro hle
    have hXY : X ≤ Subgroup.normalizer (Y : Set G) := hXA₀.trans hle
    rw [inf_eq_left.mpr hXY, Subgroup.relIndex_self] at hU
    norm_num at hU

theorem relIndex_two_pair626 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {x y : G}
    (hA : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2)
    (hU : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex (conjSub x V) = 2)
    (hA2 : (Subgroup.centralizer (conjSub x V : Set G)).relIndex
      (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) = 2) :
    (Subgroup.centralizer (conjSub y V : Set G)).relIndex
      (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmA₀, hHA₀⟩ := h.fieldType_data_pair626 hA hU hA2
  set X := conjSub x V with hX
  set Y := conjSub y V with hY
  set A := Y ⊓ Subgroup.normalizer (X : Set G) with hAdef
  set U := X ⊓ Subgroup.normalizer (Y : Set G) with hUdef
  set A₀ := A ⊓ Subgroup.centralizer (X : Set G) with hA₀
  have hX2 : IsPGroup 2 X := B2F.isPGroup_of_isElemAbelian (h.isElemAbelian_conjSub_V x)
  have hA₀Y : A₀ ≤ Y := inf_le_left.trans inf_le_left
  have hXA₀ : X ≤ Subgroup.centralizer (A₀ : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm
  have hUP : U ≤ Subgroup.centralizer (A₀ : Set G) ⊓ Subgroup.normalizer (Y : Set G) :=
    le_inf (inf_le_left.trans hXA₀) inf_le_right
  have h1 := h.relIndex_le_two_of_fieldType_conj h331 h432 h615 h6110 hE612 y hA₀Y hmA₀ hHA₀
    hUP (hX2.to_le inf_le_left)
  have hne : (Subgroup.centralizer (Y : Set G)).relIndex U ≠ 1 := by
    intro h0
    exact h.not_le_centralizer_pair626 h331 h432 h615 h6110 hE612 hU hA
      (Subgroup.relIndex_eq_one.mp h0)
  have hpow := relIndex_eq_two_pow (hX2.to_le inf_le_left : IsPGroup 2 U)
    (Subgroup.centralizer (Y : Set G))
  rw [hpow] at h1 hne ⊢
  rcases Nat.lt_or_ge (mQuot U (Subgroup.centralizer (Y : Set G))) 2 with hlt | hge
  · interval_cases hm : mQuot U (Subgroup.centralizer (Y : Set G))
    · simp at hne
    · rfl
  · have : 2 ^ 2 ≤ 2 ^ mQuot U (Subgroup.centralizer (Y : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) hge
    omega

end Hyp6Sec2

end CFSG.Quasithin.H13
