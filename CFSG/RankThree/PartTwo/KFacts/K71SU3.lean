module

public import CFSG.RankThree.PartTwo.KFacts.K71Basic
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply fixedField_card_pow)
open Matrix

section FixedField

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_card_fixedField_of_orderOf_eq_three (h : UnitaryFieldData p f K)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ f₀ : ℕ, f = 3 * f₀ ∧ 1 ≤ f₀ ∧ Nat.card (fixedField σ) = p ^ (2 * f₀) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  have hpow := fixedField_card_pow σ
  rw [hσ, h.card] at hpow
  obtain ⟨c, -, hc⟩ := FiniteField.card (fixedField σ) p
  rw [Nat.card_eq_fintype_card, hc, ← pow_mul] at hpow
  have h3c : (c : ℕ) * 3 = 2 * f := Nat.pow_right_injective h.prime.two_le hpow
  have h3f : 3 ∣ f :=
    (show Nat.Coprime 3 2 by norm_num).dvd_of_dvd_mul_left ⟨c, by rw [← h3c, mul_comm]⟩
  obtain ⟨f₀, rfl⟩ := h3f
  refine ⟨f₀, rfl, ?_, ?_⟩
  · have := h.one_le
    omega
  · rw [Nat.card_eq_fintype_card, hc]
    congr 1
    omega

theorem bar_coe_fixedField (h : UnitaryFieldData p f K) {σ : K ≃+* K} {f₀ : ℕ}
    (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ)) (x : fixedField σ) :
    h.bar (x : K) = ((h₀.bar x : fixedField σ) : K) := by
  have := h₀.finite
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  have hx : x ^ p ^ (2 * f₀) = x := by
    have h1 := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, h₀.card] at h1
  have hx' : (x : K) ^ p ^ (2 * f₀) = x := by rw [← SubmonoidClass.coe_pow, hx]
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, SubmonoidClass.coe_pow, hf,
    show 3 * f₀ = 2 * f₀ + f₀ by ring, pow_add, pow_mul, hx']

end FixedField

section Incl

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {σ : K ≃+* K} {f₀ : ℕ}
  (h₀ : UnitaryFieldData p f₀ (fixedField σ))
  (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))

include hbar in
theorem map_subtype_map_bar (M : Matrix (Fin 3) (Fin 3) (fixedField σ)) :
    (M.map (fixedField σ).subtype).map h.bar = (M.map h₀.bar).map (fixedField σ).subtype := by
  ext i j
  exact hbar (M i j)

include hbar in
theorem map_mem_unitarySU {g : GL (Fin 3) (fixedField σ)}
    (hg : g ∈ unitarySU p f₀ (fixedField σ) 3) :
    GeneralLinearGroup.map (fixedField σ).subtype g ∈ unitarySU p f K 3 := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h₀).mp hg
  have hcoe : ((GeneralLinearGroup.map (fixedField σ).subtype g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) (fixedField σ)).map
        (fixedField σ).subtype := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
  · rw [hcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · rw [hcoe, map_subtype_map_bar h h₀ hbar, ← Matrix.transpose_map, ← Matrix.map_mul, hu,
      Matrix.map_one _ (map_zero _) (map_one _)]

noncomputable def suIncl : unitarySU p f₀ (fixedField σ) 3 →* unitarySU p f K 3 :=
  ((GeneralLinearGroup.map (fixedField σ).subtype).comp
    (unitarySU p f₀ (fixedField σ) 3).subtype).codRestrict (unitarySU p f K 3) fun g =>
      map_mem_unitarySU h h₀ hbar g.2

theorem coe_suIncl_apply (g : unitarySU p f₀ (fixedField σ) 3) (i j : Fin 3) :
    (((suIncl h h₀ hbar g : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      ((g : GL (Fin 3) (fixedField σ)) i j : K) :=
  GeneralLinearGroup.map_apply _ i j _

theorem suIncl_injective : Function.Injective (suIncl h h₀ hbar) := by
  intro g g' hgg
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro i j
  apply Subtype.ext
  rw [← coe_suIncl_apply h h₀ hbar, ← coe_suIncl_apply h h₀ hbar, hgg]

theorem mem_range_suIncl_iff (g : unitarySU p f K 3) :
    g ∈ (suIncl h h₀ hbar).range ↔ suField h σ g = g := by
  constructor
  · rintro ⟨g', rfl⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    ext i j
    rw [Matrix.map_apply, coe_suIncl_apply]
    exact fixedField_apply σ _
  · intro hg
    have hfix : ∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j := by
      intro i j
      have h1 := congrArg (fun x : unitarySU p f K 3 =>
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) hg
      simpa [coe_suField, coe_glAut] using h1
    set M : Matrix (Fin 3) (Fin 3) (fixedField σ) :=
      fun i j => ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j,
        (mem_fixedField_iff σ _).mpr (hfix i j)⟩ with hM
    have hMmap : M.map (fixedField σ).subtype = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      rfl
    obtain ⟨hgdet, hgu⟩ := (mem_unitarySU_iff h).mp g.2
    have hdet1 : M.det = 1 := by
      apply (fixedField σ).subtype_injective
      rw [map_one, RingHom.map_det]
      exact (congrArg Matrix.det hMmap).trans hgdet
    have hdet : M.det ≠ 0 := by rw [hdet1]; exact one_ne_zero
    set A : GL (Fin 3) (fixedField σ) := GeneralLinearGroup.mkOfDetNeZero M hdet
    have hA : (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) = M := rfl
    have hAu : A ∈ unitarySU p f₀ (fixedField σ) 3 := by
      refine (mem_unitarySU_iff h₀).mpr ⟨by rw [hA, hdet1], ?_⟩
      rw [hA]
      have key : ((M.map h₀.bar)ᵀ * M).map (fixedField σ).subtype =
          (1 : Matrix (Fin 3) (Fin 3) (fixedField σ)).map (fixedField σ).subtype := by
        rw [Matrix.map_mul, Matrix.transpose_map, ← map_subtype_map_bar h h₀ hbar, hMmap,
          Matrix.map_one _ (map_zero _) (map_one _)]
        exact hgu
      exact Matrix.map_injective (fixedField σ).subtype_injective key
    refine ⟨⟨A, hAu⟩, ?_⟩
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    rw [coe_suIncl_apply]
    rfl

end Incl

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_barCentralizer_mulEquiv_su3 {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f) {a : G} (ha3 : a ^ 3 = 1)
    (ha : InducesKindSU3 h L hq a .field) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧
      ∃ _ : UnitaryFieldData p f₀ (fixedField σ),
        Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃*
          unitarySU p f₀ (fixedField σ) 3) := by
  obtain ⟨e, hN, hfield⟩ := ha
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq
  set β := inducedAutHom L e ⟨a, hN⟩ with hβ
  set α := MulAut.congr (suCenterEquiv h hq) (centerDescend _ β) with hα
  have hβ3 : β ^ 3 = 1 := inducedAutHom_pow_eq_one L e hN ha3
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ← map_pow, hβ3, map_one, map_one]
  have hD : α ∉ (psuConj h).range :=
    (stdPinnedPSU3_separated h).not_mem_inndiag_of_isField hfield
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq α hα3 hD
  have hlift : β = suConj h H * suField h σ * (suConj h H)⁻¹ := by
    have hγ : MulAut.congr (suCenterEquiv h hq) (centerDescend _
        (suConj h H * suField h σ * (suConj h H)⁻¹)) = α := by
      rw [hαH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
        congr_centerDescend_suConj, congr_centerDescend_suField]
    have hγ' : centerDescend _ (suConj h H * suField h σ * (suConj h H)⁻¹) =
        centerDescend _ β := (MulAut.congr _).injective (hγ.trans hα)
    apply mulAut_eq_of_inv_mul_mem_center
    intro g
    have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
      τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) hγ'
    simp only [centerDescend_mk] at h1
    exact QuotientGroup.eq.mp h1
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  refine ⟨σ, hσ3, f₀, hf, h₀, nonempty_barCentralizer_mulEquiv hN e
    ((suConj h H : unitarySU p f K 3 ≃* unitarySU p f K 3).toMonoidHom.comp
      (suIncl h h₀ hbar)) ((suConj h H).injective.comp (suIncl_injective h h₀ hbar))
    fun z => ?_⟩
  rw [← hβ, hlift]
  exact mem_range_conj_comp_iff _ _ _ (mem_range_suIncl_iff h h₀ hbar) z

theorem isoSUThree_barCentralizer_of_field {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f) {a : G} (ha3 : a ^ 3 = 1)
    (ha : InducesKindSU3 h L hq a .field) :
    ∃ f₀ : ℕ, f = 3 * f₀ ∧
      Sec8.IsoSUThree (Sec8.barCentralizer (Subgroup.zpowers a) L) (p ^ f₀) := by
  obtain ⟨σ, -, f₀, hf, h₀, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_su3 hq ha3 ha
  have := h₀.finite
  refine ⟨f₀, hf, fixedField σ, inferInstance, inferInstance, ?_, ⟨ι⟩⟩
  rw [h₀.card, ← pow_mul, mul_comm]

end Bar

end CFSG.RankThree.PartTwo.KFacts
