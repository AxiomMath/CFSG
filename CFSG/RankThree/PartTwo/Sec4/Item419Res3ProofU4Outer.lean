module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofComp
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
public import CFSG.RankThree.PartTwo.KFacts.K71SU3
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.KF.ClsSUUpper
import CFSG.RankThree.PartOne.KD4L.TriStd

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj StatedScalars)

theorem eq_top_of_isComponent_of_isSimpleGroup {Y : Type*} [Group Y] [Finite Y]
    [hs : IsSimpleGroup Y] {J : Subgroup Y} (hJ : IsComponent J) : J = ⊤ := by
  have hnc : ∃ x y : Y, x * y ≠ y * x := by
    obtain ⟨-, -, a, b, hab⟩ := hJ.1
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨x, y, fun hxy => hab ?_⟩
    have hxy' : x * y = y * x := Subtype.ext hxy
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy']
  have hY := CFSG.RankThree.PartOne.KD4L.isQuasisimple_of_isSimpleGroup hs hnc
  exact eq_of_isComponent_le hJ le_top
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hY)

section Incl

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {σ : K ≃+* K} {f₀ : ℕ}
  (h₀ : UnitaryFieldData p f₀ (fixedField σ))
  (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K)) {m : ℕ}

include hbar in
theorem map_mem_unitarySU_fixedField {g : GL (Fin m) (fixedField σ)}
    (hg : g ∈ unitarySU p f₀ (fixedField σ) m) :
    GeneralLinearGroup.map (fixedField σ).subtype g ∈ unitarySU p f K m := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h₀).mp hg
  have hcoe : ((GeneralLinearGroup.map (fixedField σ).subtype g : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = (g : Matrix (Fin m) (Fin m) (fixedField σ)).map
        (fixedField σ).subtype := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  have hmb : ((g : Matrix (Fin m) (Fin m) (fixedField σ)).map (fixedField σ).subtype).map h.bar =
      ((g : Matrix (Fin m) (Fin m) (fixedField σ)).map h₀.bar).map (fixedField σ).subtype := by
    ext i j
    exact hbar _
  refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
  · rw [hcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · rw [hcoe, hmb, ← Matrix.transpose_map, ← Matrix.map_mul, hu,
      Matrix.map_one _ (map_zero _) (map_one _)]

noncomputable def suInclFix : unitarySU p f₀ (fixedField σ) m →* unitarySU p f K m :=
  ((GeneralLinearGroup.map (fixedField σ).subtype).comp
    (unitarySU p f₀ (fixedField σ) m).subtype).codRestrict (unitarySU p f K m) fun g =>
      map_mem_unitarySU_fixedField h h₀ hbar g.2

theorem coe_suInclFix_apply (g : unitarySU p f₀ (fixedField σ) m) (i j : Fin m) :
    (((suInclFix h h₀ hbar g : unitarySU p f K m) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) i j = ((g : GL (Fin m) (fixedField σ)) i j : K) :=
  GeneralLinearGroup.map_apply _ i j _

theorem suInclFix_injective : Function.Injective (suInclFix h h₀ hbar (m := m)) := by
  intro g g' hgg
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro i j
  apply Subtype.ext
  rw [← coe_suInclFix_apply h h₀ hbar, ← coe_suInclFix_apply h h₀ hbar, hgg]

theorem mem_range_suInclFix_iff (g : unitarySU p f K m) :
    g ∈ (suInclFix h h₀ hbar).range ↔ glAut σ (g : GL (Fin m) K) = g := by
  constructor
  · rintro ⟨g', rfl⟩
    apply Units.ext
    rw [coe_glAut]
    ext i j
    rw [Matrix.map_apply, coe_suInclFix_apply]
    exact fixedField_apply σ _
  · intro hg
    have hfix : ∀ i j, σ (((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j) =
        ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j := by
      intro i j
      have h1 := congrArg (fun x : GL (Fin m) K => (x : Matrix (Fin m) (Fin m) K) i j) hg
      simpa [coe_glAut] using h1
    set M : Matrix (Fin m) (Fin m) (fixedField σ) :=
      fun i j => ⟨((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j,
        (mem_fixedField_iff σ _).mpr (hfix i j)⟩ with hM
    have hMmap : M.map (fixedField σ).subtype =
        ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := rfl
    obtain ⟨hgdet, hgu⟩ := (mem_unitarySU_iff h).mp g.2
    have hdet1 : M.det = 1 := by
      apply (fixedField σ).subtype_injective
      rw [map_one, RingHom.map_det]
      exact (congrArg Matrix.det hMmap).trans hgdet
    have hdet : M.det ≠ 0 := by rw [hdet1]; exact one_ne_zero
    set A : GL (Fin m) (fixedField σ) := GeneralLinearGroup.mkOfDetNeZero M hdet
    have hA : (A : Matrix (Fin m) (Fin m) (fixedField σ)) = M := rfl
    have hAu : A ∈ unitarySU p f₀ (fixedField σ) m := by
      refine (mem_unitarySU_iff h₀).mpr ⟨by rw [hA, hdet1], ?_⟩
      rw [hA]
      have hmb : (M.map (fixedField σ).subtype).map h.bar =
          (M.map h₀.bar).map (fixedField σ).subtype := by
        ext i j
        exact hbar (M i j)
      have key : ((M.map h₀.bar)ᵀ * M).map (fixedField σ).subtype =
          (1 : Matrix (Fin m) (Fin m) (fixedField σ)).map (fixedField σ).subtype := by
        rw [Matrix.map_mul, Matrix.transpose_map, ← hmb, hMmap,
          Matrix.map_one _ (map_zero _) (map_one _)]
        exact hgu
      exact Matrix.map_injective (fixedField σ).subtype_injective key
    refine ⟨⟨A, hAu⟩, ?_⟩
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    rw [coe_suInclFix_apply]
    rfl

end Incl

section PrimeForm

variable {n : ℕ} {K : Type} [Field K]

theorem eq_one_of_pow_four_eq_one [CharP K 2] {c : Kˣ} (hc : c ^ 4 = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ((c : K) - 1) ^ 2 ^ 2 = (c : K) ^ 2 ^ 2 - 1 ^ 2 ^ 2 :=
    sub_pow_char_pow (p := 2) (n := 2) (c : K) 1
  have h2 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have h3 : ((c : K) - 1) ^ 4 = 0 := by
    have h4 : ((c : K) - 1) ^ 4 = (c : K) ^ 4 - 1 := by simpa using h1
    rw [h4, h2, sub_self]
  have h5 : (c : K) - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h3
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h5)

theorem normOneScalars_four_eq_bot (h : UnitaryFieldData 2 n K) (H : Subgroup (GL (Fin 4) K)) :
    normOneScalars h H 4 = ⊥ := by
  have : CharP K 2 := h.charP
  rw [eq_bot_iff]
  rintro g ⟨c, -, hc4, hg⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg, eq_one_of_pow_four_eq_one hc4, map_one]
  rfl

theorem mk'_normOneScalars_injective (h : UnitaryFieldData 2 n K)
    (C : Matrix (Fin 4) (Fin 4) K) :
    Function.Injective (QuotientGroup.mk' (normOneScalars h (gramSU h C) 4)) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  exact normOneScalars_four_eq_bot h _

@[expose] noncomputable def primeFormPEquiv (h : UnitaryFieldData 2 n K)
    (C : Matrix (Fin 4) (Fin 4) K) : gramSU h C ≃* primeFormP h C :=
  MulEquiv.ofBijective (QuotientGroup.mk' (normOneScalars h (gramSU h C) 4))
    ⟨mk'_normOneScalars_injective h C, QuotientGroup.mk'_surjective _⟩

theorem fixSub_primeFormFieldHom_eq (h : UnitaryFieldData 2 n K) {C : GL (Fin 4) K}
    (hC : IsPrimeFormGram C) (φ : K ≃+* K) :
    Item426.fixSub (primeFormFieldHom h hC φ) =
      (Item426.fixSub (primeFormFieldSU h hC φ)).map (primeFormPEquiv h _).toMonoidHom := by
  rw [Item426.map_fixSub_eq]
  congr 1
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  have hsymm : (primeFormPEquiv h _).symm (g : primeFormP h (C : Matrix (Fin 4) (Fin 4) K)) =
      g := (MulEquiv.symm_apply_eq _).mpr rfl
  show primeFormFieldAut h hC φ (g : primeFormP h (C : Matrix (Fin 4) (Fin 4) K)) =
    primeFormPEquiv h _ (primeFormFieldSU h hC φ ((primeFormPEquiv h _).symm
      (g : primeFormP h (C : Matrix (Fin 4) (Fin 4) K))))
  rw [hsymm, primeFormFieldAut_mk]
  rfl

end PrimeForm

theorem fixSub_conj {X : Type*} [Group X] (γ σ : MulAut X) :
    Item426.fixSub (γ * σ * γ⁻¹) = (Item426.fixSub σ).map γ.toMonoidHom := by
  rw [Item426.map_fixSub_eq]
  congr 1

theorem card_unitarySU_four {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F) :
    Nat.card (unitarySU 2 f F 4) =
      (2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1)) := by
  have : CharP F 2 := h.charP
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq h (n := 4) (by norm_num)
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton] at hc
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hc' : (Nat.card (unitarySU 2 f F 4) : ℤ) =
      (((2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1)) : ℕ) : ℤ) := by
    rw [show unitarySU 2 f F 4 = StatedSU 4 (2 ^ f) F from rfl, hc]
    push_cast [h2, h4]
    norm_num
    ring
  exact_mod_cast hc'

theorem outer_case {n : ℕ} (hn : Odd n) {α : MulAut (projSU 4 2 n)} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) {J : Subgroup (projSU 4 2 n)} (hJC : J ≤ Item426.fixSub α)
    (hJ : IsComponent (J.subgroupOf (Item426.fixSub α))) :
    ∃ k : ℕ, Odd k ∧ Nat.card J =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
  have hn1 : 1 ≤ n := hn.pos
  have hU := unitaryFieldData_galoisField 2 n hn1
  have hC : IsPrimeFormGram (1 : GL (Fin 4) (GaloisField 2 (2 * n))) := isPrimeFormGram_one_GL
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (by norm_num)
    (fun h' => absurd h'.1 (by norm_num))
  set P := primeFormP hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) with hPdef
  let e : projSU 4 2 n ≃* P :=
    (projSUEquivStatedProj 4 2 n).trans ((unitaryPSUEquiv hU (by norm_num)).symm.trans e₃.symm)
  set β := MulAut.congr e α with hβdef
  have hβ : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut β := fun h' => hout ((isInnerAut_congr e α).mp h')
  obtain ⟨φ, H, hφ3, hβeq⟩ := WitnessU4.exists_eq_conj_primeFormFieldHom hU hC β hβ hβout
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hβout
    rw [hβeq, map_one, mul_one, mul_inv_cancel]
    exact ⟨1, map_one _⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨f₀, hf, hf₀, hcard⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three hU hσ
  have h₀ : UnitaryFieldData 2 f₀ (fixedField φ) := ⟨Nat.prime_two, hf₀, hcard⟩
  have hbar := KFacts.bar_coe_fixedField hU hf h₀
  have hf₀odd : Odd f₀ := by
    rw [hf] at hn
    exact (Nat.odd_mul.mp hn).2
  have := h₀.finite
  set Y := unitarySU 2 f₀ (fixedField φ) 4 with hYdef
  have hK₀ : Nat.card (fixedField φ) = (2 ^ f₀) ^ 2 := by rw [hcard, ← pow_mul, mul_comm]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (StatedProj (StatedSU 4 (2 ^ f₀) (fixedField φ))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (fixedField φ) 2 f₀ hK₀ 4
      (by norm_num) (by simp)
  have hYs : IsSimpleGroup Y :=
    (CFSG.RankThree.PartOne.KFU.projEquivOfBot
      (CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot hK₀ (by norm_num)
        (Res417Six.gcd_four_two_pow_add_one hf₀))).symm.isSimpleGroup
  set fφ := primeFormFieldHom hU hC φ
  set σS := primeFormFieldSU hU hC φ
  set cH := primeFormConjHom hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) H
  have h1 : (Item426.fixSub α).map e.toMonoidHom = Item426.fixSub β := Item426.map_fixSub_eq e α
  have h2 : Item426.fixSub β = (Item426.fixSub fφ).map cH.toMonoidHom := by
    rw [hβeq, fixSub_conj]
  have h3 : Item426.fixSub fφ = (Item426.fixSub σS).map (primeFormPEquiv hU _).toMonoidHom :=
    fixSub_primeFormFieldHom_eq hU hC φ
  have hSeq : unitarySU 2 n (GaloisField 2 (2 * n)) 4 = gramSU hU
      ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU hU 4
  set ι : Y →* gramSU hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) :=
    (MulEquiv.subgroupCongr hSeq).toMonoidHom.comp (suInclFix hU h₀ hbar) with hιdef
  have hιinj : Function.Injective ι :=
    (MulEquiv.subgroupCongr hSeq).injective.comp (suInclFix_injective hU h₀ hbar)
  have hrange : ι.range = Item426.fixSub σS := by
    ext y
    rw [Item426.mem_fixSub]
    constructor
    · rintro ⟨g₀, rfl⟩
      apply Subtype.ext
      change glAut φ ((suInclFix hU h₀ hbar g₀ : unitarySU 2 n _ 4) : GL (Fin 4) _) = _
      exact (mem_range_suInclFix_iff hU h₀ hbar _).mp ⟨g₀, rfl⟩
    · intro hy
      have hy' : glAut φ (y : GL (Fin 4) (GaloisField 2 (2 * n))) = y := congrArg Subtype.val hy
      have hy2 : (y : GL (Fin 4) (GaloisField 2 (2 * n))) ∈
          unitarySU 2 n (GaloisField 2 (2 * n)) 4 := by
        rw [hSeq]
        exact y.2
      obtain ⟨g₀, hg₀⟩ := (mem_range_suInclFix_iff hU h₀ hbar
        (⟨(y : GL (Fin 4) (GaloisField 2 (2 * n))), hy2⟩ :
          unitarySU 2 n (GaloisField 2 (2 * n)) 4)).mpr hy'
      refine ⟨g₀, Subtype.ext ?_⟩
      change ((suInclFix hU h₀ hbar g₀ : unitarySU 2 n (GaloisField 2 (2 * n)) 4) :
        GL (Fin 4) (GaloisField 2 (2 * n))) = (y : GL (Fin 4) (GaloisField 2 (2 * n)))
      rw [hg₀]
  set Φ : Item426.fixSub α ≃* Y :=
    (((Item426.fixSub α).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (h1.trans h2)).trans
        ((Item426.fixSub fφ).equivMapOfInjective cH.toMonoidHom cH.injective).symm)).trans
      (((MulEquiv.subgroupCongr h3).trans
        ((Item426.fixSub σS).equivMapOfInjective _ (primeFormPEquiv hU _).injective).symm).trans
        ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hιinj).symm))
  have hJY := CFSG.LocalCores.isComponent_map_mulEquiv Φ hJ
  have htop := eq_top_of_isComponent_of_isSimpleGroup hJY
  refine ⟨f₀, hf₀odd, ?_⟩
  calc Nat.card J = Nat.card (J.subgroupOf (Item426.fixSub α)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv).symm
    _ = Nat.card ((J.subgroupOf (Item426.fixSub α)).map Φ.toMonoidHom) :=
        Nat.card_congr ((J.subgroupOf (Item426.fixSub α)).equivMapOfInjective Φ.toMonoidHom
          Φ.injective).toEquiv
    _ = Nat.card (⊤ : Subgroup Y) := by rw [htop]
    _ = Nat.card Y := Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = _ := card_unitarySU_four h₀

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
