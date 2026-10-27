module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowRuTh
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusU3
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open scoped commutatorElement

section Perfect

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem le_of_perfect_commutator_mem {G : Type} [Group G] {P N : Subgroup G}
    (hP : Group.IsPerfect ↥P) (h : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ N) : P ≤ N :=
  (le_of_eq (Subgroup.isPerfect_iff.mp hP).symm).trans (Subgroup.commutator_le.mpr h)

theorem commutator_mem_inner_linear {K : Type} [Field K] {x y : MulAut (projectiveSL 3 K)}
    (hx : x ∈ linearAutGroup 3 K) (hy : y ∈ linearAutGroup 3 K) :
    ⁅x, y⁆ ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hx
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hy
  have key := map_commutatorElement (conjAut 3 K) A B
  rw [← key]
  refine conjAut_mem_range_conj_of_det_eq_pow (μ := 1) ?_
  rw [one_pow, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem perfect_le_inner_projSL (K : Type) [Field K] [Finite K]
    (P : Subgroup (MulAut (projectiveSL 3 K))) (hP : Group.IsPerfect ↥P) :
    P ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hL : P ≤ linearAutGroup 3 K :=
    le_of_perfect_commutator_mem hP fun x _ y _ =>
      OuterDerived.commutator_mem_linearAutGroup le_rfl x y
  exact le_of_perfect_commutator_mem hP fun x hx y hy =>
    commutator_mem_inner_linear (hL hx) (hL hy)

theorem commutator_mem_inner_psuConj {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {x y : MulAut (unitaryPSU h 3)}
    (hx : x ∈ (psuConj h).range) (hy : y ∈ (psuConj h).range) :
    ⁅x, y⁆ ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hy
  have key := map_commutatorElement (psuConj h) A B
  rw [← key]
  refine psuConj_mem_range_conj_of_det_eq_pow (u := 1) ?_ ?_
  · simp [UnitaryFieldData.norm]
  · rw [one_pow]
    have hc : ((⁅A, B⁆ : ↥(unitaryIsom3 h)) : GL (Fin 3) K) =
        ⁅(A : GL (Fin 3) K), (B : GL (Fin 3) K)⁆ := rfl
    rw [hc, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

theorem perfect_le_inner_unitaryPSU {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq2 : 2 < p ^ f) (P : Subgroup (MulAut (unitaryPSU h 3))) (hP : Group.IsPerfect ↥P) :
    P ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  have hL : P ≤ (psuConj h).range :=
    le_of_perfect_commutator_mem hP fun x _ y _ => commutator_mem_psuConj_range h hq2 x y
  exact le_of_perfect_commutator_mem hP fun x hx y hy =>
    commutator_mem_inner_psuConj h (hL hx) (hL hy)

theorem perfect_le_inner_of_mulEquiv {S Q : Type} [Group S] [Group Q] (e : S ≃* Q)
    (hQ : ∀ P : Subgroup (MulAut Q), Group.IsPerfect ↥P →
      P ≤ (MulAut.conj : Q →* MulAut Q).range)
    (P : Subgroup (MulAut S)) (hP : Group.IsPerfect ↥P) :
    P ≤ (MulAut.conj : S →* MulAut S).range := by
  intro x hx
  haveI : Group.IsPerfect ↥(P.map (MulAut.congr e).toMonoidHom) := Group.IsPerfect.map _
  have h1 : MulAut.congr e x ∈ P.map (MulAut.congr e).toMonoidHom := ⟨x, hx, rfl⟩
  exact (isInnerAut_congr e x).mp (hQ _ inferInstance h1)

end Perfect

@[expose] def NoSzModel (Q : Type) [Group Q] : Prop :=
  ∀ β : MulAut Q, β ^ 3 = 1 → ∀ C Y : Subgroup Q, (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
    (Y.subgroupOf C).IsSubnormal → Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card ↥Y → Y = ⊥

open CFSG.RankThree.PartTwo.Sec6.BThreeCensus (map_subgroupOf_subgroupMap) in
theorem noSzModel_of_mulEquiv {S Q : Type} [Group S] [Group Q] (e : S ≃* Q) (h : NoSzModel Q) :
    NoSzModel S := by
  intro β hβ C Y hC hYC hsn hYp hY3
  have hYp' : Group.IsPerfect (Y.map e.toMonoidHom) := Group.IsPerfect.map _
  have key := h (MulAut.congr e β) (by rw [← map_pow, hβ, map_one]) (C.map e.toMonoidHom)
    (Y.map e.toMonoidHom) (fun z => ?_) (Subgroup.map_mono hYC) ?_ hYp' ?_
  · exact (Subgroup.map_eq_bot_iff_of_injective Y e.injective).mp key
  · rw [MulAut.congr_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simp [(hC c).mp hc]
    · intro hz
      refine ⟨e.symm z, (hC _).mpr ?_, by simp⟩
      apply e.injective
      simpa using hz
  · rw [← map_subgroupOf_subgroupMap]
    exact hsn.map (e.subgroupMap C).surjective
  · rwa [Subgroup.card_map_of_injective e.injective]

section SLModel

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec6.BThreeCensus
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {K : Type} [Field K] [Finite K]

theorem noSzModel_projectiveSL_three (h3 : (3 : K) ≠ 0)
    (h3Q : 3 ∣ Nat.card (projectiveSL 3 K)) : NoSzModel (projectiveSL 3 K) := by
  have hsimple : IsSimpleGroup (projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  intro β hβ C Y hC hYC hsn hYp hY3
  have hkerc : Nat.card (proj 3 K).ker = Nat.card (scalars 3 K) := by rw [ker_proj]
  by_cases hD : β ∈ linearAutGroup 3 K
  ·
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq] at hD
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨-, d, hd⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hβ])
    have hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    by_cases hAs : ∃ a : K, (A : Matrix (Fin 3) (Fin 3) K) = a • 1
    ·
      obtain ⟨a, ha⟩ := hAs
      have hβ1 : conjAut 3 K A = 1 := by
        ext x
        obtain ⟨g, rfl⟩ := proj_surjective 3 K x
        rw [conjAut_proj, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [coe_slConjugation]
        calc (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
          _ = (g : Matrix (Fin 3) (Fin 3) K) := by
              rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z, hβ1]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsn with h | h
      · rw [Subgroup.subgroupOf_eq_bot] at h
        rw [eq_bot_iff]
        intro y hy
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy (hYC hy))
      · rw [Subgroup.subgroupOf_eq_top] at h
        exfalso
        apply hY3
        have htop : (⊤ : Subgroup (projectiveSL 3 K)) ≤ Y := by
          rw [← hCtop]
          exact h
        rw [show Y = ⊤ from eq_top_iff.mpr htop, Subgroup.card_top]
        exact h3Q
    · push Not at hAs
      obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (proj_surjective 3 K) Y
        (by rw [hkerc]; exact coprime_card_scalars hY3)
      obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
      have hfix : ∀ y ∈ Y', slConjugation 3 K A y = y := by
        refine eq_of_mul_inv_mem_center (hY'p hYp)
          (slConjugation 3 K A).toMonoidHom fun y hy => ?_
        rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
        have hyY : proj 3 K y ∈ Y := hY'map ▸ ⟨y, hy, rfl⟩
        have h1 := (hC _).mp (hYC hyY)
        rw [conjAut_proj] at h1
        change proj 3 K (slConjugation 3 K A y) * (proj 3 K y)⁻¹ = 1
        rw [h1, mul_inv_cancel]
      set Y'' : Subgroup (GL (Fin 3) K) := Y'.map SpecialLinearGroup.toGL with hY''
      have hY''bot : Y'' = ⊥ := by
        refine eq_bot_of_commute_glThree_of_pow_three_eq_smul h3 hA3 hAs Y'' ?_ ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          apply Units.ext
          have h1 := congrArg (fun z : SpecialLinearGroup (Fin 3) K =>
            (z : Matrix (Fin 3) (Fin 3) K)) (hfix y hy)
          simp only [coe_slConjugation] at h1
          change (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
            (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)
          calc (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
              (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (A : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
            _ = (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) := by
                rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
        · have := hY'p hYp
          exact Group.IsPerfect.map _
        · rwa [Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective, hY'card]
      have hY'bot : Y' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective Y' SpecialLinearGroup.toGL_injective).mp hY''bot
      rw [← hY'map, hY'bot, Subgroup.map_bot]
  ·
    obtain ⟨σ, hσ3, H, hβH⟩ := linear_order_three_field_descent (by norm_num) β hβ hD
    set τ := conjAut 3 K H with hτ
    set C₀ : Subgroup (projectiveSL 3 K) :=
      (fieldAut 3 K σ).toMonoidHom.eqLocus (MonoidHom.id _) with hC₀
    set Y₀ : Subgroup (projectiveSL 3 K) := Y.map (τ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom
      with hY₀
    have hβτ : ∀ z, β z = z ↔ fieldAut 3 K σ (τ⁻¹ z) = τ⁻¹ z := by
      intro z
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply]
      constructor
      · intro h
        have := congrArg (τ⁻¹ : MulAut (projectiveSL 3 K)) h
        rwa [show τ⁻¹ (τ (fieldAut 3 K σ (τ⁻¹ z))) = fieldAut 3 K σ (τ⁻¹ z) from
          τ.symm_apply_apply _] at this
      · intro h
        rw [h]
        exact τ.apply_symm_apply z
    have hY₀C₀ : Y₀ ≤ C₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hβτ y).mp ((hC y).mp (hYC hy))
    have hsn₀ : (Y₀.subgroupOf C₀).IsSubnormal := by
      let ρ : C →* C₀ :=
        ((τ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom.comp C.subtype).codRestrict C₀ fun c =>
          (hβτ c).mp ((hC c).mp c.2)
      have hρ : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        have hτz : τ⁻¹ (τ z) = z := τ.symm_apply_apply z
        refine ⟨⟨τ z, (hC _).mpr ((hβτ _).mpr ?_)⟩, ?_⟩
        · rw [hτz]
          exact hz
        · apply Subtype.ext
          exact hτz
      have hmap : (Y.subgroupOf C).map ρ = Y₀.subgroupOf C₀ := by
        ext ⟨z, hz⟩
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, hcz⟩
          refine ⟨c, hc, ?_⟩
          exact congrArg Subtype.val hcz
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
      rw [← hmap]
      exact hsn.map hρ
    have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
      rwa [hY₀, Subgroup.card_map_of_injective
        (f := (τ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom) (MulEquiv.injective _)]
    have hY₀p : Group.IsPerfect Y₀ := by
      have := hYp
      exact Group.IsPerfect.map _
    obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (proj_surjective 3 K) Y₀
      (by rw [hkerc]; exact coprime_card_scalars hY₀3)
    obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
    have hfix : ∀ y ∈ Y', SpecialLinearGroup.map σ.toRingHom y = y := by
      refine eq_of_mul_inv_mem_center (hY'p hY₀p) (SpecialLinearGroup.map σ.toRingHom)
        fun y hy => ?_
      rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv,
        ← fieldAut_proj]
      have hyY : proj 3 K y ∈ C₀ := hY₀C₀ (hY'map ▸ ⟨y, hy, rfl⟩)
      have h1 : fieldAut 3 K σ (proj 3 K y) = proj 3 K y := hyY
      rw [h1, mul_inv_cancel]
    set ψ := SpecialLinearGroup.map (n := Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ).subtype with hψ
    have hψi : Function.Injective ψ := sl_map_subtype_injective σ
    have hY'ψ : Y' ≤ ψ.range := fun y hy => by
      obtain ⟨y₀, hy₀⟩ := exists_sl_map_subtype_eq (hfix y hy)
      exact ⟨y₀, hy₀⟩
    set V := Y'.comap ψ with hV
    set V₁ := Y₀.comap ((proj 3 K).comp ψ) with hV₁
    have hVmap : V.map ψ = Y' := Subgroup.map_comap_eq_self hY'ψ
    have hV3 : ¬ 3 ∣ Nat.card V := by
      rw [← Subgroup.card_map_of_injective hψi, hVmap, hY'card]
      exact hY₀3
    have hVV₁ : V ≤ V₁ := fun s hs => by
      change proj 3 K (ψ s) ∈ Y₀
      rw [← hY'map]
      exact ⟨ψ s, hs, rfl⟩
    have hV₁V : V₁ ≤ V ⊔ scalars 3 (CFSG.GH74.GLS.IVK.fixedField σ) := by
      intro s hs
      have hs' : proj 3 K (ψ s) ∈ Y'.map (proj 3 K) := by rw [hY'map]; exact hs
      obtain ⟨y, hy, hys⟩ := hs'
      obtain ⟨t, ht⟩ := hY'ψ hy
      have htV : t ∈ V := by
        change ψ t ∈ Y'
        rw [ht]
        exact hy
      have hz : ψ (t⁻¹ * s) ∈ scalars 3 K := by
        rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, map_inv, hys,
          inv_mul_cancel]
      have hzs : t⁻¹ * s ∈ scalars 3 (CFSG.GH74.GLS.IVK.fixedField σ) := by
        obtain ⟨c, hc, hcz⟩ := hz
        set w := t⁻¹ * s with hw
        have hdiag : (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) =
            (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 • 1 := by
          apply eq_smul_one_of_map_eq_smul_one (CFSG.GH74.GLS.IVK.fixedField σ).subtype
          rw [show (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)).map
              (CFSG.GH74.GLS.IVK.fixedField σ).subtype = (ψ w : Matrix (Fin 3) (Fin 3) K) from rfl,
            hcz, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        have hdet := w.2
        rw [hdiag, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
        have hw0 : (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by norm_num)] at hdet
          exact zero_ne_one hdet
        refine ⟨Units.mk0 _ hw0, Units.ext (by simpa using hdet), ?_⟩
        rw [Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
        exact hdiag
      have : s = t * (t⁻¹ * s) := by group
      rw [this]
      exact Subgroup.mul_mem_sup htV hzs
    have hsn₁ : V₁.IsSubnormal := by
      let θ : SpecialLinearGroup (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ) →* C₀ :=
        ((proj 3 K).comp ψ).codRestrict C₀ fun s => by
          change fieldAut 3 K σ (proj 3 K (ψ s)) = proj 3 K (ψ s)
          rw [fieldAut_proj]
          congr 1
          ext i j
          exact CFSG.GH74.GLS.IVK.fixedField_apply σ _
      have hcomap : (Y₀.subgroupOf C₀).comap θ = V₁ := by
        ext s
        rfl
      rw [← hcomap]
      exact hsn₀.comap θ
    have hVbot := eq_bot_of_le_of_isSubnormal_sl3 hV3 hVV₁ hV₁V hsn₁
    have hY'bot : Y' = ⊥ := by rw [← hVmap, hVbot, Subgroup.map_bot]
    have hY₀bot : Y₀ = ⊥ := by rw [← hY'map, hY'bot, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective Y
      (τ⁻¹ : MulAut (projectiveSL 3 K)).injective).mp hY₀bot

end SLModel

section PSUModel

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec6.BThreeCensus
open CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {p f : ℕ} {K : Type} [Field K] [Finite K]

theorem noSzModel_unitaryPSU (h3 : (3 : K) ≠ 0)
    (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) (h3Q : 3 ∣ Nat.card (unitaryPSU h 3)) :
    NoSzModel (unitaryPSU h 3) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hsimple : IsSimpleGroup (unitaryPSU h 3) := by
    have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl
      (by
        intro h32
        have := congrArg Prod.snd h32
        simp only at this
        omega)
    exact (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
  have hcen : Subgroup.center (unitarySU p f K 3) = unitaryScalars h 3 :=
    center_unitarySU_three (h := h) hq2
  have hkerc : Nat.card (unitaryProj h 3).ker = Nat.card (unitaryScalars h 3) := by
    rw [ker_unitaryProj]
  intro β hβ C Y hC hYC hsn hYp hY3
  by_cases hD : β ∈ (psuConj h).range
  ·
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨-, d, -, hd⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hβ])
    have hA3 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    by_cases hAs : ∃ a : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a • 1
    ·
      obtain ⟨a, ha⟩ := hAs
      have ha0 : a ≠ 0 := by
        rintro rfl
        have hdet := ((A : GL (Fin 3) K)).isUnit.map Matrix.detMonoidHom
        rw [ha, zero_smul] at hdet
        simp at hdet
      have hAeq : (A : GL (Fin 3) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha0) := by
        apply Units.ext
        rw [ha, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
      have hβ1 : psuConj h A = 1 := by
        have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha0) ∈ unitaryIsom3 h :=
          hAeq ▸ A.2
        have := psuConj_scalar hmem
        rwa [show (⟨_, hmem⟩ : unitaryIsom3 h) = A from Subtype.ext hAeq.symm] at this
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z, hβ1]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsn with hb | ht
      · rw [Subgroup.subgroupOf_eq_bot] at hb
        rw [eq_bot_iff]
        intro y hy
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hb hy (hYC hy))
      · rw [Subgroup.subgroupOf_eq_top] at ht
        exfalso
        apply hY3
        have htop : (⊤ : Subgroup (unitaryPSU h 3)) ≤ Y := by
          rw [← hCtop]
          exact ht
        rw [show Y = ⊤ from eq_top_iff.mpr htop, Subgroup.card_top]
        exact h3Q
    · push Not at hAs
      obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (unitaryProj_surjective h 3) Y
        (by rw [hkerc]; exact coprime_card_unitaryScalars h hY3)
      obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
      have hfix : ∀ y ∈ Y', suConj h A y = y := by
        refine eq_of_mul_inv_mem_center (hY'p hYp) (suConj h A).toMonoidHom fun y hy => ?_
        rw [hcen, ← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv]
        have hyY : unitaryProj h 3 y ∈ Y := hY'map ▸ ⟨y, hy, rfl⟩
        have h1 := (hC _).mp (hYC hyY)
        rw [unitaryProj_apply, psuConj_mk] at h1
        change unitaryProj h 3 (suConj h A y) * (unitaryProj h 3 y)⁻¹ = 1
        rw [unitaryProj_apply, unitaryProj_apply, h1, mul_inv_cancel]
      set Y'' : Subgroup (GL (Fin 3) K) := Y'.map (unitarySU p f K 3).subtype with hY''
      have hY''bot : Y'' = ⊥ := by
        refine eq_bot_of_commute_glThree_of_pow_three_eq_smul h3 hA3 hAs Y'' ?_ ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          have h1 := congrArg (fun z : unitarySU p f K 3 => (z : GL (Fin 3) K)) (hfix y hy)
          simp only [coe_suConj, Subgroup.coe_inv] at h1
          change (y : GL (Fin 3) K) * (A : GL (Fin 3) K) = (A : GL (Fin 3) K) * (y : GL (Fin 3) K)
          calc (y : GL (Fin 3) K) * (A : GL (Fin 3) K) =
              (A : GL (Fin 3) K) * (y : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ *
                (A : GL (Fin 3) K) := by rw [h1]
            _ = (A : GL (Fin 3) K) * (y : GL (Fin 3) K) := by group
        · have := hY'p hYp
          exact Group.IsPerfect.map _
        · rwa [Subgroup.card_map_of_injective (unitarySU p f K 3).subtype_injective, hY'card]
      have hY'bot : Y' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective Y' (unitarySU p f K 3).subtype_injective).mp
          hY''bot
      rw [← hY'map, hY'bot, Subgroup.map_bot]
  ·
    obtain ⟨σ, hσ3, H, hβH⟩ := unitary_order_three_field_descent hq2 β hβ hD
    set τ := psuConj h H with hτ
    set C₀ : Subgroup (unitaryPSU h 3) := (psuField h σ).toMonoidHom.eqLocus (MonoidHom.id _)
      with hC₀
    set Y₀ : Subgroup (unitaryPSU h 3) := Y.map (τ⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom
      with hY₀
    have hβτ : ∀ z, β z = z ↔ psuField h σ (τ⁻¹ z) = τ⁻¹ z := by
      intro z
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply]
      constructor
      · intro h'
        have := congrArg (τ⁻¹ : MulAut (unitaryPSU h 3)) h'
        rwa [show τ⁻¹ (τ (psuField h σ (τ⁻¹ z))) = psuField h σ (τ⁻¹ z) from
          τ.symm_apply_apply _] at this
      · intro h'
        rw [h']
        exact τ.apply_symm_apply z
    have hY₀C₀ : Y₀ ≤ C₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hβτ y).mp ((hC y).mp (hYC hy))
    have hsn₀ : (Y₀.subgroupOf C₀).IsSubnormal := by
      let ρ : C →* C₀ :=
        ((τ⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom.comp C.subtype).codRestrict C₀ fun c =>
          (hβτ c).mp ((hC c).mp c.2)
      have hρ : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        have hτz : τ⁻¹ (τ z) = z := τ.symm_apply_apply z
        refine ⟨⟨τ z, (hC _).mpr ((hβτ _).mpr ?_)⟩, ?_⟩
        · rw [hτz]
          exact hz
        · apply Subtype.ext
          exact hτz
      have hmap : (Y.subgroupOf C).map ρ = Y₀.subgroupOf C₀ := by
        ext ⟨z, hz⟩
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, hcz⟩
          exact ⟨c, hc, congrArg Subtype.val hcz⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
      rw [← hmap]
      exact hsn.map hρ
    have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
      rwa [hY₀, Subgroup.card_map_of_injective
        (f := (τ⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom) (MulEquiv.injective _)]
    have hY₀p : Group.IsPerfect Y₀ := by
      have := hYp
      exact Group.IsPerfect.map _
    obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (unitaryProj_surjective h 3) Y₀
      (by rw [hkerc]; exact coprime_card_unitaryScalars h hY₀3)
    obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
    have hfix : ∀ y ∈ Y', suField h σ y = y := by
      refine eq_of_mul_inv_mem_center (hY'p hY₀p) (suField h σ).toMonoidHom fun y hy => ?_
      rw [hcen, ← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv]
      have hyY : unitaryProj h 3 y ∈ C₀ := hY₀C₀ (hY'map ▸ ⟨y, hy, rfl⟩)
      have h1 : psuField h σ (unitaryProj h 3 y) = unitaryProj h 3 y := hyY
      rw [unitaryProj_apply, psuField_mk] at h1
      change unitaryProj h 3 (suField h σ y) * (unitaryProj h 3 y)⁻¹ = 1
      rw [unitaryProj_apply, unitaryProj_apply, h1, mul_inv_cancel]
    obtain ⟨f₀, hf, hf₀, hcard₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
    have h₀ : UnitaryFieldData p f₀ (CFSG.GH74.GLS.IVK.fixedField σ) := ⟨h.prime, hf₀, hcard₀⟩
    have hbar := bar_coe_fixedField h hf h₀
    have : Finite (CFSG.GH74.GLS.IVK.fixedField σ) := Subtype.finite
    set ψ := suIncl h h₀ hbar with hψ
    have hψi : Function.Injective ψ := suIncl_injective h h₀ hbar
    have hY'ψ : Y' ≤ ψ.range := fun y hy => (mem_range_suIncl_iff h h₀ hbar y).mpr (hfix y hy)
    set V := Y'.comap ψ with hV
    have hVmap : V.map ψ = Y' := Subgroup.map_comap_eq_self hY'ψ
    have hVcard : Nat.card V = Nat.card Y₀ := by
      rw [← Subgroup.card_map_of_injective hψi, hVmap, hY'card]
    have hV3 : ¬ 3 ∣ Nat.card V := by rw [hVcard]; exact hY₀3
    have hVbot : V = ⊥ := by
      by_cases hq₀ : p ^ f₀ = 2
      · refine eq_bot_of_isPerfect_su3_two h₀ hq₀ V ?_ hV3
        have hVe : V ≃* Y' :=
          (MonoidHom.ofInjective (f := ψ.comp V.subtype) (hψi.comp V.subtype_injective)).trans
            (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype, hVmap]))
        have := hY'p hY₀p
        exact Group.IsPerfect.ofSurjective (f := hVe.symm.toMonoidHom) hVe.symm.surjective
      · have hq₀2 : 2 < p ^ f₀ := by
          have h1 : 2 ≤ p ^ f₀ := le_trans h.prime.two_le (Nat.le_self_pow (by omega) p)
          omega
        set V₁ := Y₀.comap ((unitaryProj h 3).comp ψ) with hV₁
        have hVV₁ : V ≤ V₁ := fun s hs => by
          change unitaryProj h 3 (ψ s) ∈ Y₀
          rw [← hY'map]
          exact ⟨ψ s, hs, rfl⟩
        have hV₁V : V₁ ≤ V ⊔ unitaryScalars h₀ 3 := by
          intro s hs
          have hs' : unitaryProj h 3 (ψ s) ∈ Y'.map (unitaryProj h 3) := by
            rw [hY'map]; exact hs
          obtain ⟨y, hy, hys⟩ := hs'
          obtain ⟨t, ht⟩ := hY'ψ hy
          have htV : t ∈ V := by
            change ψ t ∈ Y'
            rw [ht]
            exact hy
          have hz : ψ (t⁻¹ * s) ∈ unitaryScalars h 3 := by
            rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, map_inv, hys,
              inv_mul_cancel]
          have hzs : t⁻¹ * s ∈ unitaryScalars h₀ 3 := by
            obtain ⟨c, -, -, hcz⟩ := hz
            set w := t⁻¹ * s with hw
            have hdiag : ((w : GL (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) :
                Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) =
                ((w : GL (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) :
                  Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 • 1 := by
              apply eq_smul_one_of_map_eq_smul_one (CFSG.GH74.GLS.IVK.fixedField σ).subtype
                (a := (c : K))
              have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hcz
              simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
              rw [← Matrix.smul_one_eq_diagonal] at h2
              ext i j
              have h3' := congrFun (congrFun h2 i) j
              rw [coe_suIncl_apply h h₀ hbar] at h3'
              rw [Matrix.map_apply]
              exact h3'
            have hdet := ((mem_unitarySU_iff h₀).mp w.2).1
            rw [hdiag, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
            have hw0 : ((w : GL (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) :
                Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 ≠ 0 := by
              intro h0
              rw [h0, zero_pow (by norm_num)] at hdet
              exact zero_ne_one hdet
            rw [unitaryScalars_eq h₀ (by norm_num), Subgroup.mem_subgroupOf]
            refine ⟨Units.mk0 _ hw0, Units.ext ?_⟩
            rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
              ← Matrix.smul_one_eq_diagonal]
            exact hdiag.symm
          have : s = t * (t⁻¹ * s) := by group
          rw [this]
          exact Subgroup.mul_mem_sup htV hzs
        have hsn₁ : V₁.IsSubnormal := by
          let θ : unitarySU p f₀ (CFSG.GH74.GLS.IVK.fixedField σ) 3 →* C₀ :=
            ((unitaryProj h 3).comp ψ).codRestrict C₀ fun s => by
              change psuField h σ (unitaryProj h 3 (ψ s)) = unitaryProj h 3 (ψ s)
              rw [unitaryProj_apply, psuField_mk,
                (mem_range_suIncl_iff h h₀ hbar (ψ s)).mp ⟨s, rfl⟩]
          have hcomap : (Y₀.subgroupOf C₀).comap θ = V₁ := by
            ext s
            rfl
          rw [← hcomap]
          exact hsn₀.comap θ
        exact eq_bot_of_le_of_isSubnormal_su3 h₀ hq₀2 hV3 hVV₁ hV₁V hsn₁
    have hY'bot : Y' = ⊥ := by rw [← hVmap, hVbot, Subgroup.map_bot]
    have hY₀bot : Y₀ = ⊥ := by rw [← hY'map, hY'bot, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective Y
      (τ⁻¹ : MulAut (unitaryPSU h 3)).injective).mp hY₀bot

end PSUModel

section Rows

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitarySU)
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec6.BThreeCensus (three_ne_zero_of_charP)

theorem rowOf143_l3 (p e : ℕ) [Fact p.Prime] (hp3 : p ≠ 3)
    (he : 1 ≤ e) : RowOf143 (projSL 3 (GaloisField p e)) := by
  unfold RowOf143
  intro S _ _ hS hnc ⟨φ⟩ h3
  obtain ⟨τ₀⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p e)
  set e' : S ≃* projectiveSL 3 (GaloisField p e) := φ.trans τ₀ with he'def
  have h3' : 3 ∣ Nat.card (projectiveSL 3 (GaloisField p e)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact h3
  have hN := noSzModel_of_mulEquiv e'
    (noSzModel_projectiveSL_three (three_ne_zero_of_charP (F := GaloisField p e) hp3) h3')
  exact row143_of_inner_kgroup hS hnc
    (fun P _ hPp _ => perfect_le_inner_of_mulEquiv e'
      (fun Q hQ => perfect_le_inner_projSL (GaloisField p e) Q hQ) P hPp)
    (fun β hβ Y hYfix hYsub _ hYp hY3 =>
      hN β hβ (Sec4.autFix β) Y (fun z => Sec4.mem_autFix) hYfix hYsub hYp hY3)

theorem rowOf143_u3 (p e : ℕ) [Fact p.Prime] (hp3 : p ≠ 3)
    (he : 1 ≤ e) (hq : 2 < p ^ e) : RowOf143 (projSU 3 p e) := by
  unfold RowOf143
  intro S _ _ hS hnc ⟨φ⟩ h3
  have h : UnitaryFieldData p e (GaloisField p (2 * e)) :=
    ⟨Fact.out, he, GaloisField.card p (2 * e) (by omega)⟩
  obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  set e' : S ≃* unitaryPSU h 3 := φ.trans ψ.symm with he'def
  have h3' : 3 ∣ Nat.card (unitaryPSU h 3) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact h3
  have hN := noSzModel_of_mulEquiv e'
    (noSzModel_unitaryPSU (three_ne_zero_of_charP (F := GaloisField p (2 * e)) hp3) h hq h3')
  exact row143_of_inner_kgroup hS hnc
    (fun P _ hPp _ => perfect_le_inner_of_mulEquiv e'
      (fun Q hQ => perfect_le_inner_unitaryPSU h hq Q hQ) P hPp)
    (fun β hβ Y hYfix hYsub _ hYp hY3 =>
      hN β hβ (Sec4.autFix β) Y (fun z => Sec4.mem_autFix) hYfix hYsub hYp hY3)

theorem rowOf143_projSU_three_two_one : RowOf143 (projSU 3 2 1) := by
  unfold RowOf143
  intro S _ _ hS hnc ⟨φ⟩ _
  exfalso
  haveI := hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
    ⟨Nat.prime_two, le_rfl, GaloisField.card 2 (2 * 1) (by norm_num)⟩
  obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  have h216 : Nat.card (unitarySU 2 1 (GaloisField 2 (2 * 1)) 3) = 216 := by
    rw [card_unitarySU_three h]
    norm_num
  have hdvd : Nat.card S ∣ 2 ^ 3 * 3 ^ 3 := by
    rw [Nat.card_congr (φ.trans ψ.symm).toEquiv, show (2 : ℕ) ^ 3 * 3 ^ 3 = 216 by norm_num,
      ← h216]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨y, z, hy, hz, hyz⟩ := dvd_mul.mp hdvd
  obtain ⟨c, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨d, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  haveI : Fintype S := Fintype.ofFinite S
  have hsolv : Group.IsSolvable S :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := c) (b := d)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hyz)
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem rowOf143_u3_two (n : ℕ) (hn : 1 ≤ n) :
    RowOf143 (projSU 3 2 n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    exact rowOf143_projSU_three_two_one
  · exact rowOf143_u3 2 n (by norm_num) hn
      (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) h2))

theorem k143_rows_three :
    (∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf143 (projSL 3 (GaloisField p e))) ∧
    (∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf143 (projSU 3 p e)) ∧
    (∀ n : ℕ, 1 ≤ n → RowOf143 (projSL 3 (GaloisField 2 n))) ∧
    (∀ n : ℕ, 1 ≤ n → RowOf143 (projSU 3 2 n)) := by
  refine ⟨fun p e _ hp he _ => rowOf143_l3 p e (by omega) he,
    fun p e _ hp he _ => rowOf143_u3 p e (by omega) he
      (lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)),
    fun n hn => rowOf143_l3 2 n (by norm_num) hn, fun n hn => rowOf143_u3_two n hn⟩

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
