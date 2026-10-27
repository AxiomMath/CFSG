module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Field
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
import CFSG.CharacterTheory.Burnside
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec13.Item134Residual

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

variable {p f : ℕ} {K : Type} [Field K]

theorem nonempty_fixSub_suField_equiv (h : UnitaryFieldData p f K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    Nonempty (unitarySU p (f / 3) (fixedField σ) 3 ≃* fixSub (suField h σ)) := by
  set K₀ := fixedField σ with hK₀
  have h₀ : UnitaryFieldData p (f / 3) K₀ :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ
  have hbar : ∀ c : K₀, (h₀.bar c : K) = h.bar c :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσ
  set ιGL := CFSG.RankThree.Classical.subfieldGL K₀ 3 with hιGL
  have hmemiff : ∀ g₀ : GL (Fin 3) K₀,
      ιGL g₀ ∈ unitarySU p f K 3 ↔ g₀ ∈ unitarySU p (f / 3) K₀ 3 := by
    intro g₀
    rw [mem_unitarySU_iff h, mem_unitarySU_iff h₀, CFSG.RankThree.Classical.coe_subfieldGL,
      CFSG.RankThree.Classical.map_subtype_map_bar h h₀ hbar, ← transpose_map,
      ← Matrix.map_mul]
    have hinj := Matrix.map_injective (m := Fin 3) (n := Fin 3)
      (f := (K₀.subtype : K₀ → K)) Subtype.val_injective
    constructor
    · rintro ⟨hdet, hu⟩
      refine ⟨?_, hinj ?_⟩
      · apply K₀.subtype_injective
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hdet, map_one]
      · change ((((g₀ : Matrix (Fin 3) (Fin 3) K₀).map h₀.bar)ᵀ * g₀).map K₀.subtype) =
          (1 : Matrix (Fin 3) (Fin 3) K₀).map K₀.subtype
        rw [hu, Matrix.map_one _ (map_zero _) (map_one _)]
    · rintro ⟨hdet, hu⟩
      refine ⟨?_, ?_⟩
      · change (K₀.subtype.mapMatrix (g₀ : Matrix (Fin 3) (Fin 3) K₀)).det = 1
        rw [← RingHom.map_det, hdet, map_one]
      · rw [hu, Matrix.map_one _ (map_zero _) (map_one _)]
  let ι : unitarySU p (f / 3) K₀ 3 →* unitarySU p f K 3 :=
    (ιGL.comp (unitarySU p (f / 3) K₀ 3).subtype).codRestrict _ fun g₀ => (hmemiff g₀).mpr g₀.2
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (CFSG.RankThree.Classical.subfieldGL_injective K₀ 3 (congrArg Subtype.val hab))
  have hrange : ι.range = fixSub (suField h σ) := by
    ext g
    constructor
    · rintro ⟨g₀, rfl⟩
      rw [mem_fixSub]
      apply Subtype.ext
      apply Units.ext
      rw [coe_suField, coe_glAut]
      change (((g₀ : GL (Fin 3) K₀) : Matrix (Fin 3) (Fin 3) K₀).map K₀.subtype).map σ =
        ((g₀ : GL (Fin 3) K₀) : Matrix (Fin 3) (Fin 3) K₀).map K₀.subtype
      refine Matrix.ext fun i j => ?_
      exact RingHom.mem_eqLocusField.mp
        (((g₀ : GL (Fin 3) K₀) : Matrix (Fin 3) (Fin 3) K₀) i j).2
    · intro hg
      rw [mem_fixSub] at hg
      have hg' : glAut σ (g : GL (Fin 3) K) = g := by
        rw [← coe_suField (h := h) σ g, hg]
      obtain ⟨g₀, hg₀⟩ := CFSG.RankThree.Classical.exists_subfieldGL_eq_of_fixed (n := 3) hg'
      have hmem : g₀ ∈ unitarySU p (f / 3) K₀ 3 := (hmemiff g₀).mp (by rw [hg₀]; exact g.2)
      exact ⟨⟨g₀, hmem⟩, Subtype.ext hg₀⟩
  exact ⟨(MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)⟩

theorem card_SU_three_ne {r : ℕ} (hr : 3 ≤ r) : r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) ≠ 1080 := by
  have h1 : 27 ≤ r ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have h2 : 8 ≤ r ^ 2 - 1 := by
    have : 9 ≤ r ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
    omega
  have h4 : 28 ≤ r ^ 3 + 1 := by omega
  have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
  omega

theorem isPGroup_center_unitarySU {e : ℕ} {K₀ : Type} [Field K₀] (h₀ : UnitaryFieldData p e K₀)
    (hZ : Subgroup.center (unitarySU p e K₀ 3) =
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K₀).subgroupOf (unitarySU p e K₀ 3)) :
    IsPGroup 3 (Subgroup.center (unitarySU p e K₀ 3)) := by
  intro z
  refine ⟨1, ?_⟩
  have hz : (z : unitarySU p e K₀ 3) ∈
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K₀).subgroupOf (unitarySU p e K₀ 3) :=
    hZ ▸ z.2
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet : ((((z : unitarySU p e K₀ 3) : GL (Fin 3) K₀)) : Matrix (Fin 3) (Fin 3) K₀).det =
      1 := ((mem_unitarySU_iff h₀).mp (z : unitarySU p e K₀ 3).2).1
  have hc3 : c ^ 3 = 1 := by
    have h1 := Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) c
    rw [hc, Fintype.card_fin] at h1
    apply Units.ext
    rw [← h1, Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  rw [pow_one]
  apply Subtype.ext
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, ← hc, ← map_pow, hc3, map_one]
  rfl

theorem suThreeFieldComponent : K426.SUThreeFieldComponent := by
  intro p f K _ h hq hp3 α hα3 hF P hP htc
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Finite K := h.finite
  have hK2 : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h' => by
    have := (Prod.mk.inj h').2
    omega
  have hperf : Group.IsPerfect (unitarySU p f K 3) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK2 le_rfl hnq).1.1
  obtain ⟨φ, ⟨σ, rfl⟩, hφ1, d, ⟨A, rfl⟩, hτ⟩ := hF
  set γ := suConj h A with hγ
  set σs := suField h σ with hσs
  have hα : γ * σs * γ⁻¹ = α := by
    apply mulAut_eq_of_forall_inv_mul_mem_center hperf
    intro g
    rw [center_unitarySU_three (h := h) hq]
    have h1 : (((γ * σs * γ⁻¹) g : unitarySU p f K 3) : unitaryPSU h 3) =
        (psuConj h A * psuField h σ * (psuConj h A)⁻¹) (g : unitaryPSU h 3) := by
      rw [← map_inv (psuConj h) A, ← map_inv (suConj h) A]
      rfl
    have h2 : ((α g : unitarySU p f K 3) : unitaryPSU h 3) =
        (MulAut.congr (suCenterEquiv h hq) (centerDescend _ α)) (g : unitaryPSU h 3) := rfl
    rw [hτ] at h2
    exact QuotientGroup.eq.mp (h1.trans h2.symm)
  have hφ3 : psuField h σ ^ 3 = 1 := by
    have hτ3 : (psuConj h A * psuField h σ * (psuConj h A)⁻¹) ^ 3 = 1 := by
      rw [← hτ, ← map_pow, ← map_pow, hα3, map_one, map_one]
    rw [conj_pow] at hτ3
    have := congrArg (fun x => (psuConj h A)⁻¹ * x * psuConj h A) hτ3
    simpa [mul_assoc] using this
  have hσ3 : σ ^ 3 = 1 :=
    (eq_one_of_psuConj_mul_psuField_eq_one (h := h) 1 (σ ^ 3)
      (by rw [map_one, one_mul, map_pow, hφ3])).1
  have hσ1 : σ ≠ 1 := fun h1 => hφ1 (by rw [h1, map_one])
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hcongr : MulAut.congr γ σs = γ * σs * γ⁻¹ := by
    ext x
    rfl
  have hfix : MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) =
      (fixSub σs).map γ.toMonoidHom := by
    rw [← hα, ← hcongr, map_fixSub_eq]
  rw [hfix] at hP
  have hP₁ := map_mem_thetaComponentsIn γ.symm hP
  have hmm : ((fixSub σs).map γ.toMonoidHom).map γ.symm.toMonoidHom = fixSub σs := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (fixSub σs)
    ext x
    simp
  rw [hmm] at hP₁
  obtain ⟨P₁', hP₁', hP₁eq⟩ := hP₁
  obtain ⟨e₀⟩ := nonempty_fixSub_suField_equiv h hσo
  set K₀ := fixedField σ with hK₀def
  have hP₂ := map_mulEquiv_mem_thetaComponents Nat.prime_three e₀.symm hP₁'
  set P₂ := P₁'.map e₀.symm.toMonoidHom with hP₂def
  let eP : P ≃* P₂ :=
    ((P.equivMapOfInjective γ.symm.toMonoidHom γ.symm.injective).trans
      ((MulEquiv.subgroupCongr hP₁eq.symm).trans
        (P₁'.equivMapOfInjective (fixSub σs).subtype (fixSub σs).subtype_injective).symm)).trans
      (P₁'.equivMapOfInjective e₀.symm.toMonoidHom e₀.symm.injective)
  have htc₂ : IsTripleCover (P₂ ⧸ aschbacherSolvableCore 3 P₂) (alternatingGroup (Fin 6)) :=
    isTripleCover_of_mulEquiv (quotThetaEquiv eP) htc
  have hcard₂ : Nat.card (P₂ ⧸ aschbacherSolvableCore 3 P₂) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six htc₂.isExtOf
  have hP₂1 : P₂ ≠ ⊥ := by
    intro hbot
    have h2 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 P₂)
    rw [hcard₂, Subgroup.card_eq_one.mpr hbot] at h2
    omega
  have h₀ : UnitaryFieldData p (f / 3) K₀ :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσo
  have : Finite K₀ := h₀.finite
  have : CharP K₀ p := h₀.charP
  have hK₀ : Nat.card K₀ = (p ^ (f / 3)) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  by_cases hr : p ^ (f / 3) = 2
  ·
    have hp2 : p = 2 := by
      have hp := h.prime.two_le
      have hf : 1 ≤ f / 3 := h₀.one_le
      have : p ≤ p ^ (f / 3) := Nat.le_self_pow (by omega) p
      omega
    have hf1 : f / 3 = 1 := by
      subst hp2
      exact Nat.pow_right_injective le_rfl (hr.trans (pow_one 2).symm)
    have h₂ : UnitaryFieldData 2 (f / 3) K₀ := hp2 ▸ h₀
    have hcardQ : Nat.card (unitarySU 2 (f / 3) K₀ 3) = 216 :=
      CFSG.RankThree.CentralLiftU.card_statedSU_three_two h₂ hf1
    have := Fintype.ofFinite (unitarySU 2 (f / 3) K₀ 3)
    have hsolv : Group.IsSolvable (unitarySU 2 (f / 3) K₀ 3) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcardQ]; norm_num)
    subst hp2
    have : Group.IsSolvable P₂ :=
      Group.isSolvable_of_isSolvable_injective (f := P₂.subtype) P₂.subtype_injective
    have : Group.IsPerfect P₂ := hP₂.1
    have : Nontrivial P₂ := (Subgroup.nontrivial_iff_ne_bot P₂).mpr hP₂1
    exact Group.IsPerfect.not_isSolvable P₂ ‹_›
  ·
    have hnq₀ : ((3 : ℕ), p ^ (f / 3)) ≠ (3, 2) := fun h' => hr (Prod.mk.inj h').2
    obtain ⟨hQq, hQZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK₀ le_rfl
      hnq₀
    have hQθ : aschbacherSolvableCore 3 (unitarySU p (f / 3) K₀ 3) = ⊥ :=
      Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hQq (isPGroup_center_unitarySU h₀ hQZ)
    have hP₂top : P₂ = ⊤ := eq_top_of_isPerfect_of_isSubnormal hQq hP₂.1 hP₂.2.1 hP₂1
    have e₁ : P₂ ⧸ aschbacherSolvableCore 3 P₂ ≃* unitarySU p (f / 3) K₀ 3 :=
      (quotThetaEquiv ((MulEquiv.subgroupCongr hP₂top).trans Subgroup.topEquiv)).trans
        ((QuotientGroup.quotientMulEquivOfEq hQθ).trans QuotientGroup.quotientBot)
    have hcardQ : Nat.card (unitarySU p (f / 3) K₀ 3) = 1080 :=
      (Nat.card_congr e₁.toEquiv).symm.trans hcard₂
    rw [show unitarySU p (f / 3) K₀ 3 =
        CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ (f / 3)) K₀ from rfl,
      CFSG.SectionRank.OddCover.card_statedSU_three hK₀] at hcardQ
    have hr3 : 3 ≤ p ^ (f / 3) := by
      have hp := h.prime.two_le
      have hf : 1 ≤ f / 3 := h₀.one_le
      have : p ≤ p ^ (f / 3) := Nat.le_self_pow (by omega) p
      omega
    exact card_SU_three_ne hr3 hcardQ

end CFSG.RankThree.PartTwo.Sec4.Item426
