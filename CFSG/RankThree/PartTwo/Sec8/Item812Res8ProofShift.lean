module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage)


@[expose] def KFG2Ord3Inv : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 ^ m →
    ∀ y : adjointGroup .G2 k, orderOf y = 3 →
      ∃ s : adjointGroup .G2 k, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * y = y * s

@[expose] def KFPGL3Ord3Classes : Prop :=
  ∀ (π : Bool) (m : ℕ) (K : Type) [Field K], Sec4.PiField π 2 m K → Sec4.ModThree π (2 ^ m) →
    ∀ u u' : projImage (Sec4.glPi π 3 (2 ^ m) K), orderOf u = 3 → orderOf u' = 3 →
      (∃ s, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * u = u * s) → (∃ s, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * u' = u' * s) →
        ∃ g, g * u' * g⁻¹ = u ∨ g * u' * g⁻¹ = u⁻¹

namespace Item812Res8

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem exists_involution_of_isStdGraphFieldConj (hG2 : KFG2Ord3Inv) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = (2 ^ m) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hβ : γ = β * fieldActor σ σ * β⁻¹ ∨ γ = β * (fieldActor σ σ)⁻¹ * β⁻¹)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hγy : γ y = y) (hy3 : orderOf y = 3) :
    ∃ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      s ≠ 1 ∧ s ^ 2 = 1 ∧ γ s = s ∧ s * y = y * s := by
  have hK3 : Nat.card K = 2 ^ (3 * m) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hchar : ringChar K = 2 := ringChar.eq K 2
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀
  set ι := trialityG2Incl σ hchar with hι
  have hσy : σ₀ (β⁻¹ y) = β⁻¹ y := by
    rcases hβ with rfl | rfl
    · have h1 : (β * σ₀ * β⁻¹) y = y := hγy
      rw [MulAut.mul_apply, MulAut.mul_apply] at h1
      calc σ₀ (β⁻¹ y) = β⁻¹ (β (σ₀ (β⁻¹ y))) := by rw [MulAut.inv_apply_self]
        _ = β⁻¹ y := by rw [h1]
    · have h1 : (β * σ₀⁻¹ * β⁻¹) y = y := hγy
      rw [MulAut.mul_apply, MulAut.mul_apply] at h1
      have h2 : σ₀⁻¹ (β⁻¹ y) = β⁻¹ y := by
        calc σ₀⁻¹ (β⁻¹ y) = β⁻¹ (β (σ₀⁻¹ (β⁻¹ y))) := by rw [MulAut.inv_apply_self]
          _ = β⁻¹ y := by rw [h1]
      calc σ₀ (β⁻¹ y) = σ₀ (σ₀⁻¹ (β⁻¹ y)) := by rw [h2]
        _ = β⁻¹ y := by rw [MulAut.apply_inv_self]
  obtain ⟨y₀, hy₀⟩ := (mem_range_trialityG2Incl_iff σ hchar (β⁻¹ y)).mpr hσy
  have hy₀3 : orderOf y₀ = 3 := by
    rw [← orderOf_injective ι (trialityG2Incl_injective σ hchar) y₀, hy₀, MulEquiv.orderOf_eq]
    exact hy3
  obtain ⟨s₀, hs₀1, hs₀2, hs₀y⟩ := hG2 m hm (fixSubfield σ) (card_fixSubfield_of_cube hm hK hσ)
    y₀ hy₀3
  refine ⟨β (ι s₀), ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hs₀1
    apply trialityG2Incl_injective σ hchar
    rw [map_one]
    exact (map_eq_one_iff β β.injective).mp h1
  · rw [← map_pow, ← map_pow, hs₀2, map_one, map_one]
  · have hfix : σ₀ (ι s₀) = ι s₀ := (mem_range_trialityG2Incl_iff σ hchar _).mp ⟨s₀, rfl⟩
    rcases hβ with rfl | rfl
    · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix]
    · have hfix' : σ₀⁻¹ (ι s₀) = ι s₀ := by
        calc σ₀⁻¹ (ι s₀) = σ₀⁻¹ (σ₀ (ι s₀)) := by rw [hfix]
          _ = ι s₀ := MulAut.inv_apply_self _ _ _
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix']
  · have hy : y = β (ι y₀) := by rw [hy₀, MulAut.apply_inv_self]
    rw [hy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hs₀y]

end Item812Res8

open Item812Res8 Item8ModelProof

theorem kF86D4ShiftConj_of
    (hG2 : KFG2Ord3Inv) (hP : KFPGL3Ord3Classes) (hEv : KF89D4SecondCentEven) :
    Item86ResProof.KF86D4ShiftConj := by
  intro m K _ _ σ hK hσ γ y w t hγ hγy hy3 hnstd hw3 hαw ht1 ht2 hαt htw
  classical
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso
      have h1 : Nat.card K = 1 := by simpa using hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  set α := γ * MulAut.conj y with hαdef
  have hσ₀3 : σ₀ ^ 3 = 1 := LangTwistedProof.fieldActor_pow_three hK hσ
  obtain ⟨β, hβ⟩ := id hγ
  have hγ3 : γ ^ 3 = 1 := by
    rcases hβ with rfl | rfl
    · rw [conj_pow, hσ₀3]
      group
    · rw [conj_pow, inv_pow, hσ₀3]
      group
  have hγc : γ * MulAut.conj y = MulAut.conj y * γ := by
    have h1 := KFacts.mul_mulAutConj_mul_inv γ y
    rw [hγy] at h1
    calc γ * MulAut.conj y = γ * MulAut.conj y * γ⁻¹ * γ := by group
      _ = MulAut.conj y * γ := by rw [h1]
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, (Commute.mul_pow hγc 3), hγ3, ← map_pow, hy3', map_one, one_mul]
  have hγin : ¬ IsInnerAut γ := not_isInnerAut_of_isStdGraphFieldConj hm hK hσ hγ
  have hαin : ¬ IsInnerAut α := by
    rintro ⟨g, hg⟩
    apply hγin
    refine ⟨g * y⁻¹, ?_⟩
    rw [map_mul, hg, map_inv, hαdef, mul_inv_cancel_right]
  obtain ⟨π, F, _, hF, hmod, ⟨φ⟩⟩ : ∃ (π : Bool) (F : Type) (_ : Field F),
      Sec4.PiField π 2 m F ∧ Sec4.ModThree π (2 ^ m) ∧
        Nonempty (Sec4.autFix α ≃* projImage (Sec4.glPi π 3 (2 ^ m) F)) := by
    rcases Nat.even_or_odd m with hev | hodd
    · obtain ⟨F, hF, _, hFc, hφ⟩ := hEv m hev hm K σ hK hσ α hα3 hαin hnstd
      exact ⟨true, F, hF, ⟨Nat.prime_two, hm, hFc⟩,
        Item82OneProof.two_pow_mod_three_of_even hev, hφ⟩
    · rcases inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds m hodd K σ
        hK hσ α hα3 hαin with hs | ⟨-, -, -, -, -, -, F, hF, _, hFc, hφ⟩
      · exact (hnstd hs).elim
      · exact ⟨false, F, hF, ⟨Nat.prime_two, hm, hFc⟩,
          Item82OneProof.two_pow_mod_three_of_odd hodd, hφ⟩
  have hαfix : ∀ z, y * z = z * y → γ z = z → α z = z := by
    intro z hyz hγz
    rw [hαdef, MulAut.mul_apply, MulAut.conj_apply, hyz, mul_inv_cancel_right, hγz]
  have hyC : y ∈ Sec4.autFix α := Sec4.mem_autFix.mpr (hαfix y rfl hγy)
  have hwC : w ∈ Sec4.autFix α := Sec4.mem_autFix.mpr hαw
  have htC : t ∈ Sec4.autFix α := Sec4.mem_autFix.mpr hαt
  obtain ⟨s, hs1, hs2, hγs, hsy⟩ := exists_involution_of_isStdGraphFieldConj hG2 hm hK hσ hβ hγy hy3
  have hsC : s ∈ Sec4.autFix α := Sec4.mem_autFix.mpr (hαfix s hsy.symm hγs)
  set Y : Sec4.autFix α := ⟨y, hyC⟩
  set W : Sec4.autFix α := ⟨w, hwC⟩
  set T : Sec4.autFix α := ⟨t, htC⟩
  set S : Sec4.autFix α := ⟨s, hsC⟩
  have hYo : orderOf (φ Y) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hy3
  have hWo : orderOf (φ W) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hw3
  have hinvol : ∀ (Z U : Sec4.autFix α), (Z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ 1 →
      (Z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ^ 2 = 1 →
      (Z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * U = U * Z →
        ∃ s', s' ≠ 1 ∧ s' ^ 2 = 1 ∧ s' * φ U = φ U * s' := by
    intro Z U hZ1 hZ2 hZU
    refine ⟨φ Z, ?_, ?_, ?_⟩
    · intro h1
      apply hZ1
      have := φ.injective (h1.trans (map_one φ).symm)
      rw [this]
      rfl
    · rw [← map_pow]
      have : Z ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZ2)
      rw [this, map_one]
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hZU
  obtain ⟨g, hg⟩ := hP π m F hF hmod (φ Y) (φ W) hYo hWo (hinvol S Y hs1 hs2 hsy)
    (hinvol T W ht1 ht2 htw)
  refine ⟨(φ.symm g : Sec4.autFix α), Sec4.mem_autFix.mp (φ.symm g).2, ?_⟩
  have key : ∀ v : Sec4.autFix α, φ.symm g * W * (φ.symm g)⁻¹ = v →
      (φ.symm g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * w *
        (φ.symm g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)⁻¹ = v := by
    intro v hv
    rw [← hv]
    rfl
  rcases hg with hg | hg
  · left
    refine key Y ?_
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
  · right
    have := key Y⁻¹ (by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hg])
    rw [this]
    rfl

end CFSG.RankThree.PartTwo.Sec8
