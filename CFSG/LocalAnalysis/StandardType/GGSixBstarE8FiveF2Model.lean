module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveLangTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.RankThree.PartOne.KE.CTLangData

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace NoOffE8Five

local instance noOffE8FiveFactFiveF2 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankF2 : NeZero Tag.E8.rank := ⟨by decide⟩

section F2Model


theorem exists_f2Model_E8 {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] :
    ∃ ι : Multiplicative (NoOffRest.eigE8 5 3) →* adjointGroup Tag.E8 K,
      Function.Injective ι ∧
      (∀ (σ : K ≃+* K) (v : Multiplicative (NoOffRest.eigE8 5 3)),
        Units.map (entrywiseHom σ.toRingHom) ((ι v : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
          ((ι v : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) ∧
      ∀ a : adjointGroup Tag.E8 K,
        (∀ s : NoOffRest.eigE8 5 3, ∃ t : NoOffRest.eigE8 5 3,
          a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd t)) →
        ∃ u : NoOffRest.centE8W, ∀ s : NoOffRest.eigE8 5 3,
          a * ι (Multiplicative.ofAdd s) * a⁻¹ =
            ι (Multiplicative.ofAdd (NoOffRest.eigPerm 5 3 u s)) := by
  classical
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosure (ZMod 2) L := ⟨inferInstance, inferInstance⟩
  let Fr : L →+* L := iterateFrobenius L 2 1
  have hFr : ∀ c, Fr c = c ^ Nat.card (ZMod 2) := fun c => by
    rw [Nat.card_zmod]
    exact iterateFrobenius_def 2 1 c
  have h5L : ¬ ringChar L ∣ 5 := by
    rw [ringChar.eq L 2]
    decide
  obtain ⟨ζ, hζo⟩ := exists_unit_orderOf_five_of_isAlgClosed (L := L) h5L
  have hζ : ζ ^ 5 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨g₀, hg₀C, hg₀⟩ := lang_conjugator Tag.E8 (ZMod 2) (ℓ := 2) (f := 1) le_rfl L
    NoOffRest.weylE8W
  have hq : ((Nat.card (ZMod 2) : ℕ) : ZMod 5) * (3 : ZMod 5) = 1 := by
    rw [Nat.card_zmod]
    decide
  obtain ⟨ι₂, hι₂inj, hι₂⟩ := exists_langTorsionHom (K := ZMod 2) (L := L) hFr hζo hζ
    (lam := 3) hq hg₀C hg₀
  let φ : adjointGroup Tag.E8 (ZMod 2) →* adjointGroup Tag.E8 K :=
    (adjEmb Tag.E8 (ZMod 2) K).codRestrict (adjointGroup Tag.E8 K) fun y => adjEmb_mem y
  have hφinj : Function.Injective φ := fun x y hxy =>
    adjEmb_injective (K := ZMod 2) (L := K) (τ := Tag.E8) (congrArg Subtype.val hxy)
  have hφval : ∀ y, ((φ y : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
      adjEmb Tag.E8 (ZMod 2) K y := fun y => rfl
  have hφL : ∀ y, adjEmb Tag.E8 K L (φ y) = adjEmb Tag.E8 (ZMod 2) L y := fun y => by
    change baseChangeGL (algebraMap K L) ((φ y : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
      baseChangeGL (algebraMap (ZMod 2) L) (y : ModGL Tag.E8 (ZMod 2))
    rw [hφval]
    change baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap (ZMod 2) K)
      (y : ModGL Tag.E8 (ZMod 2))) = _
    rw [baseChangeGL_baseChangeGL, ← IsScalarTower.algebraMap_eq]
  refine ⟨φ.comp ι₂, hφinj.comp hι₂inj, ?_, ?_⟩
  · intro σ v
    rw [MonoidHom.comp_apply, hφval]
    have hcomp : σ.toRingHom.comp (algebraMap (ZMod 2) K) = algebraMap (ZMod 2) K :=
      RingHom.ext_zmod _ _
    have e : Units.map (entrywiseHom σ.toRingHom) (adjEmb Tag.E8 (ZMod 2) K (ι₂ v)) =
        baseChangeGL σ.toRingHom (adjEmb Tag.E8 (ZMod 2) K (ι₂ v)) := Units.ext rfl
    rw [e]
    change baseChangeGL σ.toRingHom (baseChangeGL (algebraMap (ZMod 2) K)
      ((ι₂ v : adjointGroup Tag.E8 (ZMod 2)) : ModGL Tag.E8 (ZMod 2))) =
        baseChangeGL (algebraMap (ZMod 2) K) _
    rw [baseChangeGL_baseChangeGL, hcomp]
    rfl
  · intro a ha
    exact exists_centE8W_conj_of_langTorsion (K := K) (L := L) hζo hζ NoOffRest.three_mul_three_zmod_five
      hg₀C (ι := φ.comp ι₂) (fun s => by
        rw [MonoidHom.comp_apply, hφL, hι₂ s]) ha

end F2Model

end NoOffE8Five

end CFSG.StandardType
