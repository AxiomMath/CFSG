module

public import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModuleComm
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed
import CFSG.Timmesfeld.LieEmbed.UnitaryWitt
import CFSG.Timmesfeld.Bridge.RootStructWTINatSum

public section

namespace CFSG.RankThree.GF2n.Tim81.TIModule

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.LieEmbed CFSG.RankThree.FFModules CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbedding.LeviBlock
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
open scoped MatrixGroups

section Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem exists_natCard_commSpan_sup_eq (σ : Representation (ZMod 2) G W)
    (φ : SL(2, K) →* G) {A B : Subgroup G} (hA : (upperUnipotent K).map φ = A)
    (hB : (lowerUnipotent K).map φ = B) (hqA : commSpan σ A ≤ fixSub σ A)
    (hqB : commSpan σ B ≤ fixSub σ B) (hfix : commSpan σ (A ⊔ B) ⊓ fixSub σ (A ⊔ B) = ⊥) :
    ∃ k : ℕ, Nat.card (commSpan σ (A ⊔ B)) = Nat.card K ^ (2 * k) := by
  haveI : PerfectRing K 2 := PerfectField.toPerfectRing 2
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.range_eq_map, ← NaturalModule.upperUnipotent_sup_lowerUnipotent,
      Subgroup.map_sup, hA, hB]
  have hupA : ∀ t, φ (upperElt K t) ∈ A := fun t => by
    rw [← hA]
    exact Subgroup.mem_map_of_mem φ ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)
  have hloB : ∀ t, φ (lowerElt K t) ∈ B := fun t => by
    rw [← hB]
    exact Subgroup.mem_map_of_mem φ ((mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩)
  set N := commSpan σ (A ⊔ B)
  have hinv : ∀ (g : SL(2, K)) ⦃v : W⦄, v ∈ N → (σ.comp φ) g v ∈ N := by
    intro g v hv
    have hg : φ g ∈ A ⊔ B := by
      rw [← hrange]
      exact MonoidHom.mem_range.2 ⟨g, rfl⟩
    exact apply_mem_commSpan (fun t ht => mul_mem (mul_mem hg ht) (inv_mem hg)) hv
  letI : DistribMulAction SL(2, K) N := DistribMulAction.compHom N
    (⟨N, hinv⟩ : Subrepresentation (σ.comp φ)).toRepresentation
  have hsmul : ∀ (g : SL(2, K)) (v : N), ((g • v : N) : W) = σ (φ g) v := fun _ _ => rfl
  have hquad : ∀ (s t : K) (v : N),
      upperElt K s • (upperElt K t • v - v) = upperElt K t • v - v := by
    intro s t v
    apply Subtype.ext
    rw [hsmul, Submodule.coe_sub, hsmul]
    exact mem_fixSub.1 (hqA (sub_mem_commSpan (σ := σ) (hupA t) (v : W))) _ (hupA s)
  have hfix' : ∀ v : N, (∀ x : SL(2, K), x • v = v) → v = 0 := by
    intro v hv
    have hmem : (v : W) ∈ N ⊓ fixSub σ (A ⊔ B) := by
      refine Submodule.mem_inf.2 ⟨v.2, mem_fixSub.2 fun a ha => ?_⟩
      rw [← hrange] at ha
      obtain ⟨x, rfl⟩ := ha
      rw [← hsmul, hv x]
    rw [hfix, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hspan : ∀ v : N, ∃ u ∈ NatSum.fixedUpper K N, ∃ w ∈ NatSum.fixedLower K N, v = u + w := by
    intro v
    have hv : (v : W) ∈ commSpan σ A ⊔ commSpan σ B := by
      rw [← commSpan_sup]
      exact v.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    refine ⟨⟨a, commSpan_mono le_sup_left ha⟩, NatSum.mem_fixedUpper.2 fun t => Subtype.ext ?_,
      ⟨b, commSpan_mono le_sup_right hb⟩, NatSum.mem_fixedLower.2 fun t => Subtype.ext ?_,
      Subtype.ext hab.symm⟩
    · rw [hsmul]
      exact mem_fixSub.1 (hqA ha) _ (hupA t)
    · rw [hsmul]
      exact mem_fixSub.1 (hqB hb) _ (hloB t)
  obtain ⟨k, -, -, -, -, -, hcard, -, -⟩ := NatSum.exists_natural_sum hquad hfix' hspan
  exact ⟨k, hcard⟩

end Module

section Embed

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private def outerEmb (m : ℕ) : Fin 2 → Fin (m + 2) := ![0, Fin.last (m + 1)]

private theorem outerEmb_zero (m : ℕ) : outerEmb m 0 = 0 := rfl

private theorem outerEmb_one (m : ℕ) : outerEmb m 1 = Fin.last (m + 1) := rfl

private theorem outerEmb_injective (m : ℕ) : Function.Injective (outerEmb m) := by
  have h : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := fun h => by
    have := congrArg Fin.val h
    simp at this
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij h
  · exact absurd hij.symm h
  · rfl

private theorem outerEmb_rev (m : ℕ) (i : Fin 2) :
    outerEmb m (Fin.rev i) = Fin.rev (outerEmb m i) := by
  fin_cases i
  · change Fin.last (m + 1) = Fin.rev 0
    rw [Fin.rev_zero]
  · change (0 : Fin (m + 2)) = Fin.rev (Fin.last (m + 1))
    rw [Fin.rev_last]

private noncomputable def outerSL (f m : ℕ) :
    SL(2, fixedSubfield F 2 f) →* SU (unitaryInvolution F 2 f) (m + 2) :=
  (suEmbed (unitaryInvolution F 2 f) (outerEmb_injective m) (outerEmb_rev m)).comp
    (hypHom (p := 2) (f := f) (ζ := (1 : F)) one_ne_zero (by rw [map_one, CharTwo.neg_eq]))

variable {f m : ℕ}

private theorem suMat_outerSL (x : SL(2, fixedSubfield F 2 f)) :
    suMat (unitaryInvolution F 2 f) (m + 2) (outerSL f m x) =
      extendMat (outerEmb_injective m)
        (LieType.Steinberg.hypMat (1 : F) (x : Matrix (Fin 2) (Fin 2) (fixedSubfield F 2 f))) :=
  rfl

private theorem hypMat_upperElt (s : fixedSubfield F 2 f) :
    LieType.Steinberg.hypMat (1 : F)
        (upperElt (fixedSubfield F 2 f) s : Matrix (Fin 2) (Fin 2) (fixedSubfield F 2 f)) =
      longRootMatrix (0 : Fin 2) (s : F) := by
  rw [longRootMatrix, show Fin.rev (0 : Fin 2) = 1 by decide]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LieType.Steinberg.hypMat, upperElt, Matrix.single_apply]

private theorem hypMat_lowerElt (s : fixedSubfield F 2 f) :
    LieType.Steinberg.hypMat (1 : F)
        (lowerElt (fixedSubfield F 2 f) s : Matrix (Fin 2) (Fin 2) (fixedSubfield F 2 f)) =
      longRootMatrix (1 : Fin 2) (s : F) := by
  rw [longRootMatrix, show Fin.rev (1 : Fin 2) = 0 by decide]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LieType.Steinberg.hypMat, lowerElt, Matrix.single_apply]

private theorem suMat_outerSL_upperElt (s : fixedSubfield F 2 f) :
    suMat (unitaryInvolution F 2 f) (m + 2) (outerSL f m (upperElt _ s)) =
      uTrans (unitaryInvolution F 2 f) (Pi.single 0 1) (s : F) := by
  rw [suMat_outerSL, hypMat_upperElt,
    extendMat_longRootMatrix (outerEmb_injective m) (outerEmb_rev m), outerEmb_zero, uTrans_single]

private theorem suMat_outerSL_lowerElt (s : fixedSubfield F 2 f) :
    suMat (unitaryInvolution F 2 f) (m + 2) (outerSL f m (lowerElt _ s)) =
      uTrans (unitaryInvolution F 2 f) (Pi.single (Fin.last (m + 1)) 1) (s : F) := by
  rw [suMat_outerSL, hypMat_lowerElt,
    extendMat_longRootMatrix (outerEmb_injective m) (outerEmb_rev m), outerEmb_one, uTrans_single]

private theorem map_outerSL_eq {U : Subgroup SL(2, fixedSubfield F 2 f)}
    {e : fixedSubfield F 2 f → SL(2, fixedSubfield F 2 f)} (hU : ∀ g, g ∈ U ↔ ∃ s, g = e s)
    {v : Fin (m + 2) → F}
    (he : ∀ s, suMat (unitaryInvolution F 2 f) (m + 2) (outerSL f m (e s)) =
      uTrans (unitaryInvolution F 2 f) v s)
    {T : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) v T) : U.map (outerSL f m) = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (hU x).1 hx
    exact (hT.1 _).2 ⟨(s : F), CharTwo.add_eq_zero.2 (mem_fixedSubfield.1 s.2).symm, he s⟩
  · intro hy
    obtain ⟨c, hc, hyc⟩ := (hT.1 y).1 hy
    refine Subgroup.mem_map.2 ⟨e ⟨c, mem_fixedSubfield.2 (CharTwo.add_eq_zero.1 hc).symm⟩,
      (hU _).2 ⟨_, rfl⟩, suMat_injective (unitaryInvolution F 2 f) ?_⟩
    rw [he, hyc]

end Embed

theorem exists_natCard_commSpan_eq_pow {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) (m + 2)) W)
    {T₀ T₁ : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (Fin.last (m + 1)) 1) T₁)
    (hquad : commSpan σ T₀ ≤ fixSub σ T₀)
    (hfix : commSpan σ (T₀ ⊔ T₁) ⊓ fixSub σ (T₀ ⊔ T₁) = ⊥)
    (hinf : commSpan σ T₀ ⊓ commSpan σ T₁ = ⊥)
    (hcard : Nat.card (commSpan σ T₀) = Nat.card (commSpan σ T₁))
    {w : SU (unitaryInvolution F 2 f) (m + 2)} (hw : w ∈ T₀ ⊔ T₁)
    (hwc : CFSG.Timmesfeld.ARS.conjSub T₀ w = T₁) :
    ∃ k : ℕ, Nat.card (commSpan σ T₀) = (2 ^ f) ^ k := by
  haveI : CharP (fixedSubfield F 2 f) 2 :=
    RingHom.charP (fixedSubfield F 2 f).subtype (fixedSubfield F 2 f).subtype.injective 2
  have hquad₁ : commSpan σ T₁ ≤ fixSub σ T₁ := by
    rw [← hwc, ← map_commSpan_conjSub]
    rintro _ ⟨v, hv, rfl⟩ _ ⟨t, ht, rfl⟩
    change σ (w * t * w⁻¹) (σ w v) = σ w v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
      mem_fixSub.1 (hquad hv) t ht]
  obtain ⟨k, hk⟩ := exists_natCard_commSpan_sup_eq σ (outerSL f m)
    (map_outerSL_eq (fun _ => mem_upperUnipotent_iff _) suMat_outerSL_upperElt hT₀)
    (map_outerSL_eq (fun _ => mem_lowerUnipotent_iff _) suMat_outerSL_lowerElt hT₁)
    hquad hquad₁ hfix
  have hV : Nat.card (commSpan σ (T₀ ⊔ T₁)) = Nat.card (commSpan σ T₀) ^ 2 := by
    rw [commSpan_sup, natCard_sup_of_inf_eq_bot hinf, ← hcard, sq]
  refine ⟨k, Nat.pow_left_injective two_ne_zero ?_⟩
  change Nat.card (commSpan σ T₀) ^ 2 = ((2 ^ f) ^ k) ^ 2
  rw [← hV, hk, card_fixedSubfield hF]
  ring

end CFSG.RankThree.GF2n.Tim81.TIModule
