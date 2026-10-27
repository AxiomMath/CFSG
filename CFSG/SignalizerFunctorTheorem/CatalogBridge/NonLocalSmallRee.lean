module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.RegularLemmaR
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.AdjointRep
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.Open.SignalizerFunctorDefs

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Open (signalizerFixedSubgroup)
open CFSG.SignalizerFunctorTheorem.NonLocalExc

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem hasCoord_smallReeX
    {K : Type} [Field K] (i : Fin Tag.G2.rank) (j : Fin 6) (c : K) :
    HasCoord i (smallReeX K j c : ModGL Tag.G2 K)
      (if smallReeRoot j = Pi.single i 1 then c else 0) := by
  by_cases h : smallReeRoot j = Pi.single i 1
  · simp only [h, ↓reduceIte]
    unfold smallReeX
    rw [h]
    exact hasCoord_pinnedX_single i c
  · simp only [h, ↓reduceIte]
    exact hasCoord_pinnedX_of_ne (RootOps.isRootB_iff.1 (smallReeRoot_check j).1)
      (smallReeRoot_check j).2 h c

theorem hasCoord_smallReeCoord
    (a : ℕ) {K : Type} [Field K] (t b c : K) (i : Fin Tag.G2.rank) :
    HasCoord i (smallReeCoord a K t b c : ModGL Tag.G2 K)
      ((if smallReeRoot 0 = Pi.single i 1 then t else 0) +
        (if smallReeRoot 1 = Pi.single i 1 then smallReeSigma a t else 0) +
        (if smallReeRoot 2 = Pi.single i 1 then b else 0) +
        (if smallReeRoot 3 = Pi.single i 1 then c else 0) +
        (if smallReeRoot 4 = Pi.single i 1 then smallReeSigma a b - t ^ 3 * smallReeSigma a t
          else 0) +
        (if smallReeRoot 5 = Pi.single i 1 then smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2
          else 0)) := by
  unfold smallReeCoord
  exact (((((hasCoord_smallReeX i 0 t).mul (hasCoord_smallReeX i 1 _)).mul
    (hasCoord_smallReeX i 2 b)).mul (hasCoord_smallReeX i 3 c)).mul
    (hasCoord_smallReeX i 4 _)).mul (hasCoord_smallReeX i 5 _)

theorem hasCoord_smallReeCoord_one
    (a : ℕ) {K : Type} [Field K] (i : Fin Tag.G2.rank) :
    HasCoord i (smallReeCoord a K 1 0 0 : ModGL Tag.G2 K) 1 := by
  have h := hasCoord_smallReeCoord a (1 : K) 0 0 i
  have h1 : smallReeSigma a (1 : K) = 1 := one_pow _
  have h0 : smallReeSigma a (0 : K) = 0 := zero_pow (by positivity)
  rw [h1, h0] at h
  fin_cases i
  · have e0 : smallReeRoot 0 ≠ Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e1 : smallReeRoot 1 = Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e2 : smallReeRoot 2 ≠ Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e3 : smallReeRoot 3 ≠ Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e4 : smallReeRoot 4 ≠ Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e5 : smallReeRoot 5 ≠ Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    simpa [e0, e1, e2, e3, e4, e5] using h
  · have e0 : smallReeRoot 0 = Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e1 : smallReeRoot 1 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e2 : smallReeRoot 2 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e3 : smallReeRoot 3 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e4 : smallReeRoot 4 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    have e5 : smallReeRoot 5 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by decide
    simpa [e0, e1, e2, e3, e4, e5] using h


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

omit [Finite K] [CharP K ReeTag.G2.prime] in
theorem smallReeCoord_one_mem_fixedFieldImage
    (σ : K ≃+* K) :
    (smallReeCoord a K 1 0 0 : ModGL ReeTag.G2.tag K) ∈ fixedFieldImage ReeTag.G2.tag σ := by
  have h1 : smallReeSigma a (1 : K) = 1 := one_pow _
  have h0 : smallReeSigma a (0 : K) = 0 := zero_pow (by positivity)
  unfold smallReeCoord smallReeX
  rw [h1, h0]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact pinnedX_mem_fixedFieldImage _ (by simp)

theorem nonLocalized_smallRee_of_simple
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)))
    (hcard : 3 ^ 9 ∣ Nat.card ↥(signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ))) :
    NonLocalized (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) := by
  classical
  have hp3 : Nat.Prime ReeTag.G2.prime := Nat.prime_three
  have : Fact ReeTag.G2.prime.Prime := ⟨hp3⟩
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set J₀ := signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) with hJ₀
  set Jamb : Subgroup (ModGL ReeTag.G2.tag K) := J₀.map Γ.subtype with hJamb
  have hXC : Γ ≤ adjointGroup ReeTag.G2.tag K := fun g hg => (ReeTag.mem_reeGamma.1 hg).1
  have hJX : Jamb ≤ Γ := Subgroup.map_subtype_le _
  have hsub : Jamb.subgroupOf Γ = J₀ :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective J₀
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have hyΓ : (smallReeCoord a K 1 0 0 : ModGL ReeTag.G2.tag K) ∈ Γ :=
    (Subgroup.mem_inf.1 (ReeTag.smallReeCoord_mem_reeFixedPosUnipotent hK 1 0 0)).2
  have hyJ : (smallReeCoord a K 1 0 0 : ModGL ReeTag.G2.tag K) ∈ Jamb :=
    ⟨⟨_, hyΓ⟩, Subtype.ext (by
      rw [ReeTag.coe_reeGammaFieldAut]
      exact (mem_entrywiseFixedGroup.1
        (fixedFieldImage_le (smallReeCoord_one_mem_fixedFieldImage (a := a) σ))).2), rfl⟩
  have hyU : (smallReeCoord a K 1 0 0 : ModGL ReeTag.G2.tag K) ∈ posUnipotent ReeTag.G2.tag K :=
    smallReeCoord_mem_posUnipotent a K 1 0 0
  have hnΓ : canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ Γ :=
    ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := a) hw₀
  have hn : canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ Jamb :=
    ⟨⟨_, hnΓ⟩, Subtype.ext (by
      rw [ReeTag.coe_reeGammaFieldAut]
      exact entrywise_canonicalRep σ w₀), rfl⟩
  let F := AlgebraicClosure K
  have hFr : CharP F ReeTag.G2.prime :=
    charP_of_injective_algebraMap (algebraMap K F).injective _
  let ρ : ↥Γ →* Module.End F (Label ReeTag.G2.tag → F) := (adjRep ReeTag.G2.tag K F).comp Γ.subtype
  have hρ : Function.Injective ρ := (adjRep_injective ReeTag.G2.tag K F).comp Subtype.val_injective
  have hdim : Module.finrank F (Label ReeTag.G2.tag → F) = 14 := by
    rw [finrank_label_pi, card_label_eq]
    decide
  have hcardR : Nat.card ↥(Jamb.subgroupOf Γ) = Nat.card ↥J₀ := by rw [hsub]
  have hR : ¬ Nat.card ↥(Jamb.subgroupOf Γ) ∣
      (Module.finrank F (Label ReeTag.G2.tag → F)).factorial := by
    intro h
    rw [hcardR, hdim] at h
    have h2 := hcard.trans h
    revert h2
    decide
  have hsimple : IsSimpleGroup ↥(Jamb.subgroupOf Γ) := by
    rw [hsub]
    exact hs
  have hnl := nonLocalized_of_regular_data (τ := ReeTag.G2.tag) (r := ReeTag.G2.prime) hXC hJX
    hsimple (y := fun _ => (smallReeCoord a K 1 0 0 : ModGL ReeTag.G2.tag K)) (fun _ => hyJ)
    (fun _ => hyU)
    (c := fun _ => 1) (fun _ => one_ne_zero) (hasCoord_smallReeCoord_one a) hw₀ hn ρ hρ
    (Jamb.subgroupOf Γ) le_rfl hR
  rwa [hsub] at hnl

end CFSG.SignalizerFunctorTheorem.CatalogBridge
