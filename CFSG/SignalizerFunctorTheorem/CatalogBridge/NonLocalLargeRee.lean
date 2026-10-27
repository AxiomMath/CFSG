module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.RegularLemmaR
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.BaseChangeRep
public import CFSG.LieType.Ree.LargeReeB2FixedCoordinates
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.Open.SignalizerFunctorDefs

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Open (signalizerFixedSubgroup)
open CFSG.SignalizerFunctorTheorem.NonLocalExc

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem hasCoord_largeReeX
    {K : Type} [Field K] (i : Fin Tag.F4.rank) (j : Fin 4) (c : K) :
    HasCoord i (largeReeX K j c : ModGL Tag.F4 K)
      (if largeReeRoot j = Pi.single i 1 then c else 0) := by
  by_cases h : largeReeRoot j = Pi.single i 1
  · simp only [h, ↓reduceIte]
    unfold largeReeX
    rw [h]
    exact hasCoord_pinnedX_single i c
  · simp only [h, ↓reduceIte]
    exact hasCoord_pinnedX_of_ne (largeReeRoot_pos j).1 (largeReeRoot_pos j).2 h c

theorem hasCoord_largeReeCoord_one
    (a : ℕ) {K : Type} [Field K] (i : Fin Tag.F4.rank)
    (hi : i.val = 1 ∨ i.val = 2) :
    HasCoord i (ReeTag.largeReeCoord a K 1 0 : ModGL Tag.F4 K) 1 := by
  have h1 : ReeTag.largeReeSigma a (1 : K) = 1 := one_pow _
  have h0 : ReeTag.largeReeSigma a (0 : K) = 0 := zero_pow (by positivity)
  have h : HasCoord i (ReeTag.largeReeCoord a K 1 0 : ModGL Tag.F4 K)
      ((if largeReeRoot 0 = Pi.single i 1 then (1 : K) else 0) +
        (if largeReeRoot 1 = Pi.single i 1 then ReeTag.largeReeSigma a (1 : K) else 0) +
        (if largeReeRoot 2 = Pi.single i 1 then (0 : K) else 0) +
        (if largeReeRoot 3 = Pi.single i 1 then ReeTag.largeReeSigma a (0 : K) + 1 ^ 2 *
          ReeTag.largeReeSigma a (1 : K) else 0)) := by
    unfold ReeTag.largeReeCoord largeReeP
    exact (((hasCoord_largeReeX i 0 1).mul (hasCoord_largeReeX i 1 _)).mul
      (hasCoord_largeReeX i 2 0)).mul (hasCoord_largeReeX i 3 _)
  rw [h1, h0] at h
  rcases hi with h1' | h2'
  · have hi1 : i = ⟨1, by decide⟩ := Fin.ext h1'
    subst hi1
    have e0 : largeReeRoot 0 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    have e1 : largeReeRoot 1 = Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    have e2 : largeReeRoot 2 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    have e3 : largeReeRoot 3 ≠ Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    simpa [e0, e1, e2, e3] using h
  · have hi2 : i = ⟨2, by decide⟩ := Fin.ext h2'
    subst hi2
    have e0 : largeReeRoot 0 = Pi.single (⟨2, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    have e1 : largeReeRoot 1 ≠ Pi.single (⟨2, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    have e2 : largeReeRoot 2 ≠ Pi.single (⟨2, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    have e3 : largeReeRoot 3 ≠ Pi.single (⟨2, by decide⟩ : Fin Tag.F4.rank) 1 := by decide
    simpa [e0, e1, e2, e3] using h

theorem hasCoord_xUnit_xUnit_one
    {K : Type} [Field K] (i : Fin Tag.F4.rank)
    (hi : i.val = 0 ∨ i.val = 3) :
    HasCoord i (xUnit Tag.F4 K ⟨0, by decide⟩ 1 * xUnit Tag.F4 K ⟨3, by decide⟩ 1) 1 := by
  rcases hi with h0' | h3'
  · have hi0 : i = ⟨0, by decide⟩ := Fin.ext h0'
    subst hi0
    have h0 : HasCoord (⟨0, by decide⟩ : Fin Tag.F4.rank)
        (xUnit Tag.F4 K ⟨3, by decide⟩ 1) 0 := by
      rw [← pinnedX_single]
      exact hasCoord_pinnedX_of_ne (isRoot_single _ _) (by rw [height_single]; exact one_pos)
        (by decide) 1
    have := (hasCoord_xUnit (τ := Tag.F4) (K := K) ⟨0, by decide⟩ 1).mul h0
    rwa [add_zero] at this
  · have hi3 : i = ⟨3, by decide⟩ := Fin.ext h3'
    subst hi3
    have h0 : HasCoord (⟨3, by decide⟩ : Fin Tag.F4.rank)
        (xUnit Tag.F4 K ⟨0, by decide⟩ 1) 0 := by
      rw [← pinnedX_single]
      exact hasCoord_pinnedX_of_ne (isRoot_single _ _) (by rw [height_single]; exact one_pos)
        (by decide) 1
    have := h0.mul (hasCoord_xUnit (τ := Tag.F4) (K := K) ⟨3, by decide⟩ 1)
    rwa [zero_add] at this

theorem shortRestrictHom_injective
    (t : ReeTag) {K : Type} [Field K] [Finite K]
    [CharP K t.prime] :
    Function.Injective (ReeTag.shortRestrictHom t K (CharP.cast_eq_zero K t.prime)) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => Subtype.ext ?_
  refine exceptional_short_faithful t K g.2 fun v hv => ?_
  have h := congrArg (fun e : Module.End K (t.shortModule K) =>
    (e ⟨v, hv⟩ : RootModule t.tag K)) hg
  exact h

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem largeReeCoord_one_mem_fixedFieldImage
    (σ : K ≃+* K) :
    (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K) ∈ fixedFieldImage ReeTag.F4.tag σ := by
  have h1 : ReeTag.largeReeSigma a (1 : K) = 1 := one_pow _
  have h0 : ReeTag.largeReeSigma a (0 : K) = 0 := zero_pow (by positivity)
  unfold ReeTag.largeReeCoord largeReeP largeReeX
  rw [h1, h0]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;>
    exact pinnedX_mem_fixedFieldImage _ (by simp)

theorem nonLocalized_largeRee_of_simple
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)))
    (hcard : 2 ^ 36 ∣ Nat.card ↥(signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ))) :
    NonLocalized (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  classical
  have hp2 : Nat.Prime ReeTag.F4.prime := Nat.prime_two
  have : Fact ReeTag.F4.prime.Prime := ⟨hp2⟩
  set Γ := ReeTag.F4.reeGamma K a with hΓ
  set J₀ := signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) with hJ₀
  set Jamb : Subgroup (ModGL ReeTag.F4.tag K) := J₀.map Γ.subtype with hJamb
  have hXC : Γ ≤ adjointGroup ReeTag.F4.tag K := fun g hg => (ReeTag.mem_reeGamma.1 hg).1
  have hJX : Jamb ≤ Γ := Subgroup.map_subtype_le _
  have hsub : Jamb.subgroupOf Γ = J₀ :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective J₀
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.F4.tag
  have hJmem : ∀ g : ModGL ReeTag.F4.tag K, g ∈ Γ → g ∈ fixedFieldImage ReeTag.F4.tag σ →
      g ∈ Jamb := fun g hg hgf =>
    ⟨⟨g, hg⟩, Subtype.ext (by
      rw [ReeTag.coe_reeGammaFieldAut]
      exact (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hgf)).2), rfl⟩
  have hu₁Γ : xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1 ∈
      Γ := (Subgroup.mem_inf.1 (ReeTag.f4_fixedBlock_one K a).1).2
  have hu₁F : xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1 ∈
      fixedFieldImage ReeTag.F4.tag σ :=
    mul_mem (xUnit_mem_fixedFieldImage _ (map_one σ)) (xUnit_mem_fixedFieldImage _ (map_one σ))
  have hu₁U : xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1 ∈
      posUnipotent ReeTag.F4.tag K :=
    mul_mem (LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
      (LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
  have hyBΓ : (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K) ∈ Γ :=
    (Subgroup.mem_inf.1 ((ReeTag.bijOn_largeReeCoord hK).1 (Set.mem_univ ((1 : K), (0 : K))))).2
  have hyBU : (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K) ∈
      posUnipotent ReeTag.F4.tag K := by
    unfold ReeTag.largeReeCoord largeReeP largeReeX
    refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;>
      exact pinnedX_mem_rootSpan (S := {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α})
        (largeReeRoot_pos _) _
  have hnΓ : canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ ∈ Γ :=
    (Subgroup.mem_inf.1 (ReeTag.canonicalRep_longest_mem_reeFixedMonomial (t := ReeTag.F4)
      (K := K) (a := a) hw₀)).2
  have hn : canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ ∈ Jamb :=
    ⟨⟨_, hnΓ⟩, Subtype.ext (by
      rw [ReeTag.coe_reeGammaFieldAut]
      exact entrywise_canonicalRep σ w₀), rfl⟩
  let y : Fin ReeTag.F4.tag.rank → ModGL ReeTag.F4.tag K := fun i =>
    if i.val = 0 ∨ i.val = 3 then
      xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1
    else (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K)
  have hyJ : ∀ i, y i ∈ Jamb := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [y, hi, ↓reduceIte]
      exact hJmem _ hu₁Γ hu₁F
    · simp only [y, hi, ↓reduceIte]
      exact hJmem _ hyBΓ (largeReeCoord_one_mem_fixedFieldImage σ)
  have hyU : ∀ i, y i ∈ posUnipotent ReeTag.F4.tag K := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [y, hi, ↓reduceIte]
      exact hu₁U
    · simp only [y, hi, ↓reduceIte]
      exact hyBU
  have hco : ∀ i, HasCoord i (y i) 1 := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [y, hi, ↓reduceIte]
      exact hasCoord_xUnit_xUnit_one i hi
    · simp only [y, hi, ↓reduceIte]
      refine hasCoord_largeReeCoord_one a i ?_
      have := i.2
      change i.val < 4 at this
      omega
  let F := AlgebraicClosure K
  have hFr : CharP F ReeTag.F4.prime :=
    charP_of_injective_algebraMap (algebraMap K F).injective _
  let b := ReeTag.F4.shortBasis K
  have : Fintype ↥(ReeTag.F4.shortLabels) := Fintype.ofFinite _
  let ρ₀ : ↥Γ →* Module.End K (ReeTag.F4.shortModule K) :=
    (ReeTag.shortRestrictHom ReeTag.F4 K (CharP.cast_eq_zero K ReeTag.F4.prime)).comp
      (Subgroup.inclusion hXC)
  have hρ₀ : Function.Injective ρ₀ :=
    (shortRestrictHom_injective ReeTag.F4).comp (Subgroup.inclusion_injective hXC)
  let ρ : ↥Γ →* Module.End F (↥ReeTag.F4.shortLabels → F) := matrixRep F b ρ₀
  have hρ : Function.Injective ρ := matrixRep_injective F b hρ₀
  have hdim : Module.finrank F (↥ReeTag.F4.shortLabels → F) = 26 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card, ReeTag.card_shortLabels]
    rfl
  have hcardR : Nat.card ↥(Jamb.subgroupOf Γ) = Nat.card ↥J₀ := by rw [hsub]
  have hR : ¬ Nat.card ↥(Jamb.subgroupOf Γ) ∣
      (Module.finrank F (↥ReeTag.F4.shortLabels → F)).factorial := by
    intro h
    rw [hcardR, hdim] at h
    have h2 := hcard.trans h
    revert h2
    decide
  have hsimple : IsSimpleGroup ↥(Jamb.subgroupOf Γ) := by
    rw [hsub]
    exact hs
  have hnl := nonLocalized_of_regular_data (τ := ReeTag.F4.tag) (r := ReeTag.F4.prime) hXC hJX
    hsimple (y := y) hyJ hyU (c := fun _ => 1) (fun _ => one_ne_zero) hco hw₀ hn ρ hρ
    (Jamb.subgroupOf Γ) le_rfl hR
  rwa [hsub] at hnl

end CFSG.SignalizerFunctorTheorem.CatalogBridge
