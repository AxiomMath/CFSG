module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSmallRee
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalizedBySimple
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeThreeModel
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.F4Even
import CFSG.LieType.Ree.SmallReeThreeDerived

public noncomputable section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

section

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

omit [Finite K] [CharP K ReeTag.G2.prime] in
theorem g2U₀_mem_fixedFieldImage
    (σ : K ≃+* K) : (ReeTag.g2U₀ K : ModGL ReeTag.G2.tag K) ∈ fixedFieldImage ReeTag.G2.tag σ :=
  mul_mem (pinnedX_mem_fixedFieldImage _ (by simp)) (pinnedX_mem_fixedFieldImage _ (by simp))

theorem closure_g2U₀_n_le_fixed
    (σ : K ≃+* K) {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀) :
    Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ≤
      (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)).map
        (ReeTag.G2.reeGamma K a).subtype := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · refine ⟨⟨_, ReeTag.g2U₀_mem_reeGamma K a⟩, Subtype.ext ?_, rfl⟩
    rw [ReeTag.coe_reeGammaFieldAut]
    exact (mem_entrywiseFixedGroup.1 (fixedFieldImage_le (g2U₀_mem_fixedFieldImage σ))).2
  · refine ⟨⟨_, ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := a) hw₀⟩,
      Subtype.ext ?_, rfl⟩
    rw [ReeTag.coe_reeGammaFieldAut]
    exact entrywise_canonicalRep σ w₀

theorem smallRee_threeGroup_eq_bot
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (σ : K ≃+* K) :
    ∀ E : Subgroup ↥(ReeTag.G2.reeGamma K a), IsPGroup ReeTag.G2.prime E →
      (∀ j ∈ signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ), ∀ e ∈ E,
        j * e * j⁻¹ ∈ E) → E = ⊥ := by
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
  intro E hE hnorm
  have hWr : IsPGroup ReeTag.G2.prime (E.map Γ.subtype) := hE.map _
  have hWC : E.map Γ.subtype ≤ adjointGroup ReeTag.G2.tag K := by
    rintro _ ⟨e, -, rfl⟩
    exact hXC e.2
  have hbot := eq_bot_of_isPGroup_of_normalized_regular (τ := ReeTag.G2.tag) ReeTag.G2.prime
    (hJX.trans hXC) hWC hWr (y := fun _ => (smallReeCoord a K 1 0 0 : ModGL ReeTag.G2.tag K))
    (fun _ => hyJ) (fun _ => hyU) (c := fun _ => 1) (fun _ => one_ne_zero)
    (hasCoord_smallReeCoord_one a) hw₀ hn (fun j hj w hw => by
      obtain ⟨e, he, rfl⟩ := hw
      have hj' : (⟨j, hJX hj⟩ : ↥Γ) ∈ J₀ := by
        rw [← hsub]
        exact Subgroup.mem_subgroupOf.2 hj
      exact ⟨_, hnorm _ hj' e he, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).1 hbot

theorem smallRee_eq_bot_of_ne_three
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (σ : K ≃+* K) {s : ℕ} (hs : s.Prime) (hs3 : s ≠ 3) :
    ∀ E : Subgroup ↥(ReeTag.G2.reeGamma K a), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ s = 1) →
      (∀ j ∈ signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ), ∀ e ∈ E,
        j * e * j⁻¹ ∈ E) → E = ⊥ := by
  classical
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set J₀ := signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) with hJ₀
  have hXC : Γ ≤ adjointGroup ReeTag.G2.tag K := fun g hg => (ReeTag.mem_reeGamma.1 hg).1
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨e⟩ := nonempty_srD_mulEquiv (K := K) hw₀
  have hDΓ : Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ≤
      Γ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ReeTag.g2U₀_mem_reeGamma K a
    · exact ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := a) hw₀
  have hDJ := closure_g2U₀_n_le_fixed (a := a) σ hw₀
  let ι : srP →* ↥Γ := (Subgroup.inclusion hDΓ).comp e.symm.toMonoidHom
  have hι : Function.Injective ι := (Subgroup.inclusion_injective hDΓ).comp e.symm.injective
  have hιJ : ∀ d : srP, ι d ∈ J₀ := by
    intro d
    obtain ⟨j, hj, hjd⟩ := hDJ (e.symm d).2
    have : j = ι d := Subtype.ext hjd
    rw [← this]
    exact hj
  have hK3 : CharP K 3 := inferInstanceAs (CharP K ReeTag.G2.prime)
  let F := AlgebraicClosure K
  have hF3 : CharP F 3 := charP_of_injective_algebraMap (algebraMap K F).injective 3
  have hp : ((ReeTag.G2.prime : ℕ) : K) = 0 := CharP.cast_eq_zero K ReeTag.G2.prime
  have : Fintype ReeTag.G2.shortLabels := Fintype.ofFinite _
  let ρ : ↥Γ →* Module.End F (ReeTag.G2.shortLabels → F) :=
    (shortAdjRep ReeTag.G2 K F hp).comp (Subgroup.inclusion hXC)
  have hρ : Function.Injective ρ :=
    (shortAdjRep_injective (t := ReeTag.G2) (F := F)).comp (Subgroup.inclusion_injective hXC)
  have hdim : Module.finrank F (ReeTag.G2.shortLabels → F) ≤ 7 := by
    rw [finrank_short_pi ReeTag.G2 F]
    exact le_of_eq rfl
  have hZ : ∀ x : ↥Γ, (∀ y : ↥Γ, x * y = y * x) → x = 1 := by
    intro x hx
    have hxc : x ∈ Subgroup.center ↥Γ := Subgroup.mem_center_iff.2 fun y => (hx y).symm
    rw [(small_Ree_fixed_group_center_trivial a K hK).1] at hxc
    exact Subgroup.mem_bot.1 hxc
  obtain ⟨g, w, A, hg, hw, hAcomm, hA2, hAg, hAg'⟩ := srP_data
  have : IsSimpleGroup srP := isSimpleGroup_srP
  intro E hEcomm hEexp hnorm
  refine eq_bot_of_normalized_by_simple ι hι ρ hρ hdim hZ g w hg hw A hAcomm hA2 hAg hAg' hs hs3 E
    hEcomm hEexp (fun d v hv => hnorm _ (hιJ d) v hv)

theorem subfieldNonLocalizedSmallReeBZero
    : SubfieldNonLocalizedSmallReeBZero := by
  intro a ha K _ _ _ hK p hp hp3 hpa σ hσ
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : Finite ↥(ReeTag.G2.reeGamma K a) := Subtype.finite
  refine nonLocalized_of_elemAbelian (fun s E hs hE0 hEcomm hEexp hle => hE0 ?_)
  have hnorm : ∀ j ∈ signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ), ∀ e ∈ E,
      j * e * j⁻¹ ∈ E := fun j hj e he => (Subgroup.mem_normalizer_iff.1 (hle hj) e).1 he
  by_cases hs3 : s = 3
  · subst hs3
    have : Fact (Nat.Prime 3) := ⟨hs⟩
    have hEp : IsPGroup 3 E := by
      refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
      have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
      rcases (Nat.dvd_prime hs).mp h1 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    exact smallRee_threeGroup_eq_bot hK σ E hEp hnorm
  · exact smallRee_eq_bot_of_ne_three hK σ hs hs3 E hEcomm hEexp hnorm

end

end CFSG.SignalizerFunctorTheorem.CatalogBridge
