module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.G2Regular
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.U33SmallIndex
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.ChevalleyPerm

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.GH74.KGroups.U33

variable {K : Type} [Field K] [Finite K]

theorem nonLocalized_G2_of_card_eq_two
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2) :
    NonLocalized ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) := by
  classical
  obtain ⟨r, hrK⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (ModGL .G2 K) := finite_modGL
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  set J : Subgroup ↥(adjointGroup .G2 K) :=
    (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) with hJ
  apply nonLocalized_of_elemAbelian
  intro s E hs hE0 hEcomm hEexp hle
  have hnormE : ∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E := fun j hj e he =>
    (Subgroup.mem_normalizer_iff.mp (hle hj) e).mp he
  have : Fact s.Prime := ⟨hs⟩
  have hEp : IsPGroup s E := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  by_cases hsr : s = r
  · subst hsr
    exact hE0 (eq_bot_of_isPGroup_of_normalized_subfield σ s E hEp hnormE)
  ·
    set k := fixSubfield σ with hkdef
    set f := baseChangeGL (τ := .G2) k.subtype with hf
    have hfinj : Function.Injective f := baseChangeGL_injective _
    set D : Subgroup (ModGL .G2 k) := ⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ with hD
    set Jd : Subgroup (ModGL .G2 K) := D.map f with hJd
    have hJdeq : Jd = ⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ := by
      rw [hJd, hD, Subgroup.map_commutator]
      rfl
    have hJdJ : Jd ≤ fixedFieldImage .G2 σ := by
      rw [hJdeq]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hJdX : Jd ≤ adjointGroup .G2 K := hJdJ.trans (fixedFieldImage_le_adjointGroup σ)
    have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
    obtain ⟨e1⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hLie
    have hDsimple : IsSimpleGroup ↥D := by
      rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM).2
      all_goals exact absurd h0 (by norm_num)
    let e2 : ↥D ≃* ↥Jd := D.equivMapOfInjective f hfinj
    let eΓ : ↥Jd ≃* ↥QP.originalSubgroup := e2.symm.trans e1
    have : IsSimpleGroup ↥Jd := e2.symm.isSimpleGroup
    let F := AlgebraicClosure K
    have hFr : CharP F r := charP_of_injective_algebraMap (algebraMap K F).injective r
    let ρ : ↥(adjointGroup .G2 K) →* Module.End F (Label .G2 → F) :=
      (adjRep .G2 K F).comp (adjointGroup .G2 K).subtype
    have hρ : Function.Injective ρ := (adjRep_injective .G2 K F).comp Subtype.val_injective
    have hV : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm _ a.2 _ b.2)⟩⟩
    have : Finite E := Subtype.finite
    have hinv : (Nat.card E : F) ≠ 0 := cast_card_ne_zero_of_exponent hr hs hsr hEexp
    let φ : ↥Jd →* ↥(adjointGroup .G2 K) := Subgroup.inclusion hJdX
    have hnorm : ∀ g : ↥Jd, ∀ v ∈ E, φ g * v * (φ g)⁻¹ ∈ E := fun g v hv =>
      hnormE (φ g) (Subgroup.mem_subgroupOf.2 (hJdJ g.2)) v hv
    obtain ⟨hfin, hcard⟩ := finite_card_weights ρ E hV
    have hcard14 : Nat.card (Wt ρ E) ≤ 14 := by
      have h := hcard
      rw [finrank_label_pi .G2 F, card_label_eq .G2] at h
      exact h
    have : Finite (Wt ρ E) := hfin
    have hα : weightAction ρ E φ hnorm = 1 := action_eq_one_of_simple eΓ hcard14 _
    have hcentJd : ∀ g : ↥Jd, ∀ v ∈ E, φ g * v * (φ g)⁻¹ = v := fun g =>
      centralizes_of_weightAction_eq_one ρ hρ E hV hinv φ hnorm g (by rw [hα]; rfl)
    obtain ⟨u, huJ, hureg⟩ := exists_regular_mem_commutator σ
    have huJd : u ∈ Jd := hJdeq ▸ huJ
    have hVA : E.map (adjointGroup .G2 K).subtype ≤ adjointGroup .G2 K := by
      rintro _ ⟨e, -, rfl⟩
      exact e.2
    have hbot := eq_bot_of_commute_regular (r := r) hs hsr hureg hVA (by
      rintro _ ⟨e, he, rfl⟩
      have := hEexp e he
      simpa using congrArg Subtype.val this) (by
      rintro _ ⟨e, he, rfl⟩
      have h1 := hcentJd ⟨u, huJd⟩ e he
      have h2 : (φ ⟨u, huJd⟩ : ↥(adjointGroup .G2 K)) * e * (φ ⟨u, huJd⟩)⁻¹ = e := h1
      have h3 := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      have h4 : (u : ModGL .G2 K) * (e : ModGL .G2 K) = (e : ModGL .G2 K) * u := by
        simpa [φ, mul_inv_eq_iff_eq_mul] using h3
      exact h4.symm)
    exact hE0 ((Subgroup.map_eq_bot_iff_of_injective _
      (adjointGroup .G2 K).subtype_injective).1 hbot)

end CFSG.SignalizerFunctorTheorem.NonLocalExc
