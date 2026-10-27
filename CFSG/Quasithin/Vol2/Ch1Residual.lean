module

public import CFSG.Quasithin.Background.A1bLemma126
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem opResidual_two_idem (A : Subgroup G) : opResidual 2 (opResidual 2 A) = opResidual 2 A := by
  refine le_antisymm (opResidual_le 2 _) ?_
  unfold opResidual
  refine Subgroup.closure_mono ?_
  rintro x ⟨hxA, hxc⟩
  exact ⟨Subgroup.subset_closure ⟨hxA, hxc⟩, hxc⟩

omit [Finite G] in
theorem commutator_commutator_eq_of_opResidual {U X : Subgroup G} (hU : IsElemAbelian 2 U)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hX : opResidual 2 X = X) :
    ⁅⁅U, X⁆, X⁆ = ⁅U, X⁆ := by
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (Subgroup.normalizer_commutator_ge_right U X)) ?_
  set W := ⁅U, X⁆ with hW
  set W' := ⁅W, X⁆ with hW'
  have hXW' : X ≤ Subgroup.normalizer (W' : Set G) := Subgroup.normalizer_commutator_ge_right W X
  let Tr : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (U : Set G) ∧ x ∈ Subgroup.normalizer (W' : Set G) ∧
        ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ W'}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨(Subgroup.normalizer _).mul_mem ha.1 hb.1, (Subgroup.normalizer _).mul_mem ha.2.1 hb.2.1,
          fun u hu => ?_⟩
        have e : a * b * u * (a * b)⁻¹ * u⁻¹ =
            (a * (b * u * b⁻¹ * u⁻¹) * a⁻¹) * (a * u * a⁻¹ * u⁻¹) := by group
        rw [e]
        exact W'.mul_mem ((Subgroup.mem_normalizer_iff.mp ha.2.1 _).mp (hb.2.2 u hu)) (ha.2.2 u hu)
      one_mem' := ⟨(Subgroup.normalizer _).one_mem, (Subgroup.normalizer _).one_mem,
        fun u _ => by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨(Subgroup.normalizer _).inv_mem ha.1, (Subgroup.normalizer _).inv_mem ha.2.1,
          fun u hu => ?_⟩
        have hu' : a⁻¹ * u * a ∈ U := by
          have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem ha.1) u).mp hu
          simpa using this
        have h := W'.inv_mem (ha.2.2 _ hu')
        have e : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ =
            (a * (a⁻¹ * u * a) * a⁻¹ * (a⁻¹ * u * a)⁻¹)⁻¹ := by group
        rw [e]
        exact h }
  have hsq : ∀ x ∈ X, x ^ 2 ∈ Tr := by
    intro x hx
    refine ⟨(Subgroup.normalizer _).pow_mem (hXU hx) 2, (Subgroup.normalizer _).pow_mem (hXW' hx) 2,
      fun u hu => ?_⟩
    set c : G := x * u * x⁻¹ * u⁻¹ with hc
    have hcU : c ∈ U := by
      have h1 : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hXU hx) u).mp hu
      exact U.mul_mem h1 (U.inv_mem hu)
    have hcW : c ∈ W := by
      have h1 : ⁅x, u⁆ ∈ ⁅X, U⁆ := Subgroup.commutator_mem_commutator hx hu
      rw [Subgroup.commutator_comm] at h1
      simpa [commutatorElement_def, hc] using h1
    have hc2 : x * c * x⁻¹ * c⁻¹ ∈ W' := by
      have h1 : ⁅x, c⁆ ∈ ⁅X, W⁆ := Subgroup.commutator_mem_commutator hx hcW
      rw [Subgroup.commutator_comm] at h1
      simpa [commutatorElement_def] using h1
    have hcsq : c * c = 1 := by rw [← sq]; exact hU.2 c hcU
    have e : x ^ 2 * u * (x ^ 2)⁻¹ * u⁻¹ = (x * c * x⁻¹ * c⁻¹) * (c * c) := by
      simp only [hc, pow_two]
      group
    rw [e, hcsq, mul_one]
    exact hc2
  have hXTr : X ≤ Tr := by
    rw [← hX]
    refine (Subgroup.closure_le Tr).mpr ?_
    rintro x ⟨hxX, hxc⟩
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 2) hxc.symm
    rw [← hm]
    exact Tr.pow_mem (hsq x (hX ▸ Subgroup.subset_closure ⟨hxX, hxc⟩)) m
  refine Subgroup.commutator_le.mpr fun u hu x hx => ?_
  have h := W'.inv_mem ((hXTr hx).2.2 u hu)
  have e : ⁅u, x⁆ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact h

theorem centralizes_pCoreOf_of_mem_commutator (hK : quasithinIsQTKECat G) {H U : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hUH : U ≤ H) (hU : IsElemAbelian 2 U) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2)
    {z : G} (hz : z ∈ ⁅U, opResidual 2 (H ⊓ Subgroup.normalizer (U : Set G))⁆) :
    z ∈ Subgroup.centralizer (pCoreOf q H : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  set Y := H ⊓ Subgroup.normalizer (U : Set G) with hY
  set X := opResidual 2 Y with hXdef
  have hXY : X ≤ Y := opResidual_le 2 Y
  have hXH : X ≤ H := hXY.trans inf_le_left
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := hXY.trans inf_le_right
  have hX : opResidual 2 X = X := opResidual_two_idem Y
  have hVU : ⁅U, X⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hXU
  have hV2 : IsPGroup 2 (⁅U, X⁆ : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using hU.2 x (hVU x.2))⟩
  have hVX : ⁅⁅U, X⁆, X⁆ = ⁅U, X⁆ := commutator_commutator_eq_of_opResidual hU hXU hX
  have hVel : IsElemAbelian 2 (⁅U, X⁆ : Subgroup G) := A1b.isElemAbelian_of_le hVU hU
  have hVH : ⁅U, X⁆ ≤ H := hVU.trans hUH
  have hr : CFSG.Open.pRank q (pCoreOf q H) ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hq.one_lt (CFSG.LieType.BorelTits.pCoreOf_le q H)).trans
      (pRank_le_two_of_pCoreOf_ne_bot hK hH hq hq2)
  exact centralizes_pCoreOf hq2 hXH hX hVH hV2 hVX hVel hr hz

end CFSG.Quasithin
