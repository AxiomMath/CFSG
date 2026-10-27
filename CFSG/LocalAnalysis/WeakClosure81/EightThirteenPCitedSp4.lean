module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedAut
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedSp4Fix
import CFSG.RankThree.PartTwo.Sec21.FF84S49AGen
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (uc22pwlie_charP_two)
open CFSG.QuasithinUnique.Id2519.USp4 (aut_facts exists_conj_fieldAut card_pointwiseStab_le_two
  fixedSub mem_fixedSub pointwiseStab mem_pointwiseStab)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut spSemilinearAutGroup)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spInner)

private theorem wccs_mem_inner_iff {M : Type*} [Group M] (β : MulAut M) :
    β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner M ↔
      ∃ g : M, ∀ x : M, β x = g * x * g⁻¹ := by
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, fun x => by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, MulEquiv.ext fun x => by rw [hg x]; rfl⟩

private theorem wccs_eq_or_of_card_le_two {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (hcard : Nat.card H ≤ 2) {a b c : G} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra hcon
  have hca : c ≠ a := fun h1 => hcon (Or.inl h1)
  have hcb : c ≠ b := fun h1 => hcon (Or.inr h1)
  let f : Fin 3 → H := ![(⟨a, ha⟩ : H), ⟨b, hb⟩, ⟨c, hc⟩]
  have hfinj : Function.Injective f := by
    intro i j hij
    have h2 := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hle : Nat.card (Fin 3) ≤ Nat.card H := Nat.card_le_card_of_injective f hfinj
  have h3 : Nat.card (Fin 3) = 3 := Nat.card_fin 3
  omega

private theorem wccs_notElem {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    OuterFixedNotElem (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := by
  intro β hβ2 hout
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hout
    exact ⟨1, fun x => by simp [h1]⟩
  have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq, hβ2]) hβ1
  have hβE : β ∈ spSemilinearAutGroup 2 F := (aut_facts hF).1 β hord
  have hnot : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner _ :=
    fun hmem => hout ((wccs_mem_inner_iff β).1 hmem)
  obtain ⟨σ, g, hσ1, hσσ, hβh⟩ := exists_conj_fieldAut hF hβ2 hnot hβE
  let c : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := spInner 2 F g
  let τ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := fieldAut 2 F σ
  have hβh' : β = c * τ * c⁻¹ := hβh
  obtain ⟨e'⟩ := fixedSub_fieldAut_equiv_perm_six hF hσ1 hσσ
  let p : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hp2 : p * p ≠ 1 := by decide
  let y : ↥(fixedSub τ) := e'.symm p
  have hy2 : y * y ≠ 1 := by
    intro h1
    apply hp2
    have h2 : e' (y * y) = e' (1 : ↥(fixedSub τ)) := congrArg e' h1
    rw [map_mul, map_one] at h2
    rwa [show e' y = p from e'.apply_symm_apply p] at h2
  refine ⟨c (y : _), ?_, ?_⟩
  · rw [hβh', MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, y.2]
  · intro h1
    apply hy2
    have h2 : c ((y : _) * (y : _)) = c 1 := by rw [map_mul, h1, map_one]
    exact Subtype.ext (c.injective h2)

private theorem wccs_noNormalTwo {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) :
    OuterFixedNoNormalTwo (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := by
  intro β hβ2 hout E hEp hEfix hEnor
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hout
    exact ⟨1, fun x => by simp [h1]⟩
  have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq, hβ2]) hβ1
  have hβE : β ∈ spSemilinearAutGroup 2 F := (aut_facts hF).1 β hord
  have hnot : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner _ :=
    fun hmem => hout ((wccs_mem_inner_iff β).1 hmem)
  obtain ⟨σ, g, hσ1, hσσ, hβh⟩ := exists_conj_fieldAut hF hβ2 hnot hβE
  let c : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := spInner 2 F g
  let τ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := fieldAut 2 F σ
  have hβh' : β = c * τ * c⁻¹ := hβh
  obtain ⟨e'⟩ := fixedSub_fieldAut_equiv_perm_six hF hσ1 hσσ
  have hmap : (fixedSub β).map (c⁻¹).toMonoidHom = fixedSub τ := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_fixedSub] at hx
      rw [mem_fixedSub]
      change τ (c⁻¹ x) = c⁻¹ x
      have hx' : c (τ (c⁻¹ x)) = x := by
        simpa only [hβh', MulAut.mul_apply] using hx
      have h2 := congrArg (fun z => c⁻¹ z) hx'
      simpa only [MulAut.inv_apply_self] using h2
    · intro hy
      rw [mem_fixedSub] at hy
      refine ⟨c y, ?_, ?_⟩
      · rw [mem_fixedSub, hβh', MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy]
      · change c⁻¹ (c y) = y
        exact MulEquiv.symm_apply_apply c y
  let eβ : ↥(fixedSub β) ≃* Equiv.Perm (Fin 6) :=
    ((fixedSub β).equivMapOfInjective (c⁻¹).toMonoidHom (fun x y h => c⁻¹.injective h)).trans
      ((MulEquiv.subgroupCongr hmap).trans e')
  have hNH : E ≤ fixedSub β := fun x hx => by
    rw [mem_fixedSub]
    exact hEfix x hx
  have hnor : fixedSub β ≤ CFSG.RankThree.PartTwo.Sec21.FF79.Nor E := by
    intro y hy
    show y ∈ Subgroup.normalizer (E : Set _)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hEnor y hy x hx
    · intro hx
      have hyinv : β y⁻¹ = y⁻¹ := by rw [map_inv, hy]
      have h1 := hEnor y⁻¹ hyinv (y * x * y⁻¹) hx
      have h2 : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x := by group
      rwa [h2] at h1
  exact CFSG.RankThree.PartTwo.Sec21.FF84.S4.normal_two_of_S6 eβ hNH hnor hEp

private theorem wccs_rigid {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    OuterFixedRigid (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := by
  intro β hβ2 hout γ hγ2 hγβ hγfix
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hout
    exact ⟨1, fun x => by simp [h1]⟩
  have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq, hβ2]) hβ1
  have hβE : β ∈ spSemilinearAutGroup 2 F := (aut_facts hF).1 β hord
  have hnot : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner _ :=
    fun hmem => hout ((wccs_mem_inner_iff β).1 hmem)
  obtain ⟨σ, g, hσ1, hσσ, hβh⟩ := exists_conj_fieldAut hF hβ2 hnot hβE
  let c : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := spInner 2 F g
  let τ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := fieldAut 2 F σ
  have hβh' : β = c * τ * c⁻¹ := hβh
  obtain ⟨e'⟩ := fixedSub_fieldAut_equiv_perm_six hF hσ1 hσσ
  let A6 : Subgroup (Equiv.Perm (Fin 6)) := alternatingGroup (Fin 6)
  have hA6 : Nat.card A6 = 360 := by
    show Nat.card (alternatingGroup (Fin 6)) = 360
    rw [nat_card_alternatingGroup]
    norm_num
  let fτ : Equiv.Perm (Fin 6) →* CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F) :=
    (fixedSub τ).subtype.comp e'.symm.toMonoidHom
  have hfτinj : Function.Injective fτ :=
    fun x y h => e'.symm.injective ((fixedSub τ).subtype_injective h)
  let Kτ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := A6.map fτ
  have hKτcard : Nat.card Kτ = 360 := by
    show Nat.card (A6.map fτ) = 360
    rw [Subgroup.card_map_of_injective (f := fτ) hfτinj, hA6]
  have hKτle : Kτ ≤ fixedSub τ := by
    rintro _ ⟨p, _, rfl⟩
    exact (e'.symm p).2
  let Kb : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := Kτ.map c.toMonoidHom
  have hKbcard : Nat.card Kb = 360 := by
    show Nat.card (Kτ.map c.toMonoidHom) = 360
    rw [Subgroup.card_map_of_injective (f := c.toMonoidHom) (fun x y h => c.injective h),
      hKτcard]
  have hKble : Kb ≤ fixedSub β := by
    rintro _ ⟨x, hx, rfl⟩
    change c x ∈ fixedSub β
    have hxτ : x ∈ fixedSub τ := hKτle hx
    rw [mem_fixedSub] at hxτ
    rw [mem_fixedSub, hβh', MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hxτ]
  have hβmem : β ∈ pointwiseStab Kb := by
    rw [mem_pointwiseStab]
    intro k hk
    exact mem_fixedSub.mp (hKble hk)
  have hcard := card_pointwiseStab_le_two hF hKbcard hβmem hβ2 hβ1
  have hγmem : γ ∈ pointwiseStab Kb := by
    rw [mem_pointwiseStab]
    intro k hk
    exact hγfix k (mem_fixedSub.mp (hKble hk))
  exact wccs_eq_or_of_card_le_two hcard (one_mem _) hβmem hγmem (fun h1 => hβ1 h1.symm)

theorem outerFixedNotElem_isSp4 {M : Type} [Group M] [Finite M] (h : IsSp4 M 2) :
    OuterFixedNotElem M := by
  obtain ⟨-, F, _, _, hF2, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  haveI : CharP F 2 := uc22pwlie_charP_two hF2
  have hF : Nat.card F = 4 := by rw [hF2]; norm_num
  exact outerFixedNotElem_of_mulEquiv e.symm (wccs_notElem hF)

theorem outerFixedNoNormalTwo_isSp4 {M : Type} [Group M] [Finite M] (h : IsSp4 M 2) :
    OuterFixedNoNormalTwo M := by
  obtain ⟨-, F, _, _, hF2, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  haveI : CharP F 2 := uc22pwlie_charP_two hF2
  have hF : Nat.card F = 4 := by rw [hF2]; norm_num
  exact outerFixedNoNormalTwo_of_mulEquiv e.symm (wccs_noNormalTwo hF)

theorem outerFixedRigid_isSp4 {M : Type} [Group M] [Finite M] (h : IsSp4 M 2) :
    OuterFixedRigid M := by
  obtain ⟨-, F, _, _, hF2, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  haveI : CharP F 2 := uc22pwlie_charP_two hF2
  have hF : Nat.card F = 4 := by rw [hF2]; norm_num
  exact outerFixedRigid_of_mulEquiv e.symm (wccs_rigid hF)

end CFSG.LocalAnalysis.WeakClosure81

end
