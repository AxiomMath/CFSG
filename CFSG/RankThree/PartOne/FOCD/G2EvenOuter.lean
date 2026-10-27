module

public import CFSG.RankThree.PartOne.FOCD.OuterFixed
public import CFSG.RankThree.PartOne.FOC.Assemble
import CFSG.RankThree.Chevalley.SteinbergBMG2NoninnerLocalCore
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub fixSubEquiv)

open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

open CFSG.QuasithinUnique.Id2519 (isSimpleGroup_adjointGroup_g2 g2Two_derived)

open scoped commutatorElement

theorem outerComp_of_fixed_layer {p : ℕ} {T : Type} [Group T] [Finite T] (hp : Odd p)
    (h : ∀ β : MulAut T, β ^ p = 1 → β ∉ innerAut T →
      ∃ N : Subgroup ↥(fixSub β), IsSimpleGroup ↥N ∧ (∃ a b : ↥N, a * b ≠ b * a) ∧
        commutator ↥(fixSub β) ≤ N ∧ ∀ y : ↥(fixSub β), y ^ 2 ∈ N) :
    OuterComp p T := by
  intro _ β hβp hβinn _ y hβy hyp E hE
  obtain ⟨N, hNs, hNnc, hcomm, hsq⟩ := h β hβp hβinn
  exact mem_component_of_simple_layer hE N hNs hNnc hcomm hsq hp ⟨y, hβy⟩
    (Subtype.ext (by simpa using hyp))

theorem g2Two_derived_nonabelian' {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    ∃ a b : ↥(commutator ↥(adjointGroup .G2 k)), a * b ≠ b * a := by
  obtain ⟨hs, hcard⟩ := g2Two_derived hk
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup ↥(commutator ↥(adjointGroup .G2 k)) := hs
  let _ : CommGroup ↥(commutator ↥(adjointGroup .G2 k)) :=
    { (inferInstance : Group ↥(commutator ↥(adjointGroup .G2 k))) with mul_comm := hcon }
  have hp := IsSimpleGroup.prime_card (α := ↥(commutator ↥(adjointGroup .G2 k)))
  rw [hcard] at hp
  exact absurd hp (by norm_num)

section G2


theorem outerComp_G2_even {K : Type} [Field K] [Finite K] {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) : OuterComp p (adjointGroup .G2 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  refine outerComp_of_fixed_layer hpodd ?_
  intro β hβp hβinn
  have hβ1 : β ≠ 1 := fun h => hβinn (h ▸ Subgroup.one_mem _)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hm K hK
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF β
  have hβeq : β = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpm, ⟨h0, hh0⟩, -⟩ :=
    even_G2_noninner_prime_local_core_trivial hm hK hp ⊤ le_top ⟨β, Subgroup.mem_top _⟩
      hβinn (by rw [Subgroup.orderOf_mk]; exact hβord) x σ hβeq
  obtain ⟨-, hkcard, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hm hK σ
  obtain ⟨f₀, hf₀⟩ := hpm
  have hkcard' : Nat.card (fixSubfield σ) = 2 ^ f₀ := by
    rw [hkcard, hσord, hf₀, Nat.mul_div_cancel_left f₀ hp.pos]
  have hf₀1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h] at hf₀
      omega
    · exact h
  set e : adjointGroup .G2 K ≃* adjointGroup .G2 K := MulAut.conj h0 with he
  have hcg : MulAut.congr e β = entrywiseAdjointAut .G2 σ := hh0
  have e3 : ↥(fixSub (entrywiseAdjointAut .G2 σ)) ≃* ↥(fixedFieldImage .G2 σ) :=
    (Subgroup.equivMapOfInjective _ (adjointGroup .G2 K).subtype
      (adjointGroup .G2 K).subtype_injective).trans (MulEquiv.subgroupCongr hJC1)
  let ε' : ↥(fixSub β) ≃* ↥(fixedFieldImage .G2 σ) :=
    ((fixSubEquiv e β).trans (MulEquiv.subgroupCongr (by rw [hcg]))).trans e3
  let ε : ↥(fixSub β) ≃* adjointGroup .G2 (fixSubfield σ) :=
    ε'.trans (fixedFieldImageEquiv (τ := .G2) σ).symm
  rcases Nat.lt_or_ge 1 f₀ with hf₀2 | hf₀2
  ·
    have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
      rw [hkcard']
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀2
    have hsG : IsSimpleGroup (adjointGroup .G2 (fixSubfield σ)) :=
      isSimpleGroup_adjointGroup_g2 hk3
    have hsF : IsSimpleGroup ↥(fixSub β) := ε.isSimpleGroup
    have hnc := CFSG.RankThree.Chevalley.SteinbergBT.not_commute_fixedFieldImage
      (τ := Tag.G2) (K := K) (by decide) σ
    push Not at hnc
    obtain ⟨u, v, huv⟩ := hnc
    refine ⟨⊤, Subgroup.topEquiv.isSimpleGroup, ?_, le_top, fun _ => Subgroup.mem_top _⟩
    refine ⟨⟨ε'.symm u, Subgroup.mem_top _⟩, ⟨ε'.symm v, Subgroup.mem_top _⟩, fun h => huv ?_⟩
    apply ε'.symm.injective
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h
  ·
    have hf₀eq : f₀ = 1 := le_antisymm hf₀2 hf₀1
    have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hkcard', hf₀eq, pow_one]
    obtain ⟨hDs, hDcard⟩ := g2Two_derived hk2
    have hGcard : Nat.card (adjointGroup .G2 (fixSubfield σ)) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk2]
      rfl
    set D : Subgroup (adjointGroup .G2 (fixSubfield σ)) :=
      commutator ↥(adjointGroup .G2 (fixSubfield σ)) with hD
    have hindex : D.index = 2 := by
      have h1 := Subgroup.card_mul_index D
      rw [hDcard, hGcard] at h1
      omega
    let ι : ↥D ≃* ↥(D.map ε.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective D ε.symm.toMonoidHom ε.symm.injective
    refine ⟨D.map ε.symm.toMonoidHom, ι.symm.isSimpleGroup, ?_, ?_, ?_⟩
    · obtain ⟨a, b, hab⟩ := g2Two_derived_nonabelian' hk2
      refine ⟨ι a, ι b, fun h => hab ?_⟩
      apply ι.injective
      rw [map_mul, map_mul]
      exact h
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      refine ⟨⁅ε a, ε b⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _), ?_⟩
      change ε.symm ⁅ε a, ε b⁆ = ⁅a, b⁆
      rw [map_commutatorElement, ε.symm_apply_apply, ε.symm_apply_apply]
    · intro y
      refine ⟨(ε y) ^ 2, ?_, ?_⟩
      · have := Subgroup.pow_index_mem D (ε y)
        rwa [hindex] at this
      · change ε.symm ((ε y) ^ 2) = y ^ 2
        rw [map_pow, ε.symm_apply_apply]

end G2

end CFSG.RankThree.PartOne.FOCD
