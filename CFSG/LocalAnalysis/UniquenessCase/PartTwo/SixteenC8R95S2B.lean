module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93i
import CFSG.Quasithin.H13.GoldschmidtG52Sec
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped MatrixGroups commutatorElement IsMulCommutative
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open CFSG.Theory.Representation (kerRepresentation kerRepresentation_faithful
  kerRepresentation_irreducible_iff)

variable {G : Type} [Group G] [Finite G]

theorem r95s_quot_ker_two (hK461 : UCK.K461) {Q : Type} [Group Q] [Finite Q]
    (hQK : CFSG.Open.IsKGroup Q) (hE9 : ¬ HasE9 Q) (hQperf : commutator Q = ⊤)
    {D : Subgroup Q} (hD3 : Nat.card D = 3) (hDgen : normalClosure (D : Set Q) = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod 2) Q V)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g : Q, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV ρ D = ⊥) :
    ¬ 3 ∣ Nat.card ρ.ker ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ),
      Nat.card F = 2 ^ n ∧ Nonempty (Q ⧸ ρ.ker ≃* SL(2, F)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 := not_three_dvd_card_ker ρ hE9 hD3 hfix
  refine ⟨hN3, ?_⟩
  obtain ⟨d₀, hd₀⟩ := exists_prime_orderOf_dvd_card' 3 (hD3 ▸ dvd_rfl : 3 ∣ Nat.card D)
  have hd₀1 : (d₀ : Q) ≠ 1 := fun h => by
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hd₀
    omega
  let π : Q →* Q ⧸ ρ.ker := QuotientGroup.mk' ρ.ker
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hinj : Function.Injective (kerRepresentation ρ) := kerRepresentation_faithful ρ
  have hirrb : Representation.IsIrreducible (kerRepresentation ρ) :=
    (kerRepresentation_irreducible_iff ρ).mpr
      (CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule ρ hirr)
  have hDb3 : Nat.card (D.map π) = 3 := by
    have hdvd : Nat.card (D.map π) ∣ 3 := hD3 ▸ Subgroup.card_map_dvd D π
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hmem : π d₀ ∈ D.map π := Subgroup.mem_map_of_mem π d₀.2
      rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hmem
      exact hd₀1 (eq_one_of_mem_ker_of_fixV_eq_bot ρ hD3 hfix d₀.2
        ((QuotientGroup.eq_one_iff _).mp hmem))
    · exact h3
  have hDbgen : normalClosure ((D.map π : Subgroup (Q ⧸ ρ.ker)) : Set (Q ⧸ ρ.ker)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ π hπ, hDgen,
      Subgroup.map_top_of_surjective π hπ]
  have hfixb : fixV (kerRepresentation ρ) (D.map π) = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    intro v hv
    have hv' : ∀ b ∈ D.map π, kerRepresentation ρ b v = v := hv
    show ∀ a ∈ D, ρ a v = v
    intro a ha
    exact hv' (π a) (Subgroup.mem_map_of_mem π ha)
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (Q ⧸ ρ.ker)) = 1 := by
    refine le_antisymm (pRank_three_le_one_of_not_hasE9 fun h =>
      hE9 (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient ρ.ker hN3 h)) ?_
    exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := D.map π) (by norm_num) le_top
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hDb3) (k := 1) (by rw [hDb3, pow_one])
  have hperfb : commutator (Q ⧸ ρ.ker) = ⊤ := by
    haveI : Group.IsPerfect Q := ⟨hQperf⟩
    exact Group.IsPerfect.commutator_eq_top
  have hKb : CFSG.Open.IsKGroup (Q ⧸ ρ.ker) := hQK.quotient ρ.ker
  have hfixs : CFSG.RankThree.FFModules.fixSub (kerRepresentation ρ) (D.map π) = ⊥ := hfixb
  obtain ⟨n, F, hF, hFin, φ, ψ, hFc, -⟩ := hK461 (Q ⧸ ρ.ker) hKb V (kerRepresentation ρ) hinj
    hirrb (D.map π) hDb3 hDbgen hfixs hrank hperfb
  exact ⟨F, hF, hFin, n, hFc, ⟨φ⟩⟩

theorem r95s_chief_quot_two (hK461 : UCK.K461) {K Z U W : Subgroup G}
    (hKK : CFSG.Open.IsKGroup ↥K) (hE9 : ¬ HasE9 ↥K) (hKperf : ⁅K, K⁆ = K) (hZK : Z ≤ K)
    (hZ3 : Nat.card Z = 3)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K)
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder 2 K U W)
    (hfix : ∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W) :
    ∃ (N : Subgroup ↥K) (_ : N.Normal), ¬ 3 ∣ Nat.card N ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ),
        Nat.card F = 2 ^ n ∧ Nonempty (↥K ⧸ N ≃* SL(2, F)) := by
  classical
  haveI hWn : (W.subgroupOf U).Normal := hUW.normal
  haveI hEl : IsElementaryAbelian 2 (↥U ⧸ W.subgroupOf U) := hUW.isElementaryAbelian
  haveI : Nontrivial (↥U ⧸ W.subgroupOf U) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hUW.1.ne ((Subgroup.subgroupOf_eq_top.mp htop).antisymm hUW.1.le).symm
  let ρ : Representation (ZMod 2) ↥K (Additive (↥U ⧸ W.subgroupOf U)) :=
    (Units.coeHom _).comp (CFSG.ABGLocalTools.chiefRep (p := 2) hUW.2.1 hUW.2.2.1)
  have happ : ∀ (k : ↥K) (u : ↥U), ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : ↥U ⧸ W.subgroupOf U) :=
    fun k u => CFSG.ABGLocalTools.chiefRep_apply_mk (p := 2) hUW.2.1 hUW.2.2.1 k u
  have hirr : ∀ V₀ : Submodule (ZMod 2) (Additive (↥U ⧸ W.subgroupOf U)),
      (∀ g : ↥K, ∀ v ∈ V₀, ρ g v ∈ V₀) → V₀ = ⊥ ∨ V₀ = ⊤ := fun V₀ hV₀ =>
    CFSG.ABGLocalTools.chiefRep_irreducible hUW V₀ (fun k v hv => hV₀ k v hv)
  have hfixV : fixV ρ (Z.subgroupOf K) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    have huW : (u : G) ∈ W := by
      refine hfix (u : G) u.2 fun x hx => ?_
      let k : ↥K := ⟨x, hZK hx⟩
      have hfixed := hv k (Subgroup.mem_subgroupOf.mpr hx)
      rw [happ] at hfixed
      have hmem : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : G)⁻¹ * u ∈ W :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp (Additive.ofMul.injective hfixed))
      have hcoe : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : G) = x * u * x⁻¹ := by
        rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
      rw [hcoe] at hmem
      have h2 := hUW.2.2.2.1 (u : G) u.2 _ (W.inv_mem hmem)
      rwa [show (u : G) * ((x * u * x⁻¹)⁻¹ * u)⁻¹ * (u : G)⁻¹ = x * u * x⁻¹ * (u : G)⁻¹ by
        group] at h2
    have hq : ((u : ↥U) : ↥U ⧸ W.subgroupOf U) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr huW)
    rw [Submodule.mem_bot, hq]
    rfl
  have hD3 : Nat.card (Z.subgroupOf K) = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
  have hperf : commutator ↥K = ⊤ := by
    haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨hN3, F, hF, hFin, n, hFc, hφ⟩ := r95s_quot_ker_two hK461 hKK hE9 hperf hD3
    (normalClosure_subgroupOf_eq_top hZK hKgen) ρ hirr hfixV
  exact ⟨ρ.ker, inferInstance, hN3, F, hF, hFin, n, hFc, hφ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
