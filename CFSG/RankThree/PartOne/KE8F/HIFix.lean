module

public import CFSG.RankThree.PartOne.KE8F.HICore
public import CFSG.RankThree.PartOne.KE8F.HV

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.LocalRank
open scoped Matrix Pointwise MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Fix

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem coreV_le_torus (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (hC : Subgroup.center (adjointGroup .E8 K) = ⊥) (c : adjointGroup .E8 K)
    (hcard : Nat.card (torsionC p F c) = p ^ 4) {x : adjointGroup .E8 K}
    (hxA : x ∈ torsionC p F c) {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B) :
    ∀ v ∈ coreV p B x, psiC F c v ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  have hXA : Subgroup.zpowers x ≤ torsionC p F c := by
    rw [Subgroup.zpowers_le]
    exact hxA
  have hcent : ∀ d : adjointGroup .E8 K,
      d ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (adjointGroup .E8 K)) :
        Set (adjointGroup .E8 K)) ↔ d ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) := by
    intro d
    constructor
    · intro hd
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hd x (Subgroup.mem_zpowers x)).symm
    · intro hd
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      have hxd : x * d = d * x := (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
      obtain ⟨k, rfl⟩ := hh
      exact ((Commute.zpow_left (show Commute x d from hxd) k)).eq
  exact V_le_torus F hf hK hp hp10 hpf c hcard hXA
    (fun v hv => (hcent v).2 (coreV_le_centralizer B x hv))
    (fun d hd v hv => coreV_conj_mem hB ((hcent d).1 hd) hv)
    (coreV_solvable hp hC B x) (coreV_card hp hC B x)

theorem eta_fixes_pairC (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (hC : Subgroup.center (adjointGroup .E8 K) = ⊥) (c : adjointGroup .E8 K)
    (hcard : Nat.card (torsionC p F c) = p ^ 4) {x : adjointGroup .E8 K}
    (hxA : x ∈ torsionC p F c) {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (hvis : psiC F c x ∈ Subgroup.centralizer (rootSpan .E8 L (cls α) : Set (ModGL .E8 L))) :
    ∃ P : Unit → Subgroup (ModGL .E8 L),
      IsSigmaFamily F.n (iterateFrobenius L ℓ f) (cls α) P ∧
      (∀ u ∈ P (), ∃ d, psiC F c d = u) ∧
      ∀ d : adjointGroup .E8 K, psiC F c d ∈ P () →
        (∀ v ∈ coreV p B x, v * d = d * v) ∧ ∀ η ∈ coreR p B x, η d = d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hYQ : ∀ y ∈ Subgroup.zpowers x, psiC F c y ∈
      Subgroup.centralizer (rootSpan .E8 L (cls α) : Set (ModGL .E8 L)) := by
    rintro y ⟨k, rfl⟩
    rw [map_zpow]
    exact zpow_mem hvis k
  obtain ⟨P, hP, hrat⟩ := exists_pair_family_C F hf c hα hYQ
  refine ⟨P, hP, fun u hu => ?_, ?_⟩
  · obtain ⟨d, -, hd⟩ := hrat u hu
    exact ⟨d, hd⟩
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
  have hVT := coreV_le_torus F hf hK hp hp10 hpf hC c hcard hxA hB
  set V : Subgroup (adjointGroup .E8 K) := coreV p B x with hV
  set PC : Subgroup (adjointGroup .E8 K) := (P ()).comap (psiC F c) with hPC
  have hPCD : PC ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) := by
    intro d hd
    obtain ⟨d', hd', hd'd⟩ := hrat (psiC F c d) hd
    have : d' = d := psiC_injective F c hd'd
    subst this
    exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hd' x (Subgroup.mem_zpowers x)).symm
  have hVnorm : ∀ v ∈ V, ∀ u ∈ P (), psiC F c v * u * (psiC F c v)⁻¹ ∈ P () := by
    intro v hv u hu
    have hv' := hVT v hv
    obtain ⟨hvH, hvfix⟩ := mem_twistedTorusOf.1 hv'
    exact hPnorm () (psiC F c v) (Subgroup.mem_sup_left hvH) hvfix u hu
  have hVnormalizer : ∀ v ∈ V, psiC F c v ∈ Subgroup.normalizer ((P () : Subgroup (ModGL .E8 L)) :
      Set (ModGL .E8 L)) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hVnorm v hv h hh, fun hh => ?_⟩
    have := hVnorm v⁻¹ (inv_mem hv) _ hh
    simpa [map_inv, mul_assoc] using this
  have hD'le : V ⊔ PC ≤ (Subgroup.normalizer ((P () : Subgroup (ModGL .E8 L)) :
      Set (ModGL .E8 L))).comap (psiC F c) := by
    refine sup_le (fun v hv => hVnormalizer v hv) (fun g hg => ?_)
    exact Subgroup.le_normalizer hg
  have hD'D : V ⊔ PC ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) :=
    sup_le (coreV_le_centralizer B x) hPCD
  let ψ' : (V ⊔ PC : Subgroup (adjointGroup .E8 K)) →* ModGL .E8 L :=
    (psiC F c).comp (V ⊔ PC).subtype
  have hψ'inj : Function.Injective ψ' := (psiC_injective F c).comp (Subgroup.subtype_injective _)
  have hPψ' : P () ≤ ψ'.range := by
    intro u hu
    obtain ⟨d, -, hd⟩ := hrat u hu
    have hdPC : d ∈ PC := by
      change psiC F c d ∈ P ()
      rw [hd]
      exact hu
    exact ⟨⟨d, Subgroup.mem_sup_right hdPC⟩, hd⟩
  have hnorm' : ∀ d : (V ⊔ PC : Subgroup (adjointGroup .E8 K)), ∀ u ∈ P (),
      ψ' d * u * (ψ' d)⁻¹ ∈ P () := fun d u hu =>
    (Subgroup.mem_normalizer_iff.1 (hD'le d.2) u).1 hu
  have hV'n : (V.subgroupOf (V ⊔ PC)).Normal := ⟨fun v hv d => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact coreV_conj_mem hB (hD'D d.2) hv⟩
  have hV's : Group.IsSolvable (V.subgroupOf (V ⊔ PC)) := by
    have := coreV_solvable hp hC B x
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : V ≤ V ⊔ PC)).toMonoidHom)
      (MulEquiv.injective _)
  have hcommP := commutes_of_quasisimple_embedding ψ' hψ'inj (P ()) hPψ' (hPq ()) hnorm'
    (V.subgroupOf (V ⊔ PC))
  have hVd : ∀ d : adjointGroup .E8 K, psiC F c d ∈ P () → ∀ v ∈ V, v * d = d * v := by
    intro d hd v hv
    have h := hcommP ⟨v, Subgroup.mem_sup_left hv⟩ (Subgroup.mem_subgroupOf.2 hv) _ hd
    exact psiC_injective F c (by rw [map_mul, map_mul]; exact h)
  intro d hd
  refine ⟨hVd d hd, fun η hη => ?_⟩
  have hPCq : CFSG.IsQuasisimple PC := by
    have hmap : PC.map (psiC F c) = P () := by
      rw [hPC, Subgroup.map_comap_eq]
      refine inf_of_le_right fun u hu => ?_
      obtain ⟨d, -, hd⟩ := hrat u hu
      exact ⟨d, hd⟩
    have e1 : PC ≃* P () :=
      (Subgroup.equivMapOfInjective PC (psiC F c) (psiC_injective F c)).trans
        (MulEquiv.subgroupCongr hmap)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm (hPq ())
  have hPCperf : ⁅PC, PC⁆ = PC := Subgroup.isPerfect_iff.1 hPCq.1
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    psiC_injective F c (by
      rw [map_mul, map_mul]
      exact twistedTorus_comm F (hVT a ha) (hVT b hb))
  exact eq_of_mul_inv_mem_abelian η hPCperf hVab
    (fun e he => eta_mul_inv_mem_coreV hC hB hη (hPCD he))
    (fun v hv e he => hVd e he v hv) d hd

end Fix

end CFSG.RankThree.PartOne.KE8F
