module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFixAll
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineAut
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineHc
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.exists_comm_mem_of_extraspecial (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ)
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3)
    {x : G} (hxS : conjSubgroup V x ≤ S) {a : G} (ha : a ∈ conjSubgroup V x) :
    ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H) := by
  haveI : Finite ↥(conjClosure V H) := Subtype.finite
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hVea : IsElemAbelian 2 V := h.hyp.h6.elemAbelian
  have haV : a ∈ centralizer (V : Set G) :=
    Cex16.conj_le_centralizer_of_le_S h1 hS h hxS ha
  have haa : a * a = 1 := by
    have hmem : x * a * x⁻¹ ∈ V := mem_conjSubgroup_iff.mp ha
    have hsq := IsElemAbelian.mul_self_eq_one hVea hmem
    have h' : x * (a * a) * x⁻¹ = 1 := by
      calc x * (a * a) * x⁻¹ = (x * a * x⁻¹) * (x * a * x⁻¹) := by group
        _ = 1 := hsq
    have h'' := congrArg (fun t => x⁻¹ * t * x) h'
    rwa [show x⁻¹ * (x * (a * a) * x⁻¹) * x = a * a by group,
      show x⁻¹ * 1 * x = 1 by group] at h''
  have haH : a ∈ H := hH.1.1 (hxS ha)
  have haK : a ∈ normalizer ((conjClosure V H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure V H haH
  have haN : a ∈ normalizer ((pCoreOf 2 (conjClosure V H) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjClosure V H) haK
  obtain ⟨α, hα⟩ := SevenK.IsBarMap.exists_mulAut hφ haK haN
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨k, rfl⟩ := hφ.surjective z
    change α (α (φ k)) = φ k
    let k' : ↥(conjClosure V H) :=
      ⟨a * (k : G) * a⁻¹, (Subgroup.mem_normalizer_iff.1 haK (k : G)).1 k.2⟩
    have hk' : (k' : G) = a * (k : G) * a⁻¹ := rfl
    have hstep1 : α (φ k) = φ k' := hα k k' hk'
    have hstep2 : α (φ k') = φ k := by
      refine hα k' k ?_
      rw [hk']
      have hassoc : a * (a * (k : G) * a⁻¹) * a⁻¹
          = (a * a) * (k : G) * (a⁻¹ * a⁻¹) := by group
      rw [hassoc, haa]
      have hinv : a⁻¹ * a⁻¹ = 1 := by rw [(mul_inv_rev a a).symm, haa, inv_one]
      rw [hinv]
      group
    rw [hstep1, hstep2]
  have hαfix : ∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α y = y := by
    intro y hy
    obtain ⟨k, hkV, hky⟩ := SevenK.mem_barSub.mp hy
    rw [← hky]
    have hcomm := (Subgroup.mem_centralizer_iff.mp haV (k : G) hkV).symm
    have hconj : a * (k : G) * a⁻¹ = (k : G) := by
      rw [hcomm]
      group
    exact hα k k hconj.symm
  by_cases hInner : ∃ y ∈ SevenK.barSub (conjClosure V H) φ V, α = MulAut.conj y
  · obtain ⟨y, hy, hαy⟩ := hInner
    exact SevenK.IsBarMap.exists_comm_mem_of_eq_conj hφ haK hα hy hαy
  · exfalso
    have hY : IsElemAbelian 2 (SevenK.barSub (conjClosure V H) φ V) := by
      have hsub : IsElemAbelian 2 (V.subgroupOf (conjClosure V H)) :=
        hVea.subgroupOf (conjClosure V H)
      have hmap : IsElemAbelian 2 ((V.subgroupOf (conjClosure V H)).map φ) :=
        hsub.map φ
      simpa [SevenK.barSub] using hmap
    have hgen : normalClosure
        ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ :=
      IsMinFam16.normalClosure_barSub_eq_top h1 hS h hH hV hφ
    have hne : ∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α ≠ MulAut.conj y :=
      fun y hy hyα => hInner ⟨y, hy, hyα⟩
    have hinv : ∀ z ∈ (Subgroup.center ↥(fusionOddCore X)).map
        (fusionOddCore X).subtype, α z = z⁻¹ :=
      Shape166.inv_center_of_extraspecial hY hgen hX hp hN hNc α hα2 hαfix hne
    obtain ⟨c, hodd, hcZ, hcnot⟩ :=
      IsMinFam16.exists_odd_not_mem_centralizer_V₀ h1 h5 hS h hH hV hQ hφ hX hp hN hNc
    have hcenter : (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype
        ≤ centralizer (SevenK.barSub (conjClosure V H) φ V : Set X) :=
      Shape166.center_le_centralizer_of_extraspecial hY hgen hX hp hN hNc
    have hcV : φ c ∈ centralizer (SevenK.barSub (conjClosure V H) φ V : Set X) :=
      hcenter hcZ
    have hcP : α (φ c) * φ c ∈ (⊥ : Subgroup X) := by
      rw [hinv (φ c) hcZ]
      simp
    have hc : (c : G) ∈ centralizer (V₀ : Set G) :=
      IsMinFam16.mem_centralizer_V₀_of_odd_of_mul_conj h1 h5 hS h hH hV hQ hφ hxS ha hα
        (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup X)) hodd hcV hcP
    exact hcnot hc

end CFSG.LocalAnalysis.WeakClosure81

end
