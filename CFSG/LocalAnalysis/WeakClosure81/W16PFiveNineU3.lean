module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3C
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineHc
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


theorem IsMinFam16.exists_comm_mem_of_psu (hF₁ : PSUThreeRootFacts) (hF₂ : PerfectPSUThreeFact)
    (hU3o : PSUThreeOuterInvolutionInput) (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n)
    (hcase : commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n ∧
      Nat.card (Subgroup.center X) ∣ 3)
    {x : G} (hxS : conjSubgroup V x ≤ S) {a : G} (ha : a ∈ conjSubgroup V x) :
    ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hY : IsElemAbelian 2 (SevenK.barSub (conjClosure V H) φ V) := by
    have hsub : IsElemAbelian 2 (V.subgroupOf (conjClosure V H)) :=
      hVea.subgroupOf (conjClosure V H)
    have hmap : IsElemAbelian 2 ((V.subgroupOf (conjClosure V H)).map φ) :=
      hsub.map φ
    simpa [SevenK.barSub] using hmap
  have hYcard : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 ^ n := hX.1
  by_cases hinner : ∃ y ∈ SevenK.barSub (conjClosure V H) φ V, α = MulAut.conj y
  · obtain ⟨y, hy, hαy⟩ := hinner
    exact SevenK.IsBarMap.exists_comm_mem_of_eq_conj hφ haK hα hy hαy
  · exfalso
    have hinner' : ∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α ≠ MulAut.conj y :=
      fun y hy heq => hinner ⟨y, hy, heq⟩
    obtain ⟨X₀, hX₀le, hX₀odd, hX₀notcenter, hX₀inv⟩ :=
      hU3o X n hcase.1 hcase.2.1 hcase.2.2
        (SevenK.barSub (conjClosure V H) φ V) hY hYcard α hα2 hαfix hinner'
    have hP : IsPGroup 2
        (pCoreOf 2 (centralizer (SevenK.barSub (conjClosure V H) φ V : Set X))) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hc : ∀ c : ↥(conjClosure V H), Odd (orderOf c) → φ c ∈ X₀ →
        (c : G) ∈ centralizer (V₀ : Set G) := by
      intro c hodd hcX₀
      exact IsMinFam16.mem_centralizer_V₀_of_odd_of_mul_conj h1 h5 hS h hH hV hQ hφ
        hxS ha hα hP hodd (hX₀le hcX₀) (hX₀inv (φ c) hcX₀)
    have hcenter := IsMinFam16.le_center_of_forall_mem_centralizer hF₁ hF₂ h1 h5 hS h hH hV
      hQ hφ hYcard ⟨hcase.1, hcase.2.1⟩ hX₀le hX₀odd hc
    exact hX₀notcenter hcenter

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
