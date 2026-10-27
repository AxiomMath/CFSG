module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGE0E6InnNormal
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeE6Holds
public import CFSG.LocalAnalysis.StandardType.GGE0E6Act
public import CFSG.LocalAnalysis.StandardType.GGE0MarkBridge
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem isComponentOf_of_map_map {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) (L K : Subgroup H)
    (h : IsComponentOf (L.map f) (K.map f)) : IsComponentOf L K := by
  obtain ⟨hle, hsub, hq⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, hfk⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    rwa [hf hfk] at hk
  · have h' := hsub.comap f
    rwa [Subgroup.comap_map_eq_self_of_injective hf L,
      Subgroup.comap_map_eq_self_of_injective hf K] at h'
  · exact (CFSG.Assembly.IsQuasisimple.congr (L.equivMapOfInjective f hf)).2 hq

private theorem fixedSubgroup_conj_eq_centralizer {R : Type*} [Group R] (x : R) :
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup,
    Subgroup.mem_centralizer_singleton_iff]
  change (MulAut.conj x) g = g ↔ g * x = x * g
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem ggE0Model_e6
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    GGE0ModelOn (fun p => ¬ (p = 3 ∧ 3 ∣ Nat.card K - 1)) ↥(adjointGroup .E6 K)
      ((MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range ⊔
        (AutSt.e6DiagHom K).range) := by
  have hS2 : ExcNoSuzukiReeE6 := excNoSuzukiReeE6_holds
  intro p β E hp hp2 hR hβ1 hβp hβI hEI hEexp hEβ X hX
  have hcenter : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K)
  have hker : (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).ker =
      Subgroup.center ↥(adjointGroup .E6 K) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have hy : g * y * g⁻¹ = y := by
        rw [← MulAut.conj_apply, h, MulAut.one_apply]
      calc y * g = (g * y * g⁻¹) * g := by rw [hy]
        _ = g * y := by group
    · intro h
      refine MulEquiv.ext fun y => ?_
      rw [MulAut.conj_apply, ← h y, mul_assoc, mul_inv_cancel, mul_one, MulAut.one_apply]
  have hcj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hcenter]
  obtain ⟨s, hs⟩ := ggE0_e6_mem_inn_of_pow hp hR hβI hβp
  have hs1 : s ≠ 1 := by
    intro h
    exact hβ1 (by rw [← hs, h, map_one])
  have hsp : s ^ p = 1 := by
    apply hcj
    rw [map_pow, hs, hβp, map_one]
  let E' : Subgroup ↥(adjointGroup .E6 K) := E.comap MulAut.conj
  let X' : Subgroup ↥(adjointGroup .E6 K) := X.comap MulAut.conj
  have hEinn : E ≤ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range :=
    fun ε hε => ggE0_e6_mem_inn_of_pow hp hR (hEI hε) (hEexp ε hε)
  have hEeq : E'.map MulAut.conj = E := Subgroup.map_comap_eq_self hEinn
  have hXle : X ≤ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range :=
    hX.1.trans inf_le_left
  have hXeq : X'.map MulAut.conj = X := Subgroup.map_comap_eq_self hXle
  have hE'exp : ∀ ε ∈ E', ε ^ p = 1 := by
    intro ε hε
    apply hcj
    rw [map_pow, hEexp (MulAut.conj ε) hε, map_one]
  have hE'cent : E' ≤ Subgroup.centralizer {s} := by
    intro ε hε
    have h1 : MulAut.conj ε ∈ Subgroup.centralizer {β} := hEβ hε
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    apply hcj
    simpa only [map_mul, hs] using h1
  have hcent : (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range ⊓
      Subgroup.centralizer {β} = (Subgroup.centralizer {s}).map MulAut.conj := by
    rw [← hs]
    ext x
    constructor
    · rintro ⟨hxr, hxc⟩
      obtain ⟨w, hw⟩ := hxr
      rw [← hw] at hxc ⊢
      refine ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply hcj
      simpa only [map_mul] using Subgroup.mem_centralizer_singleton_iff.mp hxc
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hw]
  have hX'map : IsComponentOf (X'.map MulAut.conj)
      ((Subgroup.centralizer {s}).map MulAut.conj) := by
    rw [hXeq, ← hcent]
    exact hX
  have hX' : IsComponentOf X' (Subgroup.centralizer {s}) :=
    isComponentOf_of_map_map MulAut.conj hcj X' (Subgroup.centralizer {s}) hX'map
  have hN : E' ≤ Subgroup.normalizer (X' : Set ↥(adjointGroup .E6 K)) :=
    hE'cent.trans (ggE0_e6_normalizes hp hp2 hR hs1 hsp hX')
  have hfix : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj s) =
      Subgroup.centralizer ({s} : Set ↥(adjointGroup .E6 K)) :=
    fixedSubgroup_conj_eq_centralizer s
  have hXfix : IsComponentOf X'
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β) := by
    rw [← hs, hfix]
    exact hX'
  have hS2' : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥X' (fun lab _ _ _ _ _ => GGChevStTag lab) :=
    fun hm => hS2 K p β hp hp2 hβ1 hβp hβI X' hXfix hm
  have hI' : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E', CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers ε) X' :=
    fun hm ε hε => ggE0_e6_innDiagOn hp hp2 hR hs1 hsp (hE'exp ε hε) (hE'cent hε) hX' hm
  have hconcl' : GGE0Concl E' X' :=
    ggE0Concl_of_innDiagOn_family (G := ↥(adjointGroup .E6 K)) hp hp2 hE'exp hN hS2' hI'
  rw [← hEeq, ← hXeq]
  exact (ggE0Concl_map_iff MulAut.conj hcj E' X').mpr hconcl'

end CFSG.StandardType
