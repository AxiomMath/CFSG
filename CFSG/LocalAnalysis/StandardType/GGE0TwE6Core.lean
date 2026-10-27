module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGE0TwE6InnNormal
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGE0TwE6Act
public import CFSG.LocalAnalysis.StandardType.GGE0MarkBridge
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem fixedSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set R) := by
  change CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
    Subgroup.centralizer ({x} : Set R)
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

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

theorem ggE0Model_twistedE6
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    GGE0ModelOn (fun p => ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1)) ↥(twistedE6RootGroup K σ)
      (twistedE6Inn K σ ⊔ twistedE6Diag K σ) := by
  have hS2 : ExcNoSuzukiReeTwE6 := excNoSuzukiReeTwE6_holds
  intro p β E hp hp2 hR hβ1 hβp hβI hEI hEexp hEβ X hX
  let C := ↥(twistedE6RootGroup K σ)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form
      (p := 2) Nat.prime_two hf K hK σ hσ
  have hcenter : Subgroup.center C = ⊥ := hZ
  have hker : (MulAut.conj : C →* MulAut C).ker = Subgroup.center C := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have hy : g * y * g⁻¹ = y := by
        rw [← MulAut.conj_apply, h, MulAut.one_apply]
      calc y * g = (g * y * g⁻¹) * g := by rw [hy]
        _ = g * y := by rw [mul_assoc (g * y) g⁻¹ g, inv_mul_cancel, mul_one]
    · intro h
      refine MulEquiv.ext fun y => ?_
      rw [MulAut.conj_apply, ← h y, mul_assoc, mul_inv_cancel, mul_one, MulAut.one_apply]
  have hcj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hcenter]
  have hβinn : β ∈ (MulAut.conj : C →* MulAut C).range :=
    ggE0_twE6_mem_inn_of_pow hf hK hσ hp hR hβI hβp
  obtain ⟨s, hs⟩ := hβinn
  have hs1 : s ≠ 1 := by
    intro h
    exact hβ1 (by rw [← hs, h, map_one])
  have hsp : s ^ p = 1 := by
    apply hcj
    rw [map_pow, hs, hβp, map_one]
  let E' : Subgroup C := E.comap (MulAut.conj : C →* MulAut C)
  let X' : Subgroup C := X.comap (MulAut.conj : C →* MulAut C)
  have hEinn : E ≤ (MulAut.conj : C →* MulAut C).range := fun ε hε =>
    ggE0_twE6_mem_inn_of_pow hf hK hσ hp hR (hEI hε) (hEexp ε hε)
  have hEeq : E'.map (MulAut.conj : C →* MulAut C) = E :=
    Subgroup.map_comap_eq_self hEinn
  have hXle : X ≤ (MulAut.conj : C →* MulAut C).range := hX.1.trans inf_le_left
  have hXeq : X'.map (MulAut.conj : C →* MulAut C) = X :=
    Subgroup.map_comap_eq_self hXle
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
  have hfix : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β =
      Subgroup.centralizer ({s} : Set C) := by
    rw [← hs]
    exact fixedSubgroup_conj_eq_centralizer s
  have hcent : (MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β} =
      (Subgroup.centralizer {s}).map (MulAut.conj : C →* MulAut C) := by
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
  have hX'map : IsComponentOf (X'.map (MulAut.conj : C →* MulAut C))
      ((Subgroup.centralizer {s}).map (MulAut.conj : C →* MulAut C)) := by
    rw [hXeq, ← hcent]
    exact hX
  have hX' : IsComponentOf X' (Subgroup.centralizer {s}) :=
    isComponentOf_of_map_map (MulAut.conj : C →* MulAut C) hcj X'
      (Subgroup.centralizer {s}) hX'map
  have hX'fix : IsComponentOf X'
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β) := by
    rw [hfix]
    exact hX'
  have hN : E' ≤ Subgroup.normalizer (X' : Set C) :=
    hE'cent.trans (ggE0_twE6_normalizes hf hK hσ hp hp2 hR hs1 hsp hX')
  have hS2' : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥X' (fun lab _ _ _ _ _ => GGChevStTag lab) :=
    fun hm => hS2 f K hf hK σ hσ p β hp hp2 hβ1 hβp hβI X' hX'fix hm
  have hI' : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E', CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers ε) X' :=
    fun hm ε hε =>
      ggE0_twE6_innDiagOn hf hK hσ hp hp2 hR hs1 hsp (hE'exp ε hε) (hE'cent hε) hX' hm
  have hconcl' : GGE0Concl E' X' :=
    ggE0Concl_of_innDiagOn_family (G := C) hp hp2 hE'exp hN hS2' hI'
  rw [← hEeq, ← hXeq]
  exact (ggE0Concl_map_iff (MulAut.conj : C →* MulAut C) hcj E' X').mpr hconcl'

end CFSG.StandardType
