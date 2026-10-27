module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrame
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiRee
public import CFSG.LocalAnalysis.StandardType.GGE0MarkBridge
public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjNormal
public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjAct
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

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

private theorem map_le_normalizer_iff {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) (E X : Subgroup H) :
    E.map f ≤ Subgroup.normalizer (X.map f : Set G) ↔
      E ≤ Subgroup.normalizer (X : Set H) := by
  constructor
  · intro h
    calc E ≤ ((E.map f).comap f) := by
          intro x hx
          exact Subgroup.mem_map_of_mem f hx
      _ ≤ (Subgroup.normalizer ((X.map f : Subgroup G) : Set G)).comap f :=
          Subgroup.comap_mono h
      _ ≤ Subgroup.normalizer (((X.map f : Subgroup G).comap f) : Set H) :=
          Subgroup.le_normalizer_comap f
      _ = Subgroup.normalizer (X : Set H) := by
          rw [Subgroup.comap_map_eq_self_of_injective hf X]
  · intro h
    calc E.map f ≤ (Subgroup.normalizer (X : Set H)).map f := Subgroup.map_mono h
      _ ≤ Subgroup.normalizer ((X.map f : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map f

private theorem largeEvenInduces_map_iff {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) (X : Subgroup H) {R : Type} [Group R] (ε : H)
    (θ : ↥(X.map f) ⧸ Subgroup.center ↥(X.map f) ≃* R) (φ : MulAut R) :
    LargeEvenInduces ((centerQuotCongr (Subgroup.equivMapOfInjective X f hf)).trans θ)
        (fun x x' : ↥X => (x' : H) = ε⁻¹ * x * ε) φ ↔
      LargeEvenInduces θ (fun y y' : ↥(X.map f) => (y' : G) = (f ε)⁻¹ * y * f ε) φ := by
  refine largeEvenInduces_congr_equiv (Subgroup.equivMapOfInjective X f hf) θ
    (fun x x' : ↥X => (x' : H) = ε⁻¹ * x * ε)
    (fun y y' : ↥(X.map f) => (y' : G) = (f ε)⁻¹ * y * f ε) ?_ φ
  intro x x'
  rw [Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_equivMapOfInjective_apply]
  constructor
  · intro h
    rw [h, map_mul, map_mul, map_inv]
  · intro h
    apply hf
    rw [map_mul, map_mul, map_inv]
    exact h

private theorem ggE0Concl_map_iff_tmp {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) (E X : Subgroup H) :
    GGE0Concl (E.map f) (X.map f) ↔ GGE0Concl E X := by
  constructor
  · intro h
    refine ⟨(map_le_normalizer_iff f hf E X).1 h.1, fun hm => ?_⟩
    have hmY : LargeEvenMarking ↥(X.map f)
        (fun lab _ _ I _ θ => GGChevStTag lab ∧ ∀ g ∈ E.map f, ∃ φ ∈ I,
          LargeEvenInduces θ (fun y y' : ↥(X.map f) => (y' : G) = g⁻¹ * y * g) φ) := by
      have hmY0 : LargeEvenMarking ↥(X.map f) (fun _ _ _ _ _ _ => True) :=
        largeEvenMarking_congr (Subgroup.equivMapOfInjective X f hf).symm
          (fun _ _ _ _ _ _ _ => trivial) hm
      exact h.2 hmY0
    refine largeEvenMarking_congr (Subgroup.equivMapOfInjective X f hf) ?_ hmY
    intro lab R _ I F θ hθ
    obtain ⟨hlab, hind⟩ := hθ
    refine ⟨hlab, ?_⟩
    intro ε hε
    obtain ⟨φ, hφ, hindφ⟩ := hind (f ε) (Subgroup.mem_map_of_mem f hε)
    exact ⟨φ, hφ, (largeEvenInduces_map_iff f hf X ε θ φ).2 hindφ⟩
  · intro h
    refine ⟨(map_le_normalizer_iff f hf E X).2 h.1, fun hm => ?_⟩
    have hmX : LargeEvenMarking ↥X
        (fun lab _ _ I _ θ => GGChevStTag lab ∧ ∀ ε ∈ E, ∃ φ ∈ I,
          LargeEvenInduces θ (fun x x' : ↥X => (x' : H) = ε⁻¹ * x * ε) φ) := by
      have hmX0 : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) :=
        largeEvenMarking_congr (Subgroup.equivMapOfInjective X f hf)
          (fun _ _ _ _ _ _ _ => trivial) hm
      exact h.2 hmX0
    refine largeEvenMarking_congr (Subgroup.equivMapOfInjective X f hf).symm ?_ hmX
    intro lab R _ I F θ hθ
    obtain ⟨hlab, hind⟩ := hθ
    rw [centerQuotCongr_symm]
    refine ⟨hlab, ?_⟩
    rintro g ⟨ε, hε, rfl⟩
    obtain ⟨φ, hφ, hindφ⟩ := hind ε hε
    refine ⟨φ, hφ, ?_⟩
    refine (largeEvenInduces_map_iff f hf X ε
      ((centerQuotCongr (Subgroup.equivMapOfInjective X f hf)).symm.trans θ) φ).1 ?_
    rw [centerQuotCongr_trans_symm_trans]
    exact hindφ

theorem ggE0Model_adjointGroup
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (hS2 : ExcNoSuzukiReeAdj τ) (K : Type) [Field K] [Finite K] [CharP K 2]
 :
    GGE0Model ↥(adjointGroup τ K)
      (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range := by
  intro p β E hp hp2 hβ1 hβp hβI hEI hEexp hEβ X hX
  have hcenter : Subgroup.center ↥(adjointGroup τ K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K)
  have hker : (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).ker =
      Subgroup.center ↥(adjointGroup τ K) := by
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
      (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hcenter]
  obtain ⟨s, hs⟩ := hβI
  have hs1 : s ≠ 1 := by
    intro h
    exact hβ1 (by rw [← hs, h, map_one])
  have hsp : s ^ p = 1 := by
    apply hcj
    rw [map_pow, hs, hβp, map_one]
  let E' : Subgroup ↥(adjointGroup τ K) := E.comap MulAut.conj
  let X' : Subgroup ↥(adjointGroup τ K) := X.comap MulAut.conj
  have hEeq : E'.map MulAut.conj = E := Subgroup.map_comap_eq_self hEI
  have hXle : X ≤ (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range :=
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
  have hcent : (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range ⊓
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
  have hN : E' ≤ Subgroup.normalizer (X' : Set ↥(adjointGroup τ K)) :=
    hE'cent.trans (ggE0_adjoint_normalizes hτ hp hp2 hs1 hsp hX')
  have hS2' : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥X' (fun lab _ _ _ _ _ => GGChevStTag lab) :=
    fun hm => hS2 K p hp hp2 s hsp X' hX' hm
  have hI' : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E', CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers ε) X' :=
    fun hm ε hε => ggE0_adjoint_innDiagOn hτ hp hp2 hs1 hsp (hE'exp ε hε) (hE'cent hε) hX' hm
  have hconcl' : GGE0Concl E' X' :=
    ggE0Concl_of_innDiagOn_family (G := ↥(adjointGroup τ K)) hp hp2 hE'exp hN hS2' hI'
  rw [← hEeq, ← hXeq]
  exact (ggE0Concl_map_iff_tmp MulAut.conj hcj E' X').mpr hconcl'

end CFSG.StandardType
