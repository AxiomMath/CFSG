module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.IndexTwo
public import CFSG.Monster.B.GSide.RecognitionExists
public import CFSG.Monster.GMS.ASegTwoA

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.GSide CFSG.Monster.B.TwoA.Amalgam

private theorem commutator_le_of_index_eq_two {G : Type*} [Group G] {H : Subgroup G}
    (h : H.index = 2) : commutator G ≤ H := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  simp only [Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff]
  tauto

theorem exists_conj_eq_of_mulAut {E : Type*} [Group E] [Finite E] {N : Subgroup E}
    (hN2 : N.index = 2) (hCN : Subgroup.centralizer (N : Set E) ≤ N)
    (hout : (MulAut.conj : N →* MulAut N).range.index ≤ 2) (σ : MulAut N) :
    ∃ x : E, ∀ n : N, ((σ n : N) : E) = x * n * x⁻¹ := by
  have hNn : N.Normal := Subgroup.normal_of_index_eq_two hN2
  obtain ⟨b, hbN⟩ : ∃ b : E, b ∉ N := by
    by_contra! h
    rw [(Subgroup.eq_top_iff' N).2 h, Subgroup.index_top] at hN2
    exact absurd hN2 (by norm_num)
  have hσb : (MulAut.conjNormal b : MulAut N) ∉ (MulAut.conj : N →* MulAut N).range :=
    fun h => hbN (CFSG.EvenSmallLie.TwoE6.mem_of_conjNormal_mem_range hCN h)
  have hInn2 : (MulAut.conj : N →* MulAut N).range.index = 2 := by
    have h0 : (MulAut.conj : N →* MulAut N).range.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have h1 : (MulAut.conj : N →* MulAut N).range.index ≠ 1 :=
      fun h => hσb ((Subgroup.index_eq_one.1 h) ▸ Subgroup.mem_top _)
    omega
  by_cases hσ : σ ∈ (MulAut.conj : N →* MulAut N).range
  · obtain ⟨n, rfl⟩ := hσ
    exact ⟨n, fun m => by rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]⟩
  · obtain ⟨n, hn⟩ : σ * (MulAut.conjNormal b)⁻¹ ∈ (MulAut.conj : N →* MulAut N).range := by
      rw [Subgroup.mul_mem_iff_of_index_two hInn2, inv_mem_iff]
      exact iff_of_false hσ hσb
    refine ⟨n * b, fun m => ?_⟩
    have h1 : σ = MulAut.conj n * MulAut.conjNormal b := by
      rw [show MulAut.conj n = σ * (MulAut.conjNormal b)⁻¹ from hn, inv_mul_cancel_right]
    rw [h1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, MulAut.conjNormal_apply]
    group

theorem perfect_and_exists_conj_of_index_two {E : Type*} [Group E] [Finite E]
    (hidx : (commutator E).index = 2) (hperf : Group.IsPerfect (commutator E))
    (hCE : Subgroup.centralizer ((commutator E : Subgroup E) : Set E) ≤ commutator E)
    (hout : (MulAut.conj : ↥(commutator E) →* MulAut ↥(commutator E)).range.index ≤ 2)
    {Y : Type*} [Group Y] {C D : Subgroup Y} (hDC : D ≤ C) (Ψ : C ≃* E)
    (hcard : 2 * Nat.card D = Nat.card C) :
    ⁅D, D⁆ = D ∧ ∀ θ : D ≃* D, ∃ g ∈ C, ∀ d : D, (θ d : Y) = g * d * g⁻¹ := by
  let f : E →* Y := C.subtype.comp Ψ.symm.toMonoidHom
  have hf : Function.Injective f := C.subtype_injective.comp Ψ.symm.injective
  have hfC : ∀ c ∈ C, c ∈ f.range := fun c hc => ⟨Ψ ⟨c, hc⟩, by simp [f]⟩
  have hfmem : ∀ x : E, f x ∈ C := fun x => (Ψ.symm x).2
  set D' : Subgroup E := D.comap f with hD'
  have hDD' : D'.map f = D := Subgroup.map_comap_eq_self fun d hd => hfC d (hDC hd)
  have hcardD' : Nat.card D' = Nat.card D := by
    have h := Nat.card_congr (Subgroup.equivMapOfInjective D' f hf).toEquiv
    rwa [hDD'] at h
  have hD'idx : D'.index = 2 := by
    have h1 := D'.card_mul_index
    have h2 : Nat.card C = Nat.card E := Nat.card_congr Ψ.toEquiv
    have hpos : 0 < Nat.card D := hcardD' ▸ Nat.card_pos
    rw [hcardD', ← h2, ← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm 2 _))
  have hD'eq : D' = commutator E := by
    have hle : commutator E ≤ D' := commutator_le_of_index_eq_two hD'idx
    have h := Subgroup.relIndex_mul_index hle
    rw [hD'idx, hidx] at h
    have h1 : (commutator E).relIndex D' = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle
  have hDeq : D = (commutator E).map f := by rw [← hDD', hD'eq]
  have := hperf
  refine ⟨by rw [hDeq, ← Subgroup.map_commutator, Subgroup.commutator_eq_self], fun θ => ?_⟩
  let e : ↥(commutator E) ≃* ↥D :=
    (Subgroup.equivMapOfInjective (commutator E) f hf).trans (MulEquiv.subgroupCongr hDeq.symm)
  have he : ∀ n : ↥(commutator E), ((e n : D) : Y) = f n := fun n => rfl
  obtain ⟨x, hx⟩ := exists_conj_eq_of_mulAut hidx hCE hout (e.trans (θ.trans e.symm))
  refine ⟨f x, hfmem x, fun d => ?_⟩
  obtain ⟨n, rfl⟩ := e.surjective d
  have h2 : (((e.symm (θ (e n))) : ↥(commutator E)) : E) = x * n * x⁻¹ := hx n
  calc ((θ (e n) : D) : Y) = ((e (e.symm (θ (e n))) : D) : Y) := by rw [e.apply_symm_apply]
    _ = f ((e.symm (θ (e n)) : ↥(commutator E)) : E) := he _
    _ = f (x * n * x⁻¹) := by rw [h2]
    _ = f x * ((e n : D) : Y) * (f x)⁻¹ := by rw [map_mul, map_mul, map_inv, he]

theorem nonempty_centralizer_mulEquiv_Eam
    (hT3 : BabyTableIII) {r : B} (hr : BabyInv 0 r) :
    Nonempty (Subgroup.centralizer ({r} : Set B) ≃* ↥Eam) := by
  have hlab : BabyInv 0 labelB :=
    ⟨orderOf_labelB, natCard_centralizer_labelB.trans
      (by norm_num [CFSG.Open.sporadicOrderTwistedE6Two, babyCentOrder])⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 (hT3.2 0 labelB r hlab hr)
  exact ⟨(centralizerConjEquiv g hg).trans
    ((centralizerVStabEquiv orderOf_labelB rank_labelB).trans vStabEam)⟩

theorem babyTwoAAutInner_of
   
    (hout : (MulAut.conj : ↥(commutator ↥Eam) →* MulAut ↥(commutator ↥Eam)).range.index ≤ 2)
    (hT3 : BabyTableIII) : BabyTwoAAutInner := by
  obtain ⟨hidx, hperf, -⟩ := short_F4_derived_standard_perfect_cover
  have hCE : Subgroup.centralizer ((commutator ↥Eam : Subgroup ↥Eam) : Set ↥Eam) ≤
      commutator ↥Eam := by
    rw [CFSG.EvenSmallLie.TwoE6.centralizer_commutator_Eam]
    exact Subgroup.zpowers_le.2 cE'_mem_commutator
  intro r hr D hDC hcard _
  obtain ⟨Ψ⟩ := nonempty_centralizer_mulEquiv_Eam hT3 hr
  obtain ⟨hDD, hinn⟩ := perfect_and_exists_conj_of_index_two hidx hperf hCE hout hDC Ψ hcard
  exact ⟨hDD, fun θ _ => hinn θ⟩

end CFSG.Monster.GMS
