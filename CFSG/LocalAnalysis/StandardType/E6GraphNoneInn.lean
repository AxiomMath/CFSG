module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepTwo
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneProof
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)
open CFSG.Open (IsElemAbelian)

theorem graphNone_hyps_conj {H : Type*} [Group H] (φ : MulAut H) {p : ℕ} {α β : MulAut H}
    {E : Subgroup (MulAut H)} (hβ1 : β ≠ 1) (hβE : β ∈ E)
    (hEinn : E ≤ (MulAut.conj : H →* MulAut H).range) (hEab : IsElemAbelian p E)
    (hEcard : p ^ 4 ≤ Nat.card E) (hEα : E ≤ Subgroup.centralizer {α}) (hα2 : α * α = 1)
    (hfix : ∀ x, β x = x → α x = x) :
    MulAut.conj φ β ≠ 1 ∧ MulAut.conj φ β ∈ E.map (MulAut.conj φ).toMonoidHom ∧
      E.map (MulAut.conj φ).toMonoidHom ≤ (MulAut.conj : H →* MulAut H).range ∧
      IsElemAbelian p (E.map (MulAut.conj φ).toMonoidHom) ∧
      p ^ 4 ≤ Nat.card (E.map (MulAut.conj φ).toMonoidHom) ∧
      E.map (MulAut.conj φ).toMonoidHom ≤ Subgroup.centralizer {φ * α * φ⁻¹} ∧
      (φ * α * φ⁻¹) * (φ * α * φ⁻¹) = 1 ∧
      ∀ y, MulAut.conj φ β y = y → (φ * α * φ⁻¹) y = y := by
  refine ⟨(MulAut.conj φ).map_eq_one_iff.not.mpr hβ1, ⟨β, hβE, rfl⟩, ?_, hEab.map _, ?_, ?_,
    ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := hEinn he
    exact ⟨φ c, (mulAut_mul_conj_mul_inv φ c).symm⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj φ).injective]
    exact hEcard
  · rintro _ ⟨e, he, rfl⟩
    have hec : e * α = α * e := Subgroup.mem_centralizer_singleton_iff.mp (hEα he)
    change φ * e * φ⁻¹ ∈ Subgroup.centralizer {φ * α * φ⁻¹}
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (φ * e * φ⁻¹) * (φ * α * φ⁻¹) = φ * (e * α) * φ⁻¹ := by group
      _ = φ * (α * e) * φ⁻¹ := by rw [hec]
      _ = (φ * α * φ⁻¹) * (φ * e * φ⁻¹) := by group
  · calc (φ * α * φ⁻¹) * (φ * α * φ⁻¹) = φ * (α * α) * φ⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  · intro y hy
    have hβx : β (φ⁻¹ y) = φ⁻¹ y := by
      have := congrArg (fun z => φ⁻¹ z) hy
      simpa [MulAut.conj_apply, MulAut.mul_apply] using this
    calc (φ * α * φ⁻¹) y = φ (α (φ⁻¹ y)) := rfl
      _ = φ (φ⁻¹ y) := by rw [hfix _ hβx]
      _ = y := by simp

theorem le_centralizer_of_fix_le {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥)
    {ξ η : MulAut H} (hξη : ∀ x, ξ x = x → η x = x) {E : Subgroup (MulAut H)}
    (hEI : E ≤ (MulAut.conj : H →* MulAut H).range) (hEξ : E ≤ Subgroup.centralizer {ξ}) :
    E ≤ Subgroup.centralizer {η} := by
  intro e he
  obtain ⟨c, rfl⟩ := hEI he
  have hcξ := Subgroup.mem_centralizer_singleton_iff.mp (hEξ he)
  have hc : ξ c = c := mulAut_conj_injective_of_center_eq_bot hZ
    (by rw [← mulAut_mul_conj_mul_inv, ← hcξ, mul_inv_cancel_right])
  have h := mulAut_mul_conj_mul_inv η c
  rw [hξη c hc] at h
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc MulAut.conj c * η = (η * MulAut.conj c * η⁻¹) * η := by rw [h]
    _ = η * MulAut.conj c := by group


@[expose] def E6GraphNoneEtaInn : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 1 ≤ f → Nat.card K = 2 ^ f →
  ∀ (η : MulAut (adjointGroup TwistTag.E6.tag K)),
    (∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    ∀ (p : ℕ) (β : MulAut (adjointGroup TwistTag.E6.tag K))
      (E : Subgroup (MulAut (adjointGroup TwistTag.E6.tag K))),
      p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E →
      E ≤ (MulAut.conj : adjointGroup TwistTag.E6.tag K →*
        MulAut (adjointGroup TwistTag.E6.tag K)).range →
      IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      E ≤ Subgroup.centralizer ({η} : Set (MulAut (adjointGroup TwistTag.E6.tag K))) →
      η * η = 1 → ¬ ∀ x, β x = x → η x = x

@[expose] def E6GraphNoneXiInn : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 1 ≤ f → Nat.card K = 2 ^ f →
  ∀ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
    (η : MulAut (adjointGroup TwistTag.E6.tag K)),
    (∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    ∀ (p : ℕ) (β : MulAut (adjointGroup TwistTag.E6.tag K))
      (E : Subgroup (MulAut (adjointGroup TwistTag.E6.tag K))),
      p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E →
      E ≤ (MulAut.conj : adjointGroup TwistTag.E6.tag K →*
        MulAut (adjointGroup TwistTag.E6.tag K)).range →
      IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      E ≤ Subgroup.centralizer
        ({MulAut.conj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, ht⟩ :
          adjointGroup TwistTag.E6.tag K) * η} : Set (MulAut (adjointGroup TwistTag.E6.tag K))) →
      (MulAut.conj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, ht⟩ :
          adjointGroup TwistTag.E6.tag K) * η) *
        (MulAut.conj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, ht⟩ :
          adjointGroup TwistTag.E6.tag K) * η) = 1 →
      ¬ ∀ x, β x = x →
        (MulAut.conj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, ht⟩ :
          adjointGroup TwistTag.E6.tag K) * η) x = x

theorem e6GraphNone_of_eta_xi_inn (hη : E6GraphNoneEtaInn) (hξ : E6GraphNoneXiInn) :
    E6GraphNone := by
  intro f K _ _ hf hK g a p β E hp hp2 hβ1 hβE hEI hEab hEcard α hEα hα2
  change adjointGroup TwistTag.E6.tag K at g
  change (Fin TwistTag.E6.tag.rank → Kˣ) at a
  change MulAut (adjointGroup TwistTag.E6.tag K) at β
  change Subgroup (MulAut (adjointGroup TwistTag.E6.tag K)) at E
  change MulAut (adjointGroup TwistTag.E6.tag K) at α
  change ¬ ∀ x : adjointGroup TwistTag.E6.tag K, β x = x → α x = x
  intro hfix
  have hEinn : E ≤ (MulAut.conj : adjointGroup TwistTag.E6.tag K →*
      MulAut (adjointGroup TwistTag.E6.tag K)).range := fun x hx =>
    e6_mem_inn_of_mem_innDiag_of_commute g a (hEI hx)
      (Subgroup.mem_centralizer_singleton_iff.mp (hEα hx))
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (CFSG.LieType.Chevalley.E6GraphHighestRoot.two_eq_zero_of_card hf hK)
  obtain ⟨ht, η, hηP, hconj, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 K hK
  obtain ⟨φ, hφ⟩ | ⟨φ, hφ⟩ :=
    hconj α (isOrdinaryDiagGraph_conj_mul_exactNormalAut_graph g a) hα2
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      graphNone_hyps_conj φ hβ1 hβE hEinn hEab hEcard hEα hα2 hfix
    rw [hφ] at h6 h7 h8
    exact hη f K hf hK η hηP p _ _ hp hp2 h1 h2 h3 h4 h5 h6 h7 h8
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      graphNone_hyps_conj φ hβ1 hβE hEinn hEab hEcard hEα hα2 hfix
    rw [hφ] at h6 h7 h8
    exact hξ f K hf hK ht η hηP p _ _ hp hp2 h1 h2 h3 h4 h5 h6 h7 h8

theorem e6GraphNoneXiInn_of_etaInn (hη : E6GraphNoneEtaInn) : E6GraphNoneXiInn := by
  intro f K _ _ _ hf hK ht η hηP p β E hp hp2 hβ1 hβE hEI hEab hEcard hEξ _hξ2 hfix
  have hchar : ringChar K = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card hf hK
  have hZ := center_adjointGroup_eq_bot (τ := TwistTag.E6.tag) (K := K)
  set t : adjointGroup TwistTag.E6.tag K := ⟨_, ht⟩ with htdef
  have hξη : ∀ x : adjointGroup TwistTag.E6.tag K, (MulAut.conj t * η) x = x → η x = x := by
    intro x hx
    refine Subtype.ext ?_
    rw [hηP]
    refine E6SecondGraphFixed.diagramMap_conj_eq_of_conj hchar x.2 ?_
    have h := congrArg Subtype.val hx
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hηP] at h
    exact h
  have hEη := le_centralizer_of_fix_le hZ hξη hEI hEξ
  have hη2 : η * η = 1 := MulEquiv.ext fun x => Subtype.ext (by
    rw [MulAut.mul_apply, hηP, hηP, MulAut.one_apply]
    calc diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K * x *
          (diagramMap TwistTag.E6 K)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ =
        (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) * x *
          (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K)⁻¹ := by group
      _ = x := by rw [diagramMap_E6_mul_self]; group)
  exact hη f K hf hK η hηP p β E hp hp2 hβ1 hβE hEI hEab hEcard hEη hη2
    fun x hx => hξη x (hfix x hx)

theorem e6GraphNone_of_etaInn (hη : E6GraphNoneEtaInn) : E6GraphNone :=
  e6GraphNone_of_eta_xi_inn hη (e6GraphNoneXiInn_of_etaInn hη)

section Twisted


@[expose] def TwistedE6GraphNoneEtaInn : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ f) →
    ∀ η : MulAut (twistedE6RootGroup K σ),
      (∀ h : twistedE6RootGroup K σ, (η h : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    ∀ (p : ℕ) (β : MulAut (twistedE6RootGroup K σ))
      (E : Subgroup (MulAut (twistedE6RootGroup K σ))),
      p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E → E ≤ twistedE6Inn K σ →
      IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      E ≤ Subgroup.centralizer ({η} : Set (MulAut (twistedE6RootGroup K σ))) →
      ¬ ∀ x, β x = x → η x = x

@[expose] def TwistedE6GraphNoneXiInn : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ f) →
    ∀ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ twistedE6RootGroup K σ)
      (η : MulAut (twistedE6RootGroup K σ)),
      (∀ h : twistedE6RootGroup K σ, (η h : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    ∀ (p : ℕ) (β : MulAut (twistedE6RootGroup K σ))
      (E : Subgroup (MulAut (twistedE6RootGroup K σ))),
      p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E → E ≤ twistedE6Inn K σ →
      IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      E ≤ Subgroup.centralizer
        ({MulAut.conj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, ht⟩ :
          twistedE6RootGroup K σ) * η} : Set (MulAut (twistedE6RootGroup K σ))) →
      ¬ ∀ x, β x = x → (MulAut.conj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, ht⟩ :
          twistedE6RootGroup K σ) * η) x = x

theorem twistedE6GraphNone_of_eta_xi_inn (hη : TwistedE6GraphNoneEtaInn)
    (hξ : TwistedE6GraphNoneXiInn) : TwistedE6GraphNone := by
  intro f K _ _ hf hK σ hσ p α β E hp hp2 hβ1 hβE hEI hEab hEcard hEα hα2 hαI hfix
  have hEinn : E ≤ twistedE6Inn K σ := fun x hx =>
    twistedE6_mem_inn_of_mem_innDiag_of_commute hf hK hσ hα2 hαI (hEI hx)
      (Subgroup.mem_centralizer_singleton_iff.mp (hEα hx))
  obtain ⟨ht, η, hηP, -, -, hconj, -, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ
  have hαinn : ∀ c, α ≠ MulAut.conj c := fun c h =>
    hαI (Subgroup.mem_sup_left ⟨c, h.symm⟩)
  obtain ⟨φ, hφ⟩ | ⟨φ, hφ⟩ := hconj α (by rw [pow_two]; exact hα2) hαinn
  · obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ :=
      graphNone_hyps_conj φ hβ1 hβE hEinn hEab hEcard hEα hα2 hfix
    rw [hφ] at h6 h8
    exact hη f K hf hK σ hσ η hηP p _ _ hp hp2 h1 h2 h3 h4 h5 h6 h8
  · obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ :=
      graphNone_hyps_conj φ hβ1 hβE hEinn hEab hEcard hEα hα2 hfix
    rw [hφ] at h6 h8
    exact hξ f K hf hK σ hσ ht η hηP p _ _ hp hp2 h1 h2 h3 h4 h5 h6 h8

theorem twistedE6GraphNoneXiInn_of_etaInn (hη : TwistedE6GraphNoneEtaInn) :
    TwistedE6GraphNoneXiInn := by
  intro f K _ _ hf hK σ hσ ht η hηP p β E hp hp2 hβ1 hβE hEI hEab hEcard hEξ hfix
  have hchar : ringChar K = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card (n := 2 * f)
    (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  set t : twistedE6RootGroup K σ := ⟨_, ht⟩ with htdef
  have hξη : ∀ x : twistedE6RootGroup K σ, (MulAut.conj t * η) x = x → η x = x := by
    intro x hx
    refine Subtype.ext ?_
    rw [hηP]
    refine E6SecondGraphFixed.diagramMap_conj_eq_of_conj hchar
      (graphFixedRootGroup_le _ _ _ x.2).1 ?_
    have h := congrArg Subtype.val hx
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hηP] at h
    exact h
  exact hη f K hf hK σ hσ η hηP p β E hp hp2 hβ1 hβE hEI hEab hEcard
    (le_centralizer_of_fix_le hZ hξη hEI hEξ) fun x hx => hξη x (hfix x hx)

theorem twistedE6GraphNone_of_etaInn (hη : TwistedE6GraphNoneEtaInn) : TwistedE6GraphNone :=
  twistedE6GraphNone_of_eta_xi_inn hη (twistedE6GraphNoneXiInn_of_etaInn hη)

end Twisted

end CFSG.StandardType
