module

public import CFSG.Milestones.ASVolI.F48.Small.Pres
public import CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF48s_Match {X : Type} [Group X] (A B : Subgroup X) (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (β : (RankTwoAmalgam.ofSubgroups A B).Completion Y),
    β.IsFaithful → β.IsSmall m →
    ∃ φ : Y ≃* ↥(A ⊔ B), (∀ a : ↥A, ((φ (β.φ1 a) : ↥(A ⊔ B)) : X) ∈ A) ∧
      ∀ b : ↥B, ((φ (β.φ2 b) : ↥(A ⊔ B)) : X) ∈ B

theorem burnsideF48s_match_of_equiv {X : Type} [Group X] {A B : Subgroup X} {m : ℕ}
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (β : (RankTwoAmalgam.ofSubgroups A B).Completion Y),
      β.IsFaithful → β.IsSmall m →
      ∃ θ : β.G0 ≃* (incl A B).G0, (∀ p, θ (f1 (c := β) p) = f1 (c := incl A B) p) ∧
        ∀ q, θ (f2 (c := β) q) = f2 (c := incl A B) q) :
    burnsideF48s_Match A B m := by
  intro Y _ _ β hβ hs
  obtain ⟨θ, h1, h2⟩ := h Y β hβ hs
  let φ : Y ≃* ↥(A ⊔ B) :=
    (burnsideF48_G0Equiv β).symm.trans (θ.trans (burnsideF48_G0Equiv (incl A B)))
  have hφ1 : ∀ a : ↥A, φ (β.φ1 a) = (incl A B).φ1 a := by
    intro a
    have e : (burnsideF48_G0Equiv β).symm (β.φ1 a) = f1 (c := β) a := by
      rw [MulEquiv.symm_apply_eq]; rfl
    show burnsideF48_G0Equiv (incl A B) (θ ((burnsideF48_G0Equiv β).symm (β.φ1 a))) = _
    rw [e]
    exact (congrArg (burnsideF48_G0Equiv (incl A B)) (h1 a)).trans rfl
  have hφ2 : ∀ b : ↥B, φ (β.φ2 b) = (incl A B).φ2 b := by
    intro b
    have e : (burnsideF48_G0Equiv β).symm (β.φ2 b) = f2 (c := β) b := by
      rw [MulEquiv.symm_apply_eq]; rfl
    show burnsideF48_G0Equiv (incl A B) (θ ((burnsideF48_G0Equiv β).symm (β.φ2 b))) = _
    rw [e]
    exact (congrArg (burnsideF48_G0Equiv (incl A B)) (h2 b)).trans rfl
  refine ⟨φ, fun a => ?_, fun b => ?_⟩
  · rw [hφ1]; exact a.2
  · rw [hφ2]; exact b.2

theorem burnsideF48s_match_of_qe {X : Type} [Group X] {A B : Subgroup X} {m : ℕ}
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (β : (RankTwoAmalgam.ofSubgroups A B).Completion Y),
      β.IsFaithful → β.IsSmall m →
      Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl A B).toCompletion) :
    burnsideF48s_Match A B m := by
  intro Y _ _ β hβ hs
  obtain ⟨φ, ψ, hφ⟩ := h Y β hβ hs
  refine ⟨φ, fun a => ?_, fun b => ?_⟩
  · have e : φ (β.φ1 a) = (incl A B).φ1 (ψ.toEquiv RankTwoIndex.one a) := hφ RankTwoIndex.one a
    rw [e]
    exact (ψ.toEquiv RankTwoIndex.one a).2
  · have e : φ (β.φ2 b) = (incl A B).φ2 (ψ.toEquiv RankTwoIndex.two b) := hφ RankTwoIndex.two b
    rw [e]
    exact (ψ.toEquiv RankTwoIndex.two b).2

@[expose] def burnsideF48s_swapC {X : Type} [Group X] {A B : Subgroup X} {Y : Type} [Group Y]
    (β : (RankTwoAmalgam.ofSubgroups A B).Completion Y) :
    (RankTwoAmalgam.ofSubgroups B A).Completion Y where
  φ1 := β.φ2
  φ12 := β.φ12.comp (MulEquiv.subgroupCongr (inf_comm B A)).toMonoidHom
  φ2 := β.φ1
  comm1 g := by
    have := β.comm2 ((MulEquiv.subgroupCongr (inf_comm B A)) g)
    exact this
  comm2 g := by
    have := β.comm1 ((MulEquiv.subgroupCongr (inf_comm B A)) g)
    exact this
  inter := by
    ext y
    have h := Subgroup.ext_iff.1 β.inter y
    constructor
    · rintro ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      obtain ⟨d, hd⟩ := h.1 ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(MulEquiv.subgroupCongr (inf_comm B A)).symm d,
        (congrArg β.φ12 (MulEquiv.apply_symm_apply (MulEquiv.subgroupCongr (inf_comm B A)) d)).trans
          hd⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h.2 ⟨_, rfl⟩
      exact ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  gen := by
    rw [sup_comm]
    exact β.gen

theorem burnsideF48s_swapC_isFaithful {X : Type} [Group X] {A B : Subgroup X} {Y : Type} [Group Y]
    {β : (RankTwoAmalgam.ofSubgroups A B).Completion Y} (hβ : β.IsFaithful) :
    (burnsideF48s_swapC β).IsFaithful :=
  ⟨hβ.2.2, hβ.2.1.comp (MulEquiv.subgroupCongr (inf_comm B A)).injective, hβ.1⟩

theorem burnsideF48s_graph_congr {G : Type*} [Group G] {G₀ G₀' : Subgroup G} (G₁ G₂ : Subgroup G)
    (h : G₀ = G₀') : Nonempty (CosetGeom.graph G₀ G₁ G₂ ≃g CosetGeom.graph G₀' G₁ G₂) := by
  subst h
  exact ⟨SimpleGraph.Iso.refl⟩

theorem burnsideF48s_geodUnique_of_iso {V W : Type*} {Γ : SimpleGraph V} {Δ : SimpleGraph W}
    (φ : Γ ≃g Δ) (m : ℕ)
    (h : ∀ p q : GPath Δ m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 → p m = q m → p = q) :
    ∀ p q : GPath Γ m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 → p m = q m → p = q := by
  intro p q hp hq h0 hm
  have hmap : ∀ a b : V, Γ.Adj a b → Δ.Adj (φ a) (φ b) := fun a b hab => φ.map_adj_iff.mpr hab
  have hgeo : ∀ r : GPath Γ m, r.IsGeodesic → (r.map φ hmap).IsGeodesic := by
    intro r hr
    show Δ.dist (r.map φ hmap 0) (r.map φ hmap m) = m
    simp only [GPath.map_apply]
    rw [H13.F431.F45.iso_dist]
    exact hr
  have h' := h (p.map φ hmap) (q.map φ hmap) (hgeo p hp) (hgeo q hq) (by simp [h0]) (by simp [hm])
  refine GPath.ext' fun i hi => ?_
  have := congrArg (fun r : GPath Δ m => r i) h'
  simp only [GPath.map_apply] at this
  exact φ.injective this

theorem burnsideF48s_swapC_isSmall {X : Type} [Group X] {A B : Subgroup X} {Y : Type} [Group Y]
    {β : (RankTwoAmalgam.ofSubgroups A B).Completion Y} {m : ℕ} (hs : β.IsSmall m) :
    (burnsideF48s_swapC β).IsSmall m := by
  intro hL
  apply hs
  obtain ⟨σ⟩ := burnsideF4gF4Two_cosetGeom_swap (β.φ1.range ⊔ β.φ2.range) β.φ1.range β.φ2.range
  obtain ⟨τ⟩ := burnsideF48s_graph_congr β.φ2.range β.φ1.range
    (sup_comm β.φ1.range β.φ2.range)
  exact burnsideF48s_geodUnique_of_iso (σ.trans τ) m hL

theorem burnsideF48s_match_swap {X : Type} [Group X] {A B : Subgroup X} {m : ℕ}
    (h : burnsideF48s_Match A B m) : burnsideF48s_Match B A m := by
  intro Y _ _ β hβ hs
  obtain ⟨φ, h1, h2⟩ := h Y (burnsideF48s_swapC β) (burnsideF48s_swapC_isFaithful hβ)
    (burnsideF48s_swapC_isSmall hs)
  refine ⟨φ.trans (MulEquiv.subgroupCongr (sup_comm A B)), fun b => ?_, fun a => ?_⟩
  · exact h2 b
  · exact h1 a

@[expose] noncomputable def burnsideF48s_restrictMatch {E X : Type} [Group E] [Group X]
    {G₀ : Subgroup E} {H₀ : Subgroup X} (θ : ↥G₀ ≃* ↥H₀) {M : Subgroup E} {Q : Subgroup X}
    (hM : M ≤ G₀) (hQ : Q ≤ H₀) (h : ∀ x : ↥G₀, (x : E) ∈ M ↔ ((θ x : ↥H₀) : X) ∈ Q) :
    ↥M ≃* ↥Q where
  toFun m := ⟨θ ⟨m, hM m.2⟩, (h _).1 m.2⟩
  invFun q := ⟨θ.symm ⟨q, hQ q.2⟩, (h _).2 (by simpa using q.2)⟩
  left_inv m := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    have e : (⟨((a * b : ↥M) : E), hM (a * b).2⟩ : ↥G₀) = ⟨a, hM a.2⟩ * ⟨b, hM b.2⟩ := rfl
    show ((θ ⟨((a * b : ↥M) : E), hM (a * b).2⟩ : ↥H₀) : X) =
      ((θ ⟨a, hM a.2⟩ : ↥H₀) : X) * θ ⟨b, hM b.2⟩
    rw [e, map_mul, Subgroup.coe_mul])

@[expose] noncomputable def burnsideF48s_amalIsoOf {E X : Type} [Group E] [Group X]
    {M₁ M₂ : Subgroup E} {A B : Subgroup X} (θ : ↥(M₁ ⊔ M₂) ≃* ↥(A ⊔ B))
    (h1 : ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A)
    (h2 : ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups A B) where
  φ1 := burnsideF48s_restrictMatch θ le_sup_left le_sup_left h1
  φ12 := burnsideF48s_restrictMatch θ (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_left)
    (fun x => by
      simp only [Subgroup.mem_inf]
      rw [h1, h2])
  φ2 := burnsideF48s_restrictMatch θ le_sup_right le_sup_right h2
  comm1 _ := Subtype.ext rfl
  comm2 _ := Subtype.ext rfl

theorem burnsideF48s_qe_of_match {E X : Type} [Group E] [Finite E] [Group X] {M₁ M₂ : Subgroup E}
    {A B : Subgroup X} {m : ℕ} (hM : burnsideF48s_Match A B m) (θ : ↥(M₁ ⊔ M₂) ≃* ↥(A ⊔ B))
    (h1 : ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A)
    (h2 : ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B)
    {Y : Type} [Group Y] [Finite Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall m) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  let ψ := burnsideF48s_amalIsoOf θ h1 h2
  let β' := burnsideF48_comap (burnsideF48_isoSymm ψ) β
  obtain ⟨φ', hφ1, hφ2⟩ := hM Y β' ((burnsideF48_comap_isFaithful_iff _ β).2 hβ)
    ((burnsideF48_comap_isSmall_iff _ β m).2 hs)
  have hb1 : ∀ x : ↥M₁, β.φ1 x = β'.φ1 (ψ.φ1 x) := fun x =>
    (congrArg β.φ1 (ψ.φ1.symm_apply_apply x)).symm
  have hb2 : ∀ x : ↥M₂, β.φ2 x = β'.φ2 (ψ.φ2 x) := fun x =>
    (congrArg β.φ2 (ψ.φ2.symm_apply_apply x)).symm
  have hθ1 : ∀ y : ↥(A ⊔ B), (y : X) ∈ A → ((θ.symm y : ↥(M₁ ⊔ M₂)) : E) ∈ M₁ := by
    intro y hy
    exact (h1 _).2 (by simpa using hy)
  have hθ2 : ∀ y : ↥(A ⊔ B), (y : X) ∈ B → ((θ.symm y : ↥(M₁ ⊔ M₂)) : E) ∈ M₂ := by
    intro y hy
    exact (h2 _).2 (by simpa using hy)
  refine burnsideF48s_qe_of_equiv β hβ (φ'.trans θ.symm) (fun x => ?_) (fun x => ?_)
  · show ((θ.symm (φ' (β.φ1 x)) : ↥(M₁ ⊔ M₂)) : E) ∈ M₁
    exact (congrArg (fun z => ((θ.symm (φ' z) : ↥(M₁ ⊔ M₂)) : E) ∈ M₁) (hb1 x)).mpr
      (hθ1 _ (hφ1 _))
  · show ((θ.symm (φ' (β.φ2 x)) : ↥(M₁ ⊔ M₂)) : E) ∈ M₂
    exact (congrArg (fun z => ((θ.symm (φ' z) : ↥(M₁ ⊔ M₂)) : E) ∈ M₂) (hb2 x)).mpr
      (hθ2 _ (hφ2 _))

theorem burnsideF48s_qe_of_match_or {E X : Type} [Group E] [Finite E] [Group X]
    {M₁ M₂ : Subgroup E} {A B : Subgroup X} {m : ℕ} (hM : burnsideF48s_Match A B m)
    (θ : ↥(M₁ ⊔ M₂) ≃* ↥(A ⊔ B))
    (hθ : ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A))
    {Y : Type} [Group Y] [Finite Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall m) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48s_qe_of_match hM θ h1 h2 β hβ hs
  · exact burnsideF48s_qe_of_match (burnsideF48s_match_swap hM)
      (θ.trans (MulEquiv.subgroupCongr (sup_comm A B))) h1 h2 β hβ hs

end CFSG.ASVolI
