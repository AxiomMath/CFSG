module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3Wr
public import CFSG.Quasithin.Background.G116IIIFStar
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

section Abstract

theorem genFittingFStar_map_eq_of_isL3_prod {Γ : Type} [Group Γ] [Finite Γ] {A Y : Subgroup Γ}
    {X : Type} [Group X] (hX : IsL3 X 1) (φ : ↥A ≃* X × X) (hAY : A ≤ Y)
    (hN : Y ≤ normalizer (A : Set Γ))
    (hC : ∀ y ∈ Y, (∀ a ∈ A, y * a = a * y) → y = 1) :
    (genFittingFStar ↥Y).map Y.subtype = A := by
  obtain ⟨H₁, H₂, hH₁A, hH₂A, hsup, -, hL₁, hL₂, hn₁, hn₂, -⟩ := s16c7_components hX φ
  have hAnorm : (A.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAY).2 hN
  have hcomp : ∀ H : Subgroup Γ, H ≤ A → (∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H) → IsL3 ↥H 1 →
      IsComponentOf (H.subgroupOf Y) ⊤ := by
    intro H hHA hHn hHL
    have hHn' : (H.subgroupOf A).Normal :=
      ⟨fun x hx b => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        simpa using hHn (b : Γ) b.2 (x : Γ) hx⟩
    have hsub : IsSubnormal H Y :=
      IsSubnormal.step hHA hHn' (IsSubnormal.step hAY hAnorm (IsSubnormal.refl Y))
    exact (isComponentOf_iff_subgroupOf.1
      ⟨hHA.trans hAY, hsub, s16c7_isQuasisimple_of_isL3 hHL⟩).2
  have hc₁ := hcomp H₁ hH₁A hn₁ hL₁
  have hc₂ := hcomp H₂ hH₂A hn₂ hL₂
  have hC' : ∀ g : ↥Y, (∀ a ∈ H₁.subgroupOf Y, g * a = a * g) →
      (∀ b ∈ H₂.subgroupOf Y, g * b = b * g) → g = 1 := by
    intro g h1 h2
    apply Subtype.ext
    have hcent : H₁ ⊔ H₂ ≤ Subgroup.centralizer ({(g : Γ)} : Set Γ) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (congrArg Subtype.val (h1 ⟨a, hAY (hH₁A ha)⟩ ha)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (congrArg Subtype.val (h2 ⟨a, hAY (hH₂A ha)⟩ ha)).symm
    refine hC g g.2 fun a ha => ?_
    rw [← hsup] at ha
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hcent ha)).symm
  rw [CFSG.Quasithin.G11.genFittingFStar_eq_sup_of_components hc₁ hc₂ hC', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le (hH₁A.trans hAY),
    Subgroup.map_subgroupOf_eq_of_le (hH₂A.trans hAY), hsup]

end Abstract

section Model

theorem L3Wreath_centralizer_eq_one {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) :
    ∀ y : MulAut V, (∀ a ∈ H, y * a = a * y) → y = 1 := by
  obtain ⟨e, he⟩ := exists_model hreal
  intro y hy
  refine congrHom_injective e ?_
  rw [map_one]
  refine eq_one_of_commute (ψ := congrHom e y) fun g => ?_
  have hg : rho g ∈ H.map (congrHom e) := by
    rw [he]
    exact MonoidHom.mem_range.2 ⟨g, rfl⟩
  obtain ⟨a, haH, hag⟩ := hg
  have h1 : congrHom e (y * a) = congrHom e (a * y) := by rw [hy a haH]
  rw [map_mul, map_mul, hag] at h1
  exact h1

theorem L3Wreath_fstar_eq {V : Type} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) {X : Type} [Group X] (hX : IsL3 X 1)
    (φ : ↥H ≃* X × X) : (genFittingFStar ↥M).map M.subtype = H :=
  genFittingFStar_map_eq_of_isL3_prod hX φ hHM hMN
    (fun y _ hy => L3Wreath_centralizer_eq_one hreal y hy)

end Model

section Cases

variable {G : Type} [Group G] [Finite G]

theorem fstarBar_eq_lBar_of_case167_7 (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h151 : Hyp151 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥)
    (h7 : Case167_7 D V₀ V hV L) : fstarBar D.M V₀ V hV = lBar V₀ V hV L := by
  obtain ⟨X, _, hX, ⟨φ⟩⟩ := h7.1
  obtain ⟨K, _, hfin, hK, hmodel⟩ := h7.2.1
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hT := tensorNat_realizes_zmod_two hK2 hmodel
  have hnorm := Mbar_le_normalizer_lBar_of_tensor D hV h151 hne hT
  have hLM : barSub V₀ V hV L ≤ Mbar D.M V₀ V hV := by
    intro φ hφ
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L φ).1 hφ
    exact (mem_barSub V₀ V hV D.M _).2 ⟨g, h151.le hgL, rfl⟩
  exact L3Wreath_fstar_eq hT hLM hnorm hX φ

theorem case167_7F_of_case167_7 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h151 : Hyp151 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (h7 : Case167_7 D V₀ V hV L) :
    Case167_7F D V₀ V hV := by
  have h := fstarBar_eq_lBar_of_case167_7 D h151 hne h7
  unfold Case167_7F
  rw [h]
  exact h7

theorem concl167F_of_concl167 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h151 : Hyp151 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (h : Concl167 D V₀ V hV L) :
    Concl167F D V₀ V hV L := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (case167_7F_of_case167_7 D h151 hne h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

end Cases

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
